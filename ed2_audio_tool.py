#!/usr/bin/env python3
"""
ED2 DOS Mod Tool

Reverse-engineering-oriented editor for the Korean DOS release of
Dragon Slayer: The Legend of Heroes II.

Supported:
- MON/M_*.DLL: NE module monster record editor (safe in-place fields + CSV)
- BGM/*.INS: 28-byte instrument record editor (named OPL-style fields + raw-safe values)
- BGM/*.MUS: exact compiled-ROL parser/editor (note, instrument, volume, pitch, tempo)
- VGM/VGZ (YM3812): direct conversion to new ED2 MUS + INS, including rhythm mode

Only Python's standard library is required.
"""
from __future__ import annotations

import argparse
import ast
import csv
import gzip
import math
import json
from decimal import Decimal, InvalidOperation, ROUND_HALF_UP
import os
import shutil
import struct
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Optional

APP_NAME = "ED2 Audio & Legacy Tool"
VERSION = "0.6.7"


class FormatError(Exception):
    pass


def u16(data: bytes | bytearray, off: int) -> int:
    return struct.unpack_from("<H", data, off)[0]


def p16(data: bytearray, off: int, value: int) -> None:
    if not 0 <= value <= 0xFFFF:
        raise ValueError("16-bit value must be 0..65535")
    struct.pack_into("<H", data, off, value)


def parse_int(text: str, bits: int = 16) -> int:
    value = int(text.strip(), 0)
    maxv = (1 << bits) - 1
    if not 0 <= value <= maxv:
        raise ValueError(f"value must be 0..{maxv}")
    return value


def backup_once(path: Path) -> Path:
    backup = path.with_name(path.name + ".bak")
    if not backup.exists():
        shutil.copy2(path, backup)
    return backup


def atomic_write(path: Path, data: bytes, make_backup: bool = True) -> None:
    if make_backup:
        backup_once(path)
    fd, tmp_name = tempfile.mkstemp(prefix=path.name + ".", suffix=".tmp", dir=str(path.parent))
    try:
        with os.fdopen(fd, "wb") as f:
            f.write(data)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp_name, path)
    except Exception:
        try:
            os.unlink(tmp_name)
        except OSError:
            pass
        raise


# ---------------------------------------------------------------------------
# MON DLL support
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class NESegment:
    index: int
    file_offset: int
    length: int
    flags: int
    min_alloc: int


def parse_ne_segments(data: bytes) -> list[NESegment]:
    if len(data) < 0x40 or data[:2] != b"MZ":
        raise FormatError("not an MZ executable")
    ne_off = struct.unpack_from("<I", data, 0x3C)[0]
    if ne_off + 0x40 > len(data) or data[ne_off:ne_off + 2] != b"NE":
        raise FormatError("not an NE executable/module")

    seg_count = u16(data, ne_off + 0x1C)
    seg_table_rel = u16(data, ne_off + 0x22)
    align_shift = u16(data, ne_off + 0x32)
    seg_table = ne_off + seg_table_rel
    if seg_table + seg_count * 8 > len(data):
        raise FormatError("truncated NE segment table")

    result: list[NESegment] = []
    for i in range(seg_count):
        sector, length, flags, min_alloc = struct.unpack_from("<HHHH", data, seg_table + i * 8)
        file_offset = sector << align_shift
        real_length = 65536 if length == 0 else length
        if file_offset > len(data):
            raise FormatError("NE segment points outside file")
        result.append(NESegment(i + 1, file_offset, real_length, flags, min_alloc))
    return result


def decode_mon_name(field: bytes) -> str:
    # Real monster names in the supplied Korean DOS files end with 0x06.
    if b"\x06" in field:
        raw = field[:field.index(0x06)]
    elif b"\x00" in field:
        raw = field[:field.index(0x00)]
    else:
        raw = field
    if not raw:
        return ""
    for enc in ("cp949", "euc-kr"):
        try:
            return raw.decode(enc)
        except UnicodeDecodeError:
            pass
    return raw.decode("latin1", errors="replace")


def encode_mon_name(name: str) -> bytes:
    raw = name.encode("cp949")
    if len(raw) > 15:
        raise ValueError("monster name is too long: CP949 encoded name must be <= 15 bytes")
    return raw + b"\x06" + b"\x00" * (15 - len(raw))


def is_monster_record(record: bytes) -> bool:
    if len(record) != 64:
        return False
    name_field = record[48:64]
    if 0x06 not in name_field:
        return False
    name = decode_mon_name(name_field).strip()
    if not name:
        return False
    hp_cur = u16(record, 4)
    hp_max = u16(record, 6)
    # Static records in this game initialize current and maximum HP together.
    # Requiring equality strongly rejects code/dialogue bytes after short boss tables.
    return hp_cur > 0 and hp_cur == hp_max


@dataclass
class MonsterRecord:
    dll_path: Path
    segment_index: int
    segment_offset: int
    slot: int
    file_offset: int
    raw: bytearray

    @property
    def name(self) -> str:
        return decode_mon_name(bytes(self.raw[48:64]))

    def get_u16(self, off: int) -> int:
        return u16(self.raw, off)

    def get_u8(self, off: int) -> int:
        return self.raw[off]


MON_BASIC_FIELDS = [
    ("record_id", "Record/slot reference (partially decoded)", 0x00, 2),
    ("level", "Monster level", 0x03, 1),
    ("hp_current", "Current HP", 0x04, 2),
    ("hp_max", "Max HP", 0x06, 2),
    ("unknown_08", "Unknown byte 08", 0x08, 1),
    ("unknown_09", "Unknown byte 09", 0x09, 1),
    ("attack", "Attack", 0x0A, 2),
    ("exp", "Raw EXP field", 0x0C, 2),
    ("gold", "Raw Gold field", 0x0E, 2),
    ("defense", "Defense", 0x10, 2),
    ("magic", "Magic", 0x12, 2),
]

def find_monster_table(data: bytes) -> tuple[NESegment, int]:
    best: Optional[tuple[NESegment, int]] = None
    for seg in parse_ne_segments(data):
        count = 0
        # The supplied files use a maximum of four battle slots. Capping at 4
        # avoids misidentifying later event data that happens to resemble a record.
        for slot in range(4):
            off = seg.file_offset + slot * 64
            if off + 64 > min(len(data), seg.file_offset + seg.length):
                break
            if not is_monster_record(data[off:off + 64]):
                break
            count += 1
        if count and (best is None or count > best[1]):
            best = (seg, count)
    if best is None:
        raise FormatError("no safe monster table found in NE segments")
    return best


def load_monsters(path: Path) -> list[MonsterRecord]:
    data = path.read_bytes()
    seg, count = find_monster_table(data)
    records: list[MonsterRecord] = []
    for slot in range(count):
        off = seg.file_offset + slot * 64
        records.append(MonsterRecord(path, seg.index, seg.file_offset, slot, off, bytearray(data[off:off + 64])))
    return records


def patch_monster(path: Path, slot: int, values: dict[str, int | str], make_backup: bool = True) -> None:
    data = bytearray(path.read_bytes())
    records = load_monsters(path)
    if not 0 <= slot < len(records):
        raise ValueError("monster slot out of range")
    rec = records[slot]
    base = rec.file_offset

    if "name" in values:
        data[base + 48:base + 64] = encode_mon_name(str(values["name"]))

    for key, _label, off, size in MON_BASIC_FIELDS:
        if key not in values:
            continue
        val = int(values[key])
        if size == 1:
            if not 0 <= val <= 255:
                raise ValueError(f"{key}: 0..255 required")
            data[base + off] = val
        else:
            if not 0 <= val <= 65535:
                raise ValueError(f"{key}: 0..65535 required")
            p16(data, base + off, val)

    if "advanced_hex" in values:
        rawhex = str(values["advanced_hex"]).replace(" ", "").replace("\n", "")
        adv = bytes.fromhex(rawhex)
        if len(adv) != 28:  # 0x14..0x2F
            raise ValueError("advanced_hex must contain exactly 28 bytes (offsets 0x14..0x2F)")
        data[base + 0x14:base + 0x30] = adv

    # Re-check the record before committing.
    if not is_monster_record(bytes(data[base:base + 64])):
        raise ValueError("edited record failed safety validation (HP must be nonzero/equal and name must be valid)")
    atomic_write(path, bytes(data), make_backup=make_backup)



def stored_exp_to_actual(stored: int) -> int:
    """Compatibility helper: v0.6 exposes the raw DLL EXP field unchanged."""
    if not 0 <= stored <= 0xFFFF:
        raise ValueError("raw EXP must be 0..65535")
    return stored


def actual_exp_to_stored(actual: int) -> int:
    """Compatibility helper: v0.6 stores the raw DLL EXP field unchanged."""
    if not 0 <= actual <= 0xFFFF:
        raise ValueError("raw EXP must be 0..65535")
    return actual


MON_BULK_FIELDS = {
    "hp": ("HP (current + max)", (0x04, 0x06), 1, 65535),
    "attack": ("Attack", (0x0A,), 0, 65535),
    "exp": ("Raw EXP field", (0x0C,), 0, 65535),
    "gold": ("Gold", (0x0E,), 0, 65535),
    "defense": ("Defense", (0x10,), 0, 65535),
    "magic": ("Magic", (0x12,), 0, 65535),
}


def parse_bulk_expression(expression: str) -> tuple[str, Decimal]:
    """Parse compact balance expressions such as +10, -5, *1.5, /2, =100."""
    text = expression.strip().replace(" ", "")
    if len(text) < 2 or text[0] not in "+-*/=":
        raise ValueError("expression must look like +10, -20, *1.5, /2, =100, or a formula using x")
    op = text[0]
    try:
        operand = Decimal(text[1:])
    except InvalidOperation as e:
        raise ValueError("invalid numeric operand in bulk expression") from e
    if not operand.is_finite():
        raise ValueError("bulk operand must be a finite number")
    if op == "/" and operand == 0:
        raise ValueError("division by zero is not allowed")
    return op, operand


def _evaluate_bulk_operation(value: int, op: str, operand: Decimal) -> Decimal:
    current = Decimal(value)
    if op == "+":
        return current + operand
    if op == "-":
        return current - operand
    if op == "*":
        return current * operand
    if op == "/":
        return current / operand
    return operand  # =


# Safe formula evaluator for bulk balance edits.  Deliberately no eval().
_BULK_FORMULA_FUNCS = {
    "log": math.log,
    "ln": math.log,
    "log10": math.log10,
    "log2": math.log2,
    "log1p": math.log1p,
}


def _eval_bulk_formula_node(node: ast.AST, x: float) -> float:
    if isinstance(node, ast.Expression):
        return _eval_bulk_formula_node(node.body, x)
    if isinstance(node, ast.Constant) and isinstance(node.value, (int, float)) and not isinstance(node.value, bool):
        return float(node.value)
    if isinstance(node, ast.Name):
        if node.id.lower() == "x":
            return float(x)
        if node.id.lower() == "e":
            return math.e
        raise ValueError(f"unknown formula name: {node.id}")
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.UAdd, ast.USub)):
        v = _eval_bulk_formula_node(node.operand, x)
        return v if isinstance(node.op, ast.UAdd) else -v
    if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Add, ast.Sub, ast.Mult, ast.Div, ast.Pow)):
        a = _eval_bulk_formula_node(node.left, x)
        b = _eval_bulk_formula_node(node.right, x)
        if isinstance(node.op, ast.Add):
            return a + b
        if isinstance(node.op, ast.Sub):
            return a - b
        if isinstance(node.op, ast.Mult):
            return a * b
        if isinstance(node.op, ast.Div):
            if b == 0:
                raise ValueError("division by zero in formula")
            return a / b
        if abs(b) > 32:
            raise ValueError("formula exponent magnitude must be <= 32")
        return a ** b
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
        name = node.func.id.lower()
        fn = _BULK_FORMULA_FUNCS.get(name)
        if fn is None:
            raise ValueError(f"unsupported function: {node.func.id}")
        if node.keywords:
            raise ValueError("formula functions do not accept keyword arguments")
        if name in ("log", "ln"):
            if len(node.args) not in (1, 2):
                raise ValueError("log() accepts log(x) or log(x, base)")
            args = [_eval_bulk_formula_node(a, x) for a in node.args]
            if args[0] <= 0:
                raise ValueError("log() requires a value > 0; use log1p(x) when zero is possible")
            if len(args) == 2 and (args[1] <= 0 or args[1] == 1):
                raise ValueError("log() base must be > 0 and not 1")
            return math.log(*args)
        if len(node.args) != 1:
            raise ValueError(f"{name}() accepts exactly one argument")
        arg = _eval_bulk_formula_node(node.args[0], x)
        if name in ("log10", "log2") and arg <= 0:
            raise ValueError(f"{name}() requires a value > 0; use log1p(x) when zero is possible")
        if name == "log1p" and arg <= -1:
            raise ValueError("log1p() requires a value > -1")
        return fn(arg)
    raise ValueError("formula may only use x, numbers, + - * / **, and log/ln/log10/log2/log1p")


def evaluate_bulk_formula(value: int, expression: str) -> float:
    try:
        tree = ast.parse(expression.strip(), mode="eval")
    except SyntaxError as e:
        raise ValueError("invalid balance formula") from e
    result = _eval_bulk_formula_node(tree, float(value))
    if not math.isfinite(result):
        raise ValueError("formula result must be finite")
    return result


def _looks_like_formula(expression: str) -> bool:
    text = expression.strip().lower()
    return "x" in text or "(" in text or text.startswith(("ln", "log10", "log2", "log1p"))


def parse_bulk_rule(expression: str) -> tuple[str, str | None, Decimal | None]:
    """Classify a compact arithmetic rule, safe formula, or progression ramp.

    Examples:
      +10, *1.5
      log10(x)*100, x + log2(x)*20, log1p(x)*50
      ramp*1.5

    v0.4.x compatibility: log*1.5 remains an alias for ramp*1.5.
    """
    raw = expression.strip()
    compact = raw.replace(" ", "")
    lower = compact.lower()
    if _looks_like_formula(raw):
        try:
            evaluate_bulk_formula(10, raw)
        except ValueError as e:
            # A formula can be syntactically valid while the probe value falls
            # outside its log domain, e.g. log(x-20).
            if "requires a value" not in str(e):
                raise
        return "formula", None, None

    progressive = False
    if lower.startswith("ramp"):
        compact = compact[4:]
        progressive = True
    elif lower.startswith("log") and len(compact) > 3 and compact[3] in "+-*/=":
        compact = compact[3:]
        progressive = True
    if progressive and not compact:
        raise ValueError("ramp expression must look like ramp*1.5 or ramp+100")
    op, operand = parse_bulk_expression(compact)
    return ("ramp" if progressive else "arithmetic"), op, operand


def progression_log_weight(index: int, count: int, curvature: float = 9.0) -> float:
    """0..1 late-game logarithmic ramp based on MON DLL order."""
    if count <= 1:
        return 1.0
    p = max(0.0, min(1.0, index / (count - 1)))
    return 1.0 - math.log1p(curvature * (1.0 - p)) / math.log1p(curvature)


def apply_bulk_rule(
    value: int, expression: str, minimum: int, maximum: int,
    progression_index: int = 0, progression_count: int = 1,
) -> tuple[int, bool]:
    mode, op, operand = parse_bulk_rule(expression)
    if mode == "formula":
        result_float = evaluate_bulk_formula(value, expression)
        rounded = int(Decimal(str(result_float)).quantize(Decimal("1"), rounding=ROUND_HALF_UP))
    else:
        assert op is not None and operand is not None
        target = _evaluate_bulk_operation(value, op, operand)
        result = target
        if mode == "ramp":
            weight = Decimal(str(progression_log_weight(progression_index, progression_count)))
            result = Decimal(value) + (target - Decimal(value)) * weight
        rounded = int(result.quantize(Decimal("1"), rounding=ROUND_HALF_UP))
    clamped = rounded < minimum or rounded > maximum
    return max(minimum, min(maximum, rounded)), clamped


def apply_bulk_expression(value: int, expression: str, minimum: int, maximum: int) -> tuple[int, bool]:
    """Apply a bulk rule without MON progression context."""
    mode, _op, _operand = parse_bulk_rule(expression)
    if mode == "ramp":
        raise ValueError("ramp expressions require MON progression context")
    return apply_bulk_rule(value, expression, minimum, maximum)


def bulk_adjust_monsters(root: Path, field: str, expression: str, make_backup: bool = True) -> dict[str, int]:
    """Apply one rule to one safe stat across all monsters.

    EXP is calculated in player-visible reward units: stored 5 is x=4, and a
    desired result of 10 is encoded back to stored 11. Stored zero remains the
    game's zero-reward special case.
    """
    key = field.strip().lower()
    if key not in MON_BULK_FIELDS:
        allowed = ", ".join(MON_BULK_FIELDS)
        raise ValueError(f"unknown bulk field '{field}'. Allowed: {allowed}")
    _label, offsets, minimum, maximum = MON_BULK_FIELDS[key]
    parse_bulk_rule(expression)

    mon_dir = root / "MON"
    if not mon_dir.is_dir():
        raise FileNotFoundError(f"MON folder not found: {mon_dir}")

    valid_files: list[tuple[Path, list[MonsterRecord]]] = []
    for path in sorted(mon_dir.glob("M_*.DLL")):
        try:
            recs = load_monsters(path)
        except Exception:
            continue
        valid_files.append((path, recs))

    files_scanned = len(valid_files)
    files_changed = 0
    records_scanned = 0
    records_changed = 0
    clamped_values = 0

    for file_index, (path, recs) in enumerate(valid_files):
        data = bytearray(path.read_bytes())
        changed_this_file = False
        for rec in recs:
            records_scanned += 1
            base = rec.file_offset
            raw_source = u16(data, base + offsets[0])
            source = stored_exp_to_actual(raw_source) if key == "exp" else raw_source
            new_value, was_clamped = apply_bulk_rule(
                source, expression, minimum, maximum, file_index, files_scanned
            )
            if was_clamped:
                clamped_values += 1
            stored_new = actual_exp_to_stored(new_value) if key == "exp" else new_value
            record_changed = False
            for off in offsets:
                old = u16(data, base + off)
                if old != stored_new:
                    p16(data, base + off, stored_new)
                    record_changed = True
            if record_changed:
                if not is_monster_record(bytes(data[base:base + 64])):
                    raise ValueError(f"{path.name} slot {rec.slot}: bulk edit failed safety validation")
                records_changed += 1
                changed_this_file = True
        if changed_this_file:
            atomic_write(path, bytes(data), make_backup=make_backup)
            files_changed += 1

    return {
        "files_scanned": files_scanned,
        "files_changed": files_changed,
        "records_scanned": records_scanned,
        "records_changed": records_changed,
        "clamped_values": clamped_values,
    }


def iter_monster_rows(root: Path) -> Iterable[dict[str, object]]:
    mon_dir = root / "MON"
    for path in sorted(mon_dir.glob("M_*.DLL")):
        try:
            recs = load_monsters(path)
        except Exception:
            continue
        for rec in recs:
            row: dict[str, object] = {
                "dll": path.name,
                "slot": rec.slot,
                "name": rec.name,
            }
            for key, _label, off, size in MON_BASIC_FIELDS:
                raw_value = rec.get_u8(off) if size == 1 else rec.get_u16(off)
                if key == "exp":
                    row["exp_stored"] = raw_value
                    row["exp_actual"] = stored_exp_to_actual(raw_value)
                else:
                    row[key] = raw_value
            row["advanced_hex"] = bytes(rec.raw[0x14:0x30]).hex(" ")
            yield row


def export_mon_csv(root: Path, out_path: Path) -> int:
    rows = list(iter_monster_rows(root))
    fields = ["dll", "slot", "name"]
    for key, _label, _off, _size in MON_BASIC_FIELDS:
        if key == "exp":
            fields.extend(["exp_stored", "exp_actual"])
        else:
            fields.append(key)
    fields.append("advanced_hex")
    with out_path.open("w", newline="", encoding="utf-8-sig") as f:
        w = csv.DictWriter(f, fieldnames=fields)
        w.writeheader()
        w.writerows(rows)
    return len(rows)


def import_mon_csv(root: Path, csv_path: Path) -> int:
    patched = 0
    with csv_path.open("r", newline="", encoding="utf-8-sig") as f:
        rows = list(csv.DictReader(f))
    by_file: dict[str, list[dict[str, str]]] = {}
    for row in rows:
        by_file.setdefault(row["dll"], []).append(row)

    for dll, file_rows in by_file.items():
        path = root / "MON" / dll
        if not path.is_file():
            raise FileNotFoundError(f"missing DLL referenced by CSV: {dll}")
        data = bytearray(path.read_bytes())
        recs = load_monsters(path)
        changed = False
        for row in file_rows:
            slot = int(row["slot"], 0)
            if not 0 <= slot < len(recs):
                raise ValueError(f"{dll}: slot {slot} is not a detected monster record")
            rec = recs[slot]
            base = rec.file_offset
            name = row.get("name", "")
            if name:
                data[base + 48:base + 64] = encode_mon_name(name)
            for key, _label, off, size in MON_BASIC_FIELDS:
                if key == "exp":
                    # New CSVs expose both the raw DLL value and the actual in-game reward.
                    # Prefer exp_actual when present. Legacy CSVs with only `exp` still import raw.
                    actual_text = row.get("exp_actual", "")
                    stored_text = row.get("exp_stored", "")
                    legacy_text = row.get("exp", "")
                    if actual_text is not None and actual_text.strip() != "":
                        actual = int(actual_text, 0)
                        val = actual_exp_to_stored(actual)
                    elif stored_text is not None and stored_text.strip() != "":
                        val = int(stored_text, 0)
                    elif legacy_text is not None and legacy_text.strip() != "":
                        val = int(legacy_text, 0)
                    else:
                        continue
                    if not 0 <= val <= 65535:
                        raise ValueError(f"{dll} slot {slot} exp: out of range")
                    p16(data, base + off, val)
                    continue

                text = row.get(key, "")
                if text is None or text.strip() == "":
                    continue
                val = int(text, 0)
                if size == 1:
                    if not 0 <= val <= 255:
                        raise ValueError(f"{dll} slot {slot} {key}: out of range")
                    data[base + off] = val
                else:
                    if not 0 <= val <= 65535:
                        raise ValueError(f"{dll} slot {slot} {key}: out of range")
                    p16(data, base + off, val)
            adv_text = row.get("advanced_hex", "").strip()
            if adv_text:
                adv = bytes.fromhex(adv_text)
                if len(adv) != 28:
                    raise ValueError(f"{dll} slot {slot}: advanced_hex must be exactly 28 bytes")
                data[base + 0x14:base + 0x30] = adv
            if not is_monster_record(bytes(data[base:base + 64])):
                raise ValueError(f"{dll} slot {slot}: edited record failed safety validation")
            changed = True
            patched += 1
        if changed:
            atomic_write(path, bytes(data), make_backup=True)
    return patched


# ---------------------------------------------------------------------------
# INS support
# ---------------------------------------------------------------------------

INS_FIELDS = [
    ("mod_ksl", "Mod KSL", 0, "0..3"),
    ("mod_multiple", "Mod MULT", 1, "0..15"),
    ("mod_feedback", "Mod feedback", 2, "0..7"),
    ("mod_attack", "Mod attack", 3, "0..15"),
    ("mod_sustain", "Mod sustain level", 4, "0..15"),
    ("mod_eg", "Mod sustain/EG flag", 5, "0..1"),
    ("mod_decay", "Mod decay", 6, "0..15"),
    ("mod_release", "Mod release", 7, "0..15"),
    ("mod_total_level", "Mod total level (higher=quieter)", 8, "0..63"),
    ("mod_am", "Mod tremolo", 9, "0..1"),
    ("mod_vib", "Mod vibrato", 10, "0..1"),
    ("mod_ksr", "Mod KSR", 11, "0..1"),
    ("mod_connection", "Mod connection", 12, "0..1"),
    ("car_ksl", "Carrier KSL", 13, "0..3"),
    ("car_multiple", "Carrier MULT", 14, "0..15"),
    ("car_feedback_raw", "Carrier feedback/raw (normally ignored)", 15, "0..255"),
    ("car_attack", "Carrier attack", 16, "0..15"),
    ("car_sustain", "Carrier sustain level", 17, "0..15"),
    ("car_eg", "Carrier sustain/EG flag", 18, "0..1"),
    ("car_decay", "Carrier decay", 19, "0..15"),
    ("car_release", "Carrier release", 20, "0..15"),
    ("car_total_level", "Carrier total level (higher=quieter)", 21, "0..63"),
    ("car_am", "Carrier tremolo", 22, "0..1"),
    ("car_vib", "Carrier vibrato", 23, "0..1"),
    ("car_ksr", "Carrier KSR", 24, "0..1"),
    ("car_connection", "Carrier connection/raw", 25, "0..1"),
    ("mod_wave", "Mod waveform", 26, "0..3"),
    ("car_wave", "Carrier waveform", 27, "0..3"),
]

# Expected ranges for a conventional 2-operator OPL timbre. The DOS files also
# contain extended/percussion records with out-of-range bytes; those are preserved.
INS_STANDARD_RANGES = {
    0: (0, 3), 1: (0, 15), 2: (0, 7), 3: (0, 15), 4: (0, 15), 5: (0, 1),
    6: (0, 15), 7: (0, 15), 8: (0, 63), 9: (0, 1), 10: (0, 1), 11: (0, 1), 12: (0, 1),
    13: (0, 3), 14: (0, 15),
    # 15 is carrier feedback and may be arbitrary/ignored.
    16: (0, 15), 17: (0, 15), 18: (0, 1), 19: (0, 15), 20: (0, 15), 21: (0, 63),
    22: (0, 1), 23: (0, 1), 24: (0, 1), 25: (0, 1), 26: (0, 3), 27: (0, 3),
}


def load_ins(path: Path) -> list[bytearray]:
    data = path.read_bytes()
    if len(data) < 2:
        raise FormatError("INS file too short")
    count = u16(data, 0)
    expected = 2 + count * 28
    if expected != len(data):
        raise FormatError(f"INS size mismatch: header count={count}, expected {expected} bytes, got {len(data)}")
    return [bytearray(data[2 + i * 28:2 + (i + 1) * 28]) for i in range(count)]


def ins_is_standard(record: bytes | bytearray) -> bool:
    return all(lo <= record[pos] <= hi for pos, (lo, hi) in INS_STANDARD_RANGES.items())


def save_ins_record(path: Path, index: int, record: bytes | bytearray, make_backup: bool = True) -> None:
    if len(record) != 28:
        raise ValueError("INS record must be exactly 28 bytes")
    data = bytearray(path.read_bytes())
    count = u16(data, 0)
    if len(data) != 2 + 28 * count or not 0 <= index < count:
        raise FormatError("invalid INS file/index")
    data[2 + index * 28:2 + (index + 1) * 28] = bytes(record)
    atomic_write(path, bytes(data), make_backup=make_backup)


def export_ins_csv(root: Path, out_path: Path) -> int:
    bgm = root / "BGM"
    rows: list[dict[str, object]] = []
    for path in sorted(bgm.glob("*.INS")):
        try:
            recs = load_ins(path)
        except Exception:
            continue
        for i, rec in enumerate(recs):
            row: dict[str, object] = {
                "ins": path.name,
                "index": i,
                "kind": "standard-opl" if ins_is_standard(rec) else "extended-or-percussion",
            }
            for key, _label, pos, _rng in INS_FIELDS:
                row[key] = rec[pos]
            row["raw_hex"] = bytes(rec).hex(" ")
            rows.append(row)
    fields = ["ins", "index", "kind"] + [x[0] for x in INS_FIELDS] + ["raw_hex"]
    with out_path.open("w", newline="", encoding="utf-8-sig") as f:
        w = csv.DictWriter(f, fieldnames=fields)
        w.writeheader()
        w.writerows(rows)
    return len(rows)


# ---------------------------------------------------------------------------
# MUS support (AdLib compiled-ROL structure, reverse engineered from ED2)
# ---------------------------------------------------------------------------

MUS_VOICE_SLOTS = 11
MUS_FIXED_HEADER = 97
MUS_BASE_PITCH = 0x1FFF
MUS_MAX_PITCH = 0x3FFE  # 14-bit ROL bend word; retail center is 0x1FFF


@dataclass
class MusHeader:
    track_count: int
    totals: list[int]
    header_end: int


@dataclass(frozen=True)
class MusTempoEvent:
    time: int
    percent: int


@dataclass(frozen=True)
class MusTimedByteEvent:
    time: int
    value: int


@dataclass(frozen=True)
class MusPitchEvent:
    time: int
    value: int


@dataclass
class MusTrackData:
    notes: list[tuple[int, int, int]]  # (file_offset, note, duration)
    instruments: list[MusTimedByteEvent]
    volumes: list[MusTimedByteEvent]
    pitches: list[MusPitchEvent]
    note_start: int
    note_end: int


@dataclass
class MusFileData:
    active_voices: int
    totals: list[int]
    instrument_counts: list[int]
    volume_counts: list[int]
    pitch_counts: list[int]
    ticks_per_beat: int
    beats_per_measure: int
    base_tempo: int
    tempo_events: list[MusTempoEvent]
    tracks: list[MusTrackData]
    data_start: int
    end_offset: int


def parse_mus(data: bytes) -> MusFileData:
    if len(data) < MUS_FIXED_HEADER:
        raise FormatError("MUS file too short")
    active = data[0]
    if active not in (9, 11):
        raise FormatError(f"unexpected MUS voice count byte: {active} (expected 9 or 11)")

    totals = [u16(data, 1 + i * 2) for i in range(MUS_VOICE_SLOTS)]
    inst_counts = [u16(data, 23 + i * 2) for i in range(MUS_VOICE_SLOTS)]
    vol_counts = [u16(data, 45 + i * 2) for i in range(MUS_VOICE_SLOTS)]
    pitch_counts = [u16(data, 67 + i * 2) for i in range(MUS_VOICE_SLOTS)]
    ticks_per_beat = u16(data, 89)
    beats_per_measure = u16(data, 91)
    base_tempo = u16(data, 93)
    tempo_count = u16(data, 95)
    if ticks_per_beat == 0 or base_tempo == 0:
        raise FormatError("invalid MUS timing header (ticks/beat and tempo must be nonzero)")

    pos = 97
    tempo_events: list[MusTempoEvent] = []
    for _ in range(tempo_count):
        if pos + 4 > len(data):
            raise FormatError("truncated MUS tempo stream")
        tempo_events.append(MusTempoEvent(u16(data, pos), u16(data, pos + 2)))
        pos += 4
    if not tempo_events:
        # Older/odd files are treated as a constant 100% tempo stream.
        tempo_events = [MusTempoEvent(0, 100)]
    data_start = pos

    tracks: list[MusTrackData] = []
    for ch in range(MUS_VOICE_SLOTS):
        note_start = pos
        note_events: list[tuple[int, int, int]] = []
        elapsed = 0
        target = totals[ch]
        while elapsed < target:
            if pos + 3 > len(data):
                raise FormatError(f"truncated MUS note stream for voice {ch}")
            off = pos
            note = data[pos]
            dur = u16(data, pos + 1)
            pos += 3
            if note > 127:
                raise FormatError(f"invalid MUS note {note} in voice {ch} at 0x{off:X}")
            if dur == 0:
                raise FormatError(f"zero-duration MUS note in voice {ch} at 0x{off:X}")
            elapsed += dur
            if elapsed > target:
                raise FormatError(f"MUS note durations exceed voice {ch} total ({elapsed}>{target})")
            note_events.append((off, note, dur))
        note_end = pos

        instruments: list[MusTimedByteEvent] = []
        for _ in range(inst_counts[ch]):
            if pos + 3 > len(data):
                raise FormatError(f"truncated MUS instrument stream for voice {ch}")
            instruments.append(MusTimedByteEvent(u16(data, pos), data[pos + 2]))
            pos += 3

        volumes: list[MusTimedByteEvent] = []
        for _ in range(vol_counts[ch]):
            if pos + 3 > len(data):
                raise FormatError(f"truncated MUS volume stream for voice {ch}")
            volumes.append(MusTimedByteEvent(u16(data, pos), data[pos + 2]))
            pos += 3

        pitches: list[MusPitchEvent] = []
        for _ in range(pitch_counts[ch]):
            if pos + 4 > len(data):
                raise FormatError(f"truncated MUS pitch stream for voice {ch}")
            pitches.append(MusPitchEvent(u16(data, pos), u16(data, pos + 2)))
            pos += 4

        tracks.append(MusTrackData(note_events, instruments, volumes, pitches, note_start, note_end))

    if pos != len(data):
        raise FormatError(f"MUS parser ended at 0x{pos:X}, but file size is 0x{len(data):X}")

    return MusFileData(
        active, totals, inst_counts, vol_counts, pitch_counts,
        ticks_per_beat, beats_per_measure, base_tempo,
        tempo_events, tracks, data_start, pos,
    )


def audit_mus_loop_seam(data: bytes) -> dict[str, object]:
    """Report control writes that occur at or after a voice's terminal note tick.

    ED2's OPL driver consumes the control streams independently from the note
    stream. A program/TL/pitch write on the same tick that a voice ends can
    therefore touch a still-releasing operator immediately before the whole
    song restarts. Generated files use this audit as a hard pop-safety check.
    """
    mus = parse_mus(data)
    global_total = max(mus.totals[:mus.active_voices], default=0)
    by_kind = {"instrument": 0, "volume": 0, "pitch": 0}
    events: list[dict[str, int | str]] = []
    zero_total_controls = 0

    for ch in range(mus.active_voices):
        total = mus.totals[ch]
        track = mus.tracks[ch]
        streams = (
            ("instrument", track.instruments),
            ("volume", track.volumes),
            ("pitch", track.pitches),
        )
        for kind, stream in streams:
            for ev in stream:
                if total == 0:
                    zero_total_controls += 1
                    events.append({
                        "channel": ch,
                        "kind": kind,
                        "time": ev.time,
                        "channel_total": total,
                    })
                elif ev.time >= total:
                    by_kind[kind] += 1
                    events.append({
                        "channel": ch,
                        "kind": kind,
                        "time": ev.time,
                        "channel_total": total,
                    })

    return {
        "global_total_ticks": global_total,
        "terminal_control_events": sum(by_kind.values()),
        "terminal_control_events_by_kind": by_kind,
        "zero_total_voice_control_events": zero_total_controls,
        "events": events,
    }


def load_mus_header(data: bytes) -> MusHeader:
    mus = parse_mus(data)
    return MusHeader(mus.active_voices, mus.totals[:mus.active_voices], mus.data_start)


@dataclass(frozen=True)
class MusCandidate:
    target_index: int
    target_total: int
    start: int
    event_count: int
    end: int
    score: float


def scan_mus_candidates(data: bytes, header: MusHeader, max_results: int = 80) -> list[MusCandidate]:
    """Compatibility wrapper: the exact parser now returns one note stream per voice."""
    mus = parse_mus(data)
    out: list[MusCandidate] = []
    for i in range(mus.active_voices):
        track = mus.tracks[i]
        if mus.totals[i] == 0:
            continue
        out.append(MusCandidate(i, mus.totals[i], track.note_start, len(track.notes), track.note_end, 100000.0 - i))
    return out[:max_results]


def read_mus_candidate_events(data: bytes, candidate: MusCandidate) -> list[tuple[int, int, int]]:
    events: list[tuple[int, int, int]] = []
    for i in range(candidate.event_count):
        off = candidate.start + i * 3
        events.append((off, data[off], u16(data, off + 1)))
    return events


def midi_note_name(note: int) -> str:
    if note == 0:
        return "0 / rest"
    names = ("C", "C#", "D", "D#", "E", "F", "F#", "G", "G#", "A", "A#", "B")
    return f"{names[note % 12]}{note // 12 - 1}"


def patch_mus_event(path: Path, offset: int, note: int, duration: int, make_backup: bool = True) -> None:
    if not 0 <= note <= 127:
        raise ValueError("note must be 0..127")
    if not 1 <= duration <= 65535:
        raise ValueError("duration must be 1..65535")
    original = path.read_bytes()
    mus = parse_mus(original)
    data = bytearray(original)
    if offset < 0 or offset + 3 > len(data):
        raise ValueError("event offset outside file")

    owner: Optional[int] = None
    old_duration = u16(data, offset + 1)
    for ch, track in enumerate(mus.tracks):
        if any(off == offset for off, _note, _dur in track.notes):
            owner = ch
            break
    if owner is None:
        raise ValueError("offset is not the start of a parsed MUS note event")

    new_total = mus.totals[owner] - old_duration + duration
    if not 0 <= new_total <= 65535:
        raise ValueError("edited duration would move the voice total outside uint16")
    data[offset] = note
    p16(data, offset + 1, duration)
    p16(data, 1 + owner * 2, new_total)
    # Validate before writing so a bad edit never corrupts the working file.
    parse_mus(bytes(data))
    atomic_write(path, bytes(data), make_backup=make_backup)


def transpose_mus_candidate(path: Path, candidate: MusCandidate, semitones: int, make_backup: bool = True) -> int:
    data = bytearray(path.read_bytes())
    changed = 0
    for off, note, _dur in read_mus_candidate_events(bytes(data), candidate):
        if note == 0:
            continue
        new_note = note + semitones
        if not 1 <= new_note <= 127:
            raise ValueError(f"transpose would move note {note} outside 1..127")
        data[off] = new_note
        changed += 1
    parse_mus(bytes(data))
    atomic_write(path, bytes(data), make_backup=make_backup)
    return changed


def select_mus_track_streams(data: bytes, header: MusHeader) -> list[Optional[MusCandidate]]:
    """Compatibility wrapper used by the MUS GUI."""
    mus = parse_mus(data)
    out: list[Optional[MusCandidate]] = []
    for i in range(mus.active_voices):
        t = mus.tracks[i]
        if mus.totals[i] == 0:
            out.append(None)
        else:
            out.append(MusCandidate(i, mus.totals[i], t.note_start, len(t.notes), t.note_end, 100000.0 - i))
    return out


def build_mus(
    active_voices: int,
    totals: list[int],
    note_tracks: list[list[tuple[int, int]]],
    instrument_tracks: list[list[MusTimedByteEvent]],
    volume_tracks: list[list[MusTimedByteEvent]],
    pitch_tracks: list[list[MusPitchEvent]],
    ticks_per_beat: int = 24,
    beats_per_measure: int = 4,
    base_tempo: int = 150,
    tempo_events: Optional[list[MusTempoEvent]] = None,
) -> bytes:
    if active_voices not in (9, 11):
        raise ValueError("active_voices must be 9 or 11")
    if not 1 <= ticks_per_beat <= 65535 or not 1 <= beats_per_measure <= 65535 or not 1 <= base_tempo <= 65535:
        raise ValueError("invalid MUS timing value")
    tempo_events = list(tempo_events or [MusTempoEvent(0, 100)])
    if not tempo_events:
        tempo_events = [MusTempoEvent(0, 100)]
    if len(tempo_events) > 65535:
        raise ValueError("too many tempo events")

    def padded(seq, factory):
        seq = list(seq)
        while len(seq) < MUS_VOICE_SLOTS:
            seq.append(factory())
        return seq[:MUS_VOICE_SLOTS]

    totals = padded(totals, lambda: 0)
    note_tracks = padded(note_tracks, list)
    instrument_tracks = padded(instrument_tracks, list)
    volume_tracks = padded(volume_tracks, list)
    pitch_tracks = padded(pitch_tracks, list)

    out = bytearray()
    out.append(active_voices)
    for v in totals:
        if not 0 <= v <= 65535:
            raise ValueError("MUS voice total exceeds uint16")
        out += struct.pack("<H", v)
    for tracks in (instrument_tracks, volume_tracks, pitch_tracks):
        for evs in tracks:
            if len(evs) > 65535:
                raise ValueError("too many MUS control events")
            out += struct.pack("<H", len(evs))
    out += struct.pack("<HHHH", ticks_per_beat, beats_per_measure, base_tempo, len(tempo_events))
    for ev in tempo_events:
        out += struct.pack("<HH", ev.time, ev.percent)

    for ch in range(MUS_VOICE_SLOTS):
        elapsed = 0
        for note, dur in note_tracks[ch]:
            if not 0 <= note <= 127 or not 1 <= dur <= 65535:
                raise ValueError(f"invalid MUS note event in voice {ch}")
            out.append(note)
            out += struct.pack("<H", dur)
            elapsed += dur
        if elapsed != totals[ch]:
            raise ValueError(f"voice {ch} note sum {elapsed} != total {totals[ch]}")
        for ev in instrument_tracks[ch]:
            if not 0 <= ev.time <= 65535 or not 0 <= ev.value <= 255:
                raise ValueError("invalid MUS instrument event")
            out += struct.pack("<HB", ev.time, ev.value)
        for ev in volume_tracks[ch]:
            if not 0 <= ev.time <= 65535 or not 0 <= ev.value <= 255:
                raise ValueError("invalid MUS volume event")
            out += struct.pack("<HB", ev.time, ev.value)
        for ev in pitch_tracks[ch]:
            if not 0 <= ev.time <= 65535 or not 0 <= ev.value <= MUS_MAX_PITCH:
                raise ValueError("invalid MUS pitch event")
            out += struct.pack("<HH", ev.time, ev.value)

    # Always self-validate generated files.
    parse_mus(bytes(out))
    return bytes(out)


# ---------------------------------------------------------------------------
# VGM/VGZ -> ED2 INS + MUS import
# ---------------------------------------------------------------------------

OPL_MOD_OFFSETS = (0, 1, 2, 8, 9, 10, 16, 17, 18)
OPL_CAR_OFFSETS = (3, 4, 5, 11, 12, 13, 19, 20, 21)
VGM_SAMPLE_RATE = 44100.0
ED2_DEFAULT_TICKS_PER_BEAT = 24
ED2_DEFAULT_BASE_TEMPO = 150
ED2_DEFAULT_BEATS_PER_MEASURE = 4
ED2_RESTART_GUARD_DEFAULT_TICKS = 12
ED2_VOLUME_MASTER = 114  # recovered from original ED2 MUS volume -> YM3812 TL pairs
OPL_VIBRATO_HZ = 6.10
OPL_VIBRATO_SHALLOW_CENTS = 7.0
OPL_VIBRATO_DEEP_CENTS = 14.0


@dataclass
class VgmNoteSpan:
    channel: int              # logical ED2 voice: 0..10
    physical_channel: int     # YM3812 channel: 0..8
    start_sample: int
    end_sample: int
    midi_note: int
    instrument: bytes
    start_frequency: float
    hardware_vibrato: bool = False
    vibrato_deep: bool = False


@dataclass(frozen=True)
class VgmPitchPoint:
    channel: int
    sample: int
    midi_note: int
    frequency: float


@dataclass(frozen=True)
class VgmVolumePoint:
    channel: int
    sample: int
    volume: int
    output_tl: int


@dataclass
class VgmAnalysis:
    total_samples: int
    ym3812_writes: int
    notes: list[VgmNoteSpan]
    instruments: list[bytes]
    channel_note_counts: list[int]
    channel_dominant_instruments: list[Optional[bytes]]
    loop_sample: Optional[int]
    rhythm_mode: bool
    pitch_points: list[VgmPitchPoint]
    volume_points: list[VgmVolumePoint]
    rhythm_trigger_counts: list[int]

    @property
    def duration_seconds(self) -> float:
        return self.total_samples / VGM_SAMPLE_RATE


def _read_vgm_bytes(path: Path) -> bytes:
    raw = path.read_bytes()
    if raw[:2] == b"\x1f\x8b" or path.suffix.lower() == ".vgz":
        try:
            raw = gzip.decompress(raw)
        except OSError as e:
            raise FormatError(f"cannot decompress VGZ: {e}") from e
    if len(raw) < 0x40 or raw[:4] != b"Vgm ":
        raise FormatError("not a VGM/VGZ file")
    return raw


def _vgm_data_offset(data: bytes) -> int:
    version = struct.unpack_from("<I", data, 0x08)[0]
    if version >= 0x00000150:
        rel = struct.unpack_from("<I", data, 0x34)[0]
        return 0x40 if rel == 0 else 0x34 + rel
    return 0x40


def _vgm_loop_file_offset(data: bytes) -> Optional[int]:
    rel = struct.unpack_from("<I", data, 0x1C)[0]
    return None if rel == 0 else 0x1C + rel


@dataclass(frozen=True)
class VgmTimingHint:
    header_rate_hz: int
    recommended_base_tempo: Optional[int]
    recommended_tick_hz: Optional[float]
    final_wait_samples: int
    last_ym_write_sample: int
    total_samples: int
    recommended_end_trim_ticks: int
    reason: Optional[str]


def inspect_vgm_timing(path: Path, ticks_per_beat: int = ED2_DEFAULT_TICKS_PER_BEAT) -> VgmTimingHint:
    """Recover the source scheduler rate and detect one terminal capture frame.

    VGM captures made from ED2/compiled-ROL playback store the driver update
    rate at header offset 0x24.  They can also end with one complete scheduler
    wait after the final YM3812 write.  That wait belongs to the capture
    container, not the MUS timeline; retaining it lengthens every final note by
    one tick and makes the restart seam differ from the retail file.
    """
    if ticks_per_beat <= 0:
        raise ValueError("ticks_per_beat must be > 0")
    data = _read_vgm_bytes(path)
    rate = struct.unpack_from("<I", data, 0x24)[0] if len(data) >= 0x28 else 0
    pos = _vgm_data_offset(data)
    sample = 0
    last_ym_write_sample = 0
    last_was_wait = False
    final_wait = 0
    final_wait_start = 0

    while pos < len(data):
        cmd = data[pos]
        pos += 1
        if cmd == 0x66:
            break
        wait = None
        if cmd == 0x61:
            if pos + 2 > len(data):
                raise FormatError("truncated VGM wait")
            wait = u16(data, pos)
            pos += 2
        elif cmd == 0x62:
            wait = 735
        elif cmd == 0x63:
            wait = 882
        elif 0x70 <= cmd <= 0x7F:
            wait = (cmd & 0x0F) + 1
        elif 0x80 <= cmd <= 0x8F:
            wait = cmd & 0x0F
        elif cmd == 0x5A:
            if pos + 2 > len(data):
                raise FormatError("truncated YM3812 write")
            pos += 2
            last_ym_write_sample = sample
            last_was_wait = False
            continue
        else:
            pos = _skip_vgm_command(data, pos, cmd)
            if pos > len(data):
                raise FormatError("VGM command runs past end of file")
            last_was_wait = False
            continue

        final_wait_start = sample
        final_wait = int(wait)
        sample += int(wait)
        last_was_wait = True

    bpm: Optional[int] = None
    tick_hz: Optional[float] = None
    if 1 <= rate <= 1000:
        candidate = int(math.floor(rate * 60.0 / ticks_per_beat + 0.5))
        if 1 <= candidate <= 65535:
            bpm = candidate
            tick_hz = ticks_per_beat * candidate / 60.0

    trim = 0
    reason: Optional[str] = None
    if last_was_wait and rate > 0 and tick_hz is not None:
        one_frame = abs(final_wait - VGM_SAMPLE_RATE / rate) <= 1.0
        one_tick = _quantize_sample(sample, tick_hz) - _quantize_sample(final_wait_start, tick_hz) == 1
        if one_frame and one_tick and last_ym_write_sample == final_wait_start:
            trim = 1
            reason = (
                f"the final {final_wait}-sample wait is one {rate} Hz capture frame "
                "after the last YM3812 write"
            )

    return VgmTimingHint(
        int(rate), bpm, tick_hz, int(final_wait if last_was_wait else 0),
        int(last_ym_write_sample), int(sample), trim, reason,
    )


def _skip_vgm_command(data: bytes, pos: int, cmd: int) -> int:
    if cmd in (0x4F, 0x50):
        return pos + 1
    if 0x51 <= cmd <= 0x5F:
        return pos + 2
    if 0xA0 <= cmd <= 0xBF:
        return pos + 2
    if 0xC0 <= cmd <= 0xDF:
        return pos + 3
    if 0xE0 <= cmd <= 0xFF:
        return pos + 4
    if cmd == 0x67:
        if pos + 6 > len(data) or data[pos] != 0x66:
            raise FormatError("malformed VGM data block")
        size = struct.unpack_from("<I", data, pos + 2)[0] & 0x7FFFFFFF
        return pos + 6 + size
    if cmd == 0x68:
        return pos + 11
    if cmd == 0x90:
        return pos + 4
    if cmd == 0x91:
        return pos + 4
    if cmd == 0x92:
        return pos + 5
    if cmd == 0x93:
        return pos + 10
    if cmd == 0x94:
        return pos + 1
    if cmd == 0x95:
        return pos + 4
    raise FormatError(f"unsupported VGM command 0x{cmd:02X} at 0x{pos-1:X}")


def _opl_frequency(a0: int, b0: int) -> float:
    fnum = a0 | ((b0 & 0x03) << 8)
    block = (b0 >> 2) & 0x07
    if fnum <= 0:
        return 0.0
    return fnum * 49716.0 / (2.0 ** (20 - block))


def _frequency_to_midi(freq: float) -> int:
    if freq <= 0:
        return 0
    note = int(math.floor(69.0 + 12.0 * math.log2(freq / 440.0) + 0.5))
    return max(1, min(127, note))


def _opl_frequency_to_midi(a0: int, b0: int) -> int:
    return _frequency_to_midi(_opl_frequency(a0, b0))


def _midi_frequency(note: int) -> float:
    return 440.0 * (2.0 ** ((note - 69) / 12.0))


def _opl_record_from_state(regs: list[int], channel: int, logical_voice: Optional[int] = None) -> bytes:
    """Convert live OPL registers to ED2's 28-byte packed timbre.

    Runtime volume attenuation is normalized out so volume writes do not create
    hundreds of false instruments.  The packed AdLib CON field is inverted
    relative to OPL C0 bit 0.
    """
    mo = OPL_MOD_OFFSETS[channel]
    ca = OPL_CAR_OFFSETS[channel]

    def op(off: int) -> list[int]:
        r20 = regs[0x20 + off]
        r40 = regs[0x40 + off]
        r60 = regs[0x60 + off]
        r80 = regs[0x80 + off]
        re0 = regs[0xE0 + off]
        return [
            (r40 >> 6) & 3,
            r20 & 15,
            (r60 >> 4) & 15,
            (r80 >> 4) & 15,
            (r20 >> 5) & 1,
            r60 & 15,
            r80 & 15,
            r40 & 63,
            (r20 >> 7) & 1,
            (r20 >> 6) & 1,
            (r20 >> 4) & 1,
            re0 & 3,
        ]

    m = op(mo)
    c = op(ca)
    c0 = regs[0xC0 + channel]
    fb = (c0 >> 1) & 7
    opl_conn = c0 & 1
    packed_conn = 0 if opl_conn else 1

    # Remove global output attenuation while retaining FM modulation balance.
    if opl_conn:
        # Additive: both operators are audible, preserve their relative TL.
        floor = min(m[7], c[7])
        m[7] -= floor
        c[7] -= floor
    else:
        # FM serial: carrier TL is overall loudness; modulator TL is timbral.
        c[7] = 0

    rec = bytearray(28)
    rec[0] = m[0]; rec[1] = m[1]; rec[2] = fb
    rec[3] = m[2]; rec[4] = m[3]; rec[5] = m[4]; rec[6] = m[5]; rec[7] = m[6]
    rec[8] = m[7]; rec[9] = m[8]; rec[10] = m[9]; rec[11] = m[10]; rec[12] = packed_conn
    rec[13] = c[0]; rec[14] = c[1]; rec[15] = 0
    rec[16] = c[2]; rec[17] = c[3]; rec[18] = c[4]; rec[19] = c[5]; rec[20] = c[6]
    rec[21] = c[7]; rec[22] = c[8]; rec[23] = c[9]; rec[24] = c[10]; rec[25] = 0
    rec[26] = m[11]; rec[27] = c[11]

    # Single-operator rhythm voices: clear the physically unrelated operator so
    # changes to the paired drum do not look like instrument changes.
    if logical_voice in (7, 9):          # snare / cymbal: physical carrier, packed as FILE modulator
        clean = bytearray(28)
        # Official ROL playback loads every 1OP percussion patch from the timbre's
        # modulator fields, even when the destination OPL cell is a carrier.
        clean[0] = rec[13]       # KSL
        clean[1] = rec[14]       # MULT
        clean[2] = 0             # feedback unused for 1OP percussion
        clean[3] = rec[16]       # attack
        clean[4] = rec[17]       # sustain
        clean[5] = rec[18]       # EG
        clean[6] = rec[19]       # decay
        clean[7] = rec[20]       # release
        clean[8] = 0             # normalize output TL
        clean[9] = rec[22]       # AM
        clean[10] = rec[23]      # VIB
        clean[11] = rec[24]      # KSR
        clean[12] = 1            # connector irrelevant; conventional nonzero value
        clean[26] = rec[27]      # waveform
        rec = clean
    elif logical_voice in (8, 10):       # tom / hi-hat: physical modulator, packed as modulator
        clean = bytearray(28)
        clean[0:13] = rec[0:13]
        clean[2] = 0
        clean[8] = 0
        clean[12] = 1
        clean[26] = rec[26]
        rec = clean
    return bytes(rec)


def _rhythm_note_from_state(regs: list[int], logical_voice: int) -> tuple[int, int, float]:
    physical = {6: 6, 7: 7, 8: 8, 9: 8, 10: 7}[logical_voice]
    freq = _opl_frequency(regs[0xA0 + physical], regs[0xB0 + physical])
    midi = _frequency_to_midi(freq)
    # Empirical inverse mapping used by this ED2 AdLib driver.  Tom and bass are
    # direct; the other one-op rhythm voices share ch7/ch8 frequency registers.
    if logical_voice == 7:
        midi -= 7
    elif logical_voice == 9:
        midi -= 26
    elif logical_voice == 10:
        midi -= 12
    return physical, max(1, min(127, midi)), freq


def _ed2_tl_from_volume(base_tl: int, volume: int) -> int:
    """ED2/AdLib driver TL scaling recovered from the supplied original MUS+VGM pairs.

    For melodic serial carriers, 7,025 of 7,150 matched note-on samples are exact
    with this integer expression; the remaining mismatches are almost entirely
    event-boundary alignment.  Additive samples tested against both operators
    matched exactly.
    """
    base_tl = max(0, min(63, int(base_tl)))
    volume = max(0, min(127, int(volume)))
    return 63 - (((63 - base_tl) * volume * ED2_VOLUME_MASTER) // (127 * 127))


def _ed2_volume_from_output_tl(output_tl: int, base_tl: int = 0) -> int:
    output_tl = max(0, min(63, int(output_tl)))
    best_err = 999
    best_volume = 127
    # Prefer the larger value when multiple compact volume values quantize to
    # the same OPL TL.  They are acoustically identical for this base TL.
    for volume in range(128):
        err = abs(_ed2_tl_from_volume(base_tl, volume) - output_tl)
        if err < best_err or (err == best_err and volume > best_volume):
            best_err = err
            best_volume = volume
    return best_volume


def _logical_output_tl(regs: list[int], logical: int, rhythm: bool) -> int:
    if rhythm and logical in (7, 8, 9, 10):
        if logical == 7:      # snare: ch7 carrier
            return regs[0x40 + OPL_CAR_OFFSETS[7]] & 63
        if logical == 8:      # tom: ch8 modulator
            return regs[0x40 + OPL_MOD_OFFSETS[8]] & 63
        if logical == 9:      # cymbal: ch8 carrier
            return regs[0x40 + OPL_CAR_OFFSETS[8]] & 63
        return regs[0x40 + OPL_MOD_OFFSETS[7]] & 63  # hi-hat
    physical = 6 if rhythm and logical == 6 else logical
    if not 0 <= physical < 9:
        return 63
    mod_tl = regs[0x40 + OPL_MOD_OFFSETS[physical]] & 63
    car_tl = regs[0x40 + OPL_CAR_OFFSETS[physical]] & 63
    additive = bool(regs[0xC0 + physical] & 1)
    return min(mod_tl, car_tl) if additive else car_tl


def _tl_write_logical_voice(reg: int, rhythm: bool) -> Optional[int]:
    if not 0x40 <= reg <= 0x55:
        return None
    off = reg - 0x40
    if off in OPL_MOD_OFFSETS:
        physical = OPL_MOD_OFFSETS.index(off)
        is_mod = True
    elif off in OPL_CAR_OFFSETS:
        physical = OPL_CAR_OFFSETS.index(off)
        is_mod = False
    else:
        return None
    if not rhythm or physical < 6:
        return physical
    if physical == 6:
        return 6
    if physical == 7:
        return 10 if is_mod else 7
    if physical == 8:
        return 8 if is_mod else 9
    return None


def analyze_vgm(path: Path) -> VgmAnalysis:
    data = _read_vgm_bytes(path)
    pos = _vgm_data_offset(data)
    loop_file = _vgm_loop_file_offset(data)
    loop_sample: Optional[int] = None
    sample = 0
    regs = [0] * 256
    active: list[Optional[tuple[int, int, int, bytes, float, bool, bool]]] = [None] * MUS_VOICE_SLOTS
    notes: list[VgmNoteSpan] = []
    pitch_points: list[VgmPitchPoint] = []
    volume_points: list[VgmVolumePoint] = []
    ym_writes = 0
    rhythm_seen = False
    rhythm_triggers = [0] * 5
    inst_counter: list[dict[bytes, int]] = [dict() for _ in range(MUS_VOICE_SLOTS)]
    unique_instruments: dict[bytes, None] = {}

    def add_pitch(logical: int, at_sample: int, freq: float) -> None:
        item = active[logical]
        if item is None or freq <= 0:
            return
        _start, _physical, note, _inst, _freq0, _hw_vib, _vib_deep = item
        point = VgmPitchPoint(logical, at_sample, note, freq)
        if pitch_points and pitch_points[-1].channel == logical and pitch_points[-1].sample == at_sample:
            pitch_points[-1] = point
        else:
            pitch_points.append(point)

    def add_volume(logical: int, at_sample: int) -> None:
        rhythm = bool(regs[0xBD] & 0x20)
        if logical < 0 or logical >= (11 if rhythm else 9):
            return
        out_tl = _logical_output_tl(regs, logical, rhythm)
        volume = _ed2_volume_from_output_tl(out_tl, 0)
        volume_points.append(VgmVolumePoint(logical, at_sample, volume, out_tl))

    def close_note(logical: int, at_sample: int) -> None:
        item = active[logical]
        if item is None:
            return
        start, physical, note, inst, freq0, hw_vib, vib_deep = item
        if at_sample > start and note > 0:
            notes.append(VgmNoteSpan(
                logical, physical, start, at_sample, note, inst, freq0,
                hw_vib, vib_deep,
            ))
        active[logical] = None

    def start_note(logical: int, physical: int, note: int, freq: float) -> None:
        close_note(logical, sample)
        inst = _opl_record_from_state(regs, physical, logical)
        # VGM hardware vibrato does not move A0/B0: the OPL chip applies its
        # global 6.1 Hz LFO internally when an operator's VIB bit is set.
        # Record this separately so conversion can bake the LFO into the MUS
        # pitch stream instead of relying on the target driver's global state.
        hw_vib = logical < 9 and bool(inst[10] or inst[23])
        vib_deep = bool(regs[0xBD] & 0x40)
        active[logical] = (sample, physical, note, inst, freq, hw_vib, vib_deep)
        unique_instruments.setdefault(inst, None)
        inst_counter[logical][inst] = inst_counter[logical].get(inst, 0) + 1
        # In OPL rhythm mode, logical voices 6..10 use percussion pitch rules
        # (some operators share the physical channel-7/8 frequency registers).
        # Their note values already carry the useful pitch approximation, so do
        # not generate misleading per-hit MUS pitch automation for them.
        rhythm_now = bool(regs[0xBD] & 0x20)
        if not rhythm_now or logical < 6:
            add_pitch(logical, sample, freq)
        add_volume(logical, sample)

    while pos < len(data):
        if loop_file is not None and pos == loop_file and loop_sample is None:
            loop_sample = sample
        cmd = data[pos]
        pos += 1
        if cmd == 0x66:
            break
        if cmd == 0x61:
            if pos + 2 > len(data):
                raise FormatError("truncated VGM wait")
            sample += u16(data, pos); pos += 2; continue
        if cmd == 0x62:
            sample += 735; continue
        if cmd == 0x63:
            sample += 882; continue
        if 0x70 <= cmd <= 0x7F:
            sample += (cmd & 0x0F) + 1; continue
        if 0x80 <= cmd <= 0x8F:
            sample += cmd & 0x0F; continue
        if cmd == 0x5A:
            if pos + 2 > len(data):
                raise FormatError("truncated YM3812 write")
            reg = data[pos]; val = data[pos + 1]; pos += 2
            ym_writes += 1

            if reg == 0xBD:
                old = regs[reg]
                old_rhythm = bool(old & 0x20)
                new_rhythm = bool(val & 0x20)
                regs[reg] = val
                if new_rhythm:
                    rhythm_seen = True
                if not old_rhythm and new_rhythm:
                    for ch in range(6, 9):
                        close_note(ch, sample)
                if old_rhythm and not new_rhythm:
                    for logical in range(6, 11):
                        close_note(logical, sample)
                if new_rhythm:
                    masks = (0x10, 0x08, 0x04, 0x02, 0x01)
                    for j, mask in enumerate(masks):
                        logical = 6 + j
                        was = bool(old & mask) if old_rhythm else False
                        now = bool(val & mask)
                        if was and not now:
                            close_note(logical, sample)
                        elif not was and now:
                            physical, note, freq = _rhythm_note_from_state(regs, logical)
                            start_note(logical, physical, note, freq)
                            rhythm_triggers[j] += 1
                continue

            if 0xA0 <= reg <= 0xA8:
                ch = reg - 0xA0
                regs[reg] = val
                rhythm = bool(regs[0xBD] & 0x20)
                if active[ch] is not None and (ch < 6 or not rhythm):
                    add_pitch(ch, sample, _opl_frequency(regs[0xA0 + ch], regs[0xB0 + ch]))
                continue

            if 0xB0 <= reg <= 0xB8:
                ch = reg - 0xB0
                old = regs[reg]
                old_key = bool(old & 0x20)
                regs[reg] = val
                new_key = bool(val & 0x20)
                rhythm = bool(regs[0xBD] & 0x20)
                melodic_allowed = ch < 6 or not rhythm
                if melodic_allowed:
                    if old_key and not new_key:
                        close_note(ch, sample)
                    elif not old_key and new_key:
                        freq = _opl_frequency(regs[0xA0 + ch], val)
                        start_note(ch, ch, _frequency_to_midi(freq), freq)
                    elif old_key and new_key:
                        add_pitch(ch, sample, _opl_frequency(regs[0xA0 + ch], val))
                continue

            # Total-level writes carry the final runtime channel volume.  Track
            # the affected logical voice after the register has been updated.
            if 0x40 <= reg <= 0x55:
                regs[reg] = val
                rhythm = bool(regs[0xBD] & 0x20)
                logical = _tl_write_logical_voice(reg, rhythm)
                if logical is not None:
                    add_volume(logical, sample)
                continue

            regs[reg] = val
            continue

        pos = _skip_vgm_command(data, pos, cmd)
        if pos > len(data):
            raise FormatError("VGM command runs past end of file")

    for ch in range(MUS_VOICE_SLOTS):
        close_note(ch, sample)

    dominant: list[Optional[bytes]] = []
    counts: list[int] = []
    for ch in range(MUS_VOICE_SLOTS):
        counts.append(sum(1 for n in notes if n.channel == ch))
        if inst_counter[ch]:
            dominant.append(max(inst_counter[ch].items(), key=lambda kv: kv[1])[0])
        else:
            dominant.append(None)

    return VgmAnalysis(
        sample, ym_writes, notes, list(unique_instruments.keys()), counts,
        dominant, loop_sample, rhythm_seen, pitch_points, volume_points, rhythm_triggers,
    )


def slice_vgm_analysis(vgm: VgmAnalysis, start_sample: int) -> VgmAnalysis:
    """Move a VGM loop body to timeline sample zero.

    ED2's compiled ROL/MUS data has no arbitrary loop-start field. The game
    repeats a MUS from its beginning, so converting only the VGM loop body makes
    that whole-song restart match the VGM loop.
    """
    start_sample = int(start_sample)
    if not 0 <= start_sample < vgm.total_samples:
        raise ValueError("loop start must be inside the VGM timeline")

    new_notes: list[VgmNoteSpan] = []
    for n in vgm.notes:
        if n.end_sample <= start_sample:
            continue
        ns = max(n.start_sample, start_sample) - start_sample
        ne = n.end_sample - start_sample
        if ne > ns:
            new_notes.append(VgmNoteSpan(
                n.channel, n.physical_channel, ns, ne, n.midi_note, n.instrument,
                n.start_frequency, n.hardware_vibrato, n.vibrato_deep
            ))

    pitch_by_channel: list[list[VgmPitchPoint]] = [[] for _ in range(MUS_VOICE_SLOTS)]
    for point in vgm.pitch_points:
        if 0 <= point.channel < MUS_VOICE_SLOTS:
            pitch_by_channel[point.channel].append(point)
    new_pitch: list[VgmPitchPoint] = []
    for ch in range(MUS_VOICE_SLOTS):
        crossing = next((n for n in vgm.notes if n.channel == ch and n.start_sample < start_sample < n.end_sample), None)
        if crossing is not None:
            freq = crossing.start_frequency
            for point in pitch_by_channel[ch]:
                if crossing.start_sample <= point.sample <= start_sample:
                    freq = point.frequency
            new_pitch.append(VgmPitchPoint(ch, 0, crossing.midi_note, freq))
        for point in pitch_by_channel[ch]:
            if point.sample >= start_sample:
                new_pitch.append(VgmPitchPoint(ch, point.sample - start_sample, point.midi_note, point.frequency))

    new_volume: list[VgmVolumePoint] = []
    volume_by_channel: list[list[VgmVolumePoint]] = [[] for _ in range(MUS_VOICE_SLOTS)]
    for point in vgm.volume_points:
        if 0 <= point.channel < MUS_VOICE_SLOTS:
            volume_by_channel[point.channel].append(point)
    for ch in range(MUS_VOICE_SLOTS):
        prior = [point for point in volume_by_channel[ch] if point.sample <= start_sample]
        if prior:
            point = prior[-1]
            new_volume.append(VgmVolumePoint(ch, 0, point.volume, point.output_tl))
        for point in volume_by_channel[ch]:
            if point.sample > start_sample:
                new_volume.append(VgmVolumePoint(ch, point.sample - start_sample, point.volume, point.output_tl))

    unique: dict[bytes, None] = {}
    counters: list[dict[bytes, int]] = [dict() for _ in range(MUS_VOICE_SLOTS)]
    counts = [0] * MUS_VOICE_SLOTS
    rhythm_counts = [0] * 5
    for n in new_notes:
        unique.setdefault(n.instrument, None)
        counts[n.channel] += 1
        counters[n.channel][n.instrument] = counters[n.channel].get(n.instrument, 0) + 1
        if 6 <= n.channel <= 10:
            rhythm_counts[n.channel - 6] += 1
    dominant: list[Optional[bytes]] = []
    for ch in range(MUS_VOICE_SLOTS):
        dominant.append(max(counters[ch].items(), key=lambda kv: kv[1])[0] if counters[ch] else None)

    return VgmAnalysis(
        vgm.total_samples - start_sample, vgm.ym3812_writes, new_notes, list(unique.keys()), counts, dominant, 0,
        vgm.rhythm_mode, sorted(new_pitch, key=lambda p: (p.sample, p.channel)),
        sorted(new_volume, key=lambda p: (p.sample, p.channel)), rhythm_counts,
    )


def _split_mus_event(note: int, duration: int) -> list[tuple[int, int]]:
    out: list[tuple[int, int]] = []
    left = duration
    while left > 0:
        part = min(left, 65535)
        out.append((note, part))
        left -= part
    return out


def _quantize_sample(sample: int, tick_hz: float) -> int:
    return max(0, int(math.floor(sample * tick_hz / VGM_SAMPLE_RATE + 0.5)))


def _coalesce_timed_byte(events: list[MusTimedByteEvent]) -> list[MusTimedByteEvent]:
    out: list[MusTimedByteEvent] = []
    for ev in sorted(events, key=lambda e: e.time):
        if out and out[-1].time == ev.time:
            out[-1] = ev
        elif not out or out[-1].value != ev.value:
            out.append(ev)
    return out


def _coalesce_pitch(events: list[MusPitchEvent]) -> list[MusPitchEvent]:
    out: list[MusPitchEvent] = []
    for ev in sorted(events, key=lambda e: e.time):
        if out and out[-1].time == ev.time:
            out[-1] = ev
        elif not out or out[-1].value != ev.value:
            out.append(ev)
    return out


def _vgm_note_track(vgm: VgmAnalysis, logical: int, total_ticks: int, tick_hz: float) -> list[tuple[int, int]]:
    spans = sorted((n for n in vgm.notes if n.channel == logical), key=lambda n: (n.start_sample, n.end_sample))
    events: list[tuple[int, int]] = []
    cursor = 0
    for span in spans:
        start = min(total_ticks, _quantize_sample(span.start_sample, tick_hz))
        end = min(total_ticks, max(start + 1, _quantize_sample(span.end_sample, tick_hz)))
        if start > cursor:
            events.extend(_split_mus_event(0, start - cursor))
            cursor = start
        if end > cursor:
            events.extend(_split_mus_event(span.midi_note, end - cursor))
            cursor = end
    if cursor < total_ticks:
        events.extend(_split_mus_event(0, total_ticks - cursor))
    if not events and total_ticks:
        events = _split_mus_event(0, total_ticks)
    return events



def _clear_ins_hardware_vibrato(record: bytes) -> bytes:
    """Clear operator VIB bits after baking the OPL LFO into MUS pitch events."""
    out = bytearray(record)
    if len(out) == 28:
        out[10] = 0
        out[23] = 0
    return bytes(out)


def _opl_note_base_frequency(midi_note: int) -> float:
    """Return the nearest frequency the ED2 OPL note table can produce.

    ED2 first converts the MUS note number to an OPL block/F-number pair, then
    applies the MUS pitch word as a signed semitone displacement.  Use the
    nearest representable YM3812 base frequency so register quantization does
    not become a false bend at note-on.
    """
    target = _midi_frequency(midi_note)
    best_frequency = target
    best_error = float("inf")
    for block in range(8):
        scale = 49716.0 / (2.0 ** (20 - block))
        fnum = max(1, min(1023, int(math.floor(target / scale + 0.5))))
        frequency = fnum * scale
        error = abs(math.log2(frequency / target))
        if error < best_error:
            best_error = error
            best_frequency = frequency
    return best_frequency


def _pitch_value_for_frequency(midi_note: int, frequency: float) -> int:
    """Encode the ED2 compiled-ROL pitch word.

    The supplied retail DS2_07.MUS aligned against 08 Field.vgz confirms a
    14-bit bipolar bend word with 0x1FFF as the neutral value and roughly one
    semitone of travel to either end.  The VGM contains already-quantized OPL
    F-numbers, so several nearby bend words can reproduce the same register
    value; conversion targets the center of the observed frequency value rather
    than claiming byte-identical recovery of the original authoring value.
    """
    base_freq = _opl_note_base_frequency(midi_note)
    if base_freq <= 0 or frequency <= 0:
        return MUS_BASE_PITCH
    semitones = 12.0 * math.log2(frequency / base_freq)
    value = MUS_BASE_PITCH + int(math.floor(semitones * 8192.0 + 0.5))
    return max(0, min(MUS_MAX_PITCH, value))


def _opl_vibrato_ratio(sample: int, deep: bool) -> float:
    """Approximate the YM3812 eight-step hardware vibrato at source time.

    The OPL LFO is a stepped triangle, not a sine.  Using source-sample time
    keeps its phase deterministic when it is baked into the MUS pitch stream.
    """
    phase = (sample * OPL_VIBRATO_HZ / VGM_SAMPLE_RATE) % 1.0
    step = int(phase * 8.0) & 7
    shape = (0.0, 0.5, 1.0, 0.5, 0.0, -0.5, -1.0, -0.5)[step]
    cents = (OPL_VIBRATO_DEEP_CENTS if deep else OPL_VIBRATO_SHALLOW_CENTS) * shape
    return 2.0 ** (cents / 1200.0)


def _build_vgm_pitch_tracks(
    vgm: VgmAnalysis,
    active_voices: int,
    total_ticks: int,
    tick_hz: float,
    bake_hardware_vibrato: bool = False,
) -> tuple[list[list[MusPitchEvent]], int]:
    """Reconstruct the effective VGM pitch curve at every MUS tick.

    Furnace effects such as 01/02/03/04 are not stored as tracker commands in
    VGM.  Furnace renders them to YM3812 A0/B0 register writes.  We therefore
    replay the resulting step curve at each MUS tick instead of quantizing each
    register write independently.  This preserves vibrato phase, portamento,
    fine pitch and note detune as closely as the MUS tick rate permits.

    Direct A0/B0 motion is always imported. Hardware VIB can either remain in
    the INS operator flags (the retail-compatible default) or be approximated
    as an eight-step OPL LFO in the MUS pitch stream. Baking is useful as a
    diagnostic on players that fail to honor the INS VIB bits; the generated
    bank clears those bits to avoid applying vibrato twice.
    """
    tracks: list[list[MusPitchEvent]] = [
        [MusPitchEvent(0, MUS_BASE_PITCH)] for _ in range(MUS_VOICE_SLOTS)
    ]
    direct_by_channel: list[list[VgmPitchPoint]] = [[] for _ in range(MUS_VOICE_SLOTS)]
    for point in sorted(vgm.pitch_points, key=lambda p: (p.channel, p.sample)):
        if 0 <= point.channel < active_voices and point.midi_note > 0:
            direct_by_channel[point.channel].append(point)

    baked_notes = 0
    for ch in range(active_voices):
        # OPL rhythm voices share frequency registers and do not have an
        # independent MUS pitch curve. Their note values already encode the
        # useful pitch approximation, so leave their pitch multiplier at unity.
        if vgm.rhythm_mode and ch >= 6:
            continue
        spans = sorted(
            (n for n in vgm.notes if n.channel == ch),
            key=lambda n: (n.start_sample, n.end_sample),
        )
        points = direct_by_channel[ch]
        point_i = 0

        for span in spans:
            if span.midi_note <= 0:
                continue
            start_tick = min(total_ticks, _quantize_sample(span.start_sample, tick_hz))
            end_tick = min(total_ticks, max(start_tick + 1, _quantize_sample(span.end_sample, tick_hz)))
            if end_tick <= start_tick:
                continue

            # Move to the first source point belonging to this note.  A note-on
            # point is always recorded, but start_frequency is the safe fallback.
            while point_i < len(points) and points[point_i].sample < span.start_sample:
                point_i += 1
            local_i = point_i
            base_frequency = span.start_frequency
            while local_i < len(points) and points[local_i].sample <= span.start_sample:
                base_frequency = points[local_i].frequency
                local_i += 1

            if bake_hardware_vibrato and span.hardware_vibrato:
                baked_notes += 1

            # Furnace 04xy is already present in A0/B0 writes. Hardware VIB does
            # not move those registers, so the optional bake adds only the OPL
            # chip's own stepped LFO rather than duplicating tracker vibrato.

            # Sample-and-hold the exact register curve at the MUS scheduler's
            # tick boundaries.  This is the equivalent of importing Furnace's
            # already-rendered 04xy waveform, not inventing a new tracker effect.
            for tick in range(start_tick, end_tick):
                sample_at_tick = int(round(tick * VGM_SAMPLE_RATE / tick_hz))
                # Do not consume points from a later note on the same channel.
                while (local_i < len(points)
                       and points[local_i].sample < span.end_sample
                       and points[local_i].sample <= sample_at_tick):
                    base_frequency = points[local_i].frequency
                    local_i += 1

                # A0/B0 already contains Furnace pitch slide/portamento/04xy.
                effective_frequency = base_frequency
                if bake_hardware_vibrato and span.hardware_vibrato:
                    effective_frequency *= _opl_vibrato_ratio(sample_at_tick, span.vibrato_deep)
                tracks[ch].append(MusPitchEvent(
                    tick, _pitch_value_for_frequency(span.midi_note, effective_frequency)
                ))

            point_i = local_i
            # MUS pitch state survives rests/notes.  Restore unity at the exact
            # note end so the following note cannot inherit an old bend when its
            # quantized start falls on a later tick.
            tracks[ch].append(MusPitchEvent(end_tick, MUS_BASE_PITCH))

    return [_coalesce_pitch(track) for track in tracks], baked_notes


def _append_mus_rest(track: list[tuple[int, int]], duration: int) -> list[tuple[int, int]]:
    """Append a rest to a compact MUS note stream, merging with a final rest."""
    if duration <= 0:
        return list(track)
    out = list(track)
    if out and out[-1][0] == 0:
        note, old = out.pop()
        out.extend(_split_mus_event(note, old + duration))
    else:
        out.extend(_split_mus_event(0, duration))
    return out


def _volume_at_tick(events: list[MusTimedByteEvent], tick: int, default: int = 127) -> int:
    value = default
    for ev in sorted(events, key=lambda e: e.time):
        if ev.time > tick:
            break
        value = ev.value
    return max(0, min(127, value))


def _add_restart_guard_fade(
    volume_tracks: list[list[MusTimedByteEvent]],
    active_voices: int,
    content_ticks: int,
    restart_guard_ticks: int,
) -> tuple[int, int, int]:
    """Fade release tails to silence before ED2's hard OPL reset.

    DRO capture of ED2's real restart path shows that the driver key-offs voices,
    then clears/reinitializes almost the entire YM3812 register set only about one
    scheduler tick later.  A release tail that is still audible is therefore
    discontinuously rewritten.  The guard inserts a short post-key-off TL fade
    and leaves several fully muted ticks before the terminal reset.
    """
    if restart_guard_ticks <= 0:
        return 0, 0, 0
    if restart_guard_ticks < 4:
        raise ValueError("restart guard must be 0 or at least 4 ticks")

    quiet_ticks = min(4, max(2, restart_guard_ticks // 3))
    fade_ticks = restart_guard_ticks - quiet_ticks
    if fade_ticks < 2:
        fade_ticks = 2
        quiet_ticks = restart_guard_ticks - fade_ticks

    inserted = 0
    for ch in range(active_voices):
        start_volume = _volume_at_tick(volume_tracks[ch], content_ticks, default=127)
        for step in range(1, fade_ticks + 1):
            # Quadratic attenuation keeps the first TL steps small and reaches
            # true silence (MUS volume 0 -> carrier TL 63) before the hard reset.
            ratio = max(0.0, 1.0 - step / fade_ticks)
            value = int(math.floor(start_volume * ratio * ratio + 0.5))
            volume_tracks[ch].append(MusTimedByteEvent(content_ticks + step, value))
            inserted += 1
        volume_tracks[ch] = _coalesce_timed_byte(volume_tracks[ch])

    return fade_ticks, quiet_ticks, inserted


def make_ed2_pair_from_vgm(
    vgm: VgmAnalysis,
    ticks_per_beat: int = ED2_DEFAULT_TICKS_PER_BEAT,
    base_tempo: int = ED2_DEFAULT_BASE_TEMPO,
    beats_per_measure: int = ED2_DEFAULT_BEATS_PER_MEASURE,
    end_trim_ticks: int = 0,
    restart_guard_ticks: int = ED2_RESTART_GUARD_DEFAULT_TICKS,
    vibrato_mode: str = "native",
    ed2_loop_seam: bool = True,
    legacy_terminal_preload: bool = False,
) -> tuple[bytes, bytes, dict[str, object]]:
    if ticks_per_beat <= 0 or base_tempo <= 0:
        raise ValueError("ticks_per_beat and base_tempo must be > 0")
    tick_hz = ticks_per_beat * base_tempo / 60.0
    raw_total_ticks = max(1, _quantize_sample(vgm.total_samples, tick_hz))
    end_trim_ticks = int(end_trim_ticks)
    restart_guard_ticks = int(restart_guard_ticks)
    if end_trim_ticks < 0:
        raise ValueError("end trim ticks must be 0 or greater")
    if end_trim_ticks >= raw_total_ticks:
        raise ValueError(
            f"end trim ticks ({end_trim_ticks}) must be smaller than the generated length ({raw_total_ticks} ticks)"
        )
    if restart_guard_ticks < 0:
        raise ValueError("restart guard ticks must be 0 or greater")
    if 0 < restart_guard_ticks < 4:
        raise ValueError("restart guard ticks must be 0 or at least 4")

    content_ticks = raw_total_ticks - end_trim_ticks
    # The diagnostic/compatibility equal-track mode deliberately disables the
    # new DRO-verified guard.  The normal GUI/CLI default leaves it enabled.
    if not ed2_loop_seam and not legacy_terminal_preload:
        restart_guard_ticks = 0
    total_ticks = content_ticks + restart_guard_ticks
    if total_ticks > 65535:
        raise ValueError(
            f"song plus restart guard is too long for the 16-bit MUS timeline ({total_ticks} ticks); "
            "lower ticks/beat, base tempo, trim the end, or reduce the guard"
        )

    vibrato_mode = vibrato_mode.strip().lower()
    if vibrato_mode not in ("native", "bake"):
        raise ValueError("vibrato_mode must be native or bake")
    bake_hardware_vibrato = vibrato_mode == "bake"

    active_voices = 11 if vgm.rhythm_mode else 9
    used_voices = range(active_voices)

    instrument_index: dict[bytes, int] = {}
    bank: list[bytes] = []
    instrument_tracks: list[list[MusTimedByteEvent]] = [[] for _ in range(MUS_VOICE_SLOTS)]
    for ch in used_voices:
        last_idx: Optional[int] = None
        for span in sorted((n for n in vgm.notes if n.channel == ch), key=lambda n: n.start_sample):
            inst = (_clear_ins_hardware_vibrato(span.instrument)
                    if bake_hardware_vibrato else span.instrument)
            idx = instrument_index.get(inst)
            if idx is None:
                idx = len(bank)
                if idx > 255:
                    raise ValueError("VGM requires more than 256 distinct timbres; MUS program index is one byte")
                instrument_index[inst] = idx
                bank.append(inst)
            tick = min(content_ticks, _quantize_sample(span.start_sample, tick_hz))
            if idx != last_idx:
                instrument_tracks[ch].append(MusTimedByteEvent(tick, idx))
                last_idx = idx

    if not bank:
        bank.append(bytes(28))
    seam_preloads = 0
    for ch in range(MUS_VOICE_SLOTS):
        instrument_tracks[ch] = [
            ev for ev in _coalesce_timed_byte(instrument_tracks[ch])
            if ev.time < content_ticks
        ]

    note_tracks: list[list[tuple[int, int]]] = [[] for _ in range(MUS_VOICE_SLOTS)]
    totals = [0] * MUS_VOICE_SLOTS
    natural_short_channels = 0
    for ch in used_voices:
        if restart_guard_ticks > 0:
            # All active streams run through the quiet guard.  This guarantees
            # that volume events can mute every operator before the driver reset.
            totals[ch] = total_ticks
            base_track = _vgm_note_track(vgm, ch, content_ticks, tick_hz)
            note_tracks[ch] = _append_mus_rest(base_track, restart_guard_ticks)
        else:
            channel_total = content_ticks
            if ed2_loop_seam:
                spans = [n for n in vgm.notes if n.channel == ch]
                if spans:
                    last_end = max(min(content_ticks, _quantize_sample(n.end_sample, tick_hz)) for n in spans)
                    if 0 < last_end < content_ticks:
                        channel_total = last_end
                        natural_short_channels += 1
            totals[ch] = channel_total
            note_tracks[ch] = _vgm_note_track(vgm, ch, channel_total, tick_hz)

    volume_tracks: list[list[MusTimedByteEvent]] = [[] for _ in range(MUS_VOICE_SLOTS)]
    for point in vgm.volume_points:
        if point.channel >= active_voices:
            continue
        tick = min(content_ticks, _quantize_sample(point.sample, tick_hz))
        volume_tracks[point.channel].append(MusTimedByteEvent(tick, point.volume))
    for ch in range(MUS_VOICE_SLOTS):
        volume_tracks[ch].insert(0, MusTimedByteEvent(0, 127))
        volume_tracks[ch] = [
            ev for ev in _coalesce_timed_byte(volume_tracks[ch])
            if ev.time < content_ticks
        ]

    restart_fade_ticks = 0
    restart_quiet_ticks = 0
    restart_guard_volume_events = 0
    if restart_guard_ticks > 0:
        restart_fade_ticks, restart_quiet_ticks, restart_guard_volume_events = _add_restart_guard_fade(
            volume_tracks, active_voices, content_ticks, restart_guard_ticks
        )

    pitch_tracks, baked_hardware_vibrato_notes = _build_vgm_pitch_tracks(
        vgm, active_voices, content_ticks, tick_hz,
        bake_hardware_vibrato=bake_hardware_vibrato,
    )
    pitch_tracks = [
        [ev for ev in track if ev.time < content_ticks]
        for track in pitch_tracks
    ]

    removed_terminal = {"instrument": 0, "volume": 0, "pitch": 0}
    for ch in range(MUS_VOICE_SLOTS):
        cutoff = totals[ch]
        if cutoff <= 0:
            removed_terminal["instrument"] += len(instrument_tracks[ch])
            removed_terminal["volume"] += len(volume_tracks[ch])
            removed_terminal["pitch"] += len(pitch_tracks[ch])
            instrument_tracks[ch] = []
            volume_tracks[ch] = []
            pitch_tracks[ch] = []
            continue

        first_program = instrument_tracks[ch][0].value if instrument_tracks[ch] else 0
        kept_inst = [ev for ev in instrument_tracks[ch] if ev.time < cutoff]
        removed_terminal["instrument"] += len(instrument_tracks[ch]) - len(kept_inst)
        if not kept_inst:
            kept_inst = [MusTimedByteEvent(0, first_program)]
        elif kept_inst[0].time > 0:
            kept_inst.insert(0, MusTimedByteEvent(0, kept_inst[0].value))
        instrument_tracks[ch] = _coalesce_timed_byte(kept_inst)

        kept_vol = [ev for ev in volume_tracks[ch] if ev.time < cutoff]
        removed_terminal["volume"] += len(volume_tracks[ch]) - len(kept_vol)
        if not kept_vol:
            kept_vol = [MusTimedByteEvent(0, 127)]
        volume_tracks[ch] = _coalesce_timed_byte(kept_vol)

        kept_pitch = [ev for ev in pitch_tracks[ch] if ev.time < cutoff]
        removed_terminal["pitch"] += len(pitch_tracks[ch]) - len(kept_pitch)
        pitch_tracks[ch] = _coalesce_pitch(kept_pitch)

    if legacy_terminal_preload:
        for ch in range(active_voices):
            if (totals[ch] > 0 and instrument_tracks[ch]
                    and instrument_tracks[ch][-1].value != instrument_tracks[ch][0].value):
                instrument_tracks[ch].append(
                    MusTimedByteEvent(total_ticks, instrument_tracks[ch][0].value)
                )
                seam_preloads += 1

    mus_data = build_mus(
        active_voices, totals, note_tracks, instrument_tracks,
        volume_tracks, pitch_tracks,
        ticks_per_beat=ticks_per_beat,
        beats_per_measure=beats_per_measure,
        base_tempo=base_tempo,
        tempo_events=[MusTempoEvent(0, 100)],
    )

    seam_audit = audit_mus_loop_seam(mus_data)
    if not legacy_terminal_preload and (
        seam_audit["terminal_control_events"] != 0
        or seam_audit["zero_total_voice_control_events"] != 0
    ):
        raise ValueError("generated MUS failed pop-safe loop seam validation")

    guard_final_volumes = [
        _volume_at_tick(volume_tracks[ch], total_ticks - 1, default=127)
        for ch in range(active_voices)
    ]
    if restart_guard_ticks > 0 and any(v != 0 for v in guard_final_volumes):
        raise ValueError("restart guard validation failed: one or more voices are not fully muted")

    ins = bytearray(struct.pack("<H", len(bank)))
    for rec in bank:
        ins += rec

    report = {
        "active_voices": active_voices,
        "rhythm_mode": vgm.rhythm_mode,
        "source_pitch_points": len(vgm.pitch_points),
        "hardware_vibrato_notes_baked": baked_hardware_vibrato_notes,
        "hardware_vibrato_mode": (
            "OPL VIB approximated in MUS pitch; output INS VIB bits cleared"
            if bake_hardware_vibrato else
            "retail-compatible native INS VIB bits preserved; direct A0/B0 pitch imported"
        ),
        "ed2_loop_seam": bool(ed2_loop_seam),
        "loop_seam_mode": (
            "legacy v0.6.5 terminal instrument preload (diagnostic)"
            if legacy_terminal_preload else
            (
                "DRO-verified release fade + silent restart guard"
                if restart_guard_ticks > 0 else
                ("pop-safe natural channel ends" if ed2_loop_seam else "pop-safe equal-length tracks")
            )
        ),
        "legacy_terminal_preload": bool(legacy_terminal_preload),
        "loop_instrument_preloads": seam_preloads,
        "terminal_control_events_removed": sum(removed_terminal.values()),
        "terminal_control_events_removed_by_kind": removed_terminal,
        "loop_seam_audit": seam_audit,
        "natural_short_channel_totals": natural_short_channels,
        "channel_totals": totals[:active_voices],
        "generated_pitch_events": sum(len(track) for track in pitch_tracks),
        "ticks_per_beat": ticks_per_beat,
        "base_tempo_bpm": base_tempo,
        "beats_per_measure": beats_per_measure,
        "tick_hz": round(tick_hz, 6),
        "raw_total_ticks": raw_total_ticks,
        "content_ticks": content_ticks,
        "end_trim_ticks": end_trim_ticks,
        "restart_guard_ticks": restart_guard_ticks,
        "restart_guard_seconds": round(restart_guard_ticks / tick_hz, 6),
        "restart_fade_ticks": restart_fade_ticks,
        "restart_quiet_ticks": restart_quiet_ticks,
        "restart_guard_volume_events": restart_guard_volume_events,
        "restart_guard_final_volumes": guard_final_volumes,
        "total_ticks": total_ticks,
        "instrument_count": len(bank),
        "instrument_events": sum(len(x) for x in instrument_tracks[:active_voices]),
        "pitch_events": sum(len(x) for x in pitch_tracks[:active_voices]),
        "volume_events": sum(len(x) for x in volume_tracks[:active_voices]),
        "volume_points_from_vgm": len(vgm.volume_points),
        "rhythm_trigger_counts": {
            "bass_drum": vgm.rhythm_trigger_counts[0],
            "snare": vgm.rhythm_trigger_counts[1],
            "tom": vgm.rhythm_trigger_counts[2],
            "cymbal": vgm.rhythm_trigger_counts[3],
            "hi_hat": vgm.rhythm_trigger_counts[4],
        },
        "volume_mode": f"dynamic TL inversion using ED2 master scale {ED2_VOLUME_MASTER}/127; serial + 1OP exact model, additive approximate after TL normalization",
    }
    return mus_data, bytes(ins), report

def convert_vgm_to_ed2_pair(
    vgm_path: Path,
    out_mus: Path,
    out_ins: Path,
    ticks_per_beat: int = ED2_DEFAULT_TICKS_PER_BEAT,
    base_tempo: int = ED2_DEFAULT_BASE_TEMPO,
    beats_per_measure: int = ED2_DEFAULT_BEATS_PER_MEASURE,
    make_backup: bool = True,
    loop_mode: str = "full",
    end_trim_ticks: int = 0,
    restart_guard_ticks: int = ED2_RESTART_GUARD_DEFAULT_TICKS,
    vibrato_mode: str = "native",
    ed2_loop_seam: bool = True,
    legacy_terminal_preload: bool = False,
) -> dict[str, object]:
    analysis = analyze_vgm(vgm_path)
    if analysis.ym3812_writes == 0:
        raise FormatError("VGM contains no YM3812 (0x5A) register writes")
    if not analysis.notes:
        raise FormatError("no YM3812 notes/rhythm triggers were detected")

    loop_mode = loop_mode.strip().lower()
    if loop_mode not in ("full", "vgm", "auto"):
        raise ValueError("loop_mode must be full, vgm, or auto")
    source_total_samples = analysis.total_samples
    source_loop_sample = analysis.loop_sample
    effective_mode = loop_mode
    if effective_mode == "auto":
        effective_mode = "vgm" if source_loop_sample is not None else "full"
    timeline_start_sample = 0
    if effective_mode == "vgm":
        if source_loop_sample is None:
            raise ValueError("VGM has no loop point; use full loop mode")
        timeline_start_sample = source_loop_sample
        analysis = slice_vgm_analysis(analysis, source_loop_sample)
        if not analysis.notes:
            raise FormatError("VGM loop body contains no detected YM3812 notes")

    tick_hz = ticks_per_beat * base_tempo / 60.0
    source_loop_tick = None if source_loop_sample is None else _quantize_sample(source_loop_sample, tick_hz)
    end_trim_ticks = int(end_trim_ticks)
    if end_trim_ticks < 0:
        raise ValueError("end_trim_ticks must be 0 or greater")
    trim_reason = "user-selected end trim" if end_trim_ticks else None

    mus_data, ins_data, detail = make_ed2_pair_from_vgm(
        analysis, ticks_per_beat=ticks_per_beat,
        base_tempo=base_tempo, beats_per_measure=beats_per_measure,
        end_trim_ticks=end_trim_ticks,
        restart_guard_ticks=restart_guard_ticks,
        vibrato_mode=vibrato_mode,
        ed2_loop_seam=ed2_loop_seam,
        legacy_terminal_preload=legacy_terminal_preload,
    )
    atomic_write(out_mus, mus_data, make_backup=make_backup and out_mus.exists())
    atomic_write(out_ins, ins_data, make_backup=make_backup and out_ins.exists())
    parsed = parse_mus(mus_data)
    return {
        "source": str(vgm_path),
        "output_mus": str(out_mus),
        "output_ins": str(out_ins),
        "source_duration_seconds": round(source_total_samples / VGM_SAMPLE_RATE, 3),
        "generated_duration_seconds": round(analysis.total_samples / VGM_SAMPLE_RATE, 3),
        "ym3812_writes": analysis.ym3812_writes,
        "detected_notes": len(analysis.notes),
        "vgm_loop_sample": source_loop_sample,
        "vgm_loop_seconds": None if source_loop_sample is None else round(source_loop_sample / VGM_SAMPLE_RATE, 6),
        "vgm_loop_tick_at_source_timeline": source_loop_tick,
        "loop_mode_requested": loop_mode,
        "loop_mode_applied": effective_mode,
        "timeline_start_sample": timeline_start_sample,
        "generated_loop_tick": 0 if effective_mode == "vgm" else None,
        "end_trim_ticks": end_trim_ticks,
        "end_trim_reason": trim_reason,
        "restart_guard_ticks_requested": int(restart_guard_ticks),
        "loop_note": (
            "VGM loop body moved to MUS tick 0; ED2 whole-song restart becomes the VGM loop. "
            "A one-time intro plus arbitrary partial loop requires an ED2 playback executable patch."
            if effective_mode == "vgm" else
            (
                (
                    f"Full source timeline retained with {end_trim_ticks} user-selected end tick(s) removed; "
                    f"{int(restart_guard_ticks)} restart-guard tick(s) added; ED2 repeats from MUS tick 0."
                )
                if end_trim_ticks else
                (
                    f"Full source timeline retained; {int(restart_guard_ticks)} restart-guard tick(s) added; "
                    "ED2 repeats from MUS tick 0."
                )
            )
        ),
        "channel_note_counts": analysis.channel_note_counts,
        "generated_mus_size": len(mus_data),
        "generated_ins_size": len(ins_data),
        "parser_roundtrip_ok": parsed.end_offset == len(mus_data),
        **detail,
    }


# ---------------------------------------------------------------------------
# DOSBox DRO v2 loop-restart audit
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class DroWriteEvent:
    time_ms: int
    pair_index: int
    chip: int
    register: int
    value: int


def parse_dro_v2(path: Path) -> tuple[dict[str, int | str], list[DroWriteEvent]]:
    data = path.read_bytes()
    if len(data) < 26 or data[:8] != b"DBRAWOPL":
        raise FormatError("not a DOSBox Raw OPL file")
    major = u16(data, 8)
    minor = u16(data, 10)
    if (major, minor) != (2, 0):
        raise FormatError(f"only DRO v2.0 is supported, got {major}.{minor}")

    pair_count = struct.unpack_from("<I", data, 12)[0]
    length_ms = struct.unpack_from("<I", data, 16)[0]
    hardware, fmt, compression, short_code, long_code, map_len = struct.unpack_from("<6B", data, 20)
    if fmt != 0 or compression != 0:
        raise FormatError("unsupported DRO v2 format/compression")
    map_start = 26
    stream_start = map_start + map_len
    if stream_start > len(data):
        raise FormatError("truncated DRO code map")
    code_map = data[map_start:stream_start]
    stream = data[stream_start:]
    if len(stream) != pair_count * 2:
        raise FormatError(
            f"DRO pair count mismatch: header={pair_count}, stream={len(stream) // 2}"
        )

    time_ms = 0
    writes: list[DroWriteEvent] = []
    for pair_index in range(pair_count):
        code = stream[pair_index * 2]
        value = stream[pair_index * 2 + 1]
        if code == short_code:
            time_ms += value + 1
            continue
        if code == long_code:
            time_ms += (value + 1) * 256
            continue
        chip = 1 if code & 0x80 else 0
        map_index = code & 0x7F
        if map_index >= len(code_map):
            raise FormatError(f"DRO code-map index {map_index} is out of range")
        writes.append(DroWriteEvent(time_ms, pair_index, chip, code_map[map_index], value))

    if time_ms != length_ms:
        raise FormatError(f"DRO duration mismatch: header={length_ms}, decoded={time_ms}")

    return {
        "signature": "DBRAWOPL",
        "version": f"{major}.{minor}",
        "pair_count": pair_count,
        "length_ms": length_ms,
        "hardware_type": hardware,
        "format": fmt,
        "compression": compression,
        "short_delay_code": short_code,
        "long_delay_code": long_code,
        "code_map_length": map_len,
        "write_count": len(writes),
    }, writes


def audit_dro_loop_restart(path: Path) -> dict[str, object]:
    header, writes = parse_dro_v2(path)
    if not writes:
        raise FormatError("DRO contains no OPL writes")

    # Find a restart/reset burst: a short window that clears most of the low-bank
    # YM3812 register state. ED2's captured loop performs this immediately after
    # key-off, which is the destructive seam seen in the supplied recording.
    reset_candidate: Optional[tuple[int, int, int]] = None
    left = 0
    zero_core_regs = {
        0x01, 0x08, 0xBD,
        *range(0x20, 0x36), *range(0x40, 0x56),
        *range(0x60, 0x76), *range(0x80, 0x96),
        *range(0xA0, 0xA9), *range(0xB0, 0xB9), *range(0xC0, 0xC9),
        *range(0xE0, 0xF6),
    }
    for right, ev in enumerate(writes):
        while writes[left].time_ms < ev.time_ms - 12:
            left += 1
        window = writes[left:right + 1]
        zero_count = sum(
            1 for w in window
            if w.chip == 0 and w.register in zero_core_regs and w.value == 0
        )
        distinct = len({
            w.register for w in window
            if w.chip == 0 and w.register in zero_core_regs and w.value == 0
        })
        if zero_count >= 70 and distinct >= 65:
            reset_candidate = (window[0].time_ms, ev.time_ms, left)
            break
    if reset_candidate is None:
        raise FormatError("no ED2-style hard OPL restart burst was detected")

    reset_window_start, reset_window_end, reset_left = reset_candidate
    # Expand to the first write in the nearby stop/restart sequence.
    sequence_start = max(0, reset_window_start - 40)
    sequence_end = reset_window_end + 40
    sequence = [w for w in writes if sequence_start <= w.time_ms <= sequence_end]

    melodic_state = [False] * 9
    rhythm_state = 0
    transitions: list[dict[str, int | str]] = []
    for w in writes:
        if w.chip != 0:
            continue
        if 0xB0 <= w.register <= 0xB8:
            ch = w.register - 0xB0
            on = bool(w.value & 0x20)
            if on != melodic_state[ch]:
                transitions.append({
                    "time_ms": w.time_ms,
                    "kind": "key_on" if on else "key_off",
                    "channel": ch,
                    "register": w.register,
                    "value": w.value,
                })
                melodic_state[ch] = on
        elif w.register == 0xBD:
            new_rhythm = w.value & 0x1F
            changed = rhythm_state ^ new_rhythm
            for bit, name in enumerate(("hi_hat", "cymbal", "tom", "snare", "bass_drum")):
                if changed & (1 << bit):
                    transitions.append({
                        "time_ms": w.time_ms,
                        "kind": "rhythm_on" if new_rhythm & (1 << bit) else "rhythm_off",
                        "channel": name,
                        "register": 0xBD,
                        "value": w.value,
                    })
            rhythm_state = new_rhythm

    pre = [x for x in transitions if reset_window_start - 40 <= int(x["time_ms"]) <= reset_window_start + 2]
    post = [x for x in transitions if reset_window_end <= int(x["time_ms"]) <= reset_window_end + 80]
    # Use the final key-off cluster that begins the hard reset. Earlier same-tick
    # off/on retriggers are ordinary note articulation, not the loop seam.
    keyoffs = [
        x for x in pre
        if x["kind"] in ("key_off", "rhythm_off")
        and int(x["time_ms"]) >= reset_window_start
    ]
    if not keyoffs:
        keyoffs = [x for x in pre if x["kind"] in ("key_off", "rhythm_off")]
    first_key_off_ms = min((int(x["time_ms"]) for x in keyoffs), default=None)
    keyons_before = [
        x for x in transitions
        if x["kind"] in ("key_on", "rhythm_on")
        and (first_key_off_ms is None or int(x["time_ms"]) < first_key_off_ms)
    ]
    keyons_after = [x for x in transitions if x["kind"] in ("key_on", "rhythm_on") and int(x["time_ms"]) >= reset_window_end]
    last_key_on_ms = max((int(x["time_ms"]) for x in keyons_before), default=None)
    first_restart_key_on_ms = min((int(x["time_ms"]) for x in keyons_after), default=None)

    destructive_regs = {
        *range(0x20, 0x36), *range(0x40, 0x56),
        *range(0x60, 0x76), *range(0x80, 0x96),
        *range(0xC0, 0xC9), *range(0xE0, 0xF6),
        0x01, 0x08, 0xBD,
    }
    destructive_writes = [
        w for w in writes
        if first_key_off_ms is not None
        and first_key_off_ms <= w.time_ms <= (first_restart_key_on_ms or reset_window_end)
        and w.chip == 0 and w.register in destructive_regs
    ]
    zero_writes = [w for w in destructive_writes if w.value == 0]
    tl_writes = [w for w in destructive_writes if 0x40 <= w.register <= 0x55]

    risk = (
        first_key_off_ms is not None
        and first_restart_key_on_ms is not None
        and first_restart_key_on_ms - first_key_off_ms < 100
        and len(destructive_writes) >= 60
    )

    boundary_rows = [
        {
            "time_ms": w.time_ms,
            "relative_ms": w.time_ms - reset_window_start,
            "pair_index": w.pair_index,
            "chip": w.chip,
            "register_hex": f"{w.register:02X}",
            "value_hex": f"{w.value:02X}",
            "category": (
                "key/frequency" if 0xA0 <= w.register <= 0xB8 else
                "total_level" if 0x40 <= w.register <= 0x55 else
                "operator" if (0x20 <= w.register <= 0x95 or 0xE0 <= w.register <= 0xF5) else
                "rhythm/global" if w.register in (0x01, 0x08, 0xBD) else
                "other"
            ),
        }
        for w in sequence
    ]

    return {
        "file": str(path),
        "header": header,
        "hard_restart_detected": True,
        "restart_risk_detected": risk,
        "reset_window_start_ms": reset_window_start,
        "reset_window_end_ms": reset_window_end,
        "last_key_on_before_reset_ms": last_key_on_ms,
        "first_key_off_ms": first_key_off_ms,
        "first_restart_key_on_ms": first_restart_key_on_ms,
        "last_note_to_keyoff_ms": (
            None if last_key_on_ms is None or first_key_off_ms is None
            else first_key_off_ms - last_key_on_ms
        ),
        "keyoff_to_restart_keyon_ms": (
            None if first_key_off_ms is None or first_restart_key_on_ms is None
            else first_restart_key_on_ms - first_key_off_ms
        ),
        "destructive_register_writes_between_keyoff_and_restart": len(destructive_writes),
        "zero_register_writes_between_keyoff_and_restart": len(zero_writes),
        "total_level_writes_between_keyoff_and_restart": len(tl_writes),
        "keyoff_transitions_near_reset": keyoffs,
        "restart_transitions": post,
        "boundary_rows": boundary_rows,
        "finding": (
            "The capture proves that ED2 performs a hard YM3812 stop/reset/reload at the song restart. "
            "The final notes are key-offed only one scheduler interval before operator, TL, envelope, "
            "waveform, feedback and rhythm registers are rewritten. Reducing the source end does not "
            "remove this reset; the converted MUS must reach volume 0 and remain silent before its terminal tick."
        ),
    }


def write_dro_boundary_csv(report: dict[str, object], out_path: Path) -> int:
    rows = list(report.get("boundary_rows", []))
    fields = ["time_ms", "relative_ms", "pair_index", "chip", "register_hex", "value_hex", "category"]
    with out_path.open("w", newline="", encoding="utf-8-sig") as f:
        writer = csv.DictWriter(f, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)
    return len(rows)

# ---------------------------------------------------------------------------
# Analysis/report
# ---------------------------------------------------------------------------


def analyze_root(root: Path) -> dict[str, object]:
    result: dict[str, object] = {"root": str(root), "tool_version": VERSION}

    mon_files = sorted((root / "MON").glob("M_*.DLL")) if (root / "MON").is_dir() else []
    mon_entries = []
    for p in mon_files:
        try:
            recs = load_monsters(p)
            mon_entries.append({
                "file": p.name,
                "records": len(recs),
                "monsters": [
                    {
                        "slot": r.slot,
                        "name": r.name,
                        "hp": r.get_u16(4),
                        "attack": r.get_u16(0x0A),
                        "exp": stored_exp_to_actual(r.get_u16(0x0C)),
                        "exp_stored": r.get_u16(0x0C),
                        "gold": r.get_u16(0x0E),
                        "defense": r.get_u16(0x10),
                        "magic": r.get_u16(0x12),
                    }
                    for r in recs
                ],
            })
        except Exception as e:
            mon_entries.append({"file": p.name, "error": str(e)})
    result["mon"] = {"files": len(mon_files), "entries": mon_entries}

    ins_files = sorted((root / "BGM").glob("*.INS")) if (root / "BGM").is_dir() else []
    ins_entries = []
    standard = extended = 0
    for p in ins_files:
        try:
            recs = load_ins(p)
            s = sum(1 for r in recs if ins_is_standard(r))
            standard += s
            extended += len(recs) - s
            ins_entries.append({"file": p.name, "instruments": len(recs), "standard_opl": s, "extended_or_percussion": len(recs) - s})
        except Exception as e:
            ins_entries.append({"file": p.name, "error": str(e)})
    result["ins"] = {"files": len(ins_files), "standard_opl": standard, "extended_or_percussion": extended, "entries": ins_entries}

    mus_files = sorted((root / "BGM").glob("*.MUS")) if (root / "BGM").is_dir() else []
    mus_entries = []
    for p in mus_files:
        try:
            d = p.read_bytes()
            h = load_mus_header(d)
            cands = scan_mus_candidates(d, h, max_results=12)
            mus_entries.append({
                "file": p.name,
                "bytes": len(d),
                "track_count": h.track_count,
                "totals": h.totals,
                "candidate_streams": [
                    {"track": c.target_index, "total": c.target_total, "offset": c.start, "events": c.event_count, "score": round(c.score, 2)}
                    for c in cands
                ],
            })
        except Exception as e:
            mus_entries.append({"file": p.name, "error": str(e)})
    result["mus"] = {"files": len(mus_files), "entries": mus_entries}
    return result


# ---------------------------------------------------------------------------
# Tkinter GUI
# ---------------------------------------------------------------------------


def run_gui(initial_root: Optional[Path] = None) -> None:
    try:
        import tkinter as tk
        from tkinter import filedialog, messagebox, ttk
    except ImportError as e:
        raise SystemExit("Tkinter is required for GUI mode. Use the CLI export/report options instead.") from e

    class App(tk.Tk):
        def __init__(self, initial: Optional[Path]):
            super().__init__()
            self.title(f"{APP_NAME} {VERSION}")
            self.geometry("1180x780")
            self.minsize(980, 650)
            self.root_dir: Optional[Path] = None
            self.mon_path: Optional[Path] = None
            self.mon_records: list[MonsterRecord] = []
            self.ins_path: Optional[Path] = None
            self.ins_records: list[bytearray] = []
            self.mus_path: Optional[Path] = None
            self.mus_data: bytes = b""
            self.mus_header: Optional[MusHeader] = None
            self.mus_candidates: list[MusCandidate] = []
            self.selected_candidate: Optional[MusCandidate] = None
            self.vgm_path: Optional[Path] = None
            self.vgm_analysis: Optional[VgmAnalysis] = None

            self._build_ui()
            if initial and initial.exists():
                self.set_root(initial)

        def _build_ui(self) -> None:
            top = ttk.Frame(self, padding=8)
            top.pack(fill="x")
            ttk.Label(top, text="Game root:").pack(side="left")
            self.root_var = tk.StringVar()
            ttk.Entry(top, textvariable=self.root_var).pack(side="left", fill="x", expand=True, padx=6)
            ttk.Button(top, text="Open folder...", command=self.choose_root).pack(side="left")
            ttk.Button(top, text="Reload", command=self.reload_root).pack(side="left", padx=(6, 0))

            self.status_var = tk.StringVar(value="Open the ED2 game folder (the folder containing BGM and MON).")
            ttk.Label(self, textvariable=self.status_var, anchor="w", padding=(8, 0, 8, 6)).pack(fill="x")

            self.nb = ttk.Notebook(self)
            self.nb.pack(fill="both", expand=True, padx=8, pady=(0, 8))
            self._build_mon_tab()
            self._build_ins_tab()
            self._build_mus_tab()
            self._build_vgm_tab()

        def choose_root(self) -> None:
            folder = filedialog.askdirectory(title="Select ED2 game folder")
            if folder:
                self.set_root(Path(folder))

        def reload_root(self) -> None:
            text = self.root_var.get().strip()
            if text:
                self.set_root(Path(text))

        def set_root(self, root: Path) -> None:
            root = root.resolve()
            if not (root / "BGM").is_dir() or not (root / "MON").is_dir():
                messagebox.showerror(APP_NAME, "The selected folder must contain both BGM and MON folders.")
                return
            self.root_dir = root
            self.root_var.set(str(root))
            self._populate_mon_files()
            self._populate_ins_files()
            self._populate_mus_files()
            self._populate_vgm_templates()
            self.status_var.set(f"Loaded: {root}")

        # ---- MON ----
        def _build_mon_tab(self) -> None:
            tab = ttk.Frame(self.nb, padding=8)
            self.nb.add(tab, text="MON monsters")
            pan = ttk.Panedwindow(tab, orient="horizontal")
            pan.pack(fill="both", expand=True)

            left = ttk.Frame(pan)
            pan.add(left, weight=1)
            ttk.Label(left, text="M_*.DLL").pack(anchor="w")
            self.mon_file_list = tk.Listbox(left, exportselection=False, width=24)
            self.mon_file_list.pack(fill="both", expand=True)
            self.mon_file_list.bind("<<ListboxSelect>>", lambda _e: self.load_selected_mon_file())
            btns = ttk.Frame(left)
            btns.pack(fill="x", pady=(6, 0))
            ttk.Button(btns, text="Export CSV", command=self.mon_export_csv).pack(side="left", fill="x", expand=True)
            ttk.Button(btns, text="Import CSV", command=self.mon_import_csv).pack(side="left", fill="x", expand=True, padx=(4, 0))

            bulk = ttk.LabelFrame(left, text="Bulk balance", padding=6)
            bulk.pack(fill="x", pady=(8, 0))
            ttk.Label(bulk, text="Stat").grid(row=0, column=0, sticky="w")
            self.mon_bulk_field_var = tk.StringVar(value="HP")
            self.mon_bulk_field_combo = ttk.Combobox(
                bulk,
                textvariable=self.mon_bulk_field_var,
                state="readonly",
                values=("HP", "Attack", "EXP", "Gold", "Defense", "Magic"),
                width=13,
            )
            self.mon_bulk_field_combo.grid(row=0, column=1, sticky="ew", padx=(4, 0))
            ttk.Label(bulk, text="Expression").grid(row=1, column=0, sticky="w", pady=(5, 0))
            self.mon_bulk_expr_var = tk.StringVar(value="*1.5")
            ttk.Entry(bulk, textvariable=self.mon_bulk_expr_var, width=14).grid(row=1, column=1, sticky="ew", padx=(4, 0), pady=(5, 0))
            ttk.Label(bulk, text="Examples: +10  *1.5  log10(x)*100  x+log2(x)*20  ramp*1.5", wraplength=210).grid(row=2, column=0, columnspan=2, sticky="w", pady=(5, 0))
            ttk.Label(bulk, text="EXP is the raw DLL field. Use ED2 Mod Studio for runtime reward estimates.", wraplength=210).grid(row=3, column=0, columnspan=2, sticky="w", pady=(4, 0))
            ttk.Button(bulk, text="Apply to ALL monsters", command=self.mon_bulk_apply).grid(row=4, column=0, columnspan=2, sticky="ew", pady=(6, 0))
            bulk.columnconfigure(1, weight=1)

            mid = ttk.Frame(pan)
            pan.add(mid, weight=1)
            ttk.Label(mid, text="Detected monster records").pack(anchor="w")
            self.mon_tree = ttk.Treeview(mid, columns=("slot", "name", "hp"), show="headings", height=18)
            for col, text, width in (("slot", "Slot", 55), ("name", "Name", 150), ("hp", "HP", 70)):
                self.mon_tree.heading(col, text=text)
                self.mon_tree.column(col, width=width, stretch=(col == "name"))
            self.mon_tree.pack(fill="both", expand=True)
            self.mon_tree.bind("<<TreeviewSelect>>", lambda _e: self.mon_show_record())

            right = ttk.Frame(pan)
            pan.add(right, weight=3)
            ttk.Label(right, text="Monster editor").pack(anchor="w")
            form_canvas = tk.Canvas(right, highlightthickness=0)
            scroll = ttk.Scrollbar(right, orient="vertical", command=form_canvas.yview)
            form_canvas.configure(yscrollcommand=scroll.set)
            scroll.pack(side="right", fill="y")
            form_canvas.pack(side="left", fill="both", expand=True)
            form = ttk.Frame(form_canvas)
            window = form_canvas.create_window((0, 0), window=form, anchor="nw")
            form.bind("<Configure>", lambda _e: form_canvas.configure(scrollregion=form_canvas.bbox("all")))
            form_canvas.bind("<Configure>", lambda e: form_canvas.itemconfigure(window, width=e.width))

            self.mon_vars: dict[str, tk.StringVar] = {}
            row = 0
            ttk.Label(form, text="Name (CP949, max 15 bytes)").grid(row=row, column=0, sticky="w", pady=2)
            self.mon_vars["name"] = tk.StringVar()
            ttk.Entry(form, textvariable=self.mon_vars["name"], width=32).grid(row=row, column=1, sticky="ew", padx=6, pady=2)
            row += 1
            for key, label, _off, size in MON_BASIC_FIELDS:
                ttk.Label(form, text=label).grid(row=row, column=0, sticky="w", pady=2)
                var = tk.StringVar()
                self.mon_vars[key] = var
                ttk.Entry(form, textvariable=var, width=20).grid(row=row, column=1, sticky="ew", padx=6, pady=2)
                value_range = "0..65535 raw" if key == "exp" else ("0..255" if size == 1 else "0..65535")
                ttk.Label(form, text=value_range).grid(row=row, column=2, sticky="w")
                row += 1

            ttk.Separator(form).grid(row=row, column=0, columnspan=3, sticky="ew", pady=8)
            row += 1
            ttk.Label(form, text="Advanced bytes 0x14..0x2F (28 bytes, hex)").grid(row=row, column=0, columnspan=3, sticky="w")
            row += 1
            self.mon_adv = tk.Text(form, height=3, wrap="word")
            self.mon_adv.grid(row=row, column=0, columnspan=3, sticky="ew", pady=(2, 6))
            row += 1
            ttk.Label(form, text="0x1D..0x23 often behaves like an action/spell ID list; 0xEF is commonly unused. Unknown bytes are deliberately not renamed.", wraplength=650).grid(row=row, column=0, columnspan=3, sticky="w", pady=(0, 8))
            row += 1
            self.mon_save_btn = ttk.Button(form, text="Save monster (creates .bak)", command=self.mon_save_record)
            self.mon_save_btn.grid(row=row, column=0, columnspan=2, sticky="w")
            form.columnconfigure(1, weight=1)

        def _populate_mon_files(self) -> None:
            self.mon_file_list.delete(0, "end")
            if not self.root_dir:
                return
            for p in sorted((self.root_dir / "MON").glob("M_*.DLL")):
                self.mon_file_list.insert("end", p.name)

        def load_selected_mon_file(self) -> None:
            sel = self.mon_file_list.curselection()
            if not sel or not self.root_dir:
                return
            self.mon_path = self.root_dir / "MON" / self.mon_file_list.get(sel[0])
            try:
                self.mon_records = load_monsters(self.mon_path)
            except Exception as e:
                messagebox.showerror(APP_NAME, f"Could not parse {self.mon_path.name}:\n{e}")
                return
            self.mon_tree.delete(*self.mon_tree.get_children())
            for rec in self.mon_records:
                self.mon_tree.insert("", "end", iid=str(rec.slot), values=(rec.slot, rec.name, rec.get_u16(4)))
            self.status_var.set(f"{self.mon_path.name}: safely detected {len(self.mon_records)} monster record(s)")
            if self.mon_records:
                self.mon_tree.selection_set("0")
                self.mon_show_record()

        def mon_show_record(self) -> None:
            sel = self.mon_tree.selection()
            if not sel:
                return
            rec = self.mon_records[int(sel[0])]
            self.mon_vars["name"].set(rec.name)
            for key, _label, off, size in MON_BASIC_FIELDS:
                value = rec.get_u8(off) if size == 1 else rec.get_u16(off)
                if key == "exp":
                    value = stored_exp_to_actual(value)
                self.mon_vars[key].set(str(value))
            self.mon_adv.delete("1.0", "end")
            self.mon_adv.insert("1.0", bytes(rec.raw[0x14:0x30]).hex(" "))

        def mon_save_record(self) -> None:
            if not self.mon_path:
                return
            sel = self.mon_tree.selection()
            if not sel:
                return
            slot = int(sel[0])
            try:
                vals: dict[str, int | str] = {"name": self.mon_vars["name"].get()}
                for key, _label, _off, size in MON_BASIC_FIELDS:
                    if key == "exp":
                        actual = int(self.mon_vars[key].get().strip(), 0)
                        vals[key] = actual_exp_to_stored(actual)
                    else:
                        vals[key] = parse_int(self.mon_vars[key].get(), 8 if size == 1 else 16)
                vals["advanced_hex"] = self.mon_adv.get("1.0", "end").strip()
                patch_monster(self.mon_path, slot, vals, make_backup=True)
                self.load_selected_mon_file()
                self.mon_tree.selection_set(str(slot))
                self.status_var.set(f"Saved {self.mon_path.name} slot {slot}; original kept as {self.mon_path.name}.bak")
            except Exception as e:
                messagebox.showerror(APP_NAME, str(e))

        def mon_bulk_apply(self) -> None:
            if not self.root_dir:
                return
            display_field = self.mon_bulk_field_var.get().strip()
            field = display_field.lower()
            expression = self.mon_bulk_expr_var.get().strip()
            try:
                parse_bulk_rule(expression)
            except Exception as e:
                messagebox.showerror(APP_NAME, str(e))
                return

            label = MON_BULK_FIELDS[field][0] if field in MON_BULK_FIELDS else display_field
            msg = (
                f"Apply {expression} to {label} for EVERY detected monster?\n\n"
                "Each changed DLL gets a one-time .bak backup.\n"
                "Results are clamped to the valid range.\n"
                "Formula x is the current stat value; log/ln/log10/log2/log1p are supported.\n"
                "EXP formulas use actual awarded EXP (stored value - 1). ramp rules use M_*.DLL progression order."
            )
            if not messagebox.askyesno(APP_NAME, msg):
                return

            old_name = self.mon_path.name if self.mon_path else None
            try:
                result = bulk_adjust_monsters(self.root_dir, field, expression, make_backup=True)
                self._populate_mon_files()
                if old_name:
                    names = list(self.mon_file_list.get(0, "end"))
                    if old_name in names:
                        idx = names.index(old_name)
                        self.mon_file_list.selection_set(idx)
                        self.mon_file_list.see(idx)
                        self.load_selected_mon_file()
                self.status_var.set(
                    f"Bulk {label} {expression}: changed {result['records_changed']}/{result['records_scanned']} monsters "
                    f"in {result['files_changed']} DLL(s); clamped {result['clamped_values']} value(s)"
                )
                messagebox.showinfo(
                    APP_NAME,
                    f"Bulk edit complete.\n\n"
                    f"Monsters scanned: {result['records_scanned']}\n"
                    f"Monsters changed: {result['records_changed']}\n"
                    f"DLLs changed: {result['files_changed']}\n"
                    f"Clamped values: {result['clamped_values']}"
                )
            except Exception as e:
                messagebox.showerror(APP_NAME, str(e))

        def mon_export_csv(self) -> None:
            if not self.root_dir:
                return
            out = filedialog.asksaveasfilename(title="Export monster CSV", defaultextension=".csv", filetypes=[("CSV", "*.csv")], initialfile="ed2_monsters.csv")
            if not out:
                return
            try:
                n = export_mon_csv(self.root_dir, Path(out))
                self.status_var.set(f"Exported {n} monster records to {out}")
            except Exception as e:
                messagebox.showerror(APP_NAME, str(e))

        def mon_import_csv(self) -> None:
            if not self.root_dir:
                return
            src = filedialog.askopenfilename(title="Import monster CSV", filetypes=[("CSV", "*.csv"), ("All files", "*.*")])
            if not src:
                return
            if not messagebox.askyesno(APP_NAME, "Import values from this CSV? Each modified DLL will get a one-time .bak backup."):
                return
            try:
                n = import_mon_csv(self.root_dir, Path(src))
                self._populate_mon_files()
                self.status_var.set(f"Imported/patched {n} monster records")
            except Exception as e:
                messagebox.showerror(APP_NAME, str(e))

        # ---- INS ----
        def _build_ins_tab(self) -> None:
            tab = ttk.Frame(self.nb, padding=8)
            self.nb.add(tab, text="INS instruments")
            pan = ttk.Panedwindow(tab, orient="horizontal")
            pan.pack(fill="both", expand=True)
            left = ttk.Frame(pan)
            pan.add(left, weight=1)
            ttk.Label(left, text="*.INS").pack(anchor="w")
            self.ins_file_list = tk.Listbox(left, exportselection=False, width=24)
            self.ins_file_list.pack(fill="both", expand=True)
            self.ins_file_list.bind("<<ListboxSelect>>", lambda _e: self.load_selected_ins_file())
            ttk.Button(left, text="Export all INS CSV", command=self.ins_export_csv).pack(fill="x", pady=(6, 0))

            mid = ttk.Frame(pan)
            pan.add(mid, weight=1)
            ttk.Label(mid, text="Instrument index").pack(anchor="w")
            self.ins_tree = ttk.Treeview(mid, columns=("idx", "kind"), show="headings")
            self.ins_tree.heading("idx", text="Index")
            self.ins_tree.heading("kind", text="Detected kind")
            self.ins_tree.column("idx", width=60, stretch=False)
            self.ins_tree.column("kind", width=180)
            self.ins_tree.pack(fill="both", expand=True)
            self.ins_tree.bind("<<TreeviewSelect>>", lambda _e: self.ins_show_record())

            right = ttk.Frame(pan)
            pan.add(right, weight=3)
            canvas = tk.Canvas(right, highlightthickness=0)
            sb = ttk.Scrollbar(right, orient="vertical", command=canvas.yview)
            canvas.configure(yscrollcommand=sb.set)
            sb.pack(side="right", fill="y")
            canvas.pack(side="left", fill="both", expand=True)
            form = ttk.Frame(canvas, padding=(6, 0))
            win = canvas.create_window((0, 0), window=form, anchor="nw")
            form.bind("<Configure>", lambda _e: canvas.configure(scrollregion=canvas.bbox("all")))
            canvas.bind("<Configure>", lambda e: canvas.itemconfigure(win, width=e.width))

            self.ins_kind_var = tk.StringVar()
            ttk.Label(form, textvariable=self.ins_kind_var, wraplength=680).grid(row=0, column=0, columnspan=3, sticky="w", pady=(0, 8))
            self.ins_vars: dict[str, tk.StringVar] = {}
            row = 1
            for key, label, _pos, rng in INS_FIELDS:
                ttk.Label(form, text=label).grid(row=row, column=0, sticky="w", pady=1)
                var = tk.StringVar()
                self.ins_vars[key] = var
                ttk.Entry(form, textvariable=var, width=14).grid(row=row, column=1, sticky="w", padx=6, pady=1)
                ttk.Label(form, text=f"OPL meaning: {rng}; editor accepts raw 0..255").grid(row=row, column=2, sticky="w")
                row += 1
            ttk.Separator(form).grid(row=row, column=0, columnspan=3, sticky="ew", pady=7)
            row += 1
            ttk.Label(form, text="Raw 28 bytes (display only)").grid(row=row, column=0, sticky="w")
            self.ins_raw_var = tk.StringVar()
            ttk.Entry(form, textvariable=self.ins_raw_var, state="readonly").grid(row=row, column=1, columnspan=2, sticky="ew", padx=6)
            row += 1
            ttk.Label(form, text="Records that violate normal OPL ranges are marked extended/percussion. Their bytes are intentionally preserved rather than normalized.", wraplength=700).grid(row=row, column=0, columnspan=3, sticky="w", pady=8)
            row += 1
            ttk.Button(form, text="Save instrument (creates .bak)", command=self.ins_save_record).grid(row=row, column=0, columnspan=2, sticky="w")
            form.columnconfigure(2, weight=1)

        def _populate_ins_files(self) -> None:
            self.ins_file_list.delete(0, "end")
            if not self.root_dir:
                return
            for p in sorted((self.root_dir / "BGM").glob("*.INS")):
                self.ins_file_list.insert("end", p.name)

        def load_selected_ins_file(self) -> None:
            sel = self.ins_file_list.curselection()
            if not sel or not self.root_dir:
                return
            self.ins_path = self.root_dir / "BGM" / self.ins_file_list.get(sel[0])
            try:
                self.ins_records = load_ins(self.ins_path)
            except Exception as e:
                messagebox.showerror(APP_NAME, str(e))
                return
            self.ins_tree.delete(*self.ins_tree.get_children())
            for i, rec in enumerate(self.ins_records):
                kind = "standard OPL" if ins_is_standard(rec) else "extended/percussion"
                self.ins_tree.insert("", "end", iid=str(i), values=(i, kind))
            self.status_var.set(f"{self.ins_path.name}: {len(self.ins_records)} instruments")
            if self.ins_records:
                self.ins_tree.selection_set("0")
                self.ins_show_record()

        def ins_show_record(self) -> None:
            sel = self.ins_tree.selection()
            if not sel:
                return
            rec = self.ins_records[int(sel[0])]
            standard = ins_is_standard(rec)
            self.ins_kind_var.set(
                "Standard 2-operator OPL-like timbre: named fields are within expected hardware ranges."
                if standard else
                "Extended/percussion record: one or more bytes are outside conventional OPL field ranges. Edit raw values carefully; the tool will not destroy or clamp them."
            )
            for key, _label, pos, _rng in INS_FIELDS:
                self.ins_vars[key].set(str(rec[pos]))
            self.ins_raw_var.set(bytes(rec).hex(" "))

        def ins_save_record(self) -> None:
            if not self.ins_path:
                return
            sel = self.ins_tree.selection()
            if not sel:
                return
            idx = int(sel[0])
            try:
                rec = bytearray(28)
                for key, _label, pos, _rng in INS_FIELDS:
                    rec[pos] = parse_int(self.ins_vars[key].get(), 8)
                save_ins_record(self.ins_path, idx, rec, make_backup=True)
                self.load_selected_ins_file()
                self.ins_tree.selection_set(str(idx))
                self.status_var.set(f"Saved {self.ins_path.name} instrument {idx}; original kept as .bak")
            except Exception as e:
                messagebox.showerror(APP_NAME, str(e))

        def ins_export_csv(self) -> None:
            if not self.root_dir:
                return
            out = filedialog.asksaveasfilename(title="Export INS CSV", defaultextension=".csv", filetypes=[("CSV", "*.csv")], initialfile="ed2_instruments.csv")
            if not out:
                return
            try:
                n = export_ins_csv(self.root_dir, Path(out))
                self.status_var.set(f"Exported {n} instruments to {out}")
            except Exception as e:
                messagebox.showerror(APP_NAME, str(e))

        # ---- MUS ----
        def _build_mus_tab(self) -> None:
            tab = ttk.Frame(self.nb, padding=8)
            self.nb.add(tab, text="MUS experimental")
            pan = ttk.Panedwindow(tab, orient="horizontal")
            pan.pack(fill="both", expand=True)
            left = ttk.Frame(pan)
            pan.add(left, weight=1)
            ttk.Label(left, text="*.MUS").pack(anchor="w")
            self.mus_file_list = tk.Listbox(left, exportselection=False, width=24)
            self.mus_file_list.pack(fill="both", expand=True)
            self.mus_file_list.bind("<<ListboxSelect>>", lambda _e: self.load_selected_mus_file())

            right = ttk.Frame(pan)
            pan.add(right, weight=4)
            ttk.Label(right, text="This MUS parser is heuristic: the leading 9/11 channel count and duration totals are stable, but the complete proprietary event layout is not yet proven. Candidate note streams are edited in-place only.", wraplength=850).pack(anchor="w", pady=(0, 7))

            hdr_frame = ttk.LabelFrame(right, text="Header duration totals")
            hdr_frame.pack(fill="x")
            self.mus_hdr_tree = ttk.Treeview(hdr_frame, columns=("track", "total"), show="headings", height=5)
            self.mus_hdr_tree.heading("track", text="Track/channel")
            self.mus_hdr_tree.heading("total", text="Total ticks")
            self.mus_hdr_tree.column("track", width=110, stretch=False)
            self.mus_hdr_tree.column("total", width=110, stretch=False)
            self.mus_hdr_tree.pack(fill="x")

            cand_frame = ttk.LabelFrame(right, text="Heuristic note+duration streams")
            cand_frame.pack(fill="both", expand=True, pady=(7, 0))
            self.mus_cand_tree = ttk.Treeview(cand_frame, columns=("track", "total", "offset", "events", "score"), show="headings", height=7)
            for c, t, w in (("track", "Target", 70), ("total", "Ticks", 80), ("offset", "File offset", 100), ("events", "Events", 80), ("score", "Score", 80)):
                self.mus_cand_tree.heading(c, text=t)
                self.mus_cand_tree.column(c, width=w, stretch=False)
            self.mus_cand_tree.pack(fill="x")
            self.mus_cand_tree.bind("<<TreeviewSelect>>", lambda _e: self.mus_show_candidate())

            ev_frame = ttk.Frame(cand_frame)
            ev_frame.pack(fill="both", expand=True, pady=(5, 0))
            self.mus_event_tree = ttk.Treeview(ev_frame, columns=("i", "off", "note", "name", "dur"), show="headings")
            for c, t, w in (("i", "#", 55), ("off", "Offset", 90), ("note", "Note", 65), ("name", "Name", 90), ("dur", "Duration", 80)):
                self.mus_event_tree.heading(c, text=t)
                self.mus_event_tree.column(c, width=w, stretch=(c == "name"))
            self.mus_event_tree.pack(side="left", fill="both", expand=True)
            ev_scroll = ttk.Scrollbar(ev_frame, orient="vertical", command=self.mus_event_tree.yview)
            ev_scroll.pack(side="right", fill="y")
            self.mus_event_tree.configure(yscrollcommand=ev_scroll.set)
            self.mus_event_tree.bind("<<TreeviewSelect>>", lambda _e: self.mus_show_event())

            edit = ttk.Frame(cand_frame)
            edit.pack(fill="x", pady=6)
            ttk.Label(edit, text="Note 0..127").pack(side="left")
            self.mus_note_var = tk.StringVar()
            ttk.Entry(edit, textvariable=self.mus_note_var, width=7).pack(side="left", padx=(4, 10))
            ttk.Label(edit, text="Duration").pack(side="left")
            self.mus_dur_var = tk.StringVar()
            ttk.Entry(edit, textvariable=self.mus_dur_var, width=8).pack(side="left", padx=(4, 10))
            ttk.Button(edit, text="Apply event + save", command=self.mus_save_event).pack(side="left")
            ttk.Label(edit, text="Transpose stream").pack(side="left", padx=(18, 4))
            self.mus_transpose_var = tk.StringVar(value="0")
            ttk.Entry(edit, textvariable=self.mus_transpose_var, width=6).pack(side="left")
            ttk.Button(edit, text="Apply", command=self.mus_transpose).pack(side="left", padx=4)

        def _populate_mus_files(self) -> None:
            self.mus_file_list.delete(0, "end")
            if not self.root_dir:
                return
            for p in sorted((self.root_dir / "BGM").glob("*.MUS")):
                self.mus_file_list.insert("end", p.name)

        def load_selected_mus_file(self) -> None:
            sel = self.mus_file_list.curselection()
            if not sel or not self.root_dir:
                return
            self.mus_path = self.root_dir / "BGM" / self.mus_file_list.get(sel[0])
            try:
                self.mus_data = self.mus_path.read_bytes()
                self.mus_header = load_mus_header(self.mus_data)
                self.mus_candidates = scan_mus_candidates(self.mus_data, self.mus_header, max_results=60)
            except Exception as e:
                messagebox.showerror(APP_NAME, str(e))
                return
            self.mus_hdr_tree.delete(*self.mus_hdr_tree.get_children())
            assert self.mus_header
            for i, total in enumerate(self.mus_header.totals):
                self.mus_hdr_tree.insert("", "end", values=(i, total))
            self.mus_cand_tree.delete(*self.mus_cand_tree.get_children())
            for i, c in enumerate(self.mus_candidates):
                self.mus_cand_tree.insert("", "end", iid=str(i), values=(c.target_index, c.target_total, f"0x{c.start:X}", c.event_count, f"{c.score:.1f}"))
            self.mus_event_tree.delete(*self.mus_event_tree.get_children())
            self.status_var.set(f"{self.mus_path.name}: {self.mus_header.track_count} tracks/channels, {len(self.mus_candidates)} candidate stream(s)")
            if self.mus_candidates:
                self.mus_cand_tree.selection_set("0")
                self.mus_show_candidate()

        def mus_show_candidate(self) -> None:
            sel = self.mus_cand_tree.selection()
            if not sel:
                return
            self.selected_candidate = self.mus_candidates[int(sel[0])]
            self.mus_event_tree.delete(*self.mus_event_tree.get_children())
            for i, (off, note, dur) in enumerate(read_mus_candidate_events(self.mus_data, self.selected_candidate)):
                self.mus_event_tree.insert("", "end", iid=str(i), values=(i, f"0x{off:X}", note, midi_note_name(note), dur))
            if self.selected_candidate.event_count:
                self.mus_event_tree.selection_set("0")
                self.mus_show_event()

        def mus_show_event(self) -> None:
            if not self.selected_candidate:
                return
            sel = self.mus_event_tree.selection()
            if not sel:
                return
            idx = int(sel[0])
            off, note, dur = read_mus_candidate_events(self.mus_data, self.selected_candidate)[idx]
            self.mus_note_var.set(str(note))
            self.mus_dur_var.set(str(dur))

        def mus_save_event(self) -> None:
            if not self.mus_path or not self.selected_candidate:
                return
            sel = self.mus_event_tree.selection()
            if not sel:
                return
            idx = int(sel[0])
            events = read_mus_candidate_events(self.mus_data, self.selected_candidate)
            off = events[idx][0]
            try:
                note = parse_int(self.mus_note_var.get(), 8)
                if note > 127:
                    raise ValueError("note must be 0..127")
                dur = parse_int(self.mus_dur_var.get(), 16)
                if dur == 0:
                    raise ValueError("duration must be nonzero")
                patch_mus_event(self.mus_path, off, note, dur, make_backup=True)
                self.load_selected_mus_file()
                self.status_var.set(f"Saved MUS event at 0x{off:X}; original kept as .bak. Re-scan performed.")
            except Exception as e:
                messagebox.showerror(APP_NAME, str(e))

        def mus_transpose(self) -> None:
            if not self.mus_path or not self.selected_candidate:
                return
            try:
                semi = int(self.mus_transpose_var.get().strip(), 0)
                c = self.selected_candidate
                changed = transpose_mus_candidate(self.mus_path, c, semi, make_backup=True)
                self.load_selected_mus_file()
                self.status_var.set(f"Transposed {changed} non-rest events by {semi:+d} semitone(s); original kept as .bak")
            except Exception as e:
                messagebox.showerror(APP_NAME, str(e))

        # ---- VGM import ----
        def _build_vgm_tab(self) -> None:
            tab = ttk.Frame(self.nb, padding=10)
            self.nb.add(tab, text="VGM import")

            intro = (
                "VGM/VGZ -> ED2 MUS + INS converter. This version builds the compiled-ROL MUS structure from scratch: "
                "melodic notes, mid-song instrument changes, pitch register changes, and OPL rhythm mode are converted. "
                "No MUS template is required."
            )
            ttk.Label(tab, text=intro, wraplength=980, justify="left").grid(row=0, column=0, columnspan=4, sticky="ew", pady=(0, 10))

            ttk.Label(tab, text="VGM / VGZ source").grid(row=1, column=0, sticky="w")
            self.vgm_file_var = tk.StringVar()
            ttk.Entry(tab, textvariable=self.vgm_file_var).grid(row=1, column=1, columnspan=2, sticky="ew", padx=6)
            ttk.Button(tab, text="Browse...", command=self.vgm_choose_file).grid(row=1, column=3, sticky="ew")

            ttk.Label(tab, text="Apply as target").grid(row=2, column=0, sticky="w", pady=(7, 0))
            self.vgm_target_var = tk.StringVar(value="DS2_09")
            self.vgm_target_combo = ttk.Combobox(tab, textvariable=self.vgm_target_var)
            self.vgm_target_combo.grid(row=2, column=1, sticky="ew", padx=6, pady=(7, 0))
            ttk.Label(tab, text="writes BGM/<name>.MUS + .INS").grid(row=2, column=2, columnspan=2, sticky="w", pady=(7, 0))

            ttk.Label(tab, text="Ticks / beat").grid(row=3, column=0, sticky="w", pady=(7, 0))
            self.vgm_tpb_var = tk.StringVar(value=str(ED2_DEFAULT_TICKS_PER_BEAT))
            ttk.Entry(tab, textvariable=self.vgm_tpb_var, width=10).grid(row=3, column=1, sticky="w", padx=6, pady=(7, 0))
            ttk.Label(tab, text="Analyze VGM auto-fills the source update rate (for example 100 Hz -> BPM 250)").grid(row=3, column=2, columnspan=2, sticky="w", pady=(7, 0))

            ttk.Label(tab, text="Base tempo BPM").grid(row=4, column=0, sticky="w", pady=(7, 0))
            self.vgm_bpm_var = tk.StringVar(value=str(ED2_DEFAULT_BASE_TEMPO))
            ttk.Entry(tab, textvariable=self.vgm_bpm_var, width=10).grid(row=4, column=1, sticky="w", padx=6, pady=(7, 0))

            ttk.Label(tab, text="Beats / measure").grid(row=5, column=0, sticky="w", pady=(7, 0))
            self.vgm_beats_var = tk.StringVar(value=str(ED2_DEFAULT_BEATS_PER_MEASURE))
            ttk.Entry(tab, textvariable=self.vgm_beats_var, width=10).grid(row=5, column=1, sticky="w", padx=6, pady=(7, 0))

            ttk.Label(tab, text="Loop handling").grid(row=6, column=0, sticky="w", pady=(7, 0))
            self.vgm_loop_var = tk.StringVar(value="Full song (restart from beginning)")
            ttk.Combobox(
                tab, textvariable=self.vgm_loop_var, state="readonly",
                values=("VGM loop body (seamless)", "Full song (restart from beginning)"),
                width=34,
            ).grid(row=6, column=1, columnspan=2, sticky="w", padx=6, pady=(7, 0))
            ttk.Label(tab, text="MUS/ROL has no native arbitrary loop-start field.").grid(row=6, column=3, sticky="w", pady=(7, 0))

            ttk.Label(tab, text="Reduce end ticks").grid(row=7, column=0, sticky="w", pady=(7, 0))
            self.vgm_end_trim_var = tk.StringVar(value="0")
            ttk.Entry(tab, textvariable=self.vgm_end_trim_var, width=10).grid(row=7, column=1, sticky="w", padx=6, pady=(7, 0))
            ttk.Label(tab, text="Removes a capture-only tail; shortening this does not prevent ED2's hard OPL restart").grid(row=7, column=2, columnspan=2, sticky="w", pady=(7, 0))

            ttk.Label(tab, text="Restart guard ticks").grid(row=8, column=0, sticky="w", pady=(7, 0))
            self.vgm_restart_guard_var = tk.StringVar(value=str(ED2_RESTART_GUARD_DEFAULT_TICKS))
            ttk.Entry(tab, textvariable=self.vgm_restart_guard_var, width=10).grid(row=8, column=1, sticky="w", padx=6, pady=(7, 0))
            ttk.Label(tab, text="Post-key-off fade + fully muted ticks before ED2 clears YM3812 registers; use 0 only for diagnosis").grid(row=8, column=2, columnspan=2, sticky="w", pady=(7, 0))

            ttk.Label(tab, text="Hardware vibrato").grid(row=9, column=0, sticky="w", pady=(7, 0))
            self.vgm_vibrato_var = tk.StringVar(value="Native INS VIB (retail-compatible)")
            ttk.Combobox(
                tab, textvariable=self.vgm_vibrato_var, state="readonly",
                values=("Native INS VIB (retail-compatible)", "Bake VIB into MUS pitch (diagnostic)"),
                width=38,
            ).grid(row=9, column=1, columnspan=2, sticky="w", padx=6, pady=(7, 0))
            ttk.Label(tab, text="Direct A0/B0 bends are imported in both modes.").grid(row=9, column=3, sticky="w", pady=(7, 0))

            ttk.Label(tab, text="Loop seam").grid(row=10, column=0, sticky="w", pady=(7, 0))
            self.vgm_seam_var = tk.StringVar(value="DRO-verified restart guard (recommended)")
            ttk.Combobox(
                tab, textvariable=self.vgm_seam_var, state="readonly",
                values=(
                    "DRO-verified restart guard (recommended)",
                    "No restart guard / equal-length tracks (diagnostic)",
                    "Legacy v0.6.5 terminal preload (diagnostic)",
                ),
                width=43,
            ).grid(row=10, column=1, columnspan=2, sticky="w", padx=6, pady=(7, 0))
            ttk.Label(tab, text="Fades release tails to volume 0 before ED2 performs its hard register reset.").grid(row=10, column=3, sticky="w", pady=(7, 0))

            buttons = ttk.Frame(tab)
            buttons.grid(row=11, column=0, columnspan=4, sticky="ew", pady=12)
            ttk.Button(buttons, text="Analyze VGM", command=self.vgm_analyze).pack(side="left")
            ttk.Button(buttons, text="Convert + Apply to game", command=self.vgm_convert_apply).pack(side="left", padx=6)

            info = ttk.LabelFrame(tab, text="VGM analysis", padding=8)
            info.grid(row=12, column=0, columnspan=4, sticky="nsew")
            self.vgm_info = tk.Text(info, height=20, wrap="word")
            self.vgm_info.pack(fill="both", expand=True)
            self.vgm_info.insert("1.0", "Choose a VGM/VGZ file and click Analyze VGM.\n")
            self.vgm_info.configure(state="disabled")

            warn = (
                "v0.5 can use the VGM loop marker by moving the loop body to MUS tick 0. This creates a seamless ED2 whole-song loop, "
                "but a one-time intro plus an arbitrary partial loop is not representable in the compiled ROL/MUS file itself. Full-song mode preserves the intro and restarts at tick 0. "
                "The restart guard adds a short muted tail because ED2 hard-resets YM3812 at every whole-song restart. Existing target files receive one-time .bak backups."
            )
            ttk.Label(tab, text=warn, wraplength=980, justify="left").grid(row=13, column=0, columnspan=4, sticky="ew", pady=(10, 0))
            tab.columnconfigure(1, weight=1)
            tab.columnconfigure(2, weight=1)
            tab.rowconfigure(12, weight=1)

        def _populate_vgm_templates(self) -> None:
            """Historical name kept because set_root() already calls it; now fills target names only."""
            if not hasattr(self, "vgm_target_combo"):
                return
            targets: list[str] = []
            if self.root_dir:
                targets = [p.stem for p in sorted((self.root_dir / "BGM").glob("*.MUS"))]
            self.vgm_target_combo["values"] = targets
            if targets and self.vgm_target_var.get() not in targets:
                self.vgm_target_var.set(targets[0])

        def vgm_choose_file(self) -> None:
            filename = filedialog.askopenfilename(title="Select VGM/VGZ", filetypes=[("VGM music", "*.vgm *.vgz"), ("All files", "*.*")])
            if filename:
                self.vgm_file_var.set(filename)
                self.vgm_path = Path(filename)
                self.vgm_analyze()

        def _show_vgm_info(self, text: str) -> None:
            self.vgm_info.configure(state="normal")
            self.vgm_info.delete("1.0", "end")
            self.vgm_info.insert("1.0", text)
            self.vgm_info.configure(state="disabled")

        def vgm_analyze(self) -> None:
            text = self.vgm_file_var.get().strip()
            if not text:
                return
            try:
                path = Path(text)
                a = analyze_vgm(path)
                tpb_hint = int(self.vgm_tpb_var.get().strip(), 0)
                timing_hint = inspect_vgm_timing(path, tpb_hint)
                if timing_hint.recommended_base_tempo is not None:
                    self.vgm_bpm_var.set(str(timing_hint.recommended_base_tempo))
                self.vgm_end_trim_var.set(str(timing_hint.recommended_end_trim_ticks))
                guard_rate = timing_hint.recommended_tick_hz
                if guard_rate is None:
                    try:
                        guard_rate = tpb_hint * int(self.vgm_bpm_var.get().strip(), 0) / 60.0
                    except Exception:
                        guard_rate = 60.0
                self.vgm_restart_guard_var.set(str(max(4, int(math.ceil(guard_rate * 0.20)))))
                self.vgm_loop_var.set(
                    "VGM loop body (seamless)" if a.loop_sample is not None
                    else "Full song (restart from beginning)"
                )
                self.vgm_path = path
                self.vgm_analysis = a
                names = ["Melodic 1", "Melodic 2", "Melodic 3", "Melodic 4", "Melodic 5", "Melodic 6",
                         "Bass drum / melodic 7", "Snare / melodic 8", "Tom / melodic 9", "Cymbal", "Hi-hat"]
                lines = [
                    f"File: {path.name}",
                    f"Duration: {a.duration_seconds:.3f} sec",
                    f"VGM header update rate: {timing_hint.header_rate_hz or 'not set'} Hz",
                    f"Recommended timing: {tpb_hint} TPB / {timing_hint.recommended_base_tempo or 'manual'} BPM"
                    + (f" = {timing_hint.recommended_tick_hz:g} ticks/sec" if timing_hint.recommended_tick_hz is not None else ""),
                    f"Recommended end trim: {timing_hint.recommended_end_trim_ticks} tick(s)"
                    + (f" ({timing_hint.reason})" if timing_hint.reason else ""),
                    f"Restart guard: {self.vgm_restart_guard_var.get()} tick(s), about 200 ms",
                    f"YM3812 register writes: {a.ym3812_writes}",
                    f"Detected note spans: {len(a.notes)}",
                    f"Normalized timbres at note-on: {len(a.instruments)}",
                    f"Rhythm mode: {'YES (11-voice ED2 MUS)' if a.rhythm_mode else 'no (9-voice ED2 MUS)'}",
                    f"Loop point: {a.loop_sample if a.loop_sample is not None else 'none'} samples",
                    f"Loop time: {a.loop_sample / VGM_SAMPLE_RATE:.6f} sec" if a.loop_sample is not None else "Loop time: none",
                    f"Loop body duration: {(a.total_samples - a.loop_sample) / VGM_SAMPLE_RATE:.6f} sec" if a.loop_sample is not None else "Loop body duration: n/a",
                    f"Direct A0/B0 pitch points: {len(a.pitch_points)}",
                    f"Hardware-vibrato notes: {sum(1 for n in a.notes if n.hardware_vibrato)}",
                    "",
                    "Logical voice note counts:",
                ]
                for ch, count in enumerate(a.channel_note_counts):
                    if ch >= 9 and not a.rhythm_mode and count == 0:
                        continue
                    lines.append(f"  {ch:2d} {names[ch]}: {count}")
                if a.rhythm_mode:
                    labels = ("Bass drum", "Snare", "Tom", "Cymbal", "Hi-hat")
                    lines += ["", "0xBD rhythm triggers:"]
                    for label, count in zip(labels, a.rhythm_trigger_counts):
                        lines.append(f"  {label}: {count}")
                lines += [
                    "",
                    "v0.6.7 conversion:",
                    "  - A0/B0 key state -> note/rest duration streams",
                    "  - 20/40/60/80/E0/C0 -> normalized 28-byte INS timbres",
                    "  - timbre changes at note-on -> MUS instrument events",
                    "  - A0/B0 frequency motion while keyed -> MUS pitch events",
                    "  - OPL operator VIB -> native INS flags, or optional MUS-pitch bake",
                    "  - DRO-verified restart guard key-offs, fades TL to silence, then leaves muted ticks before ED2 hard-reset",
                    f"  - 40h Total Level changes -> recovered MUS volume events ({len(a.volume_points)} source points)",
                    "  - 0xBD rhythm bits -> Bass/Snare/Tom/Cymbal/Hi-hat voices",
                    "  - MUS is built from scratch; no structural template is used",
                    "  - VGM loop-body mode can move the VGM loop start to MUS tick 0",
                ]
                self._show_vgm_info("\n".join(lines))
                self.status_var.set(f"Analyzed {path.name}: {len(a.notes)} notes, rhythm={'yes' if a.rhythm_mode else 'no'}")
            except Exception as e:
                messagebox.showerror(APP_NAME, str(e))

        def vgm_convert_apply(self) -> None:
            if not self.root_dir:
                return
            source = self.vgm_file_var.get().strip()
            if not source:
                messagebox.showerror(APP_NAME, "select a VGM/VGZ source")
                return
            try:
                target_stem = self.vgm_target_var.get().strip()
                if not target_stem:
                    raise ValueError("enter a target BGM base name")
                if any(c in target_stem for c in "/:*?\"<>|\\"):
                    raise ValueError("target name contains an invalid filename character")
                tpb = int(self.vgm_tpb_var.get().strip(), 0)
                bpm = int(self.vgm_bpm_var.get().strip(), 0)
                beats = int(self.vgm_beats_var.get().strip(), 0)
                end_trim = int(self.vgm_end_trim_var.get().strip(), 0)
                restart_guard = int(self.vgm_restart_guard_var.get().strip(), 0)
                if not 1 <= tpb <= 65535:
                    raise ValueError("ticks/beat must be 1..65535")
                if not 1 <= bpm <= 65535:
                    raise ValueError("base tempo must be 1..65535 BPM")
                if not 1 <= beats <= 65535:
                    raise ValueError("beats/measure must be 1..65535")
                if not 0 <= end_trim <= 65534:
                    raise ValueError("reduce end ticks must be 0..65534")
                if restart_guard < 0 or 0 < restart_guard < 4:
                    raise ValueError("restart guard must be 0 or at least 4 ticks")
                bgm = self.root_dir / "BGM"
                out_mus = bgm / f"{target_stem}.MUS"
                out_ins = bgm / f"{target_stem}.INS"
                tick_hz = tpb * bpm / 60.0
                loop_mode = "vgm" if self.vgm_loop_var.get().startswith("VGM loop") else "full"
                vibrato_mode = "bake" if self.vgm_vibrato_var.get().startswith("Bake") else "native"
                seam_choice = self.vgm_seam_var.get()
                legacy_terminal_preload = seam_choice.startswith("Legacy v0.6.5")
                ed2_loop_seam = not seam_choice.startswith("No restart guard")
                if not ed2_loop_seam or legacy_terminal_preload:
                    restart_guard = 0
                if loop_mode == "vgm":
                    analysis = self.vgm_analysis if self.vgm_analysis is not None and self.vgm_path == Path(source) else analyze_vgm(Path(source))
                    if analysis.loop_sample is None:
                        raise ValueError("selected VGM has no loop point; choose Full song mode")
                msg = (
                    f"Convert {Path(source).name} and apply as {target_stem}?\n\n"
                    f"Timing: {tpb} ticks/beat, {bpm} BPM = {tick_hz:g} ticks/sec\n"
                    f"Loop: {'VGM loop body -> MUS tick 0' if loop_mode == 'vgm' else 'full song -> restart at tick 0'}\n"
                    f"Reduce end ticks: {end_trim}\n"
                    f"Restart guard: {restart_guard} tick(s)\n"
                    f"Loop seam: {seam_choice}\n"
                    f"Output: {out_mus.name} + {out_ins.name}\n"
                    "Existing target files will receive one-time .bak backups."
                )
                if not messagebox.askyesno(APP_NAME, msg):
                    return
                report = convert_vgm_to_ed2_pair(
                    Path(source), out_mus, out_ins,
                    ticks_per_beat=tpb, base_tempo=bpm,
                    beats_per_measure=beats, make_backup=True, loop_mode=loop_mode,
                    end_trim_ticks=end_trim,
                    restart_guard_ticks=restart_guard,
                    vibrato_mode=vibrato_mode,
                    ed2_loop_seam=ed2_loop_seam,
                    legacy_terminal_preload=legacy_terminal_preload,
                )
                self._populate_ins_files()
                self._populate_mus_files()
                self._populate_vgm_templates()
                self._show_vgm_info(json.dumps(report, ensure_ascii=False, indent=2))
                self.status_var.set(f"Applied VGM -> {out_mus.name} + {out_ins.name}; .bak kept for existing targets")
                messagebox.showinfo(APP_NAME, f"Converted and applied successfully.\n\n{out_mus.name}\n{out_ins.name}")
            except Exception as e:
                messagebox.showerror(APP_NAME, str(e))


    app = App(initial_root)
    app.mainloop()


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def main(argv: Optional[list[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=APP_NAME)
    parser.add_argument("root", nargs="?", type=Path, help="ED2 game root containing BGM and MON")
    parser.add_argument("--report-json", type=Path, help="write a structural analysis report and exit")
    parser.add_argument("--export-mon-csv", type=Path, help="export detected monster records to CSV and exit")
    parser.add_argument("--import-mon-csv", type=Path, help="import monster CSV values (creates .bak files) and exit")
    parser.add_argument("--bulk-mon", nargs=2, metavar=("FIELD", "EXPR"), help="bulk-adjust all monsters; EXPR: +10, *1.5, log10(x)*100, x+log2(x)*20, ramp*1.5")
    parser.add_argument("--export-ins-csv", type=Path, help="export all INS records to CSV and exit")
    parser.add_argument("--analyze-vgm", type=Path, help="analyze a VGM/VGZ YM3812 file and print JSON")
    parser.add_argument("--analyze-dro", type=Path, help="analyze a DOSBox DRO v2 loop restart and print JSON")
    parser.add_argument("--vgm-import", nargs="+", metavar="ARG", help="convert SOURCE.vgm/vgz directly to ED2 BGM/TARGET.MUS+.INS. New syntax: SOURCE TARGET. Old SOURCE TEMPLATE TARGET is accepted for timing defaults.")
    parser.add_argument("--vgm-tpb", type=int, help=f"ticks per beat for --vgm-import (default: {ED2_DEFAULT_TICKS_PER_BEAT})")
    parser.add_argument("--vgm-bpm", type=int, help=f"base tempo BPM for --vgm-import (default: {ED2_DEFAULT_BASE_TEMPO})")
    parser.add_argument("--vgm-beats", type=int, help=f"beats per measure for --vgm-import (default: {ED2_DEFAULT_BEATS_PER_MEASURE})")
    parser.add_argument("--vgm-tick-hz", type=float, help="legacy convenience option; base BPM is derived from this tick rate and --vgm-tpb")
    parser.add_argument("--vgm-loop", choices=("full", "vgm", "auto"), default="auto", help="loop handling: full keeps intro; vgm moves VGM loop body to MUS tick 0; auto uses VGM loop when present")
    parser.add_argument("--vgm-end-trim", type=int, default=0, help="remove this many ticks from the generated MUS end (default: 0)")
    parser.add_argument("--vgm-restart-guard", type=int, help="post-key-off fade/silence ticks before ED2 hard-resets OPL (default: about 200 ms)")
    parser.add_argument("--vgm-vibrato", choices=("native", "bake"), default="native", help="native preserves INS VIB bits; bake approximates hardware VIB in MUS pitch and clears those bits")
    parser.add_argument(
        "--vgm-loop-seam",
        choices=("safe", "equal", "legacy-preload", "ed2", "legacy"),
        default="safe",
        help=(
            "safe: DRO-verified release fade plus silent restart guard (default); "
            "equal: disable the restart guard for diagnosis; "
            "legacy-preload: reproduce v0.6.5 terminal instrument writes for diagnosis. "
            "ed2/legacy are compatibility aliases for safe/equal."
        ),
    )
    parser.add_argument("--vgm-auto-config", action="store_true", help="derive BPM and proven terminal trim from the VGM header/command stream")
    parser.add_argument("--no-gui", action="store_true", help="do not start the GUI")
    args = parser.parse_args(argv)

    root = args.root.resolve() if args.root else None
    action = any((args.report_json, args.export_mon_csv, args.import_mon_csv, args.export_ins_csv, args.bulk_mon, args.analyze_vgm, args.analyze_dro, args.vgm_import))
    root_required = any((args.report_json, args.export_mon_csv, args.import_mon_csv, args.export_ins_csv, args.bulk_mon, args.vgm_import))
    if root_required and root is None:
        parser.error("ROOT is required for this CLI action")

    if args.report_json:
        report = analyze_root(root)  # type: ignore[arg-type]
        args.report_json.write_text(json.dumps(report, ensure_ascii=False, indent=2), encoding="utf-8")
        print(f"Wrote {args.report_json}")
    if args.export_mon_csv:
        n = export_mon_csv(root, args.export_mon_csv)  # type: ignore[arg-type]
        print(f"Exported {n} monster records -> {args.export_mon_csv}")
    if args.import_mon_csv:
        n = import_mon_csv(root, args.import_mon_csv)  # type: ignore[arg-type]
        print(f"Patched {n} monster records from {args.import_mon_csv}")
    if args.bulk_mon:
        field, expr = args.bulk_mon
        result = bulk_adjust_monsters(root, field, expr, make_backup=True)  # type: ignore[arg-type]
        print(
            f"Bulk {field} {expr}: changed {result['records_changed']}/{result['records_scanned']} monsters "
            f"in {result['files_changed']} DLL(s); clamped {result['clamped_values']} value(s)"
        )
    if args.export_ins_csv:
        n = export_ins_csv(root, args.export_ins_csv)  # type: ignore[arg-type]
        print(f"Exported {n} instrument records -> {args.export_ins_csv}")

    if args.analyze_vgm:
        a = analyze_vgm(args.analyze_vgm)
        timing_hint = inspect_vgm_timing(args.analyze_vgm, args.vgm_tpb or ED2_DEFAULT_TICKS_PER_BEAT)
        print(json.dumps({
            "file": str(args.analyze_vgm),
            "duration_seconds": round(a.duration_seconds, 3),
            "total_samples": a.total_samples,
            "ym3812_writes": a.ym3812_writes,
            "notes": len(a.notes),
            "unique_instruments": len(a.instruments),
            "channel_note_counts": a.channel_note_counts,
            "rhythm_mode": a.rhythm_mode,
            "rhythm_trigger_counts": a.rhythm_trigger_counts,
            "pitch_points": len(a.pitch_points),
            "volume_points": len(a.volume_points),
            "loop_sample": a.loop_sample,
            "vgm_header_rate_hz": timing_hint.header_rate_hz,
            "recommended_base_tempo": timing_hint.recommended_base_tempo,
            "recommended_tick_hz": timing_hint.recommended_tick_hz,
            "recommended_end_trim_ticks": timing_hint.recommended_end_trim_ticks,
            "timing_reason": timing_hint.reason,
        }, ensure_ascii=False, indent=2))
    if args.analyze_dro:
        dro_report = audit_dro_loop_restart(args.analyze_dro)
        # Boundary rows are useful for CSV export but too verbose for terminal JSON.
        compact = dict(dro_report)
        compact["boundary_event_count"] = len(compact.pop("boundary_rows", []))
        print(json.dumps(compact, ensure_ascii=False, indent=2))

    if args.vgm_import:
        if len(args.vgm_import) not in (2, 3):
            parser.error("--vgm-import expects SOURCE TARGET, or legacy SOURCE TEMPLATE TARGET")
        source_text = args.vgm_import[0]
        bgm = root / "BGM"  # type: ignore[operator]
        template_stem: Optional[str] = None
        if len(args.vgm_import) == 2:
            target_stem = args.vgm_import[1]
        else:
            template_stem = args.vgm_import[1]
            target_stem = args.vgm_import[2]

        tpb = args.vgm_tpb or ED2_DEFAULT_TICKS_PER_BEAT
        bpm = args.vgm_bpm or ED2_DEFAULT_BASE_TEMPO
        beats = args.vgm_beats or ED2_DEFAULT_BEATS_PER_MEASURE
        if template_stem and not any((args.vgm_tpb, args.vgm_bpm, args.vgm_beats, args.vgm_tick_hz)):
            template_path = bgm / f"{template_stem}.MUS"
            if template_path.is_file():
                tm = parse_mus(template_path.read_bytes())
                tpb, bpm, beats = tm.ticks_per_beat, tm.base_tempo, tm.beats_per_measure
        if args.vgm_tick_hz is not None:
            if args.vgm_tick_hz <= 0:
                parser.error("--vgm-tick-hz must be > 0")
            bpm = max(1, int(math.floor(args.vgm_tick_hz * 60.0 / tpb + 0.5)))
        end_trim = args.vgm_end_trim
        if args.vgm_auto_config:
            timing_hint = inspect_vgm_timing(Path(source_text), tpb)
            if timing_hint.recommended_base_tempo is not None:
                bpm = timing_hint.recommended_base_tempo
            if end_trim == 0:
                end_trim = timing_hint.recommended_end_trim_ticks

        restart_guard = args.vgm_restart_guard
        if restart_guard is None:
            restart_guard = max(4, int(math.ceil((tpb * bpm / 60.0) * 0.20)))
        if args.vgm_loop_seam in ("equal", "legacy"):
            restart_guard = 0
        if args.vgm_loop_seam == "legacy-preload":
            restart_guard = 0
        if restart_guard < 0 or 0 < restart_guard < 4:
            parser.error("--vgm-restart-guard must be 0 or at least 4")

        report = convert_vgm_to_ed2_pair(
            Path(source_text),
            bgm / f"{target_stem}.MUS",
            bgm / f"{target_stem}.INS",
            ticks_per_beat=tpb,
            base_tempo=bpm,
            beats_per_measure=beats,
            make_backup=True,
            loop_mode=args.vgm_loop,
            end_trim_ticks=end_trim,
            restart_guard_ticks=restart_guard,
            vibrato_mode=args.vgm_vibrato,
            ed2_loop_seam=args.vgm_loop_seam in ("safe", "ed2", "legacy-preload"),
            legacy_terminal_preload=args.vgm_loop_seam == "legacy-preload",
        )
        print(json.dumps(report, ensure_ascii=False, indent=2))

    if args.no_gui or action:
        return 0
    run_gui(root)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
