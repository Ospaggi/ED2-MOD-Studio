#!/usr/bin/env python3
"""ED2 Mod Studio

Reverse-engineering based content editor for the Korean IBM PC/DOS release of
Dragon Slayer: The Legend of Heroes II.

Confirmed writable systems:
- MON/M_*.DLL monster records
- MON/M_*.DLL battle-group metadata (drops, BGM, appearance references)
- ED2MAIN.EXE regular item table (IDs 0..75) and event item names (IDs 100..126)
- ED2MAIN.EXE magic parameter table (IDs 0..31)
- Read-only AI/hook analysis from bundled debug symbols
- MON/C_MO*.BZH appearance resource replacement/export
- Generic resource browser with conservative same-size replacement

All writes are atomic and create a .bak file once. Python standard library only.
"""
from __future__ import annotations

import argparse
import ast
import csv
import json
import math
import os
import shutil
import struct
import sys
import tempfile
from dataclasses import dataclass, asdict
from decimal import Decimal, InvalidOperation, ROUND_HALF_UP
from pathlib import Path
from typing import Iterable, Optional, Any

APP_NAME = "ED2 Mod Studio"
VERSION = "0.8.2"
ITEM_COUNT = 76
ITEM_NAME_BASE = 0x14A185
ITEM_STRIDE = 20
EVENT_ITEM_ID_BASE = 100
EVENT_ITEM_COUNT = 27
EVENT_ITEM_NAME_BASE = 0x14A775
EVENT_ITEM_NAME_SIZE = 14
MAGIC_COUNT = 32
MAGIC_PARAM_BASE = 0x14AA3C
MAGIC_RECORD_SIZE = 12
MAGIC_HANDLER_TABLE_BASE = 0x14B4B8


class FormatError(Exception):
    pass


def u16(data: bytes | bytearray, off: int) -> int:
    if off < 0 or off + 2 > len(data):
        raise FormatError(f"u16 read outside file at 0x{off:X}")
    return struct.unpack_from("<H", data, off)[0]


def p16(data: bytearray, off: int, value: int) -> None:
    if not 0 <= value <= 0xFFFF:
        raise ValueError("16-bit value must be 0..65535")
    if off < 0 or off + 2 > len(data):
        raise FormatError(f"u16 write outside file at 0x{off:X}")
    struct.pack_into("<H", data, off, value)


def parse_number(text: str, minimum: int, maximum: int, label: str = "value") -> int:
    value = int(text.strip(), 0)
    if not minimum <= value <= maximum:
        raise ValueError(f"{label} must be {minimum}..{maximum}")
    return value


def csv_int(value: Any, minimum: int, maximum: int, label: str) -> int:
    text = str(value).strip()
    if not text:
        raise ValueError(f"{label} is empty")
    return parse_number(text, minimum, maximum, label)


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
        with os.fdopen(fd, "wb") as fp:
            fp.write(data)
            fp.flush()
            os.fsync(fp.fileno())
        os.replace(tmp_name, path)
    except Exception:
        try:
            os.unlink(tmp_name)
        except OSError:
            pass
        raise


def restore_backup(path: Path) -> None:
    backup = path.with_name(path.name + ".bak")
    if not backup.exists():
        raise FileNotFoundError(f"No backup found: {backup.name}")
    fd, tmp_name = tempfile.mkstemp(prefix=path.name + ".", suffix=".restore.tmp", dir=str(path.parent))
    try:
        with os.fdopen(fd, "wb") as fp:
            fp.write(backup.read_bytes())
            fp.flush()
            os.fsync(fp.fileno())
        os.replace(tmp_name, path)
    except Exception:
        try:
            os.unlink(tmp_name)
        except OSError:
            pass
        raise


# ---------------------------------------------------------------------------
# Safe formula evaluator
# ---------------------------------------------------------------------------

_ALLOWED_FUNCS = {
    "log": math.log,
    "ln": math.log,
    "log10": math.log10,
    "log2": math.log2,
    "log1p": math.log1p,
    "sqrt": math.sqrt,
    "abs": abs,
    "min": min,
    "max": max,
}


def _eval_formula_node(node: ast.AST, x: float) -> float:
    if isinstance(node, ast.Expression):
        return _eval_formula_node(node.body, x)
    if isinstance(node, ast.Constant) and isinstance(node.value, (int, float)) and not isinstance(node.value, bool):
        return float(node.value)
    if isinstance(node, ast.Name):
        if node.id.lower() == "x":
            return float(x)
        if node.id.lower() == "e":
            return math.e
        if node.id.lower() == "pi":
            return math.pi
        raise ValueError(f"Unknown name: {node.id}")
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.UAdd, ast.USub)):
        value = _eval_formula_node(node.operand, x)
        return value if isinstance(node.op, ast.UAdd) else -value
    if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Add, ast.Sub, ast.Mult, ast.Div, ast.Pow, ast.Mod)):
        left = _eval_formula_node(node.left, x)
        right = _eval_formula_node(node.right, x)
        if isinstance(node.op, ast.Add):
            return left + right
        if isinstance(node.op, ast.Sub):
            return left - right
        if isinstance(node.op, ast.Mult):
            return left * right
        if isinstance(node.op, ast.Div):
            if right == 0:
                raise ValueError("Division by zero")
            return left / right
        if isinstance(node.op, ast.Mod):
            if right == 0:
                raise ValueError("Modulo by zero")
            return left % right
        if abs(right) > 32:
            raise ValueError("Exponent magnitude must be <= 32")
        return left ** right
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
        name = node.func.id.lower()
        if name not in _ALLOWED_FUNCS:
            raise ValueError(f"Unsupported function: {node.func.id}")
        if node.keywords:
            raise ValueError("Keyword arguments are not allowed")
        args = [_eval_formula_node(arg, x) for arg in node.args]
        if name in ("log", "ln"):
            if len(args) not in (1, 2):
                raise ValueError("log() accepts one value or value and base")
            if args[0] <= 0:
                raise ValueError("log() requires a positive value; use log1p(x) when zero is possible")
            if len(args) == 2 and (args[1] <= 0 or args[1] == 1):
                raise ValueError("Invalid logarithm base")
        elif name in ("log10", "log2") and (len(args) != 1 or args[0] <= 0):
            raise ValueError(f"{name}() requires one positive value")
        elif name == "log1p" and (len(args) != 1 or args[0] <= -1):
            raise ValueError("log1p() requires one value greater than -1")
        elif name == "sqrt" and (len(args) != 1 or args[0] < 0):
            raise ValueError("sqrt() requires one nonnegative value")
        elif name == "abs" and len(args) != 1:
            raise ValueError("abs() accepts one value")
        elif name in ("min", "max") and not 1 <= len(args) <= 8:
            raise ValueError(f"{name}() accepts 1..8 values")
        return float(_ALLOWED_FUNCS[name](*args))
    raise ValueError("Formula may only use x, numbers, + - * / % ** and approved math functions")


def eval_formula(x: int, expression: str) -> int:
    text = expression.strip()
    if not text:
        raise ValueError("Formula is empty")
    compact = text.replace(" ", "")
    if len(compact) >= 2 and compact[0] in "+-*/=":
        try:
            operand = Decimal(compact[1:])
        except InvalidOperation as exc:
            raise ValueError("Invalid numeric operand") from exc
        if not operand.is_finite():
            raise ValueError("Operand must be finite")
        current = Decimal(x)
        if compact[0] == "+": result = current + operand
        elif compact[0] == "-": result = current - operand
        elif compact[0] == "*": result = current * operand
        elif compact[0] == "/":
            if operand == 0: raise ValueError("Division by zero")
            result = current / operand
        else: result = operand
        return int(result.quantize(Decimal("1"), rounding=ROUND_HALF_UP))
    try:
        tree = ast.parse(text, mode="eval")
    except SyntaxError as exc:
        raise ValueError("Invalid formula") from exc
    result = _eval_formula_node(tree, float(x))
    if not math.isfinite(result):
        raise ValueError("Formula result is not finite")
    return int(Decimal(str(result)).quantize(Decimal("1"), rounding=ROUND_HALF_UP))


# ---------------------------------------------------------------------------
# NE / MON DLL parser
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
        raise FormatError("Not an MZ executable")
    ne_off = struct.unpack_from("<I", data, 0x3C)[0]
    if ne_off + 0x40 > len(data) or data[ne_off:ne_off + 2] != b"NE":
        raise FormatError("Not a 16-bit NE module")
    count = u16(data, ne_off + 0x1C)
    table = ne_off + u16(data, ne_off + 0x22)
    shift = u16(data, ne_off + 0x32)
    if table + count * 8 > len(data):
        raise FormatError("Truncated NE segment table")
    result: list[NESegment] = []
    for i in range(count):
        sector, length, flags, min_alloc = struct.unpack_from("<HHHH", data, table + i * 8)
        offset = sector << shift
        real_len = 65536 if length == 0 else length
        if offset > len(data):
            raise FormatError("NE segment outside file")
        result.append(NESegment(i + 1, offset, real_len, flags, min_alloc))
    return result


def parse_ne_exports(data: bytes) -> dict[str, tuple[int, int]]:
    """Return exported NE symbols as name -> (segment, offset).

    The Korean ED2 executable keeps most engine globals and routines in the
    resident-name table.  Parsing the actual export table lets the editor
    validate item/magic locations instead of trusting file offsets alone.
    """
    if len(data) < 0x40 or data[:2] != b"MZ":
        raise FormatError("Not an MZ executable")
    ne = struct.unpack_from("<I", data, 0x3C)[0]
    if ne + 0x40 > len(data) or data[ne:ne + 2] != b"NE":
        raise FormatError("Not a 16-bit NE module")

    entry_off = ne + u16(data, ne + 0x04)
    entry_end = entry_off + u16(data, ne + 0x06)
    ordinal = 1
    entries: dict[int, tuple[int, int]] = {}
    pos = entry_off
    while pos < entry_end:
        if pos + 2 > len(data):
            raise FormatError("Truncated NE entry table")
        count, bundle_type = data[pos], data[pos + 1]
        pos += 2
        if count == 0:
            break
        if bundle_type == 0:
            ordinal += count
            continue
        if bundle_type == 0xFF:
            for _ in range(count):
                if pos + 6 > len(data):
                    raise FormatError("Truncated movable entry bundle")
                segment = data[pos + 3]
                offset = u16(data, pos + 4)
                entries[ordinal] = (segment, offset)
                ordinal += 1
                pos += 6
        else:
            for _ in range(count):
                if pos + 3 > len(data):
                    raise FormatError("Truncated fixed entry bundle")
                offset = u16(data, pos + 1)
                entries[ordinal] = (bundle_type, offset)
                ordinal += 1
                pos += 3

    def read_name_table(offset: int, size_limit: Optional[int] = None) -> list[tuple[str, int]]:
        result_names: list[tuple[str, int]] = []
        end = len(data) if size_limit is None else min(len(data), offset + size_limit)
        pos2 = offset
        while pos2 < end:
            length = data[pos2]
            pos2 += 1
            if length == 0:
                break
            if pos2 + length + 2 > end:
                raise FormatError("Truncated NE name table")
            name = data[pos2:pos2 + length].decode("latin1")
            pos2 += length
            ord_value = u16(data, pos2)
            pos2 += 2
            result_names.append((name, ord_value))
        return result_names

    resident = read_name_table(ne + u16(data, ne + 0x26))
    nonresident_off = struct.unpack_from("<I", data, ne + 0x2C)[0]
    nonresident_size = u16(data, ne + 0x20)
    nonresident = read_name_table(nonresident_off, nonresident_size)
    exports: dict[str, tuple[int, int]] = {}
    for name, ord_value in resident + nonresident:
        if ord_value in entries:
            exports[name] = entries[ord_value]
    return exports


def ne_address_to_file(data: bytes, segment: int, offset: int) -> int:
    segments = parse_ne_segments(data)
    if not 1 <= segment <= len(segments):
        raise FormatError(f"NE segment {segment} is outside the module")
    seg = segments[segment - 1]
    if not 0 <= offset < seg.length:
        raise FormatError(f"Offset 0x{offset:X} is outside NE segment {segment}")
    return seg.file_offset + offset


def decode_cp949_terminated(field: bytes, terminators: tuple[int, ...] = (0x06, 0x00)) -> str:
    end = len(field)
    for marker in terminators:
        try:
            end = min(end, field.index(marker))
        except ValueError:
            pass
    raw = field[:end]
    for enc in ("cp949", "euc-kr"):
        try:
            return raw.decode(enc).rstrip()
        except UnicodeDecodeError:
            pass
    return raw.decode("latin1", errors="replace").rstrip()


def encode_fixed_cp949(text: str, size: int, terminator: int = 0x06, left_pad: bool = False) -> bytes:
    raw = text.encode("cp949")
    if len(raw) > size - 1:
        raise ValueError(f"Text is too long: CP949 byte length must be <= {size - 1}")
    if left_pad:
        return b" " * (size - 1 - len(raw)) + raw + bytes([terminator])
    return raw + bytes([terminator]) + b"\x00" * (size - 1 - len(raw))


def is_monster_record(raw: bytes) -> bool:
    if len(raw) != 64 or 0x06 not in raw[48:64]:
        return False
    name = decode_cp949_terminated(raw[48:64])
    hp_cur, hp_max = u16(raw, 4), u16(raw, 6)
    return bool(name) and hp_cur > 0 and hp_cur == hp_max


def find_monster_table(data: bytes) -> tuple[NESegment, int]:
    best: Optional[tuple[NESegment, int]] = None
    for seg in parse_ne_segments(data):
        count = 0
        segment_end = min(len(data), seg.file_offset + seg.length)
        for slot in range(4):
            off = seg.file_offset + slot * 64
            if off + 64 > segment_end or not is_monster_record(data[off:off + 64]):
                break
            count += 1
        if count and (best is None or count > best[1]):
            best = (seg, count)
    if best is None:
        raise FormatError("No safe monster table found")
    return best


MONSTER_FIELDS: dict[str, tuple[int, int, str]] = {
    "record_id": (0x00, 2, "Record/Sprite slot reference"),
    "level": (0x03, 1, "Monster level"),
    "hp": (0x04, 2, "HP"),
    "attack": (0x0A, 2, "Attack"),
    "exp": (0x0C, 2, "Raw EXP"),
    "gold": (0x0E, 2, "Raw Gold"),
    "defense": (0x10, 2, "Defense"),
    "magic": (0x12, 2, "Magic"),
    "speed": (0x16, 1, "Speed"),
    "luck": (0x17, 1, "Luck"),
}


@dataclass
class MonsterRecord:
    dll_path: Path
    dll_number: int
    slot: int
    file_offset: int
    segment_offset: int
    raw: bytes

    @property
    def name(self) -> str:
        return decode_cp949_terminated(self.raw[48:64])

    def value(self, key: str) -> int:
        off, size, _ = MONSTER_FIELDS[key]
        return self.raw[off] if size == 1 else u16(self.raw, off)

    @property
    def active_in_formation(self) -> bool:
        """Whether this record is enabled in the DLL's initial battle formation.

        The high bit of the first record byte is set on unused/disabled slots.
        This distinction matters for the 16-bit battle reward accumulator: only
        active formation members are included in the normal encounter total.
        """
        return (self.raw[0] & 0x80) == 0


@dataclass
class MonsterGroup:
    dll_path: Path
    dll_number: int
    segment_offset: int
    record_count: int
    monster_names: list[str]
    graphic_id0: int
    graphic_addr0: int
    graphic_id1: int
    graphic_addr1: int
    init_message: int
    player_hook: int
    death_hook: int
    init_proc: int
    attack_escape_hook: int
    before_magic_hook: int
    before_damage_hook: int
    animation_hook: int
    drop_item_id: int
    drop_chance: int
    bgm_id: int
    magic_table_ptr: int
    attack_algo: int
    defense_algo: int
    magic_algo: int
    death_algo: int
    advanced_hex: str

    @property
    def label(self) -> str:
        names = ", ".join(self.monster_names[:2])
        return f"M_{self.dll_number:03X}  {names}"

    def hook_rows(self) -> list[tuple[str, int, str]]:
        return [
            ("_MO_INIT_MESS", self.init_message, "초기 메시지/데이터 포인터"),
            ("_MO_PLY_HOOK", self.player_hook, "플레이어 행동 훅"),
            ("_MO_DEAD_HOOK", self.death_hook, "사망 훅"),
            ("_MO_INIT_PROC", self.init_proc, "전투 초기화 루틴"),
            ("_MO_ATT_ESC", self.attack_escape_hook, "공격/도주 훅"),
            ("_MO_BFR_MAG", self.before_magic_hook, "마법 적용 직전 훅"),
            ("_MO_BFR_DMG", self.before_damage_hook, "피해 적용 직전 훅"),
            ("_MO_ANIME_HOOK", self.animation_hook, "애니메이션 훅"),
            ("_MO_MAG_PTR", self.magic_table_ptr, "몬스터 마법 테이블 포인터"),
            ("_MO_ATT_ALGO", self.attack_algo, "공격 AI 진입점"),
            ("_MO_DEF_ALGO", self.defense_algo, "방어 AI 진입점"),
            ("_MO_MAG_ALGO", self.magic_algo, "마법 AI 진입점"),
            ("_MO_DED_ALGO", self.death_algo, "사망 판정 AI 진입점"),
        ]


def dll_number(path: Path) -> int:
    try:
        return int(path.stem.split("_")[-1], 16)
    except ValueError:
        return -1


def load_monsters(path: Path) -> list[MonsterRecord]:
    data = path.read_bytes()
    seg, count = find_monster_table(data)
    number = dll_number(path)
    return [
        MonsterRecord(path, number, slot, seg.file_offset + slot * 64, seg.file_offset,
                      data[seg.file_offset + slot * 64:seg.file_offset + (slot + 1) * 64])
        for slot in range(count)
    ]


def load_group(path: Path) -> MonsterGroup:
    data = path.read_bytes()
    seg, count = find_monster_table(data)
    base = seg.file_offset
    if base + 0x128 > min(len(data), seg.file_offset + seg.length):
        raise FormatError("MON group block is truncated")
    records = load_monsters(path)
    return MonsterGroup(
        path, dll_number(path), base, count, [r.name for r in records],
        u16(data, base + 0x100), u16(data, base + 0x102),
        u16(data, base + 0x104), u16(data, base + 0x106),
        u16(data, base + 0x108), u16(data, base + 0x10A),
        u16(data, base + 0x10C), u16(data, base + 0x10E),
        u16(data, base + 0x110), u16(data, base + 0x112),
        u16(data, base + 0x114), u16(data, base + 0x116),
        data[base + 0x118], data[base + 0x119], data[base + 0x11A],
        u16(data, base + 0x11C),
        u16(data, base + 0x120), u16(data, base + 0x122),
        u16(data, base + 0x124), u16(data, base + 0x126),
        data[base + 0x108:base + 0x128].hex(" ").upper(),
    )


def patch_monster(rec: MonsterRecord, values: dict[str, Any], make_backup: bool = True) -> dict[str, Any]:
    path = rec.dll_path
    data = bytearray(path.read_bytes())
    current = load_monsters(path)
    applied = dict(values)
    group = load_group(path)
    for reward_key in ("exp", "gold"):
        if reward_key in applied:
            applied[reward_key] = clamp_single_reward_raw(
                current, reward_key, rec.slot, int(applied[reward_key]), rec.dll_number, group.bgm_id
            )
    values = applied
    if rec.slot >= len(current):
        raise ValueError("Monster slot no longer exists; reload the project")
    target = current[rec.slot]
    base = target.file_offset
    if "name" in values:
        data[base + 48:base + 64] = encode_fixed_cp949(str(values["name"]), 16)
    for key in MONSTER_FIELDS:
        if key not in values:
            continue
        value = int(values[key])
        off, size, _ = MONSTER_FIELDS[key]
        if size == 1:
            if not 0 <= value <= 255: raise ValueError(f"{key}: 0..255 required")
            data[base + off] = value
        elif key == "hp":
            if not 1 <= value <= 65535: raise ValueError("HP: 1..65535 required")
            p16(data, base + 0x04, value)
            p16(data, base + 0x06, value)
        else:
            if not 0 <= value <= 65535: raise ValueError(f"{key}: 0..65535 required")
            p16(data, base + off, value)
    if "advanced_hex" in values:
        raw = bytes.fromhex(str(values["advanced_hex"]))
        if len(raw) != 24:
            raise ValueError("Advanced bytes must contain exactly 24 bytes (0x18..0x2F)")
        data[base + 0x18:base + 0x30] = raw
    if not is_monster_record(bytes(data[base:base + 64])):
        raise ValueError("Edited record failed safety validation")
    if len(data) != path.stat().st_size:
        raise AssertionError("In-place MON edit changed file size")
    atomic_write(path, bytes(data), make_backup)
    return applied


def patch_group(group: MonsterGroup, values: dict[str, int], make_backup: bool = True) -> None:
    path = group.dll_path
    data = bytearray(path.read_bytes())
    fresh = load_group(path)
    base = fresh.segment_offset
    mapping = {
        "graphic_id0": (0x100, 2, 0xFFFF),
        "graphic_addr0": (0x102, 2, 0xFFFF),
        "graphic_id1": (0x104, 2, 0xFFFF),
        "graphic_addr1": (0x106, 2, 0xFFFF),
        "drop_item_id": (0x118, 1, 255),
        "drop_chance": (0x119, 1, 100),
        "bgm_id": (0x11A, 1, 255),
    }
    for key, value in values.items():
        if key not in mapping: continue
        off, size, maximum = mapping[key]
        value = int(value)
        if not 0 <= value <= maximum:
            raise ValueError(f"{key}: 0..{maximum} required")
        if size == 1: data[base + off] = value
        else: p16(data, base + off, value)
    if data[base + 0x119] > 100:
        raise ValueError("Drop chance must be 0..100")
    atomic_write(path, bytes(data), make_backup)


# Runtime EXP estimator reconstructed from ED2MAIN.EXE.
def general_reward_90(raw: int) -> int:
    if raw <= 0: return 0
    value = (raw * 90) // 100
    return max(1, value)


def level_reward_rate(monster_level: int, party_average_level: int) -> int:
    difference = party_average_level - monster_level
    if difference <= 2: return 100
    if difference == 3: return 75
    if difference == 4: return 50
    if difference == 5: return 25
    return 0


def estimated_reward(raw: int, monster_level: int, party_average_level: int,
                     dll_num: int, bgm_id: int) -> tuple[int, str]:
    if raw <= 0: return 0, "No reward"
    if bgm_id == 8:
        return raw, "BGM 8 special battle: raw value"
    base = general_reward_90(raw)
    if dll_num >= 0x505:
        return base, "M_505+: 90%, level attenuation disabled"
    rate = level_reward_rate(monster_level, party_average_level)
    return (base * rate) // 100, f"90% × level rate {rate}%"


REWARD_ACCUMULATOR_MAX = 0xFFFF

def reward_before_accumulator(raw: int, dll_num: int, bgm_id: int) -> int:
    """Maximum value added to the 16-bit battle accumulator for one monster.

    Pre-M_505 level attenuation is intentionally not included: the guard uses
    the 100% case so the edited data stays safe at every possible party level.
    """
    if raw <= 0:
        return 0
    return raw if bgm_id == 8 else general_reward_90(raw)

def _active_records(records: list[MonsterRecord]) -> list[MonsterRecord]:
    active = [record for record in records if record.active_in_formation]
    return active or list(records)

def formation_reward_total(records: list[MonsterRecord], key: str, dll_num: int, bgm_id: int,
                           overrides: Optional[dict[int, int]] = None) -> int:
    overrides = overrides or {}
    return sum(
        reward_before_accumulator(overrides.get(record.slot, record.value(key)), dll_num, bgm_id)
        for record in _active_records(records)
    )

def max_raw_for_accumulator_reward(allowed_reward: int, dll_num: int, bgm_id: int) -> int:
    allowed_reward = max(0, min(REWARD_ACCUMULATOR_MAX, int(allowed_reward)))
    if bgm_id == 8:
        return allowed_reward
    if allowed_reward == 0:
        return 0
    # Largest raw value satisfying floor(raw * 90 / 100) <= allowed_reward.
    return min(0xFFFF, (((allowed_reward + 1) * 100) - 1) // 90)

def clamp_single_reward_raw(records: list[MonsterRecord], key: str, slot: int, desired_raw: int,
                            dll_num: int, bgm_id: int) -> int:
    target = next((record for record in records if record.slot == slot), None)
    if target is None or not target.active_in_formation:
        return max(0, min(0xFFFF, desired_raw))
    others = sum(
        reward_before_accumulator(record.value(key), dll_num, bgm_id)
        for record in _active_records(records) if record.slot != slot
    )
    allowed = max(0, REWARD_ACCUMULATOR_MAX - others)
    return min(max(0, desired_raw), max_raw_for_accumulator_reward(allowed, dll_num, bgm_id))

def fit_group_reward_raws(records: list[MonsterRecord], key: str, proposed: dict[int, int],
                          dll_num: int, bgm_id: int) -> tuple[dict[int, int], int]:
    """Proportionally reduce active formation rewards until the 16-bit sum is safe."""
    result = {record.slot: max(0, min(0xFFFF, proposed.get(record.slot, record.value(key))))
              for record in records}
    active = _active_records(records)
    total = sum(reward_before_accumulator(result[record.slot], dll_num, bgm_id) for record in active)
    if total <= REWARD_ACCUMULATOR_MAX:
        return result, 0

    # Integer binary search avoids float-dependent results. 1_000_000 means 100%.
    lo, hi = 0, 1_000_000
    while lo < hi:
        mid = (lo + hi + 1) // 2
        scaled_total = sum(
            reward_before_accumulator((result[record.slot] * mid) // 1_000_000, dll_num, bgm_id)
            for record in active
        )
        if scaled_total <= REWARD_ACCUMULATOR_MAX:
            lo = mid
        else:
            hi = mid - 1
    scale = lo
    adjusted = dict(result)
    for record in active:
        adjusted[record.slot] = (result[record.slot] * scale) // 1_000_000

    # Use any small remaining capacity without changing the relative ordering.
    while True:
        current_total = sum(
            reward_before_accumulator(adjusted[record.slot], dll_num, bgm_id) for record in active
        )
        best_slot = None
        best_gain = None
        for record in active:
            slot = record.slot
            if adjusted[slot] >= result[slot]:
                continue
            old_reward = reward_before_accumulator(adjusted[slot], dll_num, bgm_id)
            new_reward = reward_before_accumulator(adjusted[slot] + 1, dll_num, bgm_id)
            gain = new_reward - old_reward
            if current_total + gain <= REWARD_ACCUMULATOR_MAX:
                best_slot, best_gain = slot, gain
                if gain > 0:
                    break
        if best_slot is None:
            break
        adjusted[best_slot] += 1
        if best_gain == 0:
            # Zero-gain raw increments can otherwise create long loops. Jump to the
            # next reward boundary, but never beyond the requested value.
            allowed = REWARD_ACCUMULATOR_MAX - current_total
            max_raw = max_raw_for_accumulator_reward(
                reward_before_accumulator(adjusted[best_slot], dll_num, bgm_id) + allowed, dll_num, bgm_id
            )
            adjusted[best_slot] = min(result[best_slot], max(adjusted[best_slot], max_raw))
    changed = sum(adjusted[record.slot] != result[record.slot] for record in active)
    return adjusted, changed


# ---------------------------------------------------------------------------
# ED2MAIN item table
# ---------------------------------------------------------------------------

STAT_GROUP_LABELS = {
    0: "없음 / 소모품 / 특수",
    1: "공격력 PLY_ATT (+0x10)",
    2: "방어력 PLY_DEF (+0x12)",
    3: "보조 지능/MP계 PLY_INT2 (+0x0A)",
    4: "민첩 PLY_AGL (+0x16)",
    5: "행운 PLY_LUCK (+0x17)",
    6: "지능 PLY_INT (+0x15)",
    7: "없음 / 특수",
}

ITEM_KOUKA_OFFSETS = (0x00, 0x10, 0x12, 0x0A, 0x16, 0x17, 0x15, 0x00)


@dataclass
class ItemRecord:
    item_id: int
    name: str
    price: int
    price_mantissa: int
    price_exponent: int
    packed: int
    stat_group: int
    effect_id: int
    power_raw: int
    secondary_raw: int
    type_mask: int
    file_offset: int

    @property
    def power_effective(self) -> int:
        return self.power_raw * 5

    @property
    def secondary_effective(self) -> int:
        return self.secondary_raw * 10

    @property
    def stat_label(self) -> str:
        return STAT_GROUP_LABELS.get(self.stat_group, f"Group {self.stat_group}")

    @property
    def item_kouka_offset(self) -> int:
        return ITEM_KOUKA_OFFSETS[self.stat_group]

    @property
    def item_magic_id(self) -> int:
        return self.effect_id

    @property
    def item_koka_num(self) -> int:
        return self.power_effective

    @property
    def item_magic_num(self) -> int:
        return self.secondary_effective


def verify_item_table(data: bytes) -> None:
    end = ITEM_NAME_BASE + (ITEM_COUNT - 1) * ITEM_STRIDE + 20
    if end > len(data):
        raise FormatError("ED2MAIN.EXE is too small for the known item table")
    exports = parse_ne_exports(data)
    address = exports.get("ITEM_TABLE")
    if address is None or ne_address_to_file(data, *address) != ITEM_NAME_BASE:
        raise FormatError("ITEM_TABLE export does not match the known item table")


def decode_price(mantissa: int, exponent: int) -> int:
    if exponent > 9:
        raise FormatError("Item price exponent is implausibly large")
    return mantissa * (10 ** exponent)


def encode_price(price: int) -> tuple[int, int]:
    if price < 0:
        raise ValueError("Price must be nonnegative")
    if price == 0:
        return 0, 0
    mantissa = price
    exponent = 0
    while mantissa > 255 and mantissa % 10 == 0 and exponent < 9:
        mantissa //= 10
        exponent += 1
    if mantissa > 255:
        raise ValueError("Price is not exactly representable as byte × 10^exponent; use a price with enough trailing zeros")
    return mantissa, exponent


def decode_item_name(raw: bytes) -> str:
    # Names are fixed 14-byte CP949 fields, generally left padded with spaces.
    return raw.rstrip(b"\x00").decode("cp949", errors="replace").strip()


def encode_item_name(name: str) -> bytes:
    raw = name.encode("cp949")
    if len(raw) > 14:
        raise ValueError("Item name must be <= 14 bytes in CP949")
    return b" " * (14 - len(raw)) + raw


def load_items(exe_path: Path) -> list[ItemRecord]:
    data = exe_path.read_bytes()
    verify_item_table(data)
    result: list[ItemRecord] = []
    for item_id in range(ITEM_COUNT):
        off = ITEM_NAME_BASE + item_id * ITEM_STRIDE
        mantissa, exponent = data[off + 14], data[off + 15]
        packed = data[off + 16]
        result.append(ItemRecord(
            item_id, decode_item_name(data[off:off + 14]), decode_price(mantissa, exponent),
            mantissa, exponent, packed, packed >> 5, packed & 0x1F,
            data[off + 17], data[off + 18], data[off + 19], off,
        ))
    return result


def patch_item(exe_path: Path, item_id: int, values: dict[str, Any], make_backup: bool = True) -> None:
    data = bytearray(exe_path.read_bytes())
    verify_item_table(data)
    if not 0 <= item_id < ITEM_COUNT:
        raise ValueError("Regular item ID must be 0..75")
    off = ITEM_NAME_BASE + item_id * ITEM_STRIDE
    if "name" in values:
        data[off:off + 14] = encode_item_name(str(values["name"]))
    if "price" in values:
        mantissa, exponent = encode_price(int(values["price"]))
        data[off + 14] = mantissa
        data[off + 15] = exponent
    stat_group = int(values.get("stat_group", data[off + 16] >> 5))
    effect_id = int(values.get("effect_id", data[off + 16] & 0x1F))
    if not 0 <= stat_group <= 7: raise ValueError("Stat group must be 0..7")
    if not 0 <= effect_id <= 31: raise ValueError("Effect ID must be 0..31")
    data[off + 16] = (stat_group << 5) | effect_id
    for key, delta in (("power_raw", 17), ("secondary_raw", 18), ("type_mask", 19)):
        if key in values:
            value = int(values[key])
            if not 0 <= value <= 255: raise ValueError(f"{key}: 0..255 required")
            data[off + delta] = value
    if len(data) != exe_path.stat().st_size:
        raise AssertionError("In-place item edit changed executable size")
    # Reparse before commit.
    verify_item_table(bytes(data))
    atomic_write(exe_path, bytes(data), make_backup)


@dataclass
class EventItemRecord:
    item_id: int
    name: str
    file_offset: int


def verify_event_item_table(data: bytes) -> None:
    end = EVENT_ITEM_NAME_BASE + EVENT_ITEM_COUNT * EVENT_ITEM_NAME_SIZE
    if end > len(data):
        raise FormatError("ED2MAIN.EXE is too small for the event item name table")
    exports = parse_ne_exports(data)
    address = exports.get("ITEM_TABLE2")
    if address is None or ne_address_to_file(data, *address) != EVENT_ITEM_NAME_BASE:
        raise FormatError("ITEM_TABLE2 export does not match the event item table")


def load_event_items(exe_path: Path) -> list[EventItemRecord]:
    data = exe_path.read_bytes()
    verify_event_item_table(data)
    return [
        EventItemRecord(
            EVENT_ITEM_ID_BASE + index,
            decode_item_name(data[EVENT_ITEM_NAME_BASE + index * EVENT_ITEM_NAME_SIZE:
                                  EVENT_ITEM_NAME_BASE + (index + 1) * EVENT_ITEM_NAME_SIZE]),
            EVENT_ITEM_NAME_BASE + index * EVENT_ITEM_NAME_SIZE,
        )
        for index in range(EVENT_ITEM_COUNT)
    ]


def patch_event_item(exe_path: Path, item_id: int, name: str, make_backup: bool = True) -> None:
    if not EVENT_ITEM_ID_BASE <= item_id < EVENT_ITEM_ID_BASE + EVENT_ITEM_COUNT:
        raise ValueError("Event item ID must be 100..126")
    data = bytearray(exe_path.read_bytes())
    verify_event_item_table(data)
    off = EVENT_ITEM_NAME_BASE + (item_id - EVENT_ITEM_ID_BASE) * EVENT_ITEM_NAME_SIZE
    data[off:off + EVENT_ITEM_NAME_SIZE] = encode_item_name(name)
    verify_event_item_table(bytes(data))
    atomic_write(exe_path, bytes(data), make_backup)


@dataclass
class MagicRecord:
    magic_id: int
    name: str
    cost: int
    select_flags: int
    packed_select_multiplier: int
    count_raw: int
    file_offset: int
    handler_offset: int
    handler_name: str

    @property
    def secondary_select(self) -> bool:
        return bool(self.packed_select_multiplier & 0x80)

    @property
    def multiplier(self) -> int:
        return self.packed_select_multiplier & 0x7F

    @property
    def count_high(self) -> int:
        return (self.count_raw >> 4) & 0x0F

    @property
    def count_low(self) -> int:
        return self.count_raw & 0x0F


def describe_magic_multiplier(multiplier: int) -> str:
    """Return a concise Korean explanation of MAGIC_BAIRITU."""
    if not 0 <= multiplier <= 0x7F:
        return "MAGIC_BAIRITU 값이 0..127 범위를 벗어났습니다."
    if multiplier == 100:
        scale = "기준 효과와 동일"
    elif multiplier == 0:
        scale = "효과 기준값이 0"
    elif multiplier < 100:
        scale = f"기준 효과의 약 {multiplier}%"
    else:
        scale = f"기준 효과보다 약 {multiplier - 100}% 강함"
    return f"MAGIC_BAIRITU={multiplier}: 마법 효과 배율 · {scale} (100=기준)"


def describe_magic_count(count_raw: int) -> tuple[str, bool]:
    """Explain the packed MAGIC_CNT recharge timing byte.

    The low nibble is the initial countdown and the high nibble is the
    repeating countdown. A zero nibble can underflow in the original code,
    so the UI flags it as unsafe rather than presenting it as instant charge.
    """
    if not 0 <= count_raw <= 0xFF:
        return "MAGIC_CNT 값이 0..255 범위를 벗어났습니다.", True
    high = (count_raw >> 4) & 0x0F
    low = count_raw & 0x0F
    if high == 0 or low == 0:
        return (
            f"MAGIC_CNT=0x{count_raw:02X}: 시작 주기 {low}, 반복 주기 {high} · "
            "0 니블은 언더플로로 비정상 충전될 수 있으므로 사용하지 않는 것이 안전합니다.",
            True,
        )
    estimated = low + high * 14
    if high == low == 1:
        speed = "가장 빠른 안정 권장값"
    elif high == low:
        speed = f"0x11보다 대략 {high}배 느린 균일 주기"
    else:
        speed = "초기 주기와 반복 주기가 다른 사용자 설정"
    return (
        f"MAGIC_CNT=0x{count_raw:02X}: 시작 주기 {low}, 반복 주기 {high}, "
        f"예상 총 카운트 {estimated} · {speed}",
        False,
    )


def decode_magic_name(raw: bytes) -> str:
    return raw.decode("cp949", errors="replace").strip()


def encode_magic_name(name: str) -> bytes:
    raw = name.encode("cp949")
    if len(raw) > 8:
        raise ValueError("Magic name must be <= 8 bytes in CP949")
    return b" " * (8 - len(raw)) + raw


def verify_magic_table(data: bytes) -> None:
    end = MAGIC_PARAM_BASE + MAGIC_COUNT * MAGIC_RECORD_SIZE
    if end > len(data):
        raise FormatError("ED2MAIN.EXE is too small for the magic parameter table")
    exports = parse_ne_exports(data)
    handler = exports.get("MAGIC_TABLE")
    get_prm = exports.get("GET_MAGIC_PRM")
    if handler is None or get_prm is None:
        raise FormatError("Required ED2 magic exports are missing")
    if ne_address_to_file(data, *handler) != MAGIC_HANDLER_TABLE_BASE:
        raise FormatError("MAGIC_TABLE export does not match the known handler table")
    # GET_MAGIC_PRM contains: mov ah,0Ch / mul ah / add ax,363Ch
    get_prm_file = ne_address_to_file(data, *get_prm)
    if data[get_prm_file + 2:get_prm_file + 9] != bytes.fromhex("B4 0C F6 E4 05 3C 36"):
        raise FormatError("GET_MAGIC_PRM signature does not match this editor build")


def load_magics(exe_path: Path) -> list[MagicRecord]:
    data = exe_path.read_bytes()
    verify_magic_table(data)
    exports = parse_ne_exports(data)
    address_names = {address: name for name, address in exports.items()}
    result: list[MagicRecord] = []
    for magic_id in range(MAGIC_COUNT):
        off = MAGIC_PARAM_BASE + magic_id * MAGIC_RECORD_SIZE
        record = data[off:off + MAGIC_RECORD_SIZE]
        handler_offset = u16(data, MAGIC_HANDLER_TABLE_BASE + magic_id * 2)
        result.append(MagicRecord(
            magic_id=magic_id,
            name=decode_magic_name(record[:8]),
            cost=record[8],
            select_flags=record[9],
            packed_select_multiplier=record[10],
            count_raw=record[11],
            file_offset=off,
            handler_offset=handler_offset,
            handler_name=address_names.get((86, handler_offset), f"sub_{handler_offset:04X}"),
        ))
    return result


def patch_magic(exe_path: Path, magic_id: int, values: dict[str, Any], make_backup: bool = True) -> None:
    if not 0 <= magic_id < MAGIC_COUNT:
        raise ValueError("Magic ID must be 0..31")
    data = bytearray(exe_path.read_bytes())
    verify_magic_table(data)
    off = MAGIC_PARAM_BASE + magic_id * MAGIC_RECORD_SIZE
    if "name" in values:
        data[off:off + 8] = encode_magic_name(str(values["name"]))
    for key, delta in (("cost", 8), ("select_flags", 9), ("count_raw", 11)):
        if key in values:
            value = int(values[key])
            if not 0 <= value <= 255:
                raise ValueError(f"{key}: 0..255 required")
            data[off + delta] = value
    if "packed_select_multiplier" in values:
        value = int(values["packed_select_multiplier"])
        if not 0 <= value <= 255:
            raise ValueError("packed_select_multiplier: 0..255 required")
        data[off + 10] = value
    else:
        packed = data[off + 10]
        if "secondary_select" in values:
            packed = (packed | 0x80) if bool(values["secondary_select"]) else (packed & 0x7F)
        if "multiplier" in values:
            multiplier = int(values["multiplier"])
            if not 0 <= multiplier <= 0x7F:
                raise ValueError("Multiplier must be 0..127")
            packed = (packed & 0x80) | multiplier
        data[off + 10] = packed
    verify_magic_table(bytes(data))
    atomic_write(exe_path, bytes(data), make_backup)


def load_debug_symbol_catalog(base_dir: Path) -> dict[str, Any]:
    path = base_dir / "DEBUG_SYMBOLS.json"
    if not path.is_file():
        return {}
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return {}
    return raw if isinstance(raw, dict) else {}


# ---------------------------------------------------------------------------
# Appearance/resource support
# ---------------------------------------------------------------------------

@dataclass
class AppearanceAsset:
    asset_id: int
    path: Path
    size: int
    header_size_minus_one: int
    header_valid: bool
    users: list[str]


def parse_appearance_id(path: Path) -> int:
    stem = path.stem.upper()
    if not stem.startswith("C_MO"):
        return -1
    try:
        return int(stem[4:], 16)
    except ValueError:
        return -1


def validate_bzh(data: bytes) -> tuple[bool, str]:
    if len(data) < 3:
        return False, "File is too small"
    declared = u16(data, 0)
    if declared != len(data) - 1:
        return False, f"Header says {declared + 1} bytes, actual size is {len(data)}"
    return True, "Size header is valid"


def load_appearance_assets(root: Path, groups: Iterable[MonsterGroup]) -> list[AppearanceAsset]:
    users: dict[int, list[str]] = {}
    for g in groups:
        for idx, asset_id in enumerate((g.graphic_id0, g.graphic_id1)):
            if asset_id != 0xFFFF:
                users.setdefault(asset_id, []).append(f"M_{g.dll_number:03X} slot{idx}")
    result = []
    for path in sorted((root / "MON").glob("C_MO*.BZH")):
        asset_id = parse_appearance_id(path)
        data = path.read_bytes()
        declared = u16(data, 0) if len(data) >= 2 else -1
        valid, _ = validate_bzh(data)
        result.append(AppearanceAsset(asset_id, path, len(data), declared, valid, users.get(asset_id, [])))
    return result


def replace_bzh(target: Path, source: Path, make_backup: bool = True) -> None:
    data = source.read_bytes()
    valid, reason = validate_bzh(data)
    if not valid:
        raise FormatError(f"Replacement BZH failed validation: {reason}")
    atomic_write(target, data, make_backup)


# ---------------------------------------------------------------------------
# Project model, validation, CSV
# ---------------------------------------------------------------------------

class Project:
    def __init__(self, root: Path):
        self.root = root.resolve()
        self.exe = self.root / "ED2MAIN.EXE"
        self.mon_dir = self.root / "MON"
        self.validate_root()
        self.monsters: list[MonsterRecord] = []
        self.groups: list[MonsterGroup] = []
        self.items: list[ItemRecord] = []
        self.event_items: list[EventItemRecord] = []
        self.magics: list[MagicRecord] = []
        self.assets: list[AppearanceAsset] = []
        self.debug_catalog = load_debug_symbol_catalog(Path(__file__).resolve().parent)
        self.reload()

    def validate_root(self) -> None:
        if not self.exe.is_file() or not self.mon_dir.is_dir():
            raise FormatError("Select the ED2 game folder containing ED2MAIN.EXE and MON")

    def reload(self) -> None:
        monsters: list[MonsterRecord] = []
        groups: list[MonsterGroup] = []
        for path in sorted(self.mon_dir.glob("M_*.DLL")):
            try:
                records = load_monsters(path)
                group = load_group(path)
            except Exception:
                continue
            monsters.extend(records)
            groups.append(group)
        self.monsters = monsters
        self.groups = groups
        self.items = load_items(self.exe)
        self.event_items = load_event_items(self.exe)
        self.magics = load_magics(self.exe)
        self.assets = load_appearance_assets(self.root, self.groups)

    def item_display(self, item_id: int) -> str:
        if 0 <= item_id < len(self.items):
            return f"{item_id:03d} {self.items[item_id].name}"
        if EVENT_ITEM_ID_BASE <= item_id < EVENT_ITEM_ID_BASE + len(self.event_items):
            item = self.event_items[item_id - EVENT_ITEM_ID_BASE]
            return f"{item_id:03d} {item.name} [event]"
        return f"{item_id:03d} [unknown ID]"

    def debug_info(self, dll_name: str) -> dict[str, Any]:
        return dict(self.debug_catalog.get(dll_name.upper(), {}))

    def group_by_path(self, path: Path) -> MonsterGroup:
        for group in self.groups:
            if group.dll_path == path:
                return group
        raise KeyError(path)

    def import_monsters_csv(self, path: Path) -> int:
        with path.open("r", newline="", encoding="utf-8-sig") as fp:
            rows = list(csv.DictReader(fp))
        index = {(r.dll_path.name.upper(), r.slot): r for r in self.monsters}
        prepared: dict[Path, bytearray] = {}
        changed = 0
        for row_num, row in enumerate(rows, start=2):
            key = (str(row.get("dll", "")).upper(), csv_int(row.get("slot", ""), 0, 3, f"row {row_num} slot"))
            rec = index.get(key)
            if rec is None:
                raise ValueError(f"row {row_num}: monster {key[0]} slot {key[1]} was not found")
            data = prepared.setdefault(rec.dll_path, bytearray(rec.dll_path.read_bytes()))
            base = rec.file_offset
            if str(row.get("name", "")).strip():
                data[base + 48:base + 64] = encode_fixed_cp949(str(row["name"]), 16)
            mapping = {
                "level": ("level", 0, 255), "hp": ("hp", 1, 65535), "attack": ("attack", 0, 65535),
                "exp_raw": ("exp", 0, 65535), "gold_raw": ("gold", 0, 65535),
                "defense": ("defense", 0, 65535), "magic": ("magic", 0, 65535),
                "speed": ("speed", 0, 255), "luck": ("luck", 0, 255),
            }
            for column, (field, minimum, maximum) in mapping.items():
                text = str(row.get(column, "")).strip()
                if not text: continue
                value = csv_int(text, minimum, maximum, f"row {row_num} {column}")
                off, size, _ = MONSTER_FIELDS[field]
                if field == "hp": p16(data, base + 4, value); p16(data, base + 6, value)
                elif size == 1: data[base + off] = value
                else: p16(data, base + off, value)
            if not is_monster_record(bytes(data[base:base + 64])):
                raise ValueError(f"row {row_num}: edited monster failed validation")
            changed += 1
        for target, data in prepared.items():
            seg, count = find_monster_table(bytes(data))
            records = [
                MonsterRecord(target, dll_number(target), slot, seg.file_offset + slot * 64, seg.file_offset,
                              bytes(data[seg.file_offset + slot * 64:seg.file_offset + (slot + 1) * 64]))
                for slot in range(count)
            ]
            bgm_id = data[seg.file_offset + 0x11A]
            for reward_key in ("exp", "gold"):
                proposed = {record.slot: record.value(reward_key) for record in records}
                adjusted, _ = fit_group_reward_raws(records, reward_key, proposed, dll_number(target), bgm_id)
                off, _size, _label = MONSTER_FIELDS[reward_key]
                for record in records:
                    p16(data, record.file_offset + off, adjusted[record.slot])
            atomic_write(target, bytes(data), True)
        self.reload()
        return changed

    def import_groups_csv(self, path: Path) -> int:
        with path.open("r", newline="", encoding="utf-8-sig") as fp:
            rows = list(csv.DictReader(fp))
        index = {g.dll_path.name.upper(): g for g in self.groups}
        prepared: dict[Path, bytearray] = {}
        changed = 0
        columns = {
            "graphic_id0_hex": (0x100, 2, 0xFFFF), "graphic_addr0_hex": (0x102, 2, 0xFFFF),
            "graphic_id1_hex": (0x104, 2, 0xFFFF), "graphic_addr1_hex": (0x106, 2, 0xFFFF),
            "drop_item_id": (0x118, 1, 255), "drop_chance": (0x119, 1, 100), "bgm_id": (0x11A, 1, 255),
        }
        known_assets = {a.asset_id for a in self.assets}
        for row_num, row in enumerate(rows, start=2):
            name = str(row.get("dll", "")).upper()
            group = index.get(name)
            if group is None: raise ValueError(f"row {row_num}: group {name} was not found")
            data = prepared.setdefault(group.dll_path, bytearray(group.dll_path.read_bytes()))
            for column, (delta, size, maximum) in columns.items():
                text = str(row.get(column, "")).strip()
                if not text: continue
                value = csv_int(text, 0, maximum, f"row {row_num} {column}")
                if column in ("graphic_id0_hex", "graphic_id1_hex") and value != 0xFFFF and value not in known_assets:
                    raise ValueError(f"row {row_num}: C_MO{value:03X}.BZH does not exist")
                if size == 1: data[group.segment_offset + delta] = value
                else: p16(data, group.segment_offset + delta, value)
            changed += 1
        for target, data in prepared.items(): atomic_write(target, bytes(data), True)
        self.reload()
        return changed

    def import_items_csv(self, path: Path) -> int:
        with path.open("r", newline="", encoding="utf-8-sig") as fp:
            rows = list(csv.DictReader(fp))
        data = bytearray(self.exe.read_bytes())
        verify_item_table(data)
        seen: set[int] = set()
        for row_num, row in enumerate(rows, start=2):
            item_id = csv_int(row.get("item_id", ""), 0, ITEM_COUNT - 1, f"row {row_num} item_id")
            if item_id in seen: raise ValueError(f"row {row_num}: duplicate item ID {item_id}")
            seen.add(item_id)
            off = ITEM_NAME_BASE + item_id * ITEM_STRIDE
            name = str(row.get("name", "")).strip()
            if name: data[off:off + 14] = encode_item_name(name)
            price_text = str(row.get("price", "")).strip()
            if price_text:
                mantissa, exponent = encode_price(csv_int(price_text, 0, 10**12, f"row {row_num} price"))
                data[off + 14], data[off + 15] = mantissa, exponent
            group_text, effect_text = str(row.get("stat_group", "")).strip(), str(row.get("effect_id", "")).strip()
            stat_group = (data[off + 16] >> 5) if not group_text else csv_int(group_text, 0, 7, f"row {row_num} stat_group")
            effect_id = (data[off + 16] & 0x1F) if not effect_text else csv_int(effect_text, 0, 31, f"row {row_num} effect_id")
            data[off + 16] = (stat_group << 5) | effect_id
            for column, delta in (("power_raw", 17), ("secondary_raw", 18)):
                text = str(row.get(column, "")).strip()
                if text: data[off + delta] = csv_int(text, 0, 255, f"row {row_num} {column}")
            mask_text = str(row.get("type_mask_hex", "")).strip()
            if mask_text: data[off + 19] = csv_int(mask_text, 0, 255, f"row {row_num} type_mask")
        atomic_write(self.exe, bytes(data), True)
        self.reload()
        return len(seen)

    def validate(self) -> dict[str, Any]:
        warnings: list[str] = []
        errors: list[str] = []
        known_asset_ids = {a.asset_id for a in self.assets}
        for group in self.groups:
            if not 0 <= group.drop_chance <= 100:
                errors.append(f"{group.dll_path.name}: drop chance {group.drop_chance} is outside 0..100")
            for index, asset_id in enumerate((group.graphic_id0, group.graphic_id1)):
                if asset_id != 0xFFFF and asset_id not in known_asset_ids:
                    errors.append(f"{group.dll_path.name}: C_MO{asset_id:03X}.BZH for graphic {index} is missing")
            if group.drop_item_id >= ITEM_COUNT and not (
                EVENT_ITEM_ID_BASE <= group.drop_item_id < EVENT_ITEM_ID_BASE + EVENT_ITEM_COUNT
            ):
                warnings.append(f"{group.dll_path.name}: drop ID {group.drop_item_id} is unknown")
            records = [record for record in self.monsters if record.dll_path == group.dll_path]
            for reward_key, label in (("exp", "EXP"), ("gold", "Gold")):
                total = formation_reward_total(records, reward_key, group.dll_number, group.bgm_id)
                if total > REWARD_ACCUMULATOR_MAX:
                    errors.append(f"{group.dll_path.name}: {label} accumulator overflow ({total})")
        for asset in self.assets:
            if not asset.header_valid:
                errors.append(f"{asset.path.name}: invalid BZH size header")
        for item in self.items:
            try:
                # Multiple mantissa/exponent pairs can represent the same price.
                # Only reject values that cannot be represented at all.
                encode_price(item.price)
            except ValueError as exc:
                errors.append(f"Item {item.item_id}: {exc}")
        return {
            "tool": f"{APP_NAME} {VERSION}",
            "root": str(self.root),
            "counts": {
                "monster_dlls": len(self.groups),
                "monster_records": len(self.monsters),
                "regular_items": len(self.items),
                "event_items": len(self.event_items),
                "magics": len(self.magics),
                "appearance_assets": len(self.assets),
            },
            "errors": errors,
            "warnings": warnings,
            "ok": not errors,
        }

    def export_monsters_csv(self, path: Path) -> None:
        fields = ["dll", "slot", "name", "level", "hp", "attack", "exp_raw", "gold_raw", "defense", "magic", "speed", "luck"]
        with path.open("w", newline="", encoding="utf-8-sig") as fp:
            writer = csv.DictWriter(fp, fieldnames=fields)
            writer.writeheader()
            for rec in self.monsters:
                writer.writerow({
                    "dll": rec.dll_path.name, "slot": rec.slot, "name": rec.name,
                    "level": rec.value("level"), "hp": rec.value("hp"), "attack": rec.value("attack"),
                    "exp_raw": rec.value("exp"), "gold_raw": rec.value("gold"),
                    "defense": rec.value("defense"), "magic": rec.value("magic"),
                    "speed": rec.value("speed"), "luck": rec.value("luck"),
                })

    def export_groups_csv(self, path: Path) -> None:
        fields = ["dll", "monsters", "graphic_id0_hex", "graphic_addr0_hex", "graphic_id1_hex", "graphic_addr1_hex", "drop_item_id", "drop_item_name", "drop_chance", "bgm_id"]
        with path.open("w", newline="", encoding="utf-8-sig") as fp:
            writer = csv.DictWriter(fp, fieldnames=fields)
            writer.writeheader()
            for g in self.groups:
                writer.writerow({
                    "dll": g.dll_path.name, "monsters": " / ".join(g.monster_names),
                    "graphic_id0_hex": f"0x{g.graphic_id0:04X}", "graphic_addr0_hex": f"0x{g.graphic_addr0:04X}",
                    "graphic_id1_hex": f"0x{g.graphic_id1:04X}", "graphic_addr1_hex": f"0x{g.graphic_addr1:04X}",
                    "drop_item_id": g.drop_item_id, "drop_item_name": self.item_display(g.drop_item_id),
                    "drop_chance": g.drop_chance, "bgm_id": g.bgm_id,
                })

    def export_items_csv(self, path: Path) -> None:
        fields = ["item_id", "name", "price", "price_mantissa", "price_exponent", "stat_group", "stat_label", "effect_id", "power_raw", "power_effective_x5", "secondary_raw", "secondary_effective_x10", "type_mask_hex"]
        with path.open("w", newline="", encoding="utf-8-sig") as fp:
            writer = csv.DictWriter(fp, fieldnames=fields)
            writer.writeheader()
            for item in self.items:
                writer.writerow({
                    "item_id": item.item_id, "name": item.name, "price": item.price,
                    "price_mantissa": item.price_mantissa, "price_exponent": item.price_exponent,
                    "stat_group": item.stat_group, "stat_label": item.stat_label, "effect_id": item.effect_id,
                    "power_raw": item.power_raw, "power_effective_x5": item.power_effective,
                    "secondary_raw": item.secondary_raw, "secondary_effective_x10": item.secondary_effective,
                    "type_mask_hex": f"0x{item.type_mask:02X}",
                })

    def export_event_items_csv(self, path: Path) -> None:
        fields = ["item_id", "name", "file_offset_hex"]
        with path.open("w", newline="", encoding="utf-8-sig") as fp:
            writer = csv.DictWriter(fp, fieldnames=fields)
            writer.writeheader()
            for item in self.event_items:
                writer.writerow({
                    "item_id": item.item_id, "name": item.name,
                    "file_offset_hex": f"0x{item.file_offset:X}",
                })

    def export_magics_csv(self, path: Path) -> None:
        fields = [
            "magic_id", "name", "cost", "magic_slc_hex", "secondary_select",
            "magic_bairitu", "magic_cnt_hex", "count_high", "count_low",
            "handler_offset_hex", "handler_name",
        ]
        with path.open("w", newline="", encoding="utf-8-sig") as fp:
            writer = csv.DictWriter(fp, fieldnames=fields)
            writer.writeheader()
            for magic in self.magics:
                writer.writerow({
                    "magic_id": magic.magic_id, "name": magic.name, "cost": magic.cost,
                    "magic_slc_hex": f"0x{magic.select_flags:02X}",
                    "secondary_select": int(magic.secondary_select),
                    "magic_bairitu": magic.multiplier,
                    "magic_cnt_hex": f"0x{magic.count_raw:02X}",
                    "count_high": magic.count_high, "count_low": magic.count_low,
                    "handler_offset_hex": f"0x{magic.handler_offset:04X}",
                    "handler_name": magic.handler_name,
                })

    def export_ai_hooks_json(self, path: Path) -> None:
        payload: list[dict[str, Any]] = []
        for group in self.groups:
            info = self.debug_info(group.dll_path.name)
            payload.append({
                "dll": group.dll_path.name,
                "monsters": group.monster_names,
                "source": info.get("source", ""),
                "hooks": [
                    {"symbol": symbol, "offset": value, "offset_hex": f"0x{value:04X}", "description": description}
                    for symbol, value, description in group.hook_rows()
                ],
                "debug_categories": info.get("categories", {}),
            })
        path.write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8")


def file_inventory(root: Path) -> list[dict[str, Any]]:
    result = []
    for path in sorted(p for p in root.rglob("*") if p.is_file() and not p.name.endswith(".bak")):
        rel = path.relative_to(root)
        data = path.read_bytes()[:16]
        result.append({
            "relative": str(rel), "extension": path.suffix.upper() or "(none)",
            "size": path.stat().st_size, "header_hex": data.hex(" ").upper(),
        })
    return result


def write_analysis_bundle(project: Project, folder: Path) -> list[Path]:
    folder.mkdir(parents=True, exist_ok=True)
    outputs = [
        folder / "ED2_MONSTERS.csv", folder / "ED2_MONSTER_GROUPS.csv",
        folder / "ED2_ITEMS.csv", folder / "ED2_EVENT_ITEMS.csv",
        folder / "ED2_MAGIC.csv", folder / "ED2_AI_HOOKS.json",
    ]
    project.export_monsters_csv(outputs[0])
    project.export_groups_csv(outputs[1])
    project.export_items_csv(outputs[2])
    project.export_event_items_csv(outputs[3])
    project.export_magics_csv(outputs[4])
    project.export_ai_hooks_json(outputs[5])
    validation_path = folder / "VALIDATION.json"
    validation_path.write_text(json.dumps(project.validate(), ensure_ascii=False, indent=2), encoding="utf-8")
    inventory_path = folder / "FILE_INVENTORY.json"
    inventory_path.write_text(json.dumps(file_inventory(project.root), ensure_ascii=False, indent=2), encoding="utf-8")
    outputs.extend([validation_path, inventory_path])
    return outputs


# ---------------------------------------------------------------------------
# Tkinter GUI
# ---------------------------------------------------------------------------

def run_gui(initial_root: Optional[Path] = None, audio_tool: Optional[Path] = None) -> None:
    try:
        import tkinter as tk
        from tkinter import ttk, filedialog, messagebox
    except ImportError as exc:
        raise SystemExit("Tkinter is required for GUI mode") from exc

    class Studio(tk.Tk):
        def __init__(self) -> None:
            super().__init__()
            self.title(f"{APP_NAME} {VERSION}")
            self.geometry("1500x920")
            self.minsize(1080, 700)
            self.project: Optional[Project] = None
            self.audio_tool = audio_tool
            self.current_monster: Optional[MonsterRecord] = None
            self.current_group: Optional[MonsterGroup] = None
            self.current_item: Optional[ItemRecord | EventItemRecord] = None
            self.current_magic: Optional[MagicRecord] = None
            self.current_asset: Optional[AppearanceAsset] = None
            self.current_resource: Optional[Path] = None
            self.resource_paths: dict[str, Path] = {}
            self.item_entries: dict[str, Any] = {}
            self._build_style()
            self._build_ui()
            if initial_root and initial_root.exists():
                self.open_project(initial_root)

        def _build_style(self) -> None:
            style = ttk.Style(self)
            try:
                style.theme_use("vista" if sys.platform == "win32" else "clam")
            except Exception:
                pass
            style.configure("Treeview", rowheight=25)
            style.configure("Title.TLabel", font=("TkDefaultFont", 13, "bold"))
            style.configure("Section.TLabel", font=("TkDefaultFont", 10, "bold"))
            style.configure("Danger.TLabel", foreground="#A00000")

        # Shared scroll helpers ------------------------------------------
        def _wheel_bind(self, widget: Any, xview: Any, yview: Any) -> None:
            def vertical(event: Any) -> str:
                delta = -1 if getattr(event, "delta", 0) > 0 else 1
                if getattr(event, "num", 0) == 4: delta = -1
                elif getattr(event, "num", 0) == 5: delta = 1
                yview("scroll", delta * 3, "units")
                return "break"

            def horizontal(event: Any) -> str:
                delta = -1 if getattr(event, "delta", 0) > 0 else 1
                xview("scroll", delta * 3, "units")
                return "break"

            def enter(_event: Any) -> None:
                self.bind_all("<MouseWheel>", vertical)
                self.bind_all("<Shift-MouseWheel>", horizontal)
                self.bind_all("<Button-4>", vertical)
                self.bind_all("<Button-5>", vertical)

            def leave(_event: Any) -> None:
                self.unbind_all("<MouseWheel>")
                self.unbind_all("<Shift-MouseWheel>")
                self.unbind_all("<Button-4>")
                self.unbind_all("<Button-5>")

            widget.bind("<Enter>", enter, add="+")
            widget.bind("<Leave>", leave, add="+")

        def _tree(self, parent: Any, columns: tuple[str, ...], **kwargs: Any) -> Any:
            box = ttk.Frame(parent)
            box.pack(fill="both", expand=True)
            tree = ttk.Treeview(box, columns=columns, show="headings", **kwargs)
            ybar = ttk.Scrollbar(box, orient="vertical", command=tree.yview)
            xbar = ttk.Scrollbar(box, orient="horizontal", command=tree.xview)
            tree.configure(yscrollcommand=ybar.set, xscrollcommand=xbar.set)
            tree.grid(row=0, column=0, sticky="nsew")
            ybar.grid(row=0, column=1, sticky="ns")
            xbar.grid(row=1, column=0, sticky="ew")
            box.rowconfigure(0, weight=1)
            box.columnconfigure(0, weight=1)
            self._wheel_bind(tree, tree.xview, tree.yview)
            return tree

        def _text(self, parent: Any, **kwargs: Any) -> Any:
            box = ttk.Frame(parent)
            box.pack(fill="both", expand=True)
            text = tk.Text(box, wrap="none", **kwargs)
            ybar = ttk.Scrollbar(box, orient="vertical", command=text.yview)
            xbar = ttk.Scrollbar(box, orient="horizontal", command=text.xview)
            text.configure(yscrollcommand=ybar.set, xscrollcommand=xbar.set)
            text.grid(row=0, column=0, sticky="nsew")
            ybar.grid(row=0, column=1, sticky="ns")
            xbar.grid(row=1, column=0, sticky="ew")
            box.rowconfigure(0, weight=1)
            box.columnconfigure(0, weight=1)
            self._wheel_bind(text, text.xview, text.yview)
            return text

        def _scrollable_panel(self, parent: Any, padding: int = 10) -> tuple[Any, Any]:
            outer = ttk.Frame(parent)
            canvas = tk.Canvas(outer, highlightthickness=0)
            ybar = ttk.Scrollbar(outer, orient="vertical", command=canvas.yview)
            xbar = ttk.Scrollbar(outer, orient="horizontal", command=canvas.xview)
            canvas.configure(yscrollcommand=ybar.set, xscrollcommand=xbar.set)
            canvas.grid(row=0, column=0, sticky="nsew")
            ybar.grid(row=0, column=1, sticky="ns")
            xbar.grid(row=1, column=0, sticky="ew")
            outer.rowconfigure(0, weight=1)
            outer.columnconfigure(0, weight=1)
            inner = ttk.Frame(canvas, padding=padding)
            window = canvas.create_window((0, 0), window=inner, anchor="nw")
            inner.bind("<Configure>", lambda _e: canvas.configure(scrollregion=canvas.bbox("all")))
            canvas.bind("<Configure>", lambda e: canvas.itemconfigure(window, height=max(e.height, inner.winfo_reqheight())))
            self._wheel_bind(canvas, canvas.xview, canvas.yview)
            return outer, inner

        def _make_pane(self, parent: Any) -> tuple[Any, Any]:
            pane = ttk.Panedwindow(parent, orient="horizontal")
            pane.pack(fill="both", expand=True)
            left = ttk.Frame(pane, padding=6)
            right_holder = ttk.Frame(pane)
            right_outer, right = self._scrollable_panel(right_holder)
            right_outer.pack(fill="both", expand=True)
            pane.add(left, weight=3)
            pane.add(right_holder, weight=2)
            return left, right

        def _readonly_text(self, widget: Any, content: str) -> None:
            widget.configure(state="normal")
            widget.delete("1.0", "end")
            widget.insert("1.0", content)
            widget.configure(state="disabled")

        # Main window -----------------------------------------------------
        def _build_ui(self) -> None:
            toolbar = ttk.Frame(self, padding=(10, 8))
            toolbar.pack(fill="x")
            ttk.Label(toolbar, text=APP_NAME, style="Title.TLabel").pack(side="left")
            self.root_var = tk.StringVar()
            ttk.Entry(toolbar, textvariable=self.root_var).pack(side="left", fill="x", expand=True, padx=12)
            ttk.Button(toolbar, text="게임 폴더 열기", command=self.choose_project).pack(side="left")
            ttk.Button(toolbar, text="새로고침", command=self.reload_project).pack(side="left", padx=(6, 0))
            ttk.Button(toolbar, text="전체 검사", command=self.run_validation).pack(side="left", padx=(6, 0))
            self.status_var = tk.StringVar(value="ED2MAIN.EXE와 MON 폴더가 있는 게임 폴더를 선택하세요.")
            ttk.Label(self, textvariable=self.status_var, anchor="w", padding=(10, 0, 10, 6)).pack(fill="x")
            self.nb = ttk.Notebook(self)
            self.nb.pack(fill="both", expand=True, padx=10, pady=(0, 8))
            self._build_monsters_tab()
            self._build_groups_tab()
            self._build_items_tab()
            self._build_magic_tab()
            self._build_ai_tab()
            self._build_appearance_tab()
            self._build_resources_tab()
            self._build_audio_tab()
            self._build_diagnostics_tab()

        def choose_project(self) -> None:
            folder = filedialog.askdirectory(title="영웅전설 2 게임 폴더 선택")
            if folder: self.open_project(Path(folder))

        def open_project(self, root: Path) -> None:
            try:
                self.project = Project(root)
            except Exception as exc:
                messagebox.showerror(APP_NAME, str(exc))
                return
            self.root_var.set(str(self.project.root))
            self.populate_all()
            report = self.project.validate()
            self.status_var.set(
                f"로드 완료: 몬스터 {len(self.project.monsters)} / 그룹 {len(self.project.groups)} / "
                f"일반 아이템 {len(self.project.items)} / 이벤트 아이템 {len(self.project.event_items)} / "
                f"마법 {len(self.project.magics)} / 외형 {len(self.project.assets)} | "
                f"오류 {len(report['errors'])}, 경고 {len(report['warnings'])}"
            )

        def reload_project(self) -> None:
            if self.project:
                self.open_project(self.project.root)
            elif self.root_var.get().strip():
                self.open_project(Path(self.root_var.get().strip()))

        def populate_all(self) -> None:
            self.populate_monsters()
            self.populate_groups()
            self.populate_items()
            self.populate_magics()
            self.populate_ai()
            self.populate_assets()
            self.populate_resources()
            self.update_diagnostics()

        # Monsters --------------------------------------------------------
        def _build_monsters_tab(self) -> None:
            tab = ttk.Frame(self.nb); self.nb.add(tab, text="몬스터")
            left, right = self._make_pane(tab)
            bar = ttk.Frame(left); bar.pack(fill="x", pady=(0, 6))
            self.mon_search = tk.StringVar()
            ttk.Label(bar, text="검색").pack(side="left")
            e = ttk.Entry(bar, textvariable=self.mon_search); e.pack(side="left", fill="x", expand=True, padx=6)
            e.bind("<KeyRelease>", lambda _e: self.populate_monsters())
            ttk.Button(bar, text="CSV 내보내기", command=self.export_monsters_csv).pack(side="left")
            ttk.Button(bar, text="CSV 가져오기", command=self.import_monsters_csv_gui).pack(side="left", padx=(4, 0))
            cols = ("dll", "slot", "name", "level", "hp", "atk", "def", "magic", "speed", "luck", "exp", "gold")
            self.mon_tree = self._tree(left, cols, selectmode="browse")
            labels = {"dll":"DLL", "slot":"#", "name":"이름", "level":"Lv", "hp":"HP", "atk":"공격", "def":"방어", "magic":"마법", "speed":"속도", "luck":"행운", "exp":"EXP 원시값", "gold":"Gold 원시값"}
            widths = {"dll":80, "slot":40, "name":190, "level":45, "hp":80, "atk":70, "def":70, "magic":70, "speed":60, "luck":60, "exp":95, "gold":95}
            for col in cols:
                self.mon_tree.heading(col, text=labels[col]); self.mon_tree.column(col, width=widths[col], minwidth=40, anchor="w" if col == "name" else "center")
            self.mon_tree.bind("<<TreeviewSelect>>", lambda _e: self.show_monster())

            ttk.Label(right, text="몬스터 상세", style="Title.TLabel").pack(anchor="w")
            form = ttk.Frame(right); form.pack(fill="x", pady=(8, 0))
            self.mon_vars = {key: tk.StringVar() for key in ("name", "level", "hp", "attack", "defense", "magic", "speed", "luck", "exp", "gold")}
            rows = [("name","이름"),("level","몬스터 레벨"),("hp","HP"),("attack","공격"),("defense","방어"),("magic","마법"),("speed","속도"),("luck","행운"),("exp","EXP 원시값"),("gold","Gold 원시값")]
            for row, (key, label) in enumerate(rows):
                ttk.Label(form, text=label).grid(row=row, column=0, sticky="w", pady=3)
                ttk.Entry(form, textvariable=self.mon_vars[key], width=38).grid(row=row, column=1, sticky="ew", padx=(8, 0), pady=3)
            form.columnconfigure(1, weight=1)
            estimator = ttk.LabelFrame(right, text="실제 EXP 예상", padding=8); estimator.pack(fill="x", pady=10)
            self.party_level_var = tk.StringVar(value="30")
            self.party_count_var = tk.StringVar(value="4")
            ttk.Label(estimator, text="생존 파티 평균 레벨").grid(row=0, column=0, sticky="w")
            ttk.Entry(estimator, textvariable=self.party_level_var, width=8).grid(row=0, column=1, sticky="w", padx=6)
            ttk.Label(estimator, text="생존 인원").grid(row=0, column=2, sticky="w", padx=(10,0))
            ttk.Entry(estimator, textvariable=self.party_count_var, width=5).grid(row=0, column=3, sticky="w", padx=6)
            ttk.Button(estimator, text="편성 전체 계산", command=self.update_exp_estimate).grid(row=0, column=4)
            self.exp_estimate_var = tk.StringVar(value="몬스터를 선택하세요.")
            ttk.Label(estimator, textvariable=self.exp_estimate_var, wraplength=700).grid(row=1, column=0, columnspan=5, sticky="w", pady=(6, 0))
            ttk.Label(right, text="고급 바이트 0x18..0x2F", style="Section.TLabel").pack(anchor="w")
            advanced_box = ttk.Frame(right); advanced_box.pack(fill="x", pady=(4, 8))
            self.mon_advanced = self._text(advanced_box, height=3)
            btn = ttk.Frame(right); btn.pack(fill="x")
            ttk.Button(btn, text="선택 몬스터 저장 (.bak)", command=self.save_monster).pack(side="left")
            ttk.Button(btn, text="DLL 백업 복원", command=self.restore_current_mon_dll).pack(side="left", padx=6)
            bulk = ttk.LabelFrame(right, text="전체 몬스터 일괄 수식", padding=8); bulk.pack(fill="x", pady=(12, 0))
            self.bulk_stat_var = tk.StringVar(value="HP"); self.bulk_expr_var = tk.StringVar(value="*1.5")
            ttk.Combobox(bulk, textvariable=self.bulk_stat_var, state="readonly", values=("HP","Attack","Defense","Magic","Speed","Luck","EXP raw","Gold raw"), width=14).grid(row=0, column=0, sticky="w")
            ttk.Entry(bulk, textvariable=self.bulk_expr_var, width=34).grid(row=0, column=1, sticky="ew", padx=6)
            ttk.Button(bulk, text="미리보기", command=self.preview_bulk).grid(row=0, column=2)
            ttk.Button(bulk, text="전체 적용", command=self.apply_bulk).grid(row=0, column=3, padx=(6, 0))
            ttk.Label(bulk, text="예: +10, *1.5, log10(x)*100, x+log2(x)*20, max(1,x-5)").grid(row=1, column=0, columnspan=4, sticky="w", pady=(6,0))
            ttk.Label(bulk, text="EXP/Gold는 활성 편성 합계가 65,535를 넘지 않도록 자동 조정됩니다.").grid(row=2, column=0, columnspan=4, sticky="w", pady=(3,0))
            bulk.columnconfigure(1, weight=1)

        def populate_monsters(self) -> None:
            self.mon_tree.delete(*self.mon_tree.get_children())
            if not self.project: return
            needle = self.mon_search.get().strip().lower()
            for index, rec in enumerate(self.project.monsters):
                if needle and needle not in f"{rec.dll_path.name} {rec.name}".lower(): continue
                self.mon_tree.insert("", "end", iid=str(index), values=(rec.dll_path.stem, rec.slot, rec.name, rec.value("level"), rec.value("hp"), rec.value("attack"), rec.value("defense"), rec.value("magic"), rec.value("speed"), rec.value("luck"), rec.value("exp"), rec.value("gold")))

        def show_monster(self) -> None:
            if not self.project: return
            sel = self.mon_tree.selection()
            if not sel: return
            rec = self.project.monsters[int(sel[0])]; self.current_monster = rec
            self.mon_vars["name"].set(rec.name)
            for key in MONSTER_FIELDS:
                if key in self.mon_vars: self.mon_vars[key].set(str(rec.value(key)))
            self.mon_advanced.delete("1.0", "end"); self.mon_advanced.insert("1.0", rec.raw[0x18:0x30].hex(" ").upper())
            self.update_exp_estimate()

        def update_exp_estimate(self) -> None:
            if not self.project or not self.current_monster:
                self.exp_estimate_var.set("몬스터를 선택하세요."); return
            try:
                party_lv = parse_number(self.party_level_var.get(), 1, 255, "파티 평균 레벨")
                party_count = parse_number(self.party_count_var.get(), 1, 4, "생존 인원")
            except Exception as exc:
                self.exp_estimate_var.set(str(exc)); return
            rec = self.current_monster
            group = self.project.group_by_path(rec.dll_path)
            records = [record for record in self.project.monsters if record.dll_path == rec.dll_path]
            active = _active_records(records)
            exp_values = [estimated_reward(r.value("exp"), r.value("level"), party_lv, r.dll_number, group.bgm_id)[0] for r in active]
            gold_values = [estimated_reward(r.value("gold"), r.value("level"), party_lv, r.dll_number, group.bgm_id)[0] for r in active]
            exp_sum = sum(exp_values); gold_sum = sum(gold_values)
            exp_word = exp_sum & REWARD_ACCUMULATOR_MAX
            gold_word = gold_sum & REWARD_ACCUMULATOR_MAX
            share = (exp_word + party_count - 1) // party_count if exp_word else 0
            overflow = "없음" if exp_sum <= REWARD_ACCUMULATOR_MAX else f"발생: {exp_sum} → {exp_word}"
            gold_overflow = "없음" if gold_sum <= REWARD_ACCUMULATOR_MAX else f"발생: {gold_sum} → {gold_word}"
            names = ", ".join(r.name for r in active)
            self.exp_estimate_var.set(
                f"활성 편성 {len(active)}마리: {names}\n"
                f"EXP 합계 {exp_sum}, 16비트 결과 {exp_word}, 오버플로 {overflow}, "
                f"{party_count}명 기준 1인당 {share}\n"
                f"Gold 합계 {gold_sum}, 16비트 결과 {gold_word}, 오버플로 {gold_overflow}"
            )

        def save_monster(self) -> None:
            if not self.current_monster: return
            try:
                values: dict[str, Any] = {"name": self.mon_vars["name"].get(), "advanced_hex": self.mon_advanced.get("1.0", "end")}
                for key, (_off, size, _label) in MONSTER_FIELDS.items():
                    if key == "record_id": continue
                    values[key] = parse_number(self.mon_vars[key].get(), 1 if key == "hp" else 0, 255 if size == 1 else 65535, key)
                path, slot = self.current_monster.dll_path, self.current_monster.slot
                applied = patch_monster(self.current_monster, values); self.reload_project()
                for index, rec in enumerate(self.project.monsters if self.project else []):
                    if rec.dll_path == path and rec.slot == slot:
                        if self.mon_tree.exists(str(index)):
                            self.mon_tree.selection_set(str(index)); self.mon_tree.see(str(index)); self.show_monster()
                        break
                adjusted = [key.upper() for key in ("exp", "gold") if key in values and int(values[key]) != int(applied[key])]
                suffix = f" 오버플로 방지 자동 조정: {', '.join(adjusted)}" if adjusted else ""
                messagebox.showinfo(APP_NAME, "몬스터를 저장했습니다." + suffix)
            except Exception as exc: messagebox.showerror(APP_NAME, str(exc))

        def restore_current_mon_dll(self) -> None:
            if not self.current_monster: return
            if not messagebox.askyesno(APP_NAME, f"{self.current_monster.dll_path.name}.bak을 복원할까요?"): return
            try: restore_backup(self.current_monster.dll_path); self.reload_project()
            except Exception as exc: messagebox.showerror(APP_NAME, str(exc))

        def _bulk_key(self) -> tuple[str, int, int]:
            return {"HP":("hp",1,65535),"Attack":("attack",0,65535),"Defense":("defense",0,65535),"Magic":("magic",0,65535),"Speed":("speed",0,255),"Luck":("luck",0,255),"EXP raw":("exp",0,65535),"Gold raw":("gold",0,65535)}[self.bulk_stat_var.get()]

        def _bulk_proposals(self, key: str, minimum: int, maximum: int, expr: str) -> tuple[dict[Path, dict[int, int]], int, int]:
            if not self.project: return {}, 0, 0
            by_path: dict[Path, list[MonsterRecord]] = {}
            for rec in self.project.monsters:
                by_path.setdefault(rec.dll_path, []).append(rec)
            proposals: dict[Path, dict[int, int]] = {}
            clamped = adjusted = 0
            for path, records in by_path.items():
                values: dict[int, int] = {}
                for rec in records:
                    raw_new = eval_formula(rec.value(key), expr)
                    values[rec.slot] = max(minimum, min(maximum, raw_new))
                    clamped += int(values[rec.slot] != raw_new)
                if key in ("exp", "gold"):
                    group = self.project.group_by_path(path)
                    values, count = fit_group_reward_raws(records, key, values, group.dll_number, group.bgm_id)
                    adjusted += count
                proposals[path] = values
            return proposals, clamped, adjusted

        def preview_bulk(self) -> None:
            if not self.project: return
            try:
                key, minimum, maximum = self._bulk_key(); expr = self.bulk_expr_var.get()
                proposals, clamped, adjusted = self._bulk_proposals(key, minimum, maximum, expr)
                lines = []
                for rec in self.project.monsters[:12]:
                    lines.append(f"{rec.name}: {rec.value(key)} → {proposals[rec.dll_path][rec.slot]}")
                lines.append(f"\n범위 제한 {clamped}건 / 오버플로 방지 자동 조정 {adjusted}건")
                messagebox.showinfo("일괄 수식 미리보기", "\n".join(lines))
            except Exception as exc: messagebox.showerror(APP_NAME, str(exc))

        def apply_bulk(self) -> None:
            if not self.project: return
            key, minimum, maximum = self._bulk_key(); expr = self.bulk_expr_var.get()
            if not messagebox.askyesno(APP_NAME, f"전체 {len(self.project.monsters)}개 몬스터의 {self.bulk_stat_var.get()}에 '{expr}'를 적용할까요?"): return
            try:
                proposals, clamped, adjusted = self._bulk_proposals(key, minimum, maximum, expr)
                by_path: dict[Path, list[MonsterRecord]] = {}
                for rec in self.project.monsters: by_path.setdefault(rec.dll_path, []).append(rec)
                changed = 0
                for path, records in by_path.items():
                    data = bytearray(path.read_bytes())
                    for rec in records:
                        new = proposals[path][rec.slot]
                        off, size, _ = MONSTER_FIELDS[key]
                        if key == "hp": p16(data, rec.file_offset + 4, new); p16(data, rec.file_offset + 6, new)
                        elif size == 1: data[rec.file_offset + off] = new
                        else: p16(data, rec.file_offset + off, new)
                        changed += 1
                    atomic_write(path, bytes(data), True)
                self.reload_project()
                messagebox.showinfo(APP_NAME, f"{changed}개 수정 완료. 범위 제한 {clamped}건, 오버플로 방지 자동 조정 {adjusted}건.")
            except Exception as exc: messagebox.showerror(APP_NAME, str(exc))

        def export_monsters_csv(self) -> None:
            if not self.project: return
            path = filedialog.asksaveasfilename(defaultextension=".csv", initialfile="ED2_MONSTERS.csv", filetypes=[("CSV","*.csv")])
            if path: self.project.export_monsters_csv(Path(path))

        def import_monsters_csv_gui(self) -> None:
            if not self.project: return
            path = filedialog.askopenfilename(filetypes=[("CSV","*.csv")])
            if not path or not messagebox.askyesno(APP_NAME, "CSV의 몬스터 값을 적용할까요?"): return
            try: count = self.project.import_monsters_csv(Path(path)); self.populate_all(); messagebox.showinfo(APP_NAME, f"{count}개 행 적용 완료")
            except Exception as exc: messagebox.showerror(APP_NAME, str(exc))

        # Groups and drops ------------------------------------------------
        def _build_groups_tab(self) -> None:
            tab = ttk.Frame(self.nb); self.nb.add(tab, text="전투 그룹·드롭")
            left, right = self._make_pane(tab)
            bar = ttk.Frame(left); bar.pack(fill="x", pady=(0,6))
            self.group_search = tk.StringVar(); ttk.Label(bar, text="검색").pack(side="left")
            e = ttk.Entry(bar, textvariable=self.group_search); e.pack(side="left", fill="x", expand=True, padx=6); e.bind("<KeyRelease>", lambda _e: self.populate_groups())
            ttk.Button(bar, text="CSV 내보내기", command=self.export_groups_csv).pack(side="left")
            ttk.Button(bar, text="CSV 가져오기", command=self.import_groups_csv_gui).pack(side="left", padx=(4,0))
            cols = ("dll","monsters","drop","chance","bgm","gfx0","gfx1")
            self.group_tree = self._tree(left, cols, selectmode="browse")
            for col,label,width in (("dll","DLL",80),("monsters","구성 몬스터",310),("drop","_MO_ATT_TRS 드롭",230),("chance","_MO_ATT_TRP %",105),("bgm","BGM",55),("gfx0","주 외형",75),("gfx1","보조 외형",75)):
                self.group_tree.heading(col,text=label); self.group_tree.column(col,width=width,minwidth=45,anchor="w" if col in ("monsters","drop") else "center")
            self.group_tree.bind("<<TreeviewSelect>>", lambda _e: self.show_group())
            ttk.Label(right,text="전투 그룹 상세",style="Title.TLabel").pack(anchor="w")
            self.group_names_var=tk.StringVar(); ttk.Label(right,textvariable=self.group_names_var,wraplength=700).pack(anchor="w",pady=(4,10))
            form=ttk.Frame(right); form.pack(fill="x")
            self.group_vars={k:tk.StringVar() for k in ("graphic_id0","graphic_addr0","graphic_id1","graphic_addr1","drop_item_id","drop_chance","bgm_id")}
            rows=[("graphic_id0","_MO_CHR_NO0 주 외형 ID"),("graphic_addr0","_MO_CHR_ADR0"),("graphic_id1","_MO_CHR_NO1 보조 외형 ID"),("graphic_addr1","_MO_CHR_ADR1"),("drop_item_id","_MO_ATT_TRS 드롭 아이템 ID"),("drop_chance","_MO_ATT_TRP 드롭 확률 %"),("bgm_id","_MO_ATT_BGM")]
            for row,(key,label) in enumerate(rows):
                ttk.Label(form,text=label).grid(row=row,column=0,sticky="w",pady=3); ttk.Entry(form,textvariable=self.group_vars[key],width=34).grid(row=row,column=1,sticky="ew",padx=(8,0),pady=3)
            form.columnconfigure(1,weight=1)
            self.drop_name_var=tk.StringVar(); ttk.Label(right,textvariable=self.drop_name_var,style="Section.TLabel").pack(anchor="w",pady=(8,4))
            ttk.Label(right,text="AI·훅 포인터는 코드 주소이므로 이 화면에서는 읽기 전용입니다.").pack(anchor="w")
            hook_box=ttk.Frame(right); hook_box.pack(fill="both",expand=True,pady=(4,8))
            self.group_hook_tree=self._tree(hook_box,("symbol","offset","desc"),selectmode="browse")
            for col,label,width in (("symbol","심볼",160),("offset","오프셋",90),("desc","설명",350)):
                self.group_hook_tree.heading(col,text=label);self.group_hook_tree.column(col,width=width,anchor="w")
            btn=ttk.Frame(right);btn.pack(fill="x")
            ttk.Button(btn,text="그룹 저장 (.bak)",command=self.save_group).pack(side="left")
            ttk.Button(btn,text="DLL 백업 복원",command=self.restore_current_group).pack(side="left",padx=6)

        def populate_groups(self) -> None:
            self.group_tree.delete(*self.group_tree.get_children())
            if not self.project:return
            needle=self.group_search.get().strip().lower()
            for index,g in enumerate(self.project.groups):
                if needle and needle not in f"{g.dll_path.name} {' '.join(g.monster_names)} {self.project.item_display(g.drop_item_id)}".lower():continue
                self.group_tree.insert("","end",iid=str(index),values=(g.dll_path.stem," / ".join(g.monster_names),self.project.item_display(g.drop_item_id),g.drop_chance,g.bgm_id,f"{g.graphic_id0:04X}",f"{g.graphic_id1:04X}"))

        def show_group(self) -> None:
            if not self.project:return
            sel=self.group_tree.selection()
            if not sel:return
            g=self.project.groups[int(sel[0])];self.current_group=g;self.group_names_var.set(" / ".join(g.monster_names))
            for key in ("graphic_id0","graphic_addr0","graphic_id1","graphic_addr1"):
                self.group_vars[key].set(f"0x{getattr(g,key):04X}")
            self.group_vars["drop_item_id"].set(str(g.drop_item_id));self.group_vars["drop_chance"].set(str(g.drop_chance));self.group_vars["bgm_id"].set(str(g.bgm_id))
            self.drop_name_var.set("드롭: "+self.project.item_display(g.drop_item_id))
            self.group_hook_tree.delete(*self.group_hook_tree.get_children())
            for symbol,value,description in g.hook_rows(): self.group_hook_tree.insert("","end",values=(symbol,f"0x{value:04X}",description))

        def save_group(self) -> None:
            if not self.project or not self.current_group:return
            try:
                values={"graphic_id0":parse_number(self.group_vars["graphic_id0"].get(),0,0xFFFF,"graphic_id0"),"graphic_addr0":parse_number(self.group_vars["graphic_addr0"].get(),0,0xFFFF,"graphic_addr0"),"graphic_id1":parse_number(self.group_vars["graphic_id1"].get(),0,0xFFFF,"graphic_id1"),"graphic_addr1":parse_number(self.group_vars["graphic_addr1"].get(),0,0xFFFF,"graphic_addr1"),"drop_item_id":parse_number(self.group_vars["drop_item_id"].get(),0,255,"drop item"),"drop_chance":parse_number(self.group_vars["drop_chance"].get(),0,100,"drop chance"),"bgm_id":parse_number(self.group_vars["bgm_id"].get(),0,255,"BGM ID")}
                known={a.asset_id for a in self.project.assets}
                for key in ("graphic_id0","graphic_id1"):
                    if values[key]!=0xFFFF and values[key] not in known:raise ValueError(f"C_MO{values[key]:03X}.BZH does not exist")
                path=self.current_group.dll_path;patch_group(self.current_group,values);self.reload_project()
                for i,g in enumerate(self.project.groups if self.project else []):
                    if g.dll_path==path:
                        if self.group_tree.exists(str(i)):
                            self.group_tree.selection_set(str(i));self.group_tree.see(str(i));self.show_group()
                        break
                messagebox.showinfo(APP_NAME,"전투 그룹을 저장했습니다.")
            except Exception as exc:messagebox.showerror(APP_NAME,str(exc))

        def restore_current_group(self) -> None:
            if not self.current_group:return
            try:restore_backup(self.current_group.dll_path);self.reload_project()
            except Exception as exc:messagebox.showerror(APP_NAME,str(exc))

        def export_groups_csv(self) -> None:
            if not self.project:return
            path=filedialog.asksaveasfilename(defaultextension=".csv",initialfile="ED2_MONSTER_GROUPS.csv",filetypes=[("CSV","*.csv")])
            if path:self.project.export_groups_csv(Path(path))

        def import_groups_csv_gui(self) -> None:
            if not self.project:return
            path=filedialog.askopenfilename(filetypes=[("CSV","*.csv")])
            if not path or not messagebox.askyesno(APP_NAME,"CSV의 전투 그룹 값을 적용할까요?"):return
            try:count=self.project.import_groups_csv(Path(path));self.populate_all();messagebox.showinfo(APP_NAME,f"{count}개 그룹 적용 완료")
            except Exception as exc:messagebox.showerror(APP_NAME,str(exc))

        # Items -----------------------------------------------------------
        def _build_items_tab(self) -> None:
            tab=ttk.Frame(self.nb);self.nb.add(tab,text="아이템")
            left,right=self._make_pane(tab)
            bar=ttk.Frame(left);bar.pack(fill="x",pady=(0,6));self.item_search=tk.StringVar();ttk.Label(bar,text="검색").pack(side="left")
            e=ttk.Entry(bar,textvariable=self.item_search);e.pack(side="left",fill="x",expand=True,padx=6);e.bind("<KeyRelease>",lambda _e:self.populate_items())
            ttk.Button(bar,text="일반 CSV",command=self.export_items_csv).pack(side="left")
            ttk.Button(bar,text="이벤트 CSV",command=self.export_event_items_csv).pack(side="left",padx=(4,0))
            ttk.Button(bar,text="일반 CSV 가져오기",command=self.import_items_csv_gui).pack(side="left",padx=(4,0))
            cols=("kind","id","name","price","kouka","magic","koka_num","magic_num","type")
            self.item_tree=self._tree(left,cols,selectmode="browse")
            for col,label,width in (("kind","구분",65),("id","ID",45),("name","이름",200),("price","가격",90),("kouka","ITEM_KOUKA",230),("magic","ITEM_MAGIC",90),("koka_num","ITEM_KOKA_NUM",115),("magic_num","ITEM_MAGIC_NUM",125),("type","ITEM_TYPE",80)):
                self.item_tree.heading(col,text=label);self.item_tree.column(col,width=width,minwidth=45,anchor="w" if col in ("name","kouka") else "center")
            self.item_tree.bind("<<TreeviewSelect>>",lambda _e:self.show_item())
            ttk.Label(right,text="아이템 상세",style="Title.TLabel").pack(anchor="w")
            form=ttk.Frame(right);form.pack(fill="x",pady=(8,0))
            self.item_vars={k:tk.StringVar() for k in ("id","name","price","stat_group","effect_id","power_raw","secondary_raw","type_mask")}
            rows=[("id","아이템 ID"),("name","ITEM_NAME (CP949 최대 14바이트)"),("price","ITEM_COST"),("stat_group","ITEM_KOUKA 그룹 0..7"),("effect_id","ITEM_MAGIC ID 0..31"),("power_raw","ITEM_KOKA_NUM 원시값 (실제 ×5)"),("secondary_raw","ITEM_MAGIC_NUM 원시값 (실제 ×10)"),("type_mask","ITEM_TYPE 마스크")]
            self.item_entries={}
            for row,(key,label) in enumerate(rows):
                ttk.Label(form,text=label).grid(row=row,column=0,sticky="w",pady=3);ent=ttk.Entry(form,textvariable=self.item_vars[key],width=38);ent.grid(row=row,column=1,sticky="ew",padx=(8,0),pady=3);self.item_entries[key]=ent
            form.columnconfigure(1,weight=1);self.item_entries["id"].configure(state="readonly")
            self.item_effective_var=tk.StringVar();ttk.Label(right,textvariable=self.item_effective_var,style="Section.TLabel",wraplength=720).pack(anchor="w",pady=(10,3))
            self.item_usage_var=tk.StringVar();ttk.Label(right,textvariable=self.item_usage_var,wraplength=720).pack(anchor="w",pady=(0,8))
            ttk.Label(right,text="이벤트 아이템 100~126은 이름만 편집합니다. 일반 아이템 수치 필드는 GET_ITEM_PRM 코드와 디버그 심볼 기준으로 교정했습니다.",wraplength=720).pack(anchor="w",pady=(0,8))
            btn=ttk.Frame(right);btn.pack(fill="x")
            ttk.Button(btn,text="아이템 저장 (EXE.bak)",command=self.save_item).pack(side="left")
            ttk.Button(btn,text="EXE 백업 복원",command=self.restore_exe).pack(side="left",padx=6)

        def populate_items(self) -> None:
            self.item_tree.delete(*self.item_tree.get_children())
            if not self.project:return
            needle=self.item_search.get().strip().lower()
            for item in self.project.items:
                if needle and needle not in f"{item.item_id} {item.name} {item.stat_label}".lower():continue
                self.item_tree.insert("","end",iid=f"r:{item.item_id}",values=("일반",item.item_id,item.name,item.price,item.stat_label,item.effect_id,item.power_effective,item.secondary_effective,f"0x{item.type_mask:02X}"))
            for item in self.project.event_items:
                if needle and needle not in f"{item.item_id} {item.name} event 이벤트".lower():continue
                self.item_tree.insert("","end",iid=f"e:{item.item_id}",values=("이벤트",item.item_id,item.name,"-","공통 특수 파라미터","-","-","-","-"))

        def show_item(self) -> None:
            if not self.project:return
            sel=self.item_tree.selection()
            if not sel:return
            kind,raw_id=sel[0].split(":",1);item_id=int(raw_id)
            if kind=="r":
                item=self.project.items[item_id];self.current_item=item
                values={"id":item.item_id,"name":item.name,"price":item.price,"stat_group":item.stat_group,"effect_id":item.effect_id,"power_raw":item.power_raw,"secondary_raw":item.secondary_raw,"type_mask":f"0x{item.type_mask:02X}"}
                for key,value in values.items():self.item_vars[key].set(str(value))
                for key,entry in self.item_entries.items():entry.configure(state="readonly" if key=="id" else "normal")
                self.item_effective_var.set(f"{item.stat_label} · ITEM_KOUKA offset 0x{item.item_kouka_offset:02X} · ITEM_KOKA_NUM {item.power_raw}×5={item.power_effective} · ITEM_MAGIC_NUM {item.secondary_raw}×10={item.secondary_effective} · packed 0x{item.packed:02X}")
            else:
                item=self.project.event_items[item_id-EVENT_ITEM_ID_BASE];self.current_item=item
                for key in self.item_vars:self.item_vars[key].set("")
                self.item_vars["id"].set(str(item.item_id));self.item_vars["name"].set(item.name)
                for key,entry in self.item_entries.items():entry.configure(state="normal" if key=="name" else "readonly")
                self.item_effective_var.set(f"이벤트 아이템 ID {item.item_id} · ED2MAIN.EXE 0x{item.file_offset:X} · 이름만 안전 편집 가능")
            uses=[f"M_{g.dll_number:03X} ({g.drop_chance}%)" for g in self.project.groups if g.drop_item_id==item_id]
            self.item_usage_var.set("드롭 사용처: "+(", ".join(uses) if uses else "없음"))

        def save_item(self) -> None:
            if not self.project or not self.current_item:return
            try:
                item_id=self.current_item.item_id
                if isinstance(self.current_item,EventItemRecord):
                    patch_event_item(self.project.exe,item_id,self.item_vars["name"].get())
                    iid=f"e:{item_id}"
                else:
                    values={"name":self.item_vars["name"].get(),"price":parse_number(self.item_vars["price"].get(),0,10**12,"price"),"stat_group":parse_number(self.item_vars["stat_group"].get(),0,7,"ITEM_KOUKA"),"effect_id":parse_number(self.item_vars["effect_id"].get(),0,31,"ITEM_MAGIC"),"power_raw":parse_number(self.item_vars["power_raw"].get(),0,255,"ITEM_KOKA_NUM"),"secondary_raw":parse_number(self.item_vars["secondary_raw"].get(),0,255,"ITEM_MAGIC_NUM"),"type_mask":parse_number(self.item_vars["type_mask"].get(),0,255,"ITEM_TYPE")}
                    patch_item(self.project.exe,item_id,values);iid=f"r:{item_id}"
                self.reload_project()
                if self.item_tree.exists(iid):
                    self.item_tree.selection_set(iid);self.item_tree.see(iid);self.show_item()
                messagebox.showinfo(APP_NAME,"아이템을 저장했습니다.")
            except Exception as exc:messagebox.showerror(APP_NAME,str(exc))

        def restore_exe(self) -> None:
            if not self.project:return
            if not messagebox.askyesno(APP_NAME,"ED2MAIN.EXE.bak을 복원할까요?"):return
            try:restore_backup(self.project.exe);self.reload_project()
            except Exception as exc:messagebox.showerror(APP_NAME,str(exc))

        def export_items_csv(self) -> None:
            if not self.project:return
            path=filedialog.asksaveasfilename(defaultextension=".csv",initialfile="ED2_ITEMS.csv",filetypes=[("CSV","*.csv")])
            if path:self.project.export_items_csv(Path(path))

        def export_event_items_csv(self) -> None:
            if not self.project:return
            path=filedialog.asksaveasfilename(defaultextension=".csv",initialfile="ED2_EVENT_ITEMS.csv",filetypes=[("CSV","*.csv")])
            if path:self.project.export_event_items_csv(Path(path))

        def import_items_csv_gui(self) -> None:
            if not self.project:return
            path=filedialog.askopenfilename(filetypes=[("CSV","*.csv")])
            if not path or not messagebox.askyesno(APP_NAME,"CSV의 일반 아이템 테이블을 적용할까요?"):return
            try:count=self.project.import_items_csv(Path(path));self.populate_all();messagebox.showinfo(APP_NAME,f"{count}개 일반 아이템 적용 완료")
            except Exception as exc:messagebox.showerror(APP_NAME,str(exc))

        # Magic -----------------------------------------------------------
        def _build_magic_tab(self) -> None:
            tab=ttk.Frame(self.nb);self.nb.add(tab,text="마법")
            left,right=self._make_pane(tab)
            bar=ttk.Frame(left);bar.pack(fill="x",pady=(0,6));self.magic_search=tk.StringVar();ttk.Label(bar,text="검색").pack(side="left")
            e=ttk.Entry(bar,textvariable=self.magic_search);e.pack(side="left",fill="x",expand=True,padx=6);e.bind("<KeyRelease>",lambda _e:self.populate_magics())
            ttk.Button(bar,text="CSV 내보내기",command=self.export_magics_csv).pack(side="left")
            cols=("id","name","cost","slc","slc2","ratio","cnt","handler")
            self.magic_tree=self._tree(left,cols,selectmode="browse")
            for col,label,width in (("id","ID",45),("name","MAGIC_NAME",150),("cost","MAGIC_COST",85),("slc","MAGIC_SLC",85),("slc2","MAGIC_SLC2",90),("ratio","MAGIC_BAIRITU (효과%)",145),("cnt","MAGIC_CNT (충전)",125),("handler","MAGIC_TABLE handler",180)):
                self.magic_tree.heading(col,text=label);self.magic_tree.column(col,width=width,minwidth=45,anchor="w" if col in ("name","handler") else "center")
            self.magic_tree.bind("<<TreeviewSelect>>",lambda _e:self.show_magic())
            ttk.Label(right,text="마법 상세",style="Title.TLabel").pack(anchor="w")
            form=ttk.Frame(right);form.pack(fill="x",pady=(8,0))
            self.magic_vars={k:tk.StringVar() for k in ("id","name","cost","select_flags","multiplier","count_raw","handler")}
            rows=[("id","마법 ID"),("name","MAGIC_NAME (CP949 최대 8바이트)"),("cost","MAGIC_COST"),("select_flags","MAGIC_SLC 원시 플래그"),("multiplier","MAGIC_BAIRITU 효과 배율 % (0..127)"),("count_raw","MAGIC_CNT 재충전 주기 (0x11 권장 최소)"),("handler","MAGIC_TABLE 처리 함수 (읽기 전용)")]
            self.magic_entries={}
            for row,(key,label) in enumerate(rows):
                ttk.Label(form,text=label).grid(row=row,column=0,sticky="w",pady=3);ent=ttk.Entry(form,textvariable=self.magic_vars[key],width=42);ent.grid(row=row,column=1,sticky="ew",padx=(8,0),pady=3);self.magic_entries[key]=ent
                if key in ("multiplier","count_raw"):
                    ent.bind("<KeyRelease>",lambda _e:self.update_magic_parameter_help())
            self.magic_entries["id"].configure(state="readonly");self.magic_entries["handler"].configure(state="readonly");form.columnconfigure(1,weight=1)
            self.magic_secondary_var=tk.BooleanVar();ttk.Checkbutton(right,text="MAGIC_SLC2 bit7: 보조 선택 플래그",variable=self.magic_secondary_var).pack(anchor="w",pady=(8,2))
            self.magic_info_var=tk.StringVar();ttk.Label(right,textvariable=self.magic_info_var,wraplength=720,style="Section.TLabel").pack(anchor="w",pady=(4,8))
            self.magic_parameter_help_var=tk.StringVar()
            ttk.Label(right,textvariable=self.magic_parameter_help_var,wraplength=720).pack(anchor="w",pady=(0,8))
            ttk.Label(
                right,
                text=(
                    "MAGIC_BAIRITU는 마법 효과 배율입니다. 100은 기준 효과, 25는 약 25%입니다. "
                    "bit7은 배율이 아니라 MAGIC_SLC2 보조 선택 플래그로 따로 편집됩니다.\n"
                    "MAGIC_CNT는 재충전 주기입니다. 하위 니블은 최초 주기, 상위 니블은 반복 주기이며 숫자가 작을수록 빠릅니다. "
                    "0x11은 가장 빠른 안정 권장값, 0x22는 약 2배, 0x55는 약 5배 느립니다. "
                    "0x00처럼 어느 한 니블이 0인 값은 언더플로 위험이 있으므로 피하십시오."
                ),
                wraplength=720,
            ).pack(anchor="w",pady=(0,8))
            ttk.Label(right,text="MAGIC_TABLE 처리 함수 포인터는 코드 주소이므로 수정할 수 없습니다.",wraplength=720).pack(anchor="w",pady=(0,8))
            btn=ttk.Frame(right);btn.pack(fill="x")
            ttk.Button(btn,text="마법 저장 (EXE.bak)",command=self.save_magic).pack(side="left")
            ttk.Button(btn,text="EXE 백업 복원",command=self.restore_exe).pack(side="left",padx=6)

        def populate_magics(self) -> None:
            self.magic_tree.delete(*self.magic_tree.get_children())
            if not self.project:return
            needle=self.magic_search.get().strip().lower()
            for magic in self.project.magics:
                if needle and needle not in f"{magic.magic_id} {magic.name} {magic.handler_name}".lower():continue
                self.magic_tree.insert("","end",iid=str(magic.magic_id),values=(magic.magic_id,magic.name,magic.cost,f"0x{magic.select_flags:02X}",int(magic.secondary_select),magic.multiplier,f"0x{magic.count_raw:02X}",magic.handler_name))

        def show_magic(self) -> None:
            if not self.project:return
            sel=self.magic_tree.selection()
            if not sel:return
            magic=self.project.magics[int(sel[0])];self.current_magic=magic
            values={"id":magic.magic_id,"name":magic.name,"cost":magic.cost,"select_flags":f"0x{magic.select_flags:02X}","multiplier":magic.multiplier,"count_raw":f"0x{magic.count_raw:02X}","handler":f"{magic.handler_name} @ 86:{magic.handler_offset:04X}"}
            for key,value in values.items():self.magic_vars[key].set(str(value))
            self.magic_secondary_var.set(magic.secondary_select)
            self.magic_info_var.set(f"원시 packed select/multiplier=0x{magic.packed_select_multiplier:02X}")
            self.update_magic_parameter_help()

        def update_magic_parameter_help(self) -> None:
            if not hasattr(self,"magic_parameter_help_var"):
                return
            try:
                multiplier=parse_number(self.magic_vars["multiplier"].get(),0,0x7F,"MAGIC_BAIRITU")
                multiplier_text=describe_magic_multiplier(multiplier)
            except Exception as exc:
                multiplier_text=f"MAGIC_BAIRITU 입력 확인: {exc}"
            try:
                count_raw=parse_number(self.magic_vars["count_raw"].get(),0,0xFF,"MAGIC_CNT")
                count_text,_unsafe=describe_magic_count(count_raw)
            except Exception as exc:
                count_text=f"MAGIC_CNT 입력 확인: {exc}"
            self.magic_parameter_help_var.set(multiplier_text+"\n"+count_text)

        def save_magic(self) -> None:
            if not self.project or not self.current_magic:return
            try:
                magic_id=self.current_magic.magic_id
                values={"name":self.magic_vars["name"].get(),"cost":parse_number(self.magic_vars["cost"].get(),0,255,"MAGIC_COST"),"select_flags":parse_number(self.magic_vars["select_flags"].get(),0,255,"MAGIC_SLC"),"secondary_select":self.magic_secondary_var.get(),"multiplier":parse_number(self.magic_vars["multiplier"].get(),0,127,"MAGIC_BAIRITU"),"count_raw":parse_number(self.magic_vars["count_raw"].get(),0,255,"MAGIC_CNT")}
                patch_magic(self.project.exe,magic_id,values);self.reload_project()
                if self.magic_tree.exists(str(magic_id)):
                    self.magic_tree.selection_set(str(magic_id));self.magic_tree.see(str(magic_id));self.show_magic()
                messagebox.showinfo(APP_NAME,"마법을 저장했습니다.")
            except Exception as exc:messagebox.showerror(APP_NAME,str(exc))

        def export_magics_csv(self) -> None:
            if not self.project:return
            path=filedialog.asksaveasfilename(defaultextension=".csv",initialfile="ED2_MAGIC.csv",filetypes=[("CSV","*.csv")])
            if path:self.project.export_magics_csv(Path(path))

        # AI and hooks ----------------------------------------------------
        def _build_ai_tab(self) -> None:
            tab=ttk.Frame(self.nb);self.nb.add(tab,text="AI·훅")
            left,right=self._make_pane(tab)
            bar=ttk.Frame(left);bar.pack(fill="x",pady=(0,6));self.ai_search=tk.StringVar();ttk.Label(bar,text="검색").pack(side="left")
            e=ttk.Entry(bar,textvariable=self.ai_search);e.pack(side="left",fill="x",expand=True,padx=6);e.bind("<KeyRelease>",lambda _e:self.populate_ai())
            ttk.Button(bar,text="JSON 내보내기",command=self.export_ai_json).pack(side="left")
            self.ai_group_tree=self._tree(left,("dll","monsters","source"),selectmode="browse")
            for col,label,width in (("dll","DLL",80),("monsters","몬스터",300),("source","원본 ASM 경로",420)):
                self.ai_group_tree.heading(col,text=label);self.ai_group_tree.column(col,width=width,minwidth=60,anchor="w")
            self.ai_group_tree.bind("<<TreeviewSelect>>",lambda _e:self.show_ai())
            ttk.Label(right,text="AI 행동·전투 훅",style="Title.TLabel").pack(anchor="w")
            self.ai_title_var=tk.StringVar();ttk.Label(right,textvariable=self.ai_title_var,wraplength=760).pack(anchor="w",pady=(4,8))
            ttk.Label(right,text="확정된 그룹 전역 포인터",style="Section.TLabel").pack(anchor="w")
            hook_holder=ttk.Frame(right);hook_holder.pack(fill="both",expand=True,pady=(4,8))
            self.ai_hook_tree=self._tree(hook_holder,("symbol","offset","desc"),selectmode="browse")
            for col,label,width in (("symbol","심볼",180),("offset","오프셋",90),("desc","설명",380)):
                self.ai_hook_tree.heading(col,text=label);self.ai_hook_tree.column(col,width=width,anchor="w")
            ttk.Label(right,text="디버그 DLL에서 복구한 지역 함수·행동명",style="Section.TLabel").pack(anchor="w")
            symbol_holder=ttk.Frame(right);symbol_holder.pack(fill="both",expand=True,pady=(4,8))
            self.ai_symbol_tree=self._tree(symbol_holder,("category","symbol"),selectmode="browse")
            self.ai_symbol_tree.heading("category",text="분류");self.ai_symbol_tree.column("category",width=150,anchor="w")
            self.ai_symbol_tree.heading("symbol",text="심볼/행동명");self.ai_symbol_tree.column("symbol",width=520,anchor="w")
            ttk.Label(right,text="포인터 편집은 충돌 위험 때문에 제공하지 않습니다. 디버그 DLL의 로드 영역은 정식판과 동일하며, 이 화면은 이름과 주소를 읽기 전용으로 연결합니다.",wraplength=760).pack(anchor="w")

        def populate_ai(self) -> None:
            self.ai_group_tree.delete(*self.ai_group_tree.get_children())
            if not self.project:return
            needle=self.ai_search.get().strip().lower()
            for index,g in enumerate(self.project.groups):
                info=self.project.debug_info(g.dll_path.name);source=str(info.get("source",""));cats=info.get("categories",{})
                hay=f"{g.dll_path.name} {' '.join(g.monster_names)} {source} {json.dumps(cats,ensure_ascii=False)}".lower()
                if needle and needle not in hay:continue
                self.ai_group_tree.insert("","end",iid=str(index),values=(g.dll_path.stem," / ".join(g.monster_names),source))

        def show_ai(self) -> None:
            if not self.project:return
            sel=self.ai_group_tree.selection()
            if not sel:return
            g=self.project.groups[int(sel[0])];info=self.project.debug_info(g.dll_path.name)
            self.ai_title_var.set(f"{g.dll_path.name} · {' / '.join(g.monster_names)}\n{info.get('source','디버그 소스 경로 없음')}")
            self.ai_hook_tree.delete(*self.ai_hook_tree.get_children())
            for symbol,value,description in g.hook_rows():self.ai_hook_tree.insert("","end",values=(symbol,f"0x{value:04X}",description))
            self.ai_symbol_tree.delete(*self.ai_symbol_tree.get_children())
            for category,names in info.get("categories",{}).items():
                for name in names:self.ai_symbol_tree.insert("","end",values=(category,name))

        def export_ai_json(self) -> None:
            if not self.project:return
            path=filedialog.asksaveasfilename(defaultextension=".json",initialfile="ED2_AI_HOOKS.json",filetypes=[("JSON","*.json")])
            if path:self.project.export_ai_hooks_json(Path(path))

        # Appearance ------------------------------------------------------
        def _build_appearance_tab(self) -> None:
            tab=ttk.Frame(self.nb);self.nb.add(tab,text="몬스터 외형")
            left,right=self._make_pane(tab)
            self.asset_tree=self._tree(left,("id","file","size","valid","users"),selectmode="browse")
            for col,label,width in (("id","ID",65),("file","BZH",170),("size","크기",80),("valid","헤더",70),("users","사용 그룹",420)):
                self.asset_tree.heading(col,text=label);self.asset_tree.column(col,width=width,anchor="w" if col in ("file","users") else "center")
            self.asset_tree.bind("<<TreeviewSelect>>",lambda _e:self.show_asset())
            ttk.Label(right,text="몬스터 외형 리소스",style="Title.TLabel").pack(anchor="w")
            self.asset_info=tk.StringVar();ttk.Label(right,textvariable=self.asset_info,wraplength=720).pack(anchor="w",pady=(8,8))
            hexholder=ttk.Frame(right);hexholder.pack(fill="both",expand=True)
            self.asset_hex=self._text(hexholder,height=12,state="disabled")
            btn=ttk.Frame(right);btn.pack(fill="x",pady=8)
            ttk.Button(btn,text="BZH 내보내기",command=self.export_asset).pack(side="left")
            ttk.Button(btn,text="BZH 교체",command=self.import_asset).pack(side="left",padx=6)
            ttk.Button(btn,text="백업 복원",command=self.restore_asset).pack(side="left")
            assign=ttk.LabelFrame(right,text="선택 외형을 전투 그룹에 지정",padding=8);assign.pack(fill="x")
            self.asset_group_var=tk.StringVar();self.asset_group_combo=ttk.Combobox(assign,textvariable=self.asset_group_var,state="readonly",width=50);self.asset_group_combo.grid(row=0,column=0,sticky="ew")
            self.asset_slot_var=tk.StringVar(value="주 외형");ttk.Combobox(assign,textvariable=self.asset_slot_var,state="readonly",values=("주 외형","보조 외형"),width=12).grid(row=0,column=1,padx=6)
            ttk.Button(assign,text="지정",command=self.assign_asset).grid(row=0,column=2);assign.columnconfigure(0,weight=1)

        def populate_assets(self) -> None:
            self.asset_tree.delete(*self.asset_tree.get_children())
            if not self.project:return
            self.asset_group_combo.configure(values=[g.label for g in self.project.groups])
            for index,a in enumerate(self.project.assets):self.asset_tree.insert("","end",iid=str(index),values=(f"0x{a.asset_id:03X}",a.path.name,a.size,"OK" if a.header_valid else "ERROR",", ".join(a.users)))

        def show_asset(self) -> None:
            if not self.project:return
            sel=self.asset_tree.selection()
            if not sel:return
            a=self.project.assets[int(sel[0])];self.current_asset=a
            self.asset_info.set(f"{a.path.name} · {a.size} bytes · header size-1={a.header_size_minus_one} · {'정상' if a.header_valid else '비정상'}\n사용: {', '.join(a.users) or '없음'}")
            self._readonly_text(self.asset_hex,a.path.read_bytes()[:512].hex(" ").upper())

        def export_asset(self) -> None:
            if not self.current_asset:return
            path=filedialog.asksaveasfilename(initialfile=self.current_asset.path.name,defaultextension=".BZH")
            if path:shutil.copy2(self.current_asset.path,path)

        def import_asset(self) -> None:
            if not self.current_asset:return
            path=filedialog.askopenfilename(filetypes=[("BZH","*.BZH"),("All files","*")])
            if not path:return
            try:replace_bzh(self.current_asset.path,Path(path));self.reload_project();messagebox.showinfo(APP_NAME,"외형 BZH를 교체했습니다.")
            except Exception as exc:messagebox.showerror(APP_NAME,str(exc))

        def restore_asset(self) -> None:
            if not self.current_asset:return
            try:restore_backup(self.current_asset.path);self.reload_project()
            except Exception as exc:messagebox.showerror(APP_NAME,str(exc))

        def assign_asset(self) -> None:
            if not self.project or not self.current_asset:return
            group=next((g for g in self.project.groups if g.label==self.asset_group_var.get()),None)
            if not group:messagebox.showerror(APP_NAME,"전투 그룹을 선택하세요.");return
            key="graphic_id0" if self.asset_slot_var.get()=="주 외형" else "graphic_id1"
            try:patch_group(group,{key:self.current_asset.asset_id});self.reload_project();messagebox.showinfo(APP_NAME,"외형을 지정했습니다.")
            except Exception as exc:messagebox.showerror(APP_NAME,str(exc))

        # Resources -------------------------------------------------------
        def _build_resources_tab(self) -> None:
            tab=ttk.Frame(self.nb);self.nb.add(tab,text="리소스 탐색기")
            left,right=self._make_pane(tab)
            bar=ttk.Frame(left);bar.pack(fill="x",pady=(0,6));self.res_search=tk.StringVar();ttk.Label(bar,text="파일 검색").pack(side="left")
            e=ttk.Entry(bar,textvariable=self.res_search);e.pack(side="left",fill="x",expand=True,padx=6);e.bind("<KeyRelease>",lambda _e:self.populate_resources())
            self.res_tree=self._tree(left,("path","ext","size"),selectmode="browse")
            for col,label,width in (("path","상대 경로",500),("ext","형식",90),("size","크기",110)):
                self.res_tree.heading(col,text=label);self.res_tree.column(col,width=width,anchor="w" if col=="path" else "center")
            self.res_tree.bind("<<TreeviewSelect>>",lambda _e:self.show_resource())
            ttk.Label(right,text="보수적 원본 리소스 관리",style="Title.TLabel").pack(anchor="w")
            self.res_info=tk.StringVar();ttk.Label(right,textvariable=self.res_info,wraplength=720).pack(anchor="w",pady=(8,8))
            holder=ttk.Frame(right);holder.pack(fill="both",expand=True)
            self.res_hex=self._text(holder,height=15,state="disabled")
            btn=ttk.Frame(right);btn.pack(fill="x",pady=8)
            ttk.Button(btn,text="내보내기",command=self.export_resource).pack(side="left")
            ttk.Button(btn,text="같은 크기 파일로 교체",command=self.replace_resource).pack(side="left",padx=6)
            ttk.Button(btn,text="백업 복원",command=self.restore_resource).pack(side="left")

        def populate_resources(self) -> None:
            self.res_tree.delete(*self.res_tree.get_children());self.resource_paths={}
            if not self.project:return
            needle=self.res_search.get().strip().lower();index=0
            for path in sorted(p for p in self.project.root.rglob("*") if p.is_file() and not p.name.endswith(".bak")):
                rel=str(path.relative_to(self.project.root))
                if needle and needle not in rel.lower():continue
                iid=str(index);index+=1;self.resource_paths[iid]=path;self.res_tree.insert("","end",iid=iid,values=(rel,path.suffix.upper() or "(none)",path.stat().st_size))

        def show_resource(self) -> None:
            sel=self.res_tree.selection()
            if not sel:return
            path=self.resource_paths[sel[0]];self.current_resource=path
            self.res_info.set(f"{path.relative_to(self.project.root) if self.project else path.name} · {path.stat().st_size} bytes · 최초 512바이트")
            self._readonly_text(self.res_hex,path.read_bytes()[:512].hex(" ").upper())

        def export_resource(self) -> None:
            if not self.current_resource:return
            path=filedialog.asksaveasfilename(initialfile=self.current_resource.name)
            if path:shutil.copy2(self.current_resource,path)

        def replace_resource(self) -> None:
            if not self.current_resource:return
            source=filedialog.askopenfilename()
            if not source:return
            try:
                data=Path(source).read_bytes()
                if len(data)!=self.current_resource.stat().st_size:raise ValueError("원본과 크기가 정확히 같아야 합니다.")
                atomic_write(self.current_resource,data,True);self.reload_project();messagebox.showinfo(APP_NAME,"리소스를 교체했습니다.")
            except Exception as exc:messagebox.showerror(APP_NAME,str(exc))

        def restore_resource(self) -> None:
            if not self.current_resource:return
            try:restore_backup(self.current_resource);self.reload_project()
            except Exception as exc:messagebox.showerror(APP_NAME,str(exc))

        # Audio -----------------------------------------------------------
        def _build_audio_tab(self) -> None:
            tab=ttk.Frame(self.nb);outer,content=self._scrollable_panel(tab,padding=20);outer.pack(fill="both",expand=True);self.nb.add(tab,text="음악·VGM")
            ttk.Label(content,text="기존 MUS / INS / VGM 도구",style="Title.TLabel").pack(anchor="w")
            ttk.Label(content,text="VGM/VGZ→MUS+INS, OPL 악기, MUS 이벤트 편집 도구를 별도 창으로 실행합니다.",wraplength=900).pack(anchor="w",pady=(10,12))
            ttk.Button(content,text="오디오 도구 열기",command=self.launch_audio_tool).pack(anchor="w")

        def launch_audio_tool(self) -> None:
            if not self.audio_tool or not self.audio_tool.exists():messagebox.showerror(APP_NAME,"ed2_audio_tool.py를 찾을 수 없습니다.");return
            args=[sys.executable,str(self.audio_tool)]
            if self.project:args.append(str(self.project.root))
            try:
                import subprocess;subprocess.Popen(args,cwd=str(self.audio_tool.parent))
            except Exception as exc:messagebox.showerror(APP_NAME,str(exc))

        # Diagnostics -----------------------------------------------------
        def _build_diagnostics_tab(self) -> None:
            tab=ttk.Frame(self.nb,padding=10);self.nb.add(tab,text="검사·분석")
            top=ttk.Frame(tab);top.pack(fill="x")
            ttk.Button(top,text="검사 다시 실행",command=self.run_validation).pack(side="left")
            ttk.Button(top,text="분석 파일 묶음 내보내기",command=self.export_analysis).pack(side="left",padx=6)
            holder=ttk.Frame(tab);holder.pack(fill="both",expand=True,pady=(8,0))
            self.diag_text=self._text(holder)

        def update_diagnostics(self) -> None:
            if not self.project:self._readonly_text(self.diag_text,"");return
            report=self.project.validate()
            lines=[report["tool"],f"Root: {report['root']}","",json.dumps(report["counts"],ensure_ascii=False,indent=2),"",f"Errors ({len(report['errors'])})"]
            lines.extend("  - "+x for x in report["errors"]);lines.extend(["",f"Warnings ({len(report['warnings'])})"]);lines.extend("  - "+x for x in report["warnings"])
            lines.extend(["","v0.8.2 추가:","  MAGIC_BAIRITU를 마법 효과 배율(100=기준)로 설명","  MAGIC_CNT를 재충전 주기(하위=최초, 상위=반복)로 설명","  선택한 마법의 배율·충전 속도 실시간 해석과 0 니블 경고 표시","","v0.7 추가:","  아이템 ITEM_NAME/ITEM_COST/ITEM_KOUKA/ITEM_MAGIC/ITEM_KOKA_NUM/ITEM_MAGIC_NUM/ITEM_TYPE 명칭 교정","  이벤트 아이템 100..126 이름 편집","  마법 32개 MAGIC_NAME/COST/SLC/SLC2/BAIRITU/CNT 편집","  AI·훅 디버그 심볼 표시","  모든 표와 상세 패널에 가로·세로 스크롤 지원"])
            self._readonly_text(self.diag_text,"\n".join(lines))

        def run_validation(self) -> None:
            if not self.project:return
            self.project.reload();self.populate_all();report=self.project.validate();messagebox.showinfo(APP_NAME,f"검사 완료: 오류 {len(report['errors'])}, 경고 {len(report['warnings'])}")

        def export_analysis(self) -> None:
            if not self.project:return
            folder=filedialog.askdirectory(title="분석 파일을 저장할 폴더")
            if not folder:return
            try:files=write_analysis_bundle(self.project,Path(folder));messagebox.showinfo(APP_NAME,"저장 완료:\n"+"\n".join(p.name for p in files))
            except Exception as exc:messagebox.showerror(APP_NAME,str(exc))

    Studio().mainloop()


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main(argv: Optional[list[str]] = None) -> int:
    parser=argparse.ArgumentParser(description=f"{APP_NAME} {VERSION}")
    parser.add_argument("root",nargs="?",type=Path,help="ED2 game root")
    parser.add_argument("--report",type=Path,help="write validation JSON")
    parser.add_argument("--export-analysis",type=Path,help="export CSV/JSON analysis bundle")
    parser.add_argument("--no-gui",action="store_true")
    args=parser.parse_args(argv)
    if args.root and (args.report or args.export_analysis or args.no_gui):
        project=Project(args.root)
        if args.report:
            args.report.parent.mkdir(parents=True, exist_ok=True)
            args.report.write_text(json.dumps(project.validate(),ensure_ascii=False,indent=2),encoding="utf-8")
        if args.export_analysis:write_analysis_bundle(project,args.export_analysis)
        if args.no_gui:
            print(json.dumps(project.validate(),ensure_ascii=False,indent=2));return 0
    audio_tool=Path(__file__).with_name("ed2_audio_tool.py")
    run_gui(args.root,audio_tool)
    return 0


if __name__=="__main__":
    raise SystemExit(main())
