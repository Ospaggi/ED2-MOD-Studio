@echo off
py -3 "%~dp0ed2_audio_tool.py" %*
if errorlevel 1 pause
