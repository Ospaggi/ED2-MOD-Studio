@echo off
py -3 "%~dp0ed2_mod_studio.py" %*
if errorlevel 1 pause
