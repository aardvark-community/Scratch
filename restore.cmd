@echo off
SETLOCAL
PUSHD %~dp0

.paket\paket.bootstrapper.exe
if errorlevel 1 (
  exit /b %errorlevel%
)

if NOT exist paket.lock (
    echo No paket.lock found, running paket install.
    .paket\paket.exe install
)

.paket\paket.exe restore
.paket\paket.exe generate-load-scripts