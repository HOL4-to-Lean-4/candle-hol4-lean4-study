# Rebuild the reduced package on Windows. HOL4 does not build natively on Windows,
# so this uses Docker Desktop (default) or WSL.
#   scripts\build.ps1            # Docker
#   scripts\build.ps1 -Mode wsl  # run scripts/build.sh native inside the default WSL distribution
param([ValidateSet('docker','wsl')][string]$Mode = 'docker')
$ErrorActionPreference = 'Stop'
$Root = Split-Path -Parent $PSScriptRoot
New-Item -ItemType Directory -Force (Join-Path $Root 'logs') | Out-Null
function Stamp { (Get-Date).ToUniversalTime().ToString('yyyy-MM-ddTHH:mm:ssZ') }
if ($Mode -eq 'docker') {
    $log = Join-Path $Root 'logs\build-docker.log'
    Add-Content $log "image start $(Stamp)"
    docker build -f (Join-Path $Root 'docker\Dockerfile') -t candle-hol4:pinned $Root
    if ($LASTEXITCODE -ne 0) { throw 'docker build failed' }
    Add-Content $log "image end $(Stamp)"
    Add-Content $log "package start $(Stamp)"
    docker run --rm -v "$(Join-Path $Root 'package'):/work" candle-hol4:pinned Holmake
    if ($LASTEXITCODE -ne 0) { throw 'Holmake failed' }
    Add-Content $log "package end $(Stamp)"
} else {
    $wslRoot = (wsl wslpath -a ($Root -replace '\\','/')).Trim()
    wsl sh "$wslRoot/scripts/build.sh" native
    if ($LASTEXITCODE -ne 0) { throw 'WSL build failed' }
}
