#Requires -Version 7.2
$ErrorActionPreference = 'Stop'
$taskProject = [System.IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..'))
Push-Location -LiteralPath $taskProject
try {
    if (-not (Get-Command git -ErrorAction SilentlyContinue)) { throw 'Install Git before running this script.' }
    . (Join-Path $PSScriptRoot 'lean-env.ps1')
    $taskTools = Join-Path ([Environment]::GetFolderPath('UserProfile')) '.cache/lean/bootstrap'
    New-Item -ItemType Directory -Path $taskTools -Force | Out-Null
    $taskElan = Join-Path $env:ELAN_HOME 'bin/elan.exe'
    if (-not (Test-Path -LiteralPath $taskElan)) {
        $taskZip = Join-Path $taskTools 'elan.zip'
        & curl.exe -fLsS 'https://github.com/leanprover/elan/releases/download/v4.2.4/elan-x86_64-pc-windows-msvc.zip' -o $taskZip
        if ($LASTEXITCODE -ne 0) { throw 'Elan download failed.' }
        $taskHash = (Get-FileHash -LiteralPath $taskZip -Algorithm SHA256).Hash
        if ($taskHash -ne 'FAD2E980A191C15884CC1D80D170FFC5FA84F3774541020145B66D1A644C6111') {
            throw 'Elan installer SHA256 mismatch.'
        }
        $taskInstaller = Join-Path $taskTools 'elan-installer'
        Expand-Archive -LiteralPath $taskZip -DestinationPath $taskInstaller -Force
        & (Join-Path $taskInstaller 'elan-init.exe') -y --no-modify-path --default-toolchain none
        if ($LASTEXITCODE -ne 0) { throw 'Elan installation failed.' }
    }
    . (Join-Path $PSScriptRoot 'lean-env.ps1')
    & elan toolchain install (Get-Content -LiteralPath 'lean-toolchain' -Raw).Trim()
    if ($LASTEXITCODE -ne 0) { throw 'Lean installation failed.' }
    & lake exe cache get
    if ($LASTEXITCODE -ne 0) { throw 'Mathlib cache download failed.' }
    & (Join-Path $PSScriptRoot 'verify.ps1')
} finally {
    Pop-Location
}
