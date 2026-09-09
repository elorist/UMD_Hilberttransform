# Use the user-wide toolchain; preserve an explicitly configured external ELAN_HOME.
$taskLocalElan = [System.IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../.tools/elan'))
if (-not $env:ELAN_HOME -or $env:ELAN_HOME -eq $taskLocalElan) {
    $env:ELAN_HOME = Join-Path ([Environment]::GetFolderPath('UserProfile')) '.elan'
}
$taskElanBin = Join-Path $env:ELAN_HOME 'bin'
if (Test-Path -LiteralPath $taskElanBin) {
    if (($env:PATH -split [regex]::Escape([System.IO.Path]::PathSeparator)) -notcontains $taskElanBin) {
        $env:PATH = $taskElanBin + [System.IO.Path]::PathSeparator + $env:PATH
    }
}
