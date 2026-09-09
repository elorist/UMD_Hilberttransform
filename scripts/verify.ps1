#Requires -Version 7.2
$ErrorActionPreference = 'Stop'
$taskProject = [System.IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..'))
Push-Location -LiteralPath $taskProject
try {
    . (Join-Path $PSScriptRoot 'lean-env.ps1')
    $taskLean = (Get-Content -LiteralPath 'lean-toolchain' -Raw).Trim()
    $taskManifest = Get-Content -LiteralPath 'lake-manifest.json' -Raw | ConvertFrom-Json
    $taskMathlib = $taskManifest.packages | Where-Object name -eq 'mathlib'
    if ($taskLean -ne 'leanprover/lean4:v4.33.0' -or
        $taskMathlib.rev -ne 'db584cd6d46c92f209a44c0f1c829460d327499d') {
        throw 'The Lean or mathlib pin changed; review the dependency update deliberately.'
    }

    $taskFiles = @(Get-Item -LiteralPath 'HilbertUMD.lean')
    $taskFiles += Get-ChildItem -LiteralPath 'HilbertUMD' -Filter '*.lean' -Recurse
    $taskModules = @{}
    foreach ($taskFile in $taskFiles) {
        $taskSource = Get-Content -LiteralPath $taskFile.FullName -Raw
        if ($taskSource -match '\b(sorry|admit|axiom|native_decide)\b') {
            throw ('Unproved declaration or proof escape in ' + $taskFile.FullName)
        }
        $taskRelative = [System.IO.Path]::GetRelativePath($taskProject, $taskFile.FullName)
        $taskName = ($taskRelative -replace '\.lean$', '') -replace '[\\/]', '.'
        $taskModules[$taskName] = @([regex]::Matches($taskSource,
            '(?m)^import\s+(HilbertUMD(?:\.[\w]+)*)\s*$') | ForEach-Object { $_.Groups[1].Value })
    }
    $taskSeen = [System.Collections.Generic.HashSet[string]]::new()
    $taskPending = [System.Collections.Generic.Stack[string]]::new()
    $taskPending.Push('HilbertUMD')
    while ($taskPending.Count -gt 0) {
        $taskName = $taskPending.Pop()
        if (-not $taskSeen.Add($taskName)) { continue }
        if (-not $taskModules.ContainsKey($taskName)) { throw ('Missing source module: ' + $taskName) }
        foreach ($taskImport in $taskModules[$taskName]) { $taskPending.Push($taskImport) }
    }
    foreach ($taskName in $taskModules.Keys) {
        if (-not $taskSeen.Contains($taskName)) { throw ('Source module outside the main theorem: ' + $taskName) }
    }

    $taskLogs = Join-Path $taskProject '.lake/verification'
    New-Item -ItemType Directory -Path $taskLogs -Force | Out-Null
    # Remove an earlier success record before starting a new verification.
    $taskResultPath = Join-Path $taskLogs 'result.json'
    if (Test-Path -LiteralPath $taskResultPath) { Remove-Item -LiteralPath $taskResultPath }
    & lake build --wfail 2>&1 | Tee-Object -FilePath (Join-Path $taskLogs 'build.log')
    if ($LASTEXITCODE -ne 0) { throw 'Main theorem build failed.' }
    $taskAudit = & lake env lean -DwarningAsError=true tests/MainTheorem.lean 2>&1
    $taskAuditExit = $LASTEXITCODE
    $taskAudit | Tee-Object -FilePath (Join-Path $taskLogs 'audit.log')
    if ($taskAuditExit -ne 0 -or -not (($taskAudit -join "`n").Contains('PASS: full main theorem'))) {
        throw 'Main theorem dependency audit failed.'
    }
    & lake env lean -DwarningAsError=true tests/Definitions.lean 2>&1 | Tee-Object -FilePath (Join-Path $taskLogs 'definitions.log')
    if ($LASTEXITCODE -ne 0) { throw 'Mathematical definition checks failed.' }

    $taskAllAxioms = & lake env lean -DwarningAsError=true tests/AxiomAudit.lean 2>&1
    $taskAllAxiomsExit = $LASTEXITCODE
    $taskAllAxioms | Tee-Object -FilePath (Join-Path $taskLogs 'axioms.log')
    if ($taskAllAxiomsExit -ne 0 -or -not (($taskAllAxioms -join "`n").Contains('PASS: whole-project axiom audit'))) {
        throw 'Whole-project axiom audit failed.'
    }

    # Each replay loads a full import environment. Bound memory use on CI runners.
    $taskPreviousLeanThreads = $env:LEAN_NUM_THREADS
    try {
        $env:LEAN_NUM_THREADS = '1'
        & lake env leanchecker -v HilbertUMD 2>&1 | Tee-Object -FilePath (Join-Path $taskLogs 'kernel.log')
        if ($LASTEXITCODE -ne 0) { throw 'Compiled proof kernel replay failed.' }
    } finally {
        $env:LEAN_NUM_THREADS = $taskPreviousLeanThreads
    }

    [ordered]@{
        verifiedAt = [DateTimeOffset]::Now.ToString('o')
        lean = $taskLean
        mathlibCommit = $taskMathlib.rev
        paperDeclaration = 'HilbertUMD.theorem_1_1'
        mainDeclaration = 'HilbertUMD.main_theorem_p2'
        quantitativeDeclaration = 'HilbertUMD.main_theorem_p2_quantitative'
        scope = 'Theorem 1.1; dimensions 2^n; n and sqrt(n); real and complex; common positive constants; all n>=1; arbitrary UMD sample universes with equal p=2 constants; internal and quantitative companions in universe zero'
        admissions = 0
        warningsAsErrors = $true
        wholeProjectAxiomAudit = 'passed'
        kernelReplay = 'passed'
        allowedAxioms = @('propext', 'Classical.choice', 'Quot.sound')
        sourceSha256 = @(@($taskFiles + (Get-ChildItem -LiteralPath tests -Filter '*.lean')) |
            Sort-Object FullName | ForEach-Object {
                [ordered]@{
                    path = [System.IO.Path]::GetRelativePath($taskProject, $_.FullName)
                    sha256 = (Get-FileHash -LiteralPath $_.FullName -Algorithm SHA256).Hash
                }
            })
    } | ConvertTo-Json -Depth 5 | Set-Content -LiteralPath $taskResultPath -Encoding utf8
    Write-Output 'Verified the full main theorem. Reports: .lake/verification/'
} finally {
    Pop-Location
}
