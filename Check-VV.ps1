param(
    # Optional reuse of an existing, revision-checked dependency checkout.
    # Only dependencies are reused; Lake rebuilds this project's own sources.
    [string]$DependencyPackages = ''
)
$ErrorActionPreference = 'Stop'
$vvOriginalLeanPath = $env:LEAN_PATH
Push-Location $PSScriptRoot
try {
    # Lake must resolve project imports from its own build, never from stale
    # ad-hoc .olean files left in a source directory by an interactive session.
    $env:LEAN_PATH = ''
    if (-not $env:ELAN_HOME) {
        $env:ELAN_HOME = Join-Path $env:USERPROFILE '.elan'
    }
    $env:PATH = (Join-Path $env:ELAN_HOME 'bin') + ';' + $env:PATH
    New-Item -ItemType Directory -Force -Path 'verification' | Out-Null
    [ordered]@{
        status = 'checking'
        buildPassed = $false
        trustAuditPassed = $false
        requestedClosureComplete = $false
    } | ConvertTo-Json | Set-Content -LiteralPath 'verification/report.json' -Encoding utf8

    $vvVersion = (& lean --version | Out-String).Trim()
    if ($LASTEXITCODE -ne 0) { throw 'Lean toolchain unavailable.' }
    $vvLeanCommit = (& lean --githash | Out-String).Trim()
    if ($LASTEXITCODE -ne 0 -or $vvLeanCommit -ne 'b02228b03f655c0cd051d82280ad5758359ec8ba') {
        throw 'Unexpected Lean compiler commit.'
    }
    $vvLakeArgs = @()
    if ($DependencyPackages) {
        $vvDependencyRoot = (Resolve-Path -LiteralPath $DependencyPackages).Path
        $vvManifest = Get-Content -LiteralPath 'lake-manifest.json' -Raw | ConvertFrom-Json
        $vvOverrides = foreach ($vvPackage in $vvManifest.packages) {
            $vvPackagePath = (Join-Path $vvDependencyRoot $vvPackage.name).Replace('\','/')
            $vvRevision = (& git -c "safe.directory=$vvPackagePath" -C $vvPackagePath rev-parse HEAD | Out-String).Trim()
            if ($LASTEXITCODE -ne 0 -or $vvRevision -ne $vvPackage.rev) {
                throw "Dependency revision mismatch: $($vvPackage.name)"
            }
            $vvDirty = (& git -c "safe.directory=$vvPackagePath" -C $vvPackagePath status --porcelain --untracked-files=no | Out-String).Trim()
            if ($LASTEXITCODE -ne 0 -or $vvDirty) {
                throw "Dependency has tracked changes: $($vvPackage.name)"
            }
            [ordered]@{
                name = $vvPackage.name; scope = $vvPackage.scope
                type = 'path'; dir = $vvPackagePath
                inherited = $vvPackage.inherited
                configFile = $vvPackage.configFile
                manifestFile = $vvPackage.manifestFile
            }
        }
        New-Item -ItemType Directory -Force -Path '.lake' | Out-Null
        [ordered]@{ version = $vvManifest.version; packages = @($vvOverrides) } |
            ConvertTo-Json -Depth 6 | Set-Content -LiteralPath '.lake/dependency-overrides.json' -Encoding utf8
        $vvLakeArgs = @('--packages=.lake/dependency-overrides.json')
    }
    & lake @vvLakeArgs build *> 'verification/build.log'
    if ($LASTEXITCODE -ne 0) {
        Get-Content -LiteralPath 'verification/build.log' -Tail 50
        throw 'Lean build failed.'
    }
    & lake @vvLakeArgs env lean VV/Audit.lean *> 'verification/axioms.log'
    if ($LASTEXITCODE -ne 0) {
        Get-Content -LiteralPath 'verification/axioms.log' -Tail 50
        throw 'Lean trust audit failed.'
    }
    $vvAudit = Get-Content -LiteralPath 'verification/axioms.log' -Raw
    if ($vvAudit -notmatch 'PASS: (\d+) theorem declarations and (\d+) definitions audited\.') {
        throw 'The audit acceptance marker is missing.'
    }
    $vvTheorems = [int]$Matches[1]
    $vvDefinitions = [int]$Matches[2]
    $vvProblem7Match = [regex]::Match($vvAudit,
        "(?m)^'VV\.problem7' depends on axioms:\s*\[([^\]]*)\]")
    if (-not $vvProblem7Match.Success) { throw 'Missing actual Problem 7 axiom output.' }
    $vvProblem7Axioms = @($vvProblem7Match.Groups[1].Value -split ',' |
        ForEach-Object { $_.Trim() })
    $vvExpectedProblem7Axioms = @('propext','sorryAx','Classical.choice','Quot.sound')
    if ($vvProblem7Axioms.Count -ne 4 -or
        @(Compare-Object $vvExpectedProblem7Axioms $vvProblem7Axioms).Count -ne 0) {
        throw 'Unexpected actual Problem 7 axiom list.'
    }
    @(
        'Generated from the successful VV/Audit.lean run. The complete transient log is axioms.log.'
        'Allowed proof admissions: VV.P5FiniteCheck.rank_check_10_14; VV.BBEKLowEntropyCore.rootAlternative_of_positive_entropy.'
        ([regex]::Matches($vvAudit, "(?m)^'[^']+' depends on axioms:\s*\[[^\]]*\]") |
            ForEach-Object { $_.Value -replace '\s+', ' ' })
        ($vvAudit -split '\r?\n' | Where-Object {
            $_ -match 'THEORY AXIOMS AFTER|^PASS:'
        })
    ) | Set-Content -LiteralPath 'verification/final-axioms.txt' -Encoding utf8
    $vvAdmits = @(Get-ChildItem -LiteralPath 'VV' -Filter '*.lean' -Recurse |
        Select-String -Pattern '^\s*sorry\s*$')
    $vvAllowedAdmissionFiles = @('P5FiniteCheck.lean', 'BBEKLowEntropyCore.lean')
    if ($vvAdmits.Count -ne 2 -or
        @($vvAdmits | Where-Object { $_.Filename -notin $vvAllowedAdmissionFiles }).Count -ne 0 -or
        @($vvAdmits | Select-Object -ExpandProperty Filename -Unique).Count -ne 2) {
        throw 'Expected exactly the specified finite computation and EL-core admissions.'
    }
    $vvExplicitAxioms = @(Get-ChildItem -LiteralPath 'VV' -Filter '*.lean' -Recurse |
        Select-String -Pattern '^\s*(?:(?:private|protected|unsafe|noncomputable)\s+)*(?:axiom|opaque)\b')
    if ($vvExplicitAxioms.Count -ne 0) {
        throw 'A project source explicitly declares an axiom or opaque interface.'
    }
    $vvSources = @((Get-Item -LiteralPath 'VV.lean')) +
        @(Get-ChildItem -LiteralPath 'VV' -Filter '*.lean' -Recurse) +
        @(Get-Item -LiteralPath 'lakefile.toml','lake-manifest.json','lean-toolchain','Check-VV.ps1','VV/Entropy/LICENSE','VV/Entropy/NOTICE')
    $vvHashes = foreach ($vvSource in $vvSources) {
        [ordered]@{
            file = [IO.Path]::GetRelativePath($PSScriptRoot, $vvSource.FullName)
            sha256 = (Get-FileHash -LiteralPath $vvSource.FullName -Algorithm SHA256).Hash
        }
    }
    [ordered]@{
        checkedUtc = [DateTime]::UtcNow.ToString('o')
        status = 'verified-with-two-specified-admissions'
        buildPassed = $true
        trustAuditPassed = $true
        requestedClosureComplete = $true
        fullySorryFree = $false
        leanToolchain = 'leanprover/lean4:v4.20.1'
        compilerVersionOutput = $vvVersion
        compilerCommit = $vvLeanCommit
        mathlibCommit = '5c0c94b3f563ed756b48b9439788c53b0d56a897'
        dependencyPackagesReused = $DependencyPackages
        auditedTheoremDeclarations = $vvTheorems
        auditedDefinitions = $vvDefinitions
        permittedAxioms = @('propext','Classical.choice','Quot.sound')
        sorryDeclarations = $vvAdmits.Count
        customAxiomOrOpaqueDeclarations = $vvExplicitAxioms.Count
        admittedFiniteComputation = 'VV.P5FiniteCheck.rank_check_10_14'
        admittedELCore = 'VV.BBEKLowEntropyCore.rootAlternative_of_positive_entropy'
        finiteComputationType = '(VV.P5Window.windowGraph 10 14).checkEventuallyDeterministic = true'
        finiteComputationExecuted = $false
        theoryAuditMethod = 'Validate the exact types of the finite check and EL core; abstract only those two proof declarations; audit every other project declaration and transitive dependency.'
        problem3 = 'closed: VV.problem3_classification'
        problem4 = 'closed: VV.Problem4.problem4_all_periods; finiteness and class count <= 3*l*4^l'
        problem5 = 'all theory closed; one unexecuted finite check: VV.P5FiniteCheck.rank_check_10_14'
        problem7 = 'VV.problem7 : VV.Problem7.Statement; no external hypotheses; depends only on the named EL-core admission beyond the standard axioms'
        bbekTheorem42 = 'VV.bbekTheorem42 : VV.P7BoxCover.BBEKTheorem42; internally constructed'
        problem7Axioms = $vvProblem7Axioms
        bbekOriginalSource = 'Badziahin-Bugeaud-Einsiedler-Kleinbock, arXiv:1405.5545v2, Theorem 4.2 and Section 5'
        bbekProposition51 = 'closed for p=2 on the actual S-arithmetic quotient: VV.BBEKOrbit.proposition51'
        bbekNewTheorySorryDeclarations = 1
        bbekMahlerCompactness = 'closed: VV.BBEKMahler.compact_K'
        bbekTopologicalEntropy = 'closed: actual trapped parameter positive box dimension implies positive cover entropy'
        bbekRemainingTheory = @('The single EL low-entropy core: leafwise entropy, shearing, and exceptional-branch elimination imply a nonzero invariant root element')
        sourceHashes = $vvHashes
    } | ConvertTo-Json -Depth 7 | Set-Content -LiteralPath 'verification/report.json' -Encoding utf8
    Write-Output "PASS: build and trust audit; $vvTheorems theorem declarations and $vvDefinitions definitions."
    Write-Output 'Problems 3 and 4 are closed. Problem 5 retains its finite check. VV.problem7 has no external hypotheses and retains only the specified EL-core admission.'
} finally {
    $env:LEAN_PATH = $vvOriginalLeanPath
    Pop-Location
}
