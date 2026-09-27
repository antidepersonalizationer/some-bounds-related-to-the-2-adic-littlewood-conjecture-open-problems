param([string]$DependencyPackages = '')
$ErrorActionPreference = 'Stop'
$vvSavedLeanPath = $env:LEAN_PATH
Push-Location -LiteralPath $PSScriptRoot
try {
  $vvConfig = Get-Content -LiteralPath 'audit-config.json' -Raw | ConvertFrom-Json
  New-Item -ItemType Directory -Path 'verification' -Force | Out-Null
  @{status='checking';buildPassed=$false;trustAuditPassed=$false} | ConvertTo-Json |
    Set-Content -LiteralPath 'verification/report.json' -Encoding utf8
  $vvModules = @{}
  foreach ($vvTop in @('VV','Foundations','Research')) {
    if (Test-Path -LiteralPath "$vvTop.lean") { $vvModules[$vvTop] = "$vvTop.lean" }
    if (Test-Path -LiteralPath $vvTop) {
      foreach ($vvFile in Get-ChildItem -LiteralPath $vvTop -Filter '*.lean' -Recurse) {
        $vvRel = [IO.Path]::GetRelativePath($PSScriptRoot,$vvFile.FullName)
        $vvMod = $vvRel.Substring(0,$vvRel.Length-5).Replace('\','.').Replace('/','.')
        $vvModules[$vvMod] = $vvRel
      }
    }
  }
  $vvReached = [Collections.Generic.HashSet[string]]::new()
  $vvStack = [Collections.Generic.Stack[string]]::new()
  foreach ($vvRoot in @('VV','Foundations','Research')) {
    if ($vvModules.ContainsKey($vvRoot)) { $vvStack.Push($vvRoot) }
  }
  foreach ($vvAudit in $vvConfig.audits) { $vvStack.Push($vvAudit.Replace('/','.').Replace('.lean','')) }
  while ($vvStack.Count -gt 0) {
    $vvMod = $vvStack.Pop()
    if (-not $vvReached.Add($vvMod)) { continue }
    foreach ($vvLine in Get-Content -LiteralPath $vvModules[$vvMod]) {
      if ($vvLine -match '^\s*import\s+(.+)$') {
        foreach ($vvImp in ((($Matches[1] -split '--',2)[0]) -split '\s+' | Where-Object { $_ })) {
          if ($vvImp -match '^(VV|Foundations|Research)(\.|$)') {
            if (-not $vvModules.ContainsKey($vvImp)) { throw "Missing project import: $vvMod -> $vvImp" }
            $vvStack.Push($vvImp)
          }
        }
      }
    }
  }
  if ($vvReached.Count -ne $vvModules.Count) { throw 'Uncovered project module.' }
  $vvAdmittedFiles = @($vvConfig.admissions.PSObject.Properties.Name)
  $vvAdmits = @()
  foreach ($vvRel in $vvModules.Values) {
    $vvText = Get-Content -LiteralPath $vvRel -Raw
    if ($vvText -match '(?m)^\s*(?:(?:private|protected|unsafe|noncomputable)\s+)*(?:axiom|opaque)\b') {
      throw "Forbidden source axiom/opaque: $vvRel"
    }
    $vvCount = ([regex]::Matches($vvText,'(?m)^\s*sorry\s*$')).Count
    if ($vvCount) {
      $vvPortable = $vvRel.Replace('\','/')
      if ($vvCount -ne 1 -or $vvPortable -notin $vvAdmittedFiles) { throw "Unexpected admission: $vvRel" }
      $vvAdmits += $vvPortable
    }
  }
  if ($vvAdmits.Count -ne $vvAdmittedFiles.Count) { throw 'Admission inventory mismatch.' }
  $env:LEAN_PATH = ''
  if (-not $env:ELAN_HOME) { $env:ELAN_HOME = Join-Path $env:USERPROFILE '.elan' }
  $env:PATH = (Join-Path $env:ELAN_HOME 'bin') + ';' + $env:PATH
  $vvCommit = (& lean --githash | Out-String).Trim()
  if ($LASTEXITCODE -ne 0 -or $vvCommit -ne 'b02228b03f655c0cd051d82280ad5758359ec8ba') { throw 'Compiler identity mismatch.' }
  $vvArgs = @()
  if ($DependencyPackages) {
    $vvDeps = (Resolve-Path -LiteralPath $DependencyPackages).Path
    $vvManifest = Get-Content -LiteralPath 'lake-manifest.json' -Raw | ConvertFrom-Json
    $vvOverrides = foreach ($vvPkg in $vvManifest.packages) {
      $vvPath = (Join-Path $vvDeps $vvPkg.name).Replace('\','/')
      $vvRev = (& git -c "safe.directory=$vvPath" -C $vvPath rev-parse HEAD | Out-String).Trim()
      if ($LASTEXITCODE -ne 0 -or $vvRev -ne $vvPkg.rev) { throw "Dependency revision mismatch: $($vvPkg.name)" }
      $vvDirty = (& git -c "safe.directory=$vvPath" -C $vvPath status --porcelain --untracked-files=no | Out-String).Trim()
      if ($LASTEXITCODE -ne 0 -or $vvDirty) { throw "Dirty dependency: $($vvPkg.name)" }
      [ordered]@{name=$vvPkg.name;scope=$vvPkg.scope;type='path';dir=$vvPath;inherited=$vvPkg.inherited;configFile=$vvPkg.configFile;manifestFile=$vvPkg.manifestFile}
    }
    New-Item -ItemType Directory -Path '.lake' -Force | Out-Null
    @{version=$vvManifest.version;packages=@($vvOverrides)} | ConvertTo-Json -Depth 6 |
      Set-Content -LiteralPath '.lake/dependency-overrides.json' -Encoding utf8
    $vvArgs = @('--packages=.lake/dependency-overrides.json')
  }
  & lake @vvArgs build *> 'verification/build.log'
  if ($LASTEXITCODE -ne 0) { Get-Content 'verification/build.log' -Tail 45; throw 'Build failed.' }
  $vvCounts = @()
  $vvAxiomOutput = @()
  foreach ($vvAudit in $vvConfig.audits) {
    $vvLog = 'verification/' + $vvAudit.Replace('/','-').Replace('.lean','.log')
    & lake @vvArgs env lean $vvAudit *> $vvLog
    if ($LASTEXITCODE -ne 0) { Get-Content $vvLog -Tail 45; throw "Audit failed: $vvAudit" }
    $vvText = Get-Content -LiteralPath $vvLog -Raw
    if ($vvText -notmatch 'PASS: (\d+) theorem declarations and (\d+) definitions audited\.') { throw 'Missing audit acceptance marker.' }
    $vvCounts += @{audit=$vvAudit;theorems=[int]$Matches[1];definitions=[int]$Matches[2]}
    $vvAxiomOutput += @([regex]::Matches($vvText,"(?m)^'[^']+' depends on axioms:\s*\[[^\]]*\]") |
      ForEach-Object { $_.Value -replace '\s+',' ' })
    $vvAxiomOutput += @($vvText -split '\r?\n' | Where-Object {$_ -match '^PASS:|^ADMISSION COUNT:|^THEORY AXIOMS AFTER'})
  }
  $vvAxiomOutput | Set-Content -LiteralPath 'verification/final-axioms.txt' -Encoding utf8
  $vvHashFiles = @($vvModules.Values) + @('lakefile.toml','lake-manifest.json','lean-toolchain','audit-config.json','Check-Project.ps1','VV/Entropy/LICENSE','VV/Entropy/NOTICE')
  $vvHashes = foreach ($vvRel in $vvHashFiles) {
    @{file=$vvRel.Replace('\','/');sha256=(Get-FileHash -LiteralPath $vvRel -Algorithm SHA256).Hash}
  }
  [ordered]@{
    checkedUtc=[DateTime]::UtcNow.ToString('o');kind=$vvConfig.kind
    status='verified-with-explicit-boundaries';buildPassed=$true;trustAuditPassed=$true
    compilerCommit=$vvCommit;mathlibCommit='5c0c94b3f563ed756b48b9439788c53b0d56a897'
    sourceModules=$vvModules.Count;audits=$vvCounts;sourceSorryCount=$vvAdmits.Count
    admissions=$vvConfig.admissions;customAxiomOrOpaqueDeclarations=0
    allowedOrdinaryAxioms=@('propext','Classical.choice','Quot.sound')
    dependencyCachesReused=[bool]$DependencyPackages;cleanCloneBuild=$false
    unchangedProjectCachesMayBeReused=$true;finiteEnumerationExecuted=$false
    elCompleted=$false;sourceHashes=$vvHashes
  } | ConvertTo-Json -Depth 7 | Set-Content -LiteralPath 'verification/report.json' -Encoding utf8
  Write-Output "PASS: $($vvConfig.kind); $($vvModules.Count) source modules; $($vvAdmits.Count) explicitly admitted proof(s)."
} finally { $env:LEAN_PATH=$vvSavedLeanPath; Pop-Location }
