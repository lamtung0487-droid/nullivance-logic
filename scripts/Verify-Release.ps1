param(
  [switch]$AllowDirty,
  [switch]$SkipLeanBuild,
  [switch]$SkipPdfBuild
)

$ErrorActionPreference = 'Stop'
$projectRoot = Split-Path -Parent $PSScriptRoot
$leanRoot = Join-Path $projectRoot 'Nullivance'

function Assert-True {
  param(
    [Parameter(Mandatory)] [bool]$Condition,
    [Parameter(Mandatory)] [string]$Message
  )
  if (-not $Condition) { throw $Message }
}

Write-Host 'Checking required release files and metadata'
$required = @(
  'README.md', 'LICENSE', 'CITATION.cff', '.zenodo.json', 'ARTIFACT.md',
  'RELEASE_CHECKLIST.md', 'CHANGELOG.md', 'docs/CLAIM_LEDGER.md',
  'docs/DOC_LEAN_MATRIX.md', 'Nullivance/lean-toolchain',
  'Nullivance/lakefile.toml', 'Nullivance/lake-manifest.json',
  'papers/npl-core/main.tex', 'papers/npl-finite-fo/main.tex',
  'scripts/Build-Papers.ps1', 'scripts/Verify-ManuscriptLeanRefs.ps1',
  'scripts/Update-ClaimLedger.ps1', 'scripts/New-ReleasePackage.ps1',
  'scripts/Verify-Archive.ps1'
)
foreach ($relative in $required) {
  $path = Join-Path $projectRoot $relative
  Assert-True (Test-Path -LiteralPath $path -PathType Leaf) "Missing required file: $relative"
}

$zenodo = Get-Content -LiteralPath (Join-Path $projectRoot '.zenodo.json') -Raw |
  ConvertFrom-Json
Assert-True ($zenodo.version -eq '0.7.1') '.zenodo.json must declare version 0.7.1.'
Assert-True ($zenodo.license -eq 'cc-by-4.0') '.zenodo.json license is inconsistent.'
$repositoryUrl = 'https://github.com/lamtung0487-droid/nullivance-logic'
$versionDoi = '10.5281/zenodo.21964600'
$repositoryRelation = $zenodo.related_identifiers |
  Where-Object { $_.identifier -eq $repositoryUrl -and $_.relation -eq 'isSupplementTo' }
Assert-True ($null -ne $repositoryRelation) '.zenodo.json lacks the canonical repository relation.'
Assert-True ($zenodo.notes -match [regex]::Escape($versionDoi)) '.zenodo.json lacks the version DOI.'

$cff = Get-Content -LiteralPath (Join-Path $projectRoot 'CITATION.cff') -Raw -Encoding utf8
Assert-True ($cff -match '(?m)^cff-version: 1\.2\.0$') 'CITATION.cff must use CFF 1.2.0.'
Assert-True ($cff -match '(?m)^version: 0\.7\.1$') 'CITATION.cff version is not 0.7.1.'
Assert-True ($cff -match '(?m)^license: CC-BY-4\.0$') 'CITATION.cff license is inconsistent.'
Assert-True ($cff -match '(?m)^    email: lamtung0481@gmail\.com$') 'CITATION.cff contact email is inconsistent.'
Assert-True ($cff -match [regex]::Escape($repositoryUrl)) 'CITATION.cff lacks the canonical repository URL.'
Assert-True ($cff -match [regex]::Escape($versionDoi)) 'CITATION.cff lacks the version DOI.'

foreach ($manuscript in @('papers/npl-core/main.tex', 'papers/npl-finite-fo/main.tex')) {
  $manuscriptText = Get-Content -LiteralPath (Join-Path $projectRoot $manuscript) -Raw -Encoding utf8
  Assert-True ($manuscriptText -match 'lamtung0481@gmail\.com') `
    "$manuscript contact email is inconsistent."
  Assert-True ($manuscriptText -match [regex]::Escape($repositoryUrl)) `
    "$manuscript lacks the canonical repository URL."
  Assert-True ($manuscriptText -match [regex]::Escape($versionDoi)) `
    "$manuscript lacks the version DOI."
}

$toolchain = (Get-Content -LiteralPath (Join-Path $leanRoot 'lean-toolchain') -Raw).Trim()
Assert-True ($toolchain -eq 'leanprover/lean4:v4.32.1') "Unexpected Lean toolchain: $toolchain"
Assert-True ($toolchain -notmatch '(?i)(rc|alpha|beta|nightly)') 'Release toolchain is not stable.'

$lakefile = Get-Content -LiteralPath (Join-Path $leanRoot 'lakefile.toml') -Raw
Assert-True ($lakefile -match '(?m)^version = "0\.7\.1"$') 'Lake package version is inconsistent.'
Assert-True ($lakefile -match '(?m)^rev = "v4\.32\.1"$') 'mathlib tag is not pinned in lakefile.toml.'

$manifest = Get-Content -LiteralPath (Join-Path $leanRoot 'lake-manifest.json') -Raw |
  ConvertFrom-Json
$mathlib = $manifest.packages | Where-Object { $_.name -eq 'mathlib' }
Assert-True ($null -ne $mathlib) 'mathlib is missing from lake-manifest.json.'
Assert-True ($mathlib.rev -eq '520045ab14e26149ee970e2e617ca04b09bde5d6') `
  "Unexpected mathlib revision: $($mathlib.rev)"

Push-Location $projectRoot
try {
  $gitCommand = Get-Command git -ErrorAction SilentlyContinue
  $insideWorktree = $false
  if ($null -ne $gitCommand) {
    $worktreeResult = git rev-parse --is-inside-work-tree 2>$null
    $insideWorktree = $LASTEXITCODE -eq 0 -and ($worktreeResult -join '').Trim() -eq 'true'
  }

  if ($insideWorktree) {
    if (-not $AllowDirty) {
      $dirty = git status --porcelain
      Assert-True ([string]::IsNullOrWhiteSpace(($dirty -join "`n"))) `
        'Release verification requires a clean Git worktree. Use -AllowDirty only during development.'
    }

    git diff --check
    Assert-True ($LASTEXITCODE -eq 0) 'git diff --check reported whitespace errors.'
  }
  else {
    Write-Host 'No Git metadata found; verifying extracted source contents.'
  }
}
finally {
  Pop-Location
}

Write-Host 'Checking canonical status-label integrity'
$canonicalFiles = Get-ChildItem -LiteralPath (Join-Path $projectRoot 'docs') -File |
  Where-Object { $_.Name -match '^0[1-5]-.*\.md$' } |
  Sort-Object Name
$headerPattern = '^\*\*(Definition|Convention|Lemma|Proposition|Theorem|Corollary|Remark|Conjecture) ([0-9]+\.[0-9]+)'
$statusPattern = '`\[(DRAFT|CONJECTURE|PROVEN|VERIFIED|REFUTED)\]`'
$numbers = [System.Collections.Generic.List[string]]::new()
foreach ($file in $canonicalFiles) {
  $lineNumber = 0
  foreach ($line in Get-Content -LiteralPath $file.FullName -Encoding utf8) {
    $lineNumber++
    if ($line -notmatch $headerPattern) { continue }
    $number = $Matches[2]
    $numbers.Add($number)
    $statuses = [regex]::Matches($line, $statusPattern)
    Assert-True ($statuses.Count -eq 1) `
      "$($file.Name):$lineNumber item $number must carry exactly one status label on its heading."
  }
}
Assert-True ($numbers.Count -gt 0) 'No canonical numbered items were found.'
$duplicates = $numbers | Group-Object | Where-Object Count -gt 1
Assert-True ($duplicates.Count -eq 0) `
  "Duplicate canonical numbers: $(($duplicates.Name | Sort-Object) -join ', ')"

$ledgerTemp = Join-Path ([System.IO.Path]::GetTempPath()) `
  ("nullivance-claim-ledger-{0}.md" -f [guid]::NewGuid())
try {
  & (Join-Path $PSScriptRoot 'Update-ClaimLedger.ps1') -OutputPath $ledgerTemp
  $expectedLedger = Get-Content -LiteralPath $ledgerTemp -Raw -Encoding utf8
  $actualLedger = Get-Content -LiteralPath (Join-Path $projectRoot 'docs/CLAIM_LEDGER.md') -Raw -Encoding utf8
  Assert-True ($expectedLedger -ceq $actualLedger) `
    'docs/CLAIM_LEDGER.md is stale; run scripts/Update-ClaimLedger.ps1.'
}
finally {
  if (Test-Path -LiteralPath $ledgerTemp) {
    Remove-Item -LiteralPath $ledgerTemp -Force
  }
}

Write-Host 'Scanning Lean sources for proof holes and custom axioms'
$leanSources = Get-ChildItem -LiteralPath (Join-Path $leanRoot 'Nullivance') -Filter '*.lean' -File
foreach ($file in $leanSources) {
  $lines = Get-Content -LiteralPath $file.FullName -Encoding utf8
  for ($index = 0; $index -lt $lines.Count; $index++) {
    $line = $lines[$index]
    $proofHolePattern = '^\s*(sorry|admit)\b|\b(by|exact)\s+(sorry|admit)\b|:=\s*(sorry|admit)\b'
    Assert-True ($line -notmatch $proofHolePattern) `
      "$($file.Name):$($index + 1) contains a proof-hole command."
    Assert-True ($line -notmatch '^\s*(axiom|opaque)\s+') `
      "$($file.Name):$($index + 1) introduces a custom axiom or opaque declaration."
  }
}

if (-not $SkipLeanBuild) {
  Write-Host 'Building the complete Lean import root'
  Push-Location $leanRoot
  try {
    lake build
    Assert-True ($LASTEXITCODE -eq 0) 'lake build failed.'
  }
  finally {
    Pop-Location
  }
}

& (Join-Path $PSScriptRoot 'Verify-ManuscriptLeanRefs.ps1')

if (-not $SkipPdfBuild) {
  & (Join-Path $PSScriptRoot 'Build-Papers.ps1')
}

Write-Host "Release verification passed: $($numbers.Count) canonical items checked."
