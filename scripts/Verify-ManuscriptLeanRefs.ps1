$ErrorActionPreference = 'Stop'
$projectRoot = Split-Path -Parent $PSScriptRoot
$leanRoot = Join-Path $projectRoot 'Nullivance'
$papers = @(
  (Join-Path $projectRoot 'papers/npl-core/main.tex'),
  (Join-Path $projectRoot 'papers/npl-finite-fo/main.tex')
)

$names = [System.Collections.Generic.HashSet[string]]::new([System.StringComparer]::Ordinal)
foreach ($paper in $papers) {
  $text = Get-Content -LiteralPath $paper -Raw -Encoding utf8
  $blocks = [regex]::Matches(
    $text,
    '\[L:(.*?)\]',
    [System.Text.RegularExpressions.RegexOptions]::Singleline
  )
  foreach ($block in $blocks) {
    foreach ($match in [regex]::Matches($block.Groups[1].Value, '\\lean\{([^}]*)\}')) {
      $name = $match.Groups[1].Value.Replace('\_', '_').Replace('\lb', '')
      $name = [regex]::Replace($name, '\s+', '')
      [void]$names.Add($name)
    }
  }
}

if ($names.Count -eq 0) {
  throw 'No Lean references were extracted from manuscript [L] markers.'
}

$auditFile = Join-Path ([System.IO.Path]::GetTempPath()) `
  ("nullivance-manuscript-refs-{0}.lean" -f [guid]::NewGuid())
$source = [System.Collections.Generic.List[string]]::new()
$source.Add('import Nullivance')
$source.Add('namespace Nullivance')
$source.Add('open Syntax Semantics Continuous ProofTheory Metatheory Operational FiniteFO Generative')
foreach ($name in ($names | Sort-Object)) {
  $source.Add("#check $name")
}
$source.Add('end Nullivance')

try {
  [System.IO.File]::WriteAllLines(
    $auditFile,
    $source,
    [System.Text.UTF8Encoding]::new($false)
  )
  Push-Location $leanRoot
  try {
    $output = lake env lean $auditFile 2>&1
    if ($LASTEXITCODE -ne 0) {
      $output | Write-Host
      throw 'At least one manuscript [L] reference does not resolve in Lean.'
    }
  }
  finally {
    Pop-Location
  }
}
finally {
  if (Test-Path -LiteralPath $auditFile) {
    Remove-Item -LiteralPath $auditFile -Force
  }
}

Write-Host "Manuscript-Lean reference gate passed: $($names.Count) declarations resolved."
