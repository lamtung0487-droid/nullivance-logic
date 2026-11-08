[CmdletBinding()]
param([switch]$SkipLibraryBuild, [switch]$SkipPdf)
$ErrorActionPreference = 'Stop'
$projectRoot = Split-Path -Parent $PSScriptRoot
$logRoot = Join-Path $projectRoot 'output/publication-dr0149'
New-Item -ItemType Directory -Force -Path $logRoot | Out-Null
function Run-Logged([string]$Name, [string]$Program, [string[]]$Arguments) {
  Write-Host "Checking $Name"
  & $Program @Arguments *> (Join-Path $logRoot "$Name.log")
  if ($LASTEXITCODE -ne 0) { throw "$Name failed; see output/publication-dr0149/$Name.log" }
}
Push-Location $projectRoot
try {
  Run-Logged 'prepare' 'python' @('scripts/Prepare-ResearchPublication.py')
  Push-Location Nullivance
  try {
    Run-Logged 'lean-version' 'lake' @('env','lean','--version')
    if (-not $SkipLibraryBuild) { Run-Logged 'lake-build' 'lake' @('build') }
    Run-Logged 'research-validation' 'lake' @('env','lean','ResearchValidation.lean')
    Run-Logged 'recognition-validation' 'lake' @('env','lean','RecognitionValidation.lean')
    Run-Logged 'publication-validation' 'lake' @('env','lean','PublicationValidation.lean')
  } finally { Pop-Location }
  Run-Logged 'dependency-pins' 'python' @('scripts/Check-ResearchDependencyPins.py')
  Run-Logged 'audit-inventory' 'python' @('scripts/Audit-ResearchPublication.py')
  if (-not $SkipPdf) {
    $oldEpoch = $env:SOURCE_DATE_EPOCH
    $oldForce = $env:FORCE_SOURCE_DATE
    # 2026-11-08 00:00:00 UTC, the explicit research snapshot date.
    $env:SOURCE_DATE_EPOCH = '1794096000'
    $env:FORCE_SOURCE_DATE = '1'
    Push-Location papers/npl-research-2026
    try {
      Run-Logged 'pdf-pass1' 'pdflatex' @('-interaction=nonstopmode','-halt-on-error','-file-line-error','main.tex')
      Run-Logged 'bibliography' 'bibtex' @('main')
      Run-Logged 'pdf-pass2' 'pdflatex' @('-interaction=nonstopmode','-halt-on-error','-file-line-error','main.tex')
      Run-Logged 'pdf-pass3' 'pdflatex' @('-interaction=nonstopmode','-halt-on-error','-file-line-error','main.tex')
      $pdfLog = Get-Content main.log -Raw
      if ($pdfLog -match 'Overfull \\[hv]box|There were undefined|Citation .* undefined|Reference .* undefined') {
        throw 'PDF has overflow or unresolved references; inspect main.log.'
      }
    } finally {
      Pop-Location
      $env:SOURCE_DATE_EPOCH = $oldEpoch
      $env:FORCE_SOURCE_DATE = $oldForce
    }
  }
  Write-Host 'Research snapshot checks passed. No upload, push, or release performed.'
} finally { Pop-Location }
