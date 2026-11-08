[CmdletBinding()]
param([switch]$SkipLibraryBuild, [switch]$SkipPdf)
$ErrorActionPreference = 'Stop'
$runnerArgs = @(Join-Path $PSScriptRoot 'Verify-ResearchPublication.py')
if ($SkipLibraryBuild) { $runnerArgs += '--skip-library-build' }
if ($SkipPdf) { $runnerArgs += '--skip-pdf' }
& python @runnerArgs
if ($LASTEXITCODE -ne 0) { throw 'Publication verification failed; inspect output/publication-dr0149.' }
