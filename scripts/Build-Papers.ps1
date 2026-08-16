param(
  [string[]]$Paper = @('npl-core', 'npl-finite-fo'),
  [string]$ReleaseEpoch = '1786838400'
)

$ErrorActionPreference = 'Stop'
$projectRoot = Split-Path -Parent $PSScriptRoot

foreach ($command in @('pdflatex', 'bibtex')) {
  if (-not (Get-Command $command -ErrorAction SilentlyContinue)) {
    throw "Required command '$command' is not available on PATH."
  }
}

function Invoke-Checked {
  param(
    [Parameter(Mandatory)] [string]$Command,
    [Parameter(Mandatory)] [string[]]$Arguments
  )

  & $Command @Arguments
  if ($LASTEXITCODE -ne 0) {
    throw "Command failed ($LASTEXITCODE): $Command $($Arguments -join ' ')"
  }
}

$previousSourceDateEpoch = [Environment]::GetEnvironmentVariable('SOURCE_DATE_EPOCH', 'Process')
$previousForceSourceDate = [Environment]::GetEnvironmentVariable('FORCE_SOURCE_DATE', 'Process')
[Environment]::SetEnvironmentVariable('SOURCE_DATE_EPOCH', $ReleaseEpoch, 'Process')
[Environment]::SetEnvironmentVariable('FORCE_SOURCE_DATE', '1', 'Process')

try {
foreach ($name in $Paper) {
  $paperDir = Join-Path $projectRoot "papers/$name"
  $source = Join-Path $paperDir 'main.tex'
  if (-not (Test-Path -LiteralPath $source -PathType Leaf)) {
    throw "Missing manuscript source: $source"
  }

  Write-Host "Building $name"
  Push-Location $paperDir
  try {
    $latexArgs = @('-interaction=nonstopmode', '-halt-on-error', '-file-line-error', 'main.tex')
    Invoke-Checked pdflatex $latexArgs
    Invoke-Checked bibtex @('main')
    Invoke-Checked pdflatex $latexArgs
    Invoke-Checked pdflatex $latexArgs

    if (-not (Test-Path -LiteralPath 'main.pdf' -PathType Leaf)) {
      throw "PDF was not produced for $name."
    }

    $log = Get-Content -LiteralPath 'main.log' -Raw -Encoding utf8
    $fatalDiagnostics = @(
      'There were undefined references',
      'There were undefined citations',
      'Citation .* undefined',
      'Reference .* undefined',
      'Overfull \\hbox',
      'Overfull \\vbox'
    )
    foreach ($pattern in $fatalDiagnostics) {
      if ($log -match $pattern) {
        throw "LaTeX quality gate failed for ${name}: pattern '$pattern'."
      }
    }
  }
  finally {
    Pop-Location
  }
}

Write-Host 'Both manuscript PDFs passed the reproducible build gate.'
}
finally {
  [Environment]::SetEnvironmentVariable('SOURCE_DATE_EPOCH', $previousSourceDateEpoch, 'Process')
  [Environment]::SetEnvironmentVariable('FORCE_SOURCE_DATE', $previousForceSourceDate, 'Process')
}
