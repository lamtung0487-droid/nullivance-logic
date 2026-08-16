param(
  [Parameter(Mandatory)] [string]$ArchivePath,
  [Parameter(Mandatory)] [string]$ChecksumPath,
  [string]$Version = '0.7.1'
)

$ErrorActionPreference = 'Stop'

$archive = (Resolve-Path -LiteralPath $ArchivePath).Path
$checksum = (Resolve-Path -LiteralPath $ChecksumPath).Path
$archiveName = Split-Path -Leaf $archive

$sidecar = (Get-Content -LiteralPath $checksum -Raw -Encoding utf8).Trim()
if ($sidecar -notmatch '^([0-9a-fA-F]{64})  (\S+)$') {
  throw 'Malformed SHA-256 sidecar.'
}
if ($Matches[2] -ne $archiveName) {
  throw "Checksum filename '$($Matches[2])' does not match '$archiveName'."
}

$expectedHash = $Matches[1].ToLowerInvariant()
$actualHash = (Get-FileHash -LiteralPath $archive -Algorithm SHA256).Hash.ToLowerInvariant()
if ($actualHash -ne $expectedHash) {
  throw "SHA-256 mismatch: expected $expectedHash, found $actualHash."
}

Add-Type -AssemblyName System.IO.Compression.FileSystem
$zip = [System.IO.Compression.ZipFile]::OpenRead($archive)
try {
  $prefix = "Nullivance-$Version/"
  $entries = @($zip.Entries | ForEach-Object FullName)
  $required = @(
    'README.md', 'LICENSE', 'CITATION.cff', '.zenodo.json', 'ARTIFACT.md',
    'RELEASE_CHECKLIST.md', 'CHANGELOG.md', 'docs/CLAIM_LEDGER.md',
    'docs/DOC_LEAN_MATRIX.md', 'Nullivance/lean-toolchain',
    'Nullivance/lakefile.toml', 'Nullivance/lake-manifest.json',
    'papers/npl-core/main.tex', 'papers/npl-core/main.pdf',
    'papers/npl-finite-fo/main.tex', 'papers/npl-finite-fo/main.pdf',
    'scripts/Verify-Release.ps1'
  )
  foreach ($relative in $required) {
    if ($entries -notcontains "$prefix$relative") {
      throw "Archive is missing required entry: $relative"
    }
  }

  $allowedFilePatterns = @(
    '^(\.gitattributes|\.gitignore|\.zenodo\.json|ARTIFACT\.md|CHANGELOG\.md|CITATION\.cff|LICENSE|README\.md|RELEASE_CHECKLIST\.md)$',
    '^\.github/workflows/[^/]+\.yml$',
    '^Nullivance/(\.gitignore|README\.md|lean-toolchain|lakefile\.toml|lake-manifest\.json|Nullivance\.lean|Nullivance/[^/]+\.lean)$',
    '^Nullivance/\.github/workflows/[^/]+\.yml$',
    '^docs/(00-motivation\.md|0[1-5]-[^/]+\.md|GLOSSARY\.md|WORKFLOW\.md|CLAIM_LEDGER\.md|DOC_LEAN_MATRIX\.md|decisions/DR-[0-9]{4}-[^/]+\.md)$',
    '^papers/(npl-core|npl-finite-fo)/(README\.md|main\.tex|main\.pdf)$',
    '^references/(bibliography\.bib|npl-positioning\.md)$',
    '^scripts/[^/]+\.ps1$'
  )
  foreach ($entry in $entries) {
    if (-not $entry.StartsWith($prefix, [System.StringComparison]::Ordinal)) {
      throw "Archive entry is outside the release prefix: $entry"
    }
    $relative = $entry.Substring($prefix.Length)
    if ([string]::IsNullOrWhiteSpace($relative) -or $relative.EndsWith('/')) {
      continue
    }
    $allowed = $false
    foreach ($pattern in $allowedFilePatterns) {
      if ($relative -match $pattern) { $allowed = $true; break }
    }
    if (-not $allowed) {
      throw "Unexpected file found in archive: $relative"
    }
  }
}
finally {
  $zip.Dispose()
}

Write-Host "Archive verified: $archiveName"
Write-Host "SHA-256 $actualHash"
