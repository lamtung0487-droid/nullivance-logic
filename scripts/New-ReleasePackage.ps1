param(
  [string]$Version = '0.7.0',
  [string]$Tag
)

$ErrorActionPreference = 'Stop'
$projectRoot = Split-Path -Parent $PSScriptRoot
if (-not $Tag) { $Tag = "v$Version" }

Push-Location $projectRoot
try {
  $dirty = git status --porcelain
  if (-not [string]::IsNullOrWhiteSpace(($dirty -join "`n"))) {
    throw 'Release packaging requires a clean Git worktree.'
  }

  $head = (git rev-parse HEAD).Trim()
  if ($LASTEXITCODE -ne 0) { throw 'Cannot resolve HEAD.' }
  $tagCommit = (git rev-parse "$Tag^{commit}" 2>$null).Trim()
  if ($LASTEXITCODE -ne 0 -or [string]::IsNullOrWhiteSpace($tagCommit)) {
    throw "Tag '$Tag' does not exist."
  }
  if ($tagCommit -ne $head) {
    throw "Tag '$Tag' does not point to HEAD ($head)."
  }

  & (Join-Path $PSScriptRoot 'Verify-Release.ps1')
  if ($LASTEXITCODE -ne 0) { throw 'Release verification failed.' }

  $dirtyAfterVerification = git status --porcelain
  if (-not [string]::IsNullOrWhiteSpace(($dirtyAfterVerification -join "`n"))) {
    throw 'Release verification changed tracked files; rebuild and commit deterministic outputs before packaging.'
  }

  $dist = Join-Path $projectRoot 'dist'
  New-Item -ItemType Directory -Path $dist -Force | Out-Null
  $archive = Join-Path $dist "Nullivance-$Version.zip"
  $checksum = "$archive.sha256"

  git archive --format=zip --prefix="Nullivance-$Version/" --output=$archive $Tag
  if ($LASTEXITCODE -ne 0) { throw 'git archive failed.' }

  $hash = (Get-FileHash -LiteralPath $archive -Algorithm SHA256).Hash.ToLowerInvariant()
  [System.IO.File]::WriteAllText(
    $checksum,
    "$hash  $(Split-Path -Leaf $archive)`n",
    [System.Text.UTF8Encoding]::new($false)
  )

  & (Join-Path $PSScriptRoot 'Verify-Archive.ps1') `
    -ArchivePath $archive -ChecksumPath $checksum -Version $Version
  if ($LASTEXITCODE -ne 0) { throw 'Archive verification failed.' }

  Write-Host "Created $archive"
  Write-Host "SHA-256 $hash"
}
finally {
  Pop-Location
}
