"""Verify a research payload manifest without executing the payload."""
from pathlib import Path, PurePosixPath
import hashlib
import sys

root = Path(sys.argv[1] if len(sys.argv)>1 else '.').resolve()
manifest = root/'SOURCE_MANIFEST.sha256'
seen = set()
for line in manifest.read_text(encoding='utf-8').splitlines():
    digest, rel = line.split('  ', 1)
    path = PurePosixPath(rel)
    if path.is_absolute() or '..' in path.parts or rel in seen:
        raise SystemExit('Unsafe or duplicate manifest path')
    p = root.joinpath(*path.parts)
    if not p.is_file() or p.is_symlink() or not p.resolve().is_relative_to(root):
        raise SystemExit(f'Missing or unsafe payload: {rel}')
    if hashlib.sha256(p.read_bytes()).hexdigest() != digest:
        raise SystemExit(f'Hash mismatch: {rel}')
    seen.add(rel)
# Ignore later generated build output; flag unexpected initial files elsewhere.
extras = []
for p in root.rglob('*'):
    if not p.is_file(): continue
    rel = p.relative_to(root)
    if '.lake' in rel.parts or rel.parts[0] == 'output': continue
    if rel.as_posix() == 'SOURCE_MANIFEST.sha256': continue
    if rel.as_posix() not in seen and p.suffix not in {'.aux','.log','.out','.toc','.bbl','.blg'}:
        extras.append(rel.as_posix())
if extras:
    raise SystemExit(f'Unexpected payload files: {extras}')
print(f'Verified {len(seen)} payload hashes.')
