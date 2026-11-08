"""Strict manifest verification before execution; explicit post-build allowances."""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import os
import re

parser = argparse.ArgumentParser()
parser.add_argument('root', nargs='?', default='.')
parser.add_argument('--allow-generated', action='store_true')
args = parser.parse_args()
root = Path(args.root).resolve()
manifest = root / 'SOURCE_MANIFEST.sha256'
seen, folded = set(), set()
for line in manifest.read_text(encoding='utf-8').splitlines():
    digest, rel = line.split('  ', 1)
    path = PurePosixPath(rel)
    if (not re.fullmatch('[0-9a-f]{64}', digest) or path.is_absolute()
        or '..' in path.parts or '\\' in rel or ':' in rel
        or path.as_posix() != rel or rel.casefold() in folded):
        raise SystemExit('Unsafe, malformed or duplicate manifest path')
    p = root.joinpath(*path.parts)
    if not p.is_file() or p.is_symlink() or not p.resolve().is_relative_to(root):
        raise SystemExit(f'Missing or unsafe payload: {rel}')
    if hashlib.sha256(p.read_bytes()).hexdigest() != digest:
        raise SystemExit(f'Hash mismatch: {rel}')
    seen.add(rel)
    folded.add(rel.casefold())

def generated(rel):
    parts = rel.parts
    return (parts[0] == 'output'
        or parts[:2] == ('Nullivance', '.lake')
        or parts[:2] == ('scripts', '__pycache__')
        or (len(parts) == 3 and parts[0] == 'papers'
            and parts[1] in {'npl-core', 'npl-finite-fo', 'npl-research-2026'}
            and rel.stem == 'main' and rel.suffix in {'.aux','.log','.out','.toc','.bbl','.blg'}))

extras = []
for directory, dirs, files in os.walk(root, followlinks=False):
    if args.allow_generated:
        dirs[:] = [d for d in dirs if not generated((Path(directory) / d).relative_to(root))]
    for name in files:
        p = Path(directory) / name
        rel = p.relative_to(root)
        if rel.as_posix() in seen or rel.as_posix() == 'SOURCE_MANIFEST.sha256':
            continue
        if args.allow_generated and generated(rel):
            continue
        extras.append(rel.as_posix())
if extras:
    raise SystemExit(f'Unexpected payload files: {extras}')
print(f'Verified {len(seen)} payload hashes; mode: ' +
      ('post-build' if args.allow_generated else 'strict'))
