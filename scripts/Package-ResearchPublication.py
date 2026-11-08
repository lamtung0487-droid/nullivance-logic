"""Package a scoped source snapshot without uploading or altering Git.

All output is new, under dist/. Existing artifact directories are never replaced.
The package deliberately omits .lake, .git, session logs and unrelated backups.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import shutil
import zipfile

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser()
parser.add_argument('--name', default='nullivance-research-DR0149-2026-11-08')
parser.add_argument('--stage-only', action='store_true')
args = parser.parse_args()
if not re.fullmatch(r'[a-zA-Z0-9_-]+', args.name):
    raise SystemExit('Artifact name must be a simple safe basename')
dest = ROOT / 'dist' / args.name
if dest.exists() or dest.with_suffix('.zip').exists():
    raise SystemExit('Artifact already exists; choose a new name, never overwrite it')

selected = set()
for p in (ROOT / 'Nullivance').rglob('*.lean'):
    if '.lake' not in p.parts:
        selected.add(p)
for name in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']:
    selected.add(ROOT / 'Nullivance' / name)
for name in ['LICENSE', 'CITATION.cff']:
    selected.add(ROOT / name)
for name in ['Prepare-ResearchPublication.py', 'Audit-ResearchPublication.py',
             'Verify-ResearchPublication.ps1', 'Package-ResearchPublication.py',
             'Check-ResearchManifest.py', 'Check-ResearchDependencyPins.py']:
    selected.add(ROOT / 'scripts' / name)
for folder in ['npl-core', 'npl-finite-fo', 'npl-research-2026']:
    for p in (ROOT / 'papers' / folder).iterdir():
        if p.is_file() and p.suffix in {'.tex', '.bib', '.pdf', '.json', '.md'}:
            selected.add(p)
selected.add(ROOT / 'references' / 'bibliography.bib')
for p in (ROOT / 'docs').glob('*.md'):
    if re.match(r'0[0-5]-', p.name) or p.name in {'WORKFLOW.md', 'DOC_LEAN_MATRIX.md', 'CLAIM_LEDGER.md'}:
        selected.add(p)
for i in range(1,150):
    records = list((ROOT / 'docs' / 'decisions').glob(f'DR-{i:04d}-*.md'))
    if len(records) != 1:
        raise SystemExit(f'Missing/ambiguous DR-{i:04d}')
    selected.add(records[0])

# Fail before writing a package if required inputs/evidence are absent.
for p in selected:
    if not p.is_file() or p.is_symlink():
        raise SystemExit(f'Invalid source input: {p.relative_to(ROOT)}')
logs = ROOT / 'output' / 'publication-dr0149'
audit = json.loads((logs / 'audit-inventory.json').read_text(encoding='utf-8'))
anchors = json.loads((ROOT / 'papers/npl-research-2026/anchors.json').read_text())
if set(audit['dependency_audits']['publication-validation']) != set(anchors):
    raise SystemExit('Stale publication audit')
for item in audit['lean_sources']:
    if hashlib.sha256((ROOT/item['path']).read_bytes()).hexdigest() != item['sha256']:
        raise SystemExit(f'Stale source audit: {item["path"]}')
for item in audit['publication_inputs']:
    if hashlib.sha256((ROOT/item['path']).read_bytes()).hexdigest() != item['sha256']:
        raise SystemExit(f'Stale manuscript input audit: {item["path"]}')
for kind in ['lake-build', 'research-validation', 'recognition-validation', 'publication-validation']:
    if not (logs/f'{kind}.log').is_file():
        raise SystemExit(f'Missing validation evidence: {kind}')

# A scoped heuristic, not a claim of complete secret detection.
secret = re.compile(rb'(?i)(-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----|github_pat_[A-Za-z0-9_]{20,}|gh[pousr]_[A-Za-z0-9]{30,}|sk-proj-[A-Za-z0-9_-]{30,})')
for p in selected:
    if p.suffix != '.pdf' and secret.search(p.read_bytes()):
        raise SystemExit(f'Potential credential in {p.relative_to(ROOT)}; do not package')
dest.mkdir(parents=True)
for p in sorted(selected):
    target = dest / p.relative_to(ROOT)
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(p, target)

readme = '''# Nullivance research snapshot through DR-0149

Author: Trinh Tung Lam. Contact: lamtung0481@gmail.com.
Snapshot date: 2026-11-08. Core mathematical baseline:
48bd5f4260fd7982176d7a2060be4e956e1fd49c.

Start with papers/npl-research-2026/main.pdf, its README.md, claim-review.md,
and TOM_TAT_VI.md. The earlier npl-core and npl-finite-fo papers are unchanged
historical companions, not updated versions of their archived DOI.

Reproduce from this root:
  python scripts/Check-ResearchManifest.py .
  pwsh -NoProfile -File scripts/Verify-ResearchPublication.ps1

Lean/mathlib are pinned to 4.32.1. Obtain dependencies without running lake
update; optionally use lake exe cache get inside Nullivance. Python 3.11+,
PowerShell 7, and LaTeX/pdflatex+bibtex prerequisites are listed in the paper README.
The supplied verification folder records actual checks and dependency audits.
It is not a formal certificate of prose equivalence or external peer review.

The design records are chronological scientific provenance. Their historical
next-step notes can be superseded by later records; consult the new synthesis
for current scope. CITATION.cff describes the old software release; SNAPSHOT.json
identifies this distinct research artifact. No new DOI or release tag is claimed.

This package contains no .git database, .lake dependency cache, private sessions,
credentials, or agent conversation logs. It is a reproducible research artifact,
not a backup of every local or historical file. A manifest authenticates bytes
relative to itself, not truth or a publisher's endorsement. No upload is authorized.
'''
(dest/'README.md').write_text(readme, encoding='utf-8')
(dest/'SNAPSHOT.json').write_text(json.dumps({
    'title': 'Nullivance Logic: Formal Semantics, Quantified Equality, and Certified Recognition',
    'author': 'Trinh Tung Lam', 'contact': 'lamtung0481@gmail.com',
    'date': '2026-11-08', 'through': 'DR-0149',
    'mathematical_baseline': '48bd5f4260fd7982176d7a2060be4e956e1fd49c',
    'lean': 'leanprover/lean4:v4.32.1',
    'mathlib': '520045ab14e26149ee970e2e617ca04b09bde5d6',
    'license': 'CC-BY-4.0', 'publication_status': 'local research consolidation; not submitted',
    'new_doi': None, 'manuscript_anchor_count': len(anchors),
    'scope': 'See manuscript hypotheses, claim-review.md, and exact Lean types.'
}, indent=2)+'\n', encoding='utf-8')
verification = dest/'verification'
verification.mkdir()
for p in sorted(logs.iterdir()):
    if p.suffix not in {'.log', '.json', '.md'}: continue
    raw = p.read_bytes()
    body = raw.decode('utf-16' if raw.startswith(b'\xff\xfe') else 'utf-8-sig')
    # Logs are scientific checking output; redact machine-local path prefixes.
    body = body.replace(str(ROOT), '<artifact-root>').replace(ROOT.as_posix(), '<artifact-root>')
    body = re.sub(r'C:[/\\]Users[/\\][^/\\\s]+', '<user-profile>', body)
    (verification/p.name).write_text(body, encoding='utf-8')

payload = sorted(p for p in dest.rglob('*') if p.is_file())
manifest = ''.join(f'{hashlib.sha256(p.read_bytes()).hexdigest()}  {p.relative_to(dest).as_posix()}\n' for p in payload)
(dest/'SOURCE_MANIFEST.sha256').write_text(manifest, encoding='utf-8')
if not args.stage_only:
    zip_path = dest.with_suffix('.zip')
    with zipfile.ZipFile(zip_path, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as z:
        for p in sorted(dest.rglob('*')):
            if not p.is_file(): continue
            info = zipfile.ZipInfo(args.name+'/'+p.relative_to(dest).as_posix(), (2026,11,8,0,0,0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            z.writestr(info, p.read_bytes(), compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)
    digest = hashlib.sha256(zip_path.read_bytes()).hexdigest()
    zip_path.with_suffix('.zip.sha256').write_text(f'{digest}  {zip_path.name}\n', encoding='ascii')
    print(f'ZIP {zip_path}\nSHA256 {digest}')
print(f'Staged {len(payload)} payload files at {dest}')
