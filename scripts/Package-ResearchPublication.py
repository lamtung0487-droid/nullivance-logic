"""Package only receipt-bound inputs; never upload, overwrite a release, or alter Git."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import shutil
import zipfile
from ResearchPublicationEvidence import payload_sources, validate_receipt, EVIDENCE

ROOT = Path(__file__).resolve().parents[1]
release = json.loads((ROOT/'papers/research-release.json').read_text(encoding='utf-8'))
parser = argparse.ArgumentParser()
parser.add_argument('--name',default='nullivance-research-'+release['version'])
parser.add_argument('--stage-only',action='store_true')
args = parser.parse_args()
if not re.fullmatch(r'[a-zA-Z0-9_-]+',args.name):
    raise SystemExit('Artifact name must be a simple safe basename')
dest = ROOT/'dist'/args.name
if dest.exists() or dest.with_suffix('.zip').exists():
    raise SystemExit('Artifact already exists; choose a new name, never overwrite it')
receipt = validate_receipt(ROOT)
selected = payload_sources(ROOT)
logs = ROOT/'output/publication-dr0149'
audit = json.loads((logs/'audit-inventory.json').read_text(encoding='utf-8'))
anchors = json.loads((ROOT/'papers/npl-research-2026/anchors.json').read_text())
if set(audit['dependency_audits']['publication-validation']) != set(anchors):
    raise SystemExit('Stale publication audit')
for item in audit['lean_sources']+audit['publication_inputs']:
    if hashlib.sha256((ROOT/item['path']).read_bytes()).hexdigest()!=item['sha256']:
        raise SystemExit('Stale source audit: '+item['path'])
secret = re.compile(rb'(?i)(-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----|github_pat_[A-Za-z0-9_]{20,}|gh[pousr]_[A-Za-z0-9]{30,}|sk-proj-[A-Za-z0-9_-]{30,})')
for p in selected:
    if not p.is_file() or p.is_symlink():
        raise SystemExit('Invalid input: '+str(p.relative_to(ROOT)))
    if p.suffix!='.pdf' and secret.search(p.read_bytes()):
        raise SystemExit('Potential credential: '+str(p.relative_to(ROOT)))
dest.mkdir(parents=True)
for p in selected:
    target=dest/p.relative_to(ROOT)
    target.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(p,target)
readme = ('# '+release['title']+'\n\nCollection '+release['version']+'; '+release['display_date']+'.\n\n'
    'Author: Trinh Tung Lam. Contact: lamtung0481@gmail.com.\n\n'
    'Read papers/npl-research-2026/main.pdf first (Part I). Part II is\n'
    'papers/npl-core/main.pdf; Part III is papers/npl-finite-fo/main.pdf.\n'
    'All three are current collection editions, not unchanged v0.7.1 PDFs.\n'
    'See papers/npl-research-2026/VERSION_HISTORY.md and TOM_TAT_VI.md.\n\n'
    'Verify before executing: python scripts/Check-ResearchManifest.py .\n'
    'Reproduce: python scripts/Verify-ResearchPublication.py\n\n'
    'The paper README specifies prerequisites and scope. Evidence is in\n'
    'verification/verification-receipt.json and its bound logs. The dependency\n'
    'cache is not included. No git database, credentials, private chats, or\n'
    'local backups are included. Hashes establish relative byte consistency,\n'
    'not external peer review, empirical truth, or adversarial authenticity.\n\n'
    'The concept DOI identifies the version family; select '+release['version']+'\n'
    'on https://doi.org/'+release['concept_doi']+' for the matching record.\n')
(dest/'README.md').write_text(readme,encoding='utf-8',newline='\n')
snapshot=dict(release,author='Trinh Tung Lam',contact='lamtung0481@gmail.com',
              lean='leanprover/lean4:v4.32.1',mathlib='520045ab14e26149ee970e2e617ca04b09bde5d6',
              license='CC-BY-4.0',artifact_revision=release['version'],
              manuscript_anchor_count=len(anchors),
              scope='Mathematical results under the manuscript hypotheses; no empirical cognition claim.')
(dest/'SNAPSHOT.json').write_text(json.dumps(snapshot,indent=2)+'\n',encoding='utf-8',newline='\n')
verification=dest/'verification'
verification.mkdir()
for name in (*EVIDENCE,'verification-receipt.json'):
    shutil.copyfile(logs/name,verification/name)
validate_receipt(dest,evidence_dir=verification)
if validate_receipt(ROOT)!=receipt:
    raise SystemExit('Verification run changed during packaging')
payload=sorted(p for p in dest.rglob('*') if p.is_file())
manifest=''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.relative_to(dest).as_posix()+'\n' for p in payload)
(dest/'SOURCE_MANIFEST.sha256').write_text(manifest,encoding='utf-8',newline='\n')
if not args.stage_only:
    zip_path=dest.with_suffix('.zip')
    with zipfile.ZipFile(zip_path,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
        for p in sorted(dest.rglob('*')):
            if not p.is_file(): continue
            info=zipfile.ZipInfo(args.name+'/'+p.relative_to(dest).as_posix(),(2026,11,9,0,0,0))
            info.compress_type=zipfile.ZIP_DEFLATED
            info.external_attr=0o100644<<16
            z.writestr(info,p.read_bytes(),compress_type=zipfile.ZIP_DEFLATED,compresslevel=9)
    digest=hashlib.sha256(zip_path.read_bytes()).hexdigest()
    zip_path.with_suffix('.zip.sha256').write_text(digest+'  '+zip_path.name+'\n',encoding='ascii',newline='\n')
    print(f'ZIP {zip_path}\nSHA256 {digest}')
print(f'Staged {len(payload)} payload files at {dest}')
