"""Fail-closed local publication evidence; not adversarial cryptographic attestation."""
from pathlib import Path
import hashlib
import json
import os

SCHEMA = 2
LOG_REL = 'output/publication-dr0149'
STEPS = ('prepare', 'packaging-tests', 'lean-version', 'lake-build', 'research-validation',
         'recognition-validation', 'publication-validation', 'companion-validation', 'dependency-pins',
         'audit-inventory',
         'core-pdf-pass1', 'core-bibliography', 'core-pdf-pass2', 'core-pdf-pass3',
         'finite-pdf-pass1', 'finite-bibliography', 'finite-pdf-pass2', 'finite-pdf-pass3',
         'pdf-pass1', 'bibliography', 'pdf-pass2', 'pdf-pass3', 'editorial-checks')
EVIDENCE = tuple(x + '.log' for x in STEPS) + ('dependency-pins.json', 'audit-inventory.json')
SCRIPTS = ('Prepare-ResearchPublication.py', 'Audit-ResearchPublication.py',
           'Verify-ResearchPublication.ps1', 'Verify-ResearchPublication.py',
           'ResearchPublicationEvidence.py', 'Test-ResearchPublicationEvidence.py',
           'Package-ResearchPublication.py', 'Check-ResearchManifest.py',
           'Check-ResearchDependencyPins.py', 'Check-ResearchEditorial.py')

class EvidenceError(ValueError):
    pass

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def write_json(path, value):
    tmp = path.with_suffix(path.suffix + '.tmp')
    tmp.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n',
                   encoding='utf-8', newline='\n')
    tmp.replace(path)

def payload_sources(root):
    selected = set()
    for directory, dirs, files in os.walk(root / 'Nullivance'):
        dirs[:] = [d for d in dirs if d != '.lake']
        selected.update(Path(directory) / f for f in files if f.endswith('.lean'))
    for name in ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json'):
        selected.add(root / 'Nullivance' / name)
    for name in ('LICENSE', 'CITATION.cff', '.gitattributes'):
        selected.add(root / name)
    selected.update(root / 'scripts' / name for name in SCRIPTS)
    for folder in ('npl-core', 'npl-finite-fo', 'npl-research-2026'):
        selected.update(p for p in (root / 'papers' / folder).iterdir()
                        if p.is_file() and p.suffix in {'.tex', '.bib', '.pdf', '.json', '.md'})
    selected.add(root / 'references/bibliography.bib')
    selected.add(root / 'references/npl-positioning.md')
    selected.add(root / 'papers/research-release.json')
    selected.update(p for p in (root / 'docs').glob('*.md')
                    if p.name.startswith(tuple(f'0{i}-' for i in range(6)))
                    or p.name in {'WORKFLOW.md', 'DOC_LEAN_MATRIX.md', 'CLAIM_LEDGER.md'})
    for i in range(1, 150):
        matches = list((root / 'docs/decisions').glob(f'DR-{i:04d}-*.md'))
        if len(matches) != 1:
            raise EvidenceError(f'Missing/ambiguous DR-{i:04d}')
        selected.add(matches[0])
    for p in selected:
        if not p.is_file() or p.is_symlink() or not p.resolve().is_relative_to(root.resolve()):
            raise EvidenceError(f'Missing or unsafe source: {p}')
    return sorted(selected)

def input_hashes(root):
    result = {}
    for p in payload_sources(root):
        raw = p.read_bytes()
        if p.suffix != '.pdf':
            raw.decode('utf-8-sig')
            if b'\r' in raw:
                raise EvidenceError(f'Non-LF source: {p.relative_to(root)}')
        result[p.relative_to(root).as_posix()] = hashlib.sha256(raw).hexdigest()
    return result

def evidence_hashes(logs):
    return {name: sha(logs / name) for name in EVIDENCE}

def validate_receipt(root, inputs=None, evidence_dir=None):
    logs = root / LOG_REL if evidence_dir is None else evidence_dir
    try:
        receipt = json.loads((logs / 'verification-receipt.json').read_text(encoding='utf-8'))
        if receipt.get('schema') != SCHEMA or receipt.get('status') != 'passed':
            raise EvidenceError('A successful verification receipt is required')
        if receipt.get('skipped') != [] or not receipt.get('run_id'):
            raise EvidenceError('Skipped or unidentified verification run')
        steps = receipt.get('commands', [])
        if [s.get('name') for s in steps] != list(STEPS):
            raise EvidenceError('Incomplete/reordered verification commands')
        if any(type(s.get('exit_code')) is not int or s['exit_code'] != 0 for s in steps):
            raise EvidenceError('A required verification command failed')
        actual = input_hashes(root) if inputs is None else inputs
        if receipt.get('inputs') != actual:
            raise EvidenceError('Stale receipt: source, PDF, config or verification tooling changed')
        if receipt.get('evidence') != evidence_hashes(logs):
            raise EvidenceError('Stale or altered verification evidence')
        if 'Build completed successfully' not in (logs / 'lake-build.log').read_text(encoding='utf-8'):
            raise EvidenceError('Library build success marker is absent')
        pins = json.loads((logs / 'dependency-pins.json').read_text(encoding='utf-8'))
        expected = {p['name']: p['rev'] for p in json.loads(
            (root / 'Nullivance/lake-manifest.json').read_text())['packages']}
        if len(pins) != len(expected) or {p['name']: p['actual'] for p in pins} != expected:
            raise EvidenceError('Dependency evidence does not match the manifest')
        if not all(p['matches'] is True and p['tracked_clean'] is True for p in pins):
            raise EvidenceError('Dirty or mismatched dependency evidence')
        audit = json.loads((logs / 'audit-inventory.json').read_text(encoding='utf-8'))
        if audit['proof_holes_or_custom_axioms'] or any(audit['nonstandard_audited_dependencies'].values()):
            raise EvidenceError('Unaccepted axiom or proof-hole audit')
        return receipt
    except (OSError, KeyError, TypeError, json.JSONDecodeError) as exc:
        raise EvidenceError(f'Missing or malformed verification evidence: {exc}') from exc
