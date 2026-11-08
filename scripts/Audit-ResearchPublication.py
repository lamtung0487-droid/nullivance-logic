"""Audit generated Lean dependency logs and inventory source trust boundaries."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'output' / 'publication-dr0149'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}

def read_log(path):
    raw = path.read_bytes()
    if raw.startswith(b'\xff\xfe'):
        return raw.decode('utf-16')
    return raw.decode('utf-8-sig')

def dependencies(text):
    items = {}
    for m in re.finditer(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text):
        items[m[1]] = [s.strip() for s in m[2].split(',') if s.strip()]
    for m in re.finditer(r"'([^']+)' does not depend on any axioms", text):
        items[m[1]] = []
    return items

def strip_lean_comments_strings(s):
    # Nested /- -/ comments, -- comments, and string literals. Preserve newlines.
    out, i, depth, quoted = [], 0, 0, False
    while i < len(s):
        pair = s[i:i+2]
        c = s[i]
        if depth:
            if pair == '/-': depth += 1; i += 2; continue
            if pair == '-/': depth -= 1; i += 2; continue
            out.append('\n' if c == '\n' else ' '); i += 1; continue
        if quoted:
            if c == '\\': out.extend('  '); i += 2; continue
            if c == '"': quoted = False
            out.append('\n' if c == '\n' else ' '); i += 1; continue
        if pair == '/-': depth = 1; out.extend('  '); i += 2; continue
        if pair == '--':
            j = s.find('\n', i)
            if j == -1: break
            out.append(' ' * (j-i)); i = j; continue
        if c == '"': quoted = True; out.append(' '); i += 1; continue
        out.append(c); i += 1
    if depth or quoted:
        raise ValueError('Unclosed comment/string in Lean source')
    return ''.join(out)

anchors = json.loads((ROOT / 'papers/npl-research-2026/anchors.json').read_text())
logs = {}
for kind in ['research-validation', 'recognition-validation', 'publication-validation', 'companion-validation']:
    body = read_log(OUT / f'{kind}.log')
    if re.search(r'\berror(?:\(|:)|sorryAx', body):
        raise SystemExit(f'Failed Lean log: {kind}')
    entries = dependencies(body)
    if not entries:
        raise SystemExit(f'No dependency audits: {kind}')
    logs[kind] = entries
publication = logs['publication-validation']
if set(publication) != set(anchors):
    raise SystemExit(f'Anchor coverage mismatch: {set(anchors)^set(publication)}')
for name, axioms in {**publication, **logs['companion-validation']}.items():
    if set(axioms) - STANDARD:
        raise SystemExit(f'Nonstandard publication dependency: {name}: {axioms}')

sources, native, holes = [], [], []
for p in sorted((ROOT / 'Nullivance').rglob('*.lean')):
    if '.lake' in p.parts: continue
    raw = p.read_bytes()
    stripped = strip_lean_comments_strings(raw.decode('utf-8-sig'))
    rel = p.relative_to(ROOT).as_posix()
    sources.append({'path': rel, 'sha256': hashlib.sha256(raw).hexdigest()})
    for m in re.finditer(r'\b(sorry|admit|axiom)\b', stripped):
        holes.append({'path': rel, 'line': stripped.count('\n', 0, m.start())+1, 'token': m[0]})
    for m in re.finditer(r'\b(native_decide|ofReduceBool)\b', stripped):
        native.append({'path': rel, 'line': stripped.count('\n', 0, m.start())+1, 'token': m[0]})
if holes:
    raise SystemExit(f'Proof holes/custom axioms: {holes}')
nonstandard = {kind: {n: ax for n, ax in entries.items() if set(ax)-STANDARD}
               for kind, entries in logs.items()}
extracted = {}
for kind, entries in logs.items():
    path = OUT / f'extracted-{kind}.log'
    if path.exists():
        body = read_log(path)
        if re.search(r'\berror(?:\(|:)|sorryAx', body) or dependencies(body) != entries:
            raise SystemExit(f'Extracted dependency audit mismatch: {kind}')
        extracted[kind] = len(entries)
result = {'snapshot': 'DR-0149', 'date': '2026-11-09',
          'baseline': '48bd5f4260fd7982176d7a2060be4e956e1fd49c',
          'counts': {k: len(v) for k,v in logs.items()},
          'standard_axioms_allowed_for_report': sorted(STANDARD),
          'dependency_audits': logs, 'nonstandard_audited_dependencies': nonstandard,
          'matching_extracted_audit_counts': extracted,
          'proof_holes_or_custom_axioms': holes, 'native_source_occurrences': native,
          'lean_sources': sources,
          'publication_inputs': [
              {'path': name, 'sha256': hashlib.sha256((ROOT/name).read_bytes()).hexdigest()}
              for name in ['papers/npl-research-2026/main.tex',
                           'papers/npl-research-2026/snapshot-references.bib',
                           'papers/npl-research-2026/catalog.json',
                           'papers/npl-research-2026/anchors.json']]}
(OUT / 'audit-inventory.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8', newline='\n')
print(json.dumps({'counts': result['counts'], 'lean_sources': len(sources),
                  'native_source_occurrences': len(native),
                  'nonstandard_audited_dependencies': {k:len(v) for k,v in nonstandard.items()}}, indent=2))
