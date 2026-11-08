"""Generate the DR catalog and Lean anchor audit; no network or repository mutation.

Only generated publication files are written. No source theorem is rewritten.
Run with Python 3.11+ from any directory.
"""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
PAPER = ROOT / 'papers' / 'npl-research-2026'

def tex(s):
    return ''.join({'&': r'\&', '%': r'\%', '$': r'\$', '#': r'\#',
                    '_': r'\_', '{': r'\{', '}': r'\}', '~': r'\textasciitilde{}',
                    '^': r'\textasciicircum{}', '\\': r'\textbackslash{}',
                    '—': '---', '–': '--', 'α': r'$\alpha$', 'Θ': r'$\Theta$',
                    '∀': r'$\forall$', '∃': r'$\exists$', '≤': r'$\le$',
                    '→': r'$\to$', '↔': r'$\leftrightarrow$'}.get(c, c) for c in s)

records = []
for i in range(1, 150):
    matches = sorted((ROOT / 'docs' / 'decisions').glob(f'DR-{i:04d}-*.md'))
    if len(matches) != 1:
        raise SystemExit(f'Expected exactly one DR-{i:04d}, got {matches}')
    p = matches[0]
    raw = p.read_bytes()
    body = raw.decode('utf-8-sig')
    heading = body.splitlines()[0].lstrip('# ').strip()
    title = re.sub(r'^DR-\d+\s*[—–:-]+\s*', '', heading)
    modules = sorted(set(re.findall(r'[A-Za-z][A-Za-z0-9_/]*\.lean', body)))
    resolved = []
    for m in modules:
        candidates = [ROOT / m, ROOT / 'Nullivance' / m,
                      ROOT / 'Nullivance' / 'Nullivance' / Path(m).name]
        found = next((q for q in candidates if q.is_file()), None)
        if found:
            resolved.append(found.relative_to(ROOT).as_posix())
    records.append({'id': f'DR-{i:04d}', 'title': title,
                    'path': p.relative_to(ROOT).as_posix(),
                    'sha256': hashlib.sha256(raw).hexdigest(),
                    'explicit_lean_paths': sorted(set(resolved))})

PAPER.mkdir(parents=True, exist_ok=True)
(PAPER / 'catalog.json').write_text(json.dumps(records, indent=2, ensure_ascii=False)+'\n', encoding='utf-8')
lines = [r'\small', r'\begin{longtable}{p{.14\linewidth}p{.79\linewidth}}',
         r'\toprule Record & Topic\\\midrule\endhead']
for r in records:
    lines.append(f"{r['id']} & {tex(r['title'])}\\\\")
lines += [r'\bottomrule', r'\end{longtable}', r'\normalsize']
(PAPER / 'catalog.tex').write_text('\n'.join(lines)+'\n', encoding='utf-8')

manuscript = (PAPER / 'main.tex').read_text(encoding='utf-8')
anchors = sorted(set(re.findall(r'\\leanref\{(Nullivance\.[A-Za-z0-9_.]+)\}', manuscript)))
if not anchors:
    raise SystemExit('No theorem anchors found')
audit = ['import Nullivance', '', '-- Generated from the publication manuscript.',
         '-- Types and transitive axiom dependencies, not merely name existence.',
         'set_option pp.universes false', '']
for a in anchors:
    audit += [f'#check {a}', f'#print axioms {a}', '']
(ROOT / 'Nullivance' / 'PublicationValidation.lean').write_text('\n'.join(audit), encoding='utf-8')
(PAPER / 'anchors.json').write_text(json.dumps(anchors, indent=2)+'\n', encoding='utf-8')
print(f'Generated {len(records)} records and {len(anchors)} Lean anchors.')
