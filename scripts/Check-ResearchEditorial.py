"""Check version labels and all three PDF reading surfaces, not mathematical prose."""
from pathlib import Path
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
release = json.loads((ROOT/'papers/research-release.json').read_text(encoding='utf-8'))
version = release['version']
cff = (ROOT/'CITATION.cff').read_text(encoding='utf-8')
if f'version: {version}\n' not in cff or release['concept_doi'] not in cff:
    raise SystemExit('Citation metadata differs from collection identity')
checks = []
for part in release['parts']:
    directory = ROOT/'papers'/part['folder']
    labels = (directory/'release.tex').read_text(encoding='utf-8')
    if ('\\newcommand{\\PublicationVersion}{'+version+'}') not in labels:
        raise SystemExit('Stale generated version: '+part['folder'])
    source = (directory/'main.tex').read_text(encoding='utf-8')
    if '\\input{release.tex}' not in source or '\\date{\\PublicationDate' not in source:
        raise SystemExit('Manuscript bypasses generated identity: '+part['folder'])
    text = subprocess.run(['pdftotext','-layout',str(directory/'main.pdf'),'-'],
                          check=True,capture_output=True).stdout.decode('utf-8')
    first = text.split('\f')[0]
    if version not in first or part['label'] not in re.sub(r'\s+',' ',first):
        raise SystemExit('PDF first-page identity missing: '+part['folder'])
    if 'August 2026 — release v0.7.1' in first or '??' in text:
        raise SystemExit('Old cover or unresolved reference: '+part['folder'])
    checks.append({'part':part['folder'],'version':version,'pdf_text_characters':len(text)})
print(json.dumps(checks,indent=2))
