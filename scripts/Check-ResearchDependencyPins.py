"""Check actual dependency commits and tracked cleanliness after Lake setup."""
from pathlib import Path
import json
import subprocess

root = Path(__file__).resolve().parents[1]
manifest = json.loads((root/'Nullivance/lake-manifest.json').read_text())
checks = []
for package in manifest['packages']:
    path = root/'Nullivance/.lake/packages'/package['name']
    def git(*args):
        return subprocess.run(['git','-C',str(path),*args], check=True,
                              text=True, capture_output=True).stdout.strip()
    actual = git('rev-parse','HEAD')
    dirty = git('status','--porcelain','--untracked-files=no')
    checks.append({'name':package['name'], 'expected':package['rev'], 'actual':actual,
                   'matches':actual==package['rev'], 'tracked_clean':not dirty})
out = root/'output/publication-dr0149'
out.mkdir(parents=True,exist_ok=True)
(out/'dependency-pins.json').write_text(json.dumps(checks,indent=2)+'\n',encoding='utf-8')
if not all(c['matches'] and c['tracked_clean'] for c in checks):
    raise SystemExit('Dependency revision/cleanliness mismatch; see dependency-pins.json')
print(f'All {len(checks)} dependency revisions match; tracked dependency files are clean.')
