"""Run the full three-paper verification gate; invalidate success before work."""
from pathlib import Path
import argparse
from datetime import datetime, timezone
import os
import re
import subprocess
import sys
import uuid
from ResearchPublicationEvidence import (SCHEMA, LOG_REL, STEPS, input_hashes,
    evidence_hashes, write_json, validate_receipt, EvidenceError)

ROOT = Path(__file__).resolve().parents[1]

def run(root, skip_library=False, skip_pdf=False):
    logs = root / LOG_REL
    logs.mkdir(parents=True, exist_ok=True)
    receipt_path = logs / 'verification-receipt.json'
    skipped = (['lake-build'] if skip_library else [])
    if skip_pdf:
        skipped += [n for n in STEPS if 'pdf-pass' in n or 'bibliography' in n or n=='editorial-checks']
    receipt = dict(schema=SCHEMA, run_id=str(uuid.uuid4()), status='running',
                   started_utc=datetime.now(timezone.utc).isoformat(),
                   commands=[], skipped=skipped)
    write_json(receipt_path, receipt)
    env = dict(os.environ, SOURCE_DATE_EPOCH='1794182400', FORCE_SOURCE_DATE='1')

    def command(name, args, cwd):
        print(f'Checking {name}', flush=True)
        completed = subprocess.run(args, cwd=cwd, env=env, stdout=subprocess.PIPE,
                                   stderr=subprocess.STDOUT)
        body = completed.stdout.decode('utf-8', errors='replace').replace('\r\n', '\n')
        body = body.replace(str(root), '<artifact-root>').replace(root.as_posix(), '<artifact-root>')
        body = re.sub(r'[A-Za-z]:[/\\]Users[/\\][^/\\\s]+', '<user-profile>', body)
        (logs / (name + '.log')).write_text(body, encoding='utf-8', newline='\n')
        receipt['commands'].append(dict(name=name, exit_code=completed.returncode))
        write_json(receipt_path, receipt)
        if completed.returncode:
            raise EvidenceError(f'{name} exited {completed.returncode}; inspect {name}.log')

    def build_pdf(folder, prefix):
        paper = root / 'papers' / folder
        args = ['pdflatex', '-interaction=nonstopmode', '-halt-on-error', '-file-line-error', 'main.tex']
        command(prefix+'pdf-pass1', args, paper)
        command(prefix+'bibliography', ['bibtex', 'main'], paper)
        command(prefix+'pdf-pass2', args, paper)
        command(prefix+'pdf-pass3', args, paper)
        body = (paper / 'main.log').read_text(errors='replace')
        if re.search(r'Overfull \\[hv]box|Missing character:|There were undefined|Citation .* undefined|Reference .* undefined', body):
            raise EvidenceError(f'{folder}: layout, glyph or reference errors')
        if not (paper / 'main.pdf').is_file():
            raise EvidenceError(f'{folder}: missing PDF')

    try:
        command('prepare', [sys.executable, 'scripts/Prepare-ResearchPublication.py'], root)
        before = {k:v for k,v in input_hashes(root).items() if not k.endswith('.pdf')}
        command('packaging-tests', [sys.executable, 'scripts/Test-ResearchPublicationEvidence.py'], root)
        lean = root / 'Nullivance'
        command('lean-version', ['lake', 'env', 'lean', '--version'], lean)
        if not skip_library:
            command('lake-build', ['lake', 'build'], lean)
        for name, file in [('research-validation','ResearchValidation.lean'),
                           ('recognition-validation','RecognitionValidation.lean'),
                           ('publication-validation','PublicationValidation.lean'),
                           ('companion-validation','CompanionValidation.lean')]:
            command(name, ['lake','env','lean',file], lean)
        command('dependency-pins', [sys.executable,'scripts/Check-ResearchDependencyPins.py'], root)
        command('audit-inventory', [sys.executable,'scripts/Audit-ResearchPublication.py'], root)
        if not skip_pdf:
            for folder, prefix in [('npl-core','core-'), ('npl-finite-fo','finite-'), ('npl-research-2026','')]:
                build_pdf(folder,prefix)
            command('editorial-checks', [sys.executable,'scripts/Check-ResearchEditorial.py'], root)
        current = input_hashes(root)
        if {k:v for k,v in current.items() if not k.endswith('.pdf')} != before:
            raise EvidenceError('Inputs changed during verification; run again')
        receipt.update(status='incomplete' if skipped else 'passed', inputs=current,
                       finished_utc=datetime.now(timezone.utc).isoformat())
        if not skipped:
            receipt['evidence'] = evidence_hashes(logs)
        write_json(receipt_path,receipt)
        if not skipped:
            validate_receipt(root)
        print('Checks completed. ' + ('Diagnostic only; packaging blocked.' if skipped else
              'Complete verification receipt written. No upload or push performed.'))
        return 0
    except BaseException as exc:
        receipt.update(status='failed',failure=str(exc),finished_utc=datetime.now(timezone.utc).isoformat())
        write_json(receipt_path,receipt)
        print(f'Verification failed: {exc}',file=sys.stderr)
        return 1

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--skip-library-build',action='store_true')
    parser.add_argument('--skip-pdf',action='store_true')
    args = parser.parse_args()
    sys.exit(run(ROOT,args.skip_library_build,args.skip_pdf))
