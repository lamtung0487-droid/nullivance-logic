"""Adversarial regression tests for local evidence consistency (not Lean proofs)."""
from pathlib import Path
import copy
import importlib.util
import json
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
import ResearchPublicationEvidence as E

spec = importlib.util.spec_from_file_location('publication_runner', Path(__file__).with_name('Verify-ResearchPublication.py'))
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

class EvidenceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='nullivance-evidence-test-')
        self.root = Path(self.temp.name).resolve()
        self.logs = self.root / E.LOG_REL
        self.logs.mkdir(parents=True)
        self.inputs = []
        for name in ('source.lean', 'paper.pdf', 'tool.py', 'config.toml'):
            p = self.root / name
            p.write_bytes(b'fixture\n')
            self.inputs.append(p)
        (self.root / 'Nullivance').mkdir()
        p = self.root / 'Nullivance/lake-manifest.json'
        E.write_json(p, {'packages': [{'name': 'testdep', 'rev': 'abc'}]})
        self.inputs.append(p)
        self.inventory = patch.object(E, 'payload_sources', lambda root: list(self.inputs))
        self.inventory.start()
        for name in E.EVIDENCE:
            (self.logs / name).write_text('fixture\n', encoding='utf-8', newline='\n')
        (self.logs / 'lake-build.log').write_text('Build completed successfully (1 job).\n', newline='\n')
        E.write_json(self.logs / 'dependency-pins.json', [dict(name='testdep', actual='abc', matches=True, tracked_clean=True)])
        E.write_json(self.logs / 'audit-inventory.json', dict(proof_holes_or_custom_axioms=[], nonstandard_audited_dependencies={'test': {}}))
        self.receipt = dict(schema=E.SCHEMA, run_id='unit-test', status='passed', skipped=[],
                            commands=[dict(name=n, exit_code=0) for n in E.STEPS],
                            inputs=E.input_hashes(self.root), evidence=E.evidence_hashes(self.logs))
        self.save()

    def tearDown(self):
        self.inventory.stop()
        self.temp.cleanup()

    def save(self):
        E.write_json(self.logs / 'verification-receipt.json', self.receipt)

    def rejected(self):
        with self.assertRaises(E.EvidenceError):
            E.validate_receipt(self.root)

    def test_valid(self):
        self.assertEqual(E.validate_receipt(self.root), self.receipt)

    def test_missing_receipt(self):
        (self.logs / 'verification-receipt.json').unlink()
        self.rejected()

    def test_unfinished_or_failed(self):
        for status in ('running', 'failed', 'incomplete'):
            with self.subTest(status=status):
                self.receipt['status'] = status
                self.save()
                self.rejected()

    def test_failed_exit(self):
        self.receipt['commands'][2]['exit_code'] = 1
        self.save()
        self.rejected()

    def test_skipped_build_or_pdf(self):
        for name in ('lake-build', 'pdf-pass3'):
            self.receipt['skipped'] = [name]
            self.save()
            self.rejected()

    def test_missing_step(self):
        self.receipt['commands'].pop()
        self.save()
        self.rejected()

    def test_old_collection_schema_rejected(self):
        self.receipt['schema'] = 1
        self.save()
        self.rejected()

    def test_each_new_companion_gate_is_mandatory(self):
        original = copy.deepcopy(self.receipt['commands'])
        for name in ('companion-validation', 'core-pdf-pass3',
                     'finite-pdf-pass3', 'editorial-checks'):
            with self.subTest(step=name):
                self.receipt['commands'] = [s for s in original if s['name'] != name]
                self.save()
                self.rejected()

    def test_source_pdf_config_tool_changes(self):
        for p in self.inputs:
            with self.subTest(file=p.name):
                old = p.read_bytes()
                p.write_bytes(old + b'changed\n')
                self.rejected()
                p.write_bytes(old)

    def test_new_input(self):
        p = self.root / 'new.lean'
        p.write_bytes(b'new\n')
        self.inputs.append(p)
        self.rejected()

    def test_crlf_rejected(self):
        self.inputs[0].write_bytes(b'fixture\r\n')
        self.rejected()

    def test_missing_evidence(self):
        (self.logs / 'publication-validation.log').unlink()
        self.rejected()

    def test_failed_build_log_with_old_receipt(self):
        (self.logs / 'lake-build.log').write_text('error: synthetic failure\nBuild failed\n', newline='\n')
        self.rejected()

    def test_failed_build_even_if_log_hash_replaced(self):
        (self.logs / 'lake-build.log').write_text('Build failed\n', newline='\n')
        self.receipt['evidence'] = E.evidence_hashes(self.logs)
        self.save()
        self.rejected()

    def test_dirty_dependency(self):
        E.write_json(self.logs / 'dependency-pins.json', [dict(name='testdep', actual='abc', matches=True, tracked_clean=False)])
        self.receipt['evidence'] = E.evidence_hashes(self.logs)
        self.save()
        self.rejected()

    def test_unexpected_axiom(self):
        E.write_json(self.logs / 'audit-inventory.json', dict(proof_holes_or_custom_axioms=[], nonstandard_audited_dependencies={'test': {'bad': ['sorryAx']}}))
        self.receipt['evidence'] = E.evidence_hashes(self.logs)
        self.save()
        self.rejected()

    def test_runner_failure_invalidates_prior_success(self):
        with patch.object(runner.subprocess, 'run', return_value=subprocess.CompletedProcess([], 2, b'synthetic failure')):
            self.assertEqual(runner.run(self.root), 1)
        self.rejected()
        receipt = json.loads((self.logs / 'verification-receipt.json').read_text())
        self.assertEqual(receipt['status'], 'failed')
        self.assertEqual(receipt['commands'][0]['exit_code'], 2)

    def test_runner_missing_executable_invalidates_success(self):
        with patch.object(runner.subprocess, 'run', side_effect=FileNotFoundError('synthetic missing tool')):
            self.assertEqual(runner.run(self.root), 1)
        self.rejected()

    def test_runner_skipped_checks_cannot_create_success(self):
        with patch.object(runner.subprocess, 'run', return_value=subprocess.CompletedProcess([], 0, b'test')):
            self.assertEqual(runner.run(self.root, skip_library=True, skip_pdf=True), 0)
        self.rejected()
        self.assertEqual(json.loads((self.logs / 'verification-receipt.json').read_text())['status'], 'incomplete')

    def test_manifest_strict_and_generated_modes(self):
        fixture = self.root / 'manifest-fixture'
        fixture.mkdir()
        source = fixture / 'source.lean'
        source.write_bytes(b'fixture\n')
        manifest = fixture / 'SOURCE_MANIFEST.sha256'
        original = E.sha(source) + '  source.lean\n'
        manifest.write_text(original, newline='\n')
        checker = Path(__file__).with_name('Check-ResearchManifest.py')
        def check(ok, *flags):
            p = subprocess.run([sys.executable, str(checker), str(fixture), *flags], capture_output=True)
            self.assertEqual(p.returncode == 0, ok, p.stderr + p.stdout)
        check(True)
        extra = fixture / 'private-notes.log'
        extra.write_bytes(b'not a secret; synthetic extra file\n')
        check(False)
        check(False, '--allow-generated')
        extra.unlink()
        generated = fixture / 'output'
        generated.mkdir()
        (generated / 'test.log').write_bytes(b'generated\n')
        check(False)
        check(True, '--allow-generated')
        source.write_bytes(b'modified\n')
        check(False, '--allow-generated')
        source.write_bytes(b'fixture\n')
        for rel in ('../source.lean', 'C:/outside', 'x\\source.lean'):
            manifest.write_text(E.sha(source) + '  ' + rel + '\n', newline='\n')
            check(False, '--allow-generated')
        manifest.write_text(original + original, newline='\n')
        check(False, '--allow-generated')

if __name__ == '__main__':
    unittest.main(verbosity=2)
