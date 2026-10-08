#!/usr/bin/env python3
"""Adversarial regression for frozen v1 evidence manifest integrity."""
import importlib.util
from pathlib import Path
import shutil
import tempfile

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location('archived_integrity', HERE/'audit_archived_v1_integrity.py')
assert SPEC.loader is not None
mod = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(mod)


def main():
    names = [
        'EVIDENCE_MANIFEST_v1.sha256', 'worker.py',
        'run_pilot_v1.py', 'verify_evidence_v1.py',
        'raw_certification_v1.jsonl', 'summary_certification_v1.json',
        'recomputed_certification_v1.json', 'raw_reproduction_v1.jsonl',
        'summary_reproduction_v1.json', 'recomputed_reproduction_v1.json',
        'reproduction_comparison.json',
    ]
    with tempfile.TemporaryDirectory() as tmp:
        dst = Path(tmp)
        for name in names:
            shutil.copy2(HERE / name, dst / name)
        manifest = dst / 'EVIDENCE_MANIFEST_v1.sha256'
        frozen = manifest.read_text()
        assert mod.verify(dst)['all_checks_pass']
        assert mod.verify(dst)['manifest_entries'] == 10

        file = dst / 'raw_certification_v1.jsonl'
        original = file.read_bytes()
        file.write_bytes(original + b'\n')
        assert not mod.verify(dst)['all_checks_pass'], 'raw tampering passed'
        file.write_bytes(original)

        for mode in ('remove_summary', 'remove_comparison', 'duplicate', 'append_extra'):
            lines = frozen.splitlines()
            if mode == 'remove_summary':
                lines = [s for s in lines if not s.endswith('  summary_certification_v1.json')]
            elif mode == 'remove_comparison':
                lines = [s for s in lines if not s.endswith('  reproduction_comparison.json')]
            elif mode == 'duplicate':
                lines.append(lines[0])
            else:
                lines.append('0' * 64 + '  unregistered.json')
            manifest.write_text('\n'.join(lines) + '\n')
            result = mod.verify(dst)
            assert not result['all_checks_pass'], (mode, result)
            assert any('manifest' in x for x in result['problems']), (mode, result)
            manifest.write_text(frozen)

    print('archived v1 full-10 integrity regressions: PASS')


if __name__ == '__main__':
    main()
