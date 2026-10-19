"""Run independent kernel tests and write a reproducible source-bound receipt."""

import argparse
from datetime import datetime, timezone
from hashlib import sha256
import json
from pathlib import Path
import platform
import sys
import unittest


ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))


class RecordingResult(unittest.TextTestResult):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.passed_ids = []

    def addSuccess(self, test):
        super().addSuccess(test)
        self.passed_ids.append(test.id())


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=ROOT / "evidence/runtime-verification.json")
    args = parser.parse_args()
    suite = unittest.defaultTestLoader.discover(str(ROOT / "tests"))
    result = unittest.TextTestRunner(verbosity=2, resultclass=RecordingResult).run(suite)
    files = sorted(ROOT.rglob("*.py"))
    receipt = {
        "schema": "ueot_qm.runtime_verification.v1",
        "created_at_utc": datetime.now(timezone.utc).isoformat(),
        "python": platform.python_version(),
        "status": "PASS" if result.wasSuccessful() else "FAIL",
        "test_methods_run": result.testsRun,
        "passed": result.passed_ids,
        "failures": [{"test": t.id(), "traceback": error} for t, error in result.failures],
        "errors": [{"test": t.id(), "traceback": error} for t, error in result.errors],
        "skipped": [{"test": t.id(), "reason": reason} for t, reason in result.skipped],
        "sources": [{"path": p.relative_to(ROOT).as_posix(),
                     "sha256": sha256(p.read_bytes()).hexdigest()} for p in files],
        "limits": [
            "Exact executable calculations on Gaussian rational inputs, Hilbert dimensions 1..4",
            "Test methods contain multiple examples; this count is not a theorem count",
            "This receipt does not state that Python execution was verified by Lean",
            "Finite protocol and scalar trace certificates retain their declared coverage",
        ],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(receipt, indent=2, ensure_ascii=False) + "\n")
    return 0 if result.wasSuccessful() else 1


if __name__ == "__main__":
    raise SystemExit(main())
