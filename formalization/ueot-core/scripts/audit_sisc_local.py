#!/usr/bin/env python3
"""SISC local-only exact-head reproducibility gate. Never pushes or rewrites data."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[3]
CORE = ROOT / "formalization/ueot-core"
EVIDENCE = CORE / "docs/compression/theory_completion/scientific_closure/evidence"
RAW = EVIDENCE / "c7_sisc_sqlite_method_v1"
BASE = "f744194dabdbb8632e69b1d9cbc1f0e347877571"
BRANCH = "research/sisc-local-20261008"


def run(args, cwd=ROOT, output=False):
    result = subprocess.run(args, cwd=cwd, text=True, capture_output=True)
    if result.returncode != 0:
        print("FAILED:", " ".join(args), file=sys.stderr)
        print((result.stdout + result.stderr)[-6000:], file=sys.stderr)
        raise SystemExit(result.returncode)
    if output:
        print((result.stdout + result.stderr).strip()[-500:])
    return result.stdout


def main():
    assert run(["git", "branch", "--show-current"]).strip() == BRANCH
    assert run(["git", "rev-parse", "main"]).strip() == BASE
    assert run(["git", "merge-base", "main", "HEAD"]).strip() == BASE
    assert run(["git", "rev-parse", "origin/main"]).strip() == BASE
    assert not run(["git", "status", "--porcelain=v1", "-uno"]).strip(), "tracked edits present"
    assert not run(["git", "diff", "--check", "main...HEAD"]).strip()

    subjects = run(["git", "log", "--reverse", "--format=%s", "main..HEAD"]).splitlines()
    expected = ["sisc(si-0):", "sisc(si-1):", "sisc(si-2):", "sisc(si-3):",
                "sisc(si-4):", "sisc(c5):", "sisc(c6):", "sisc(c7-a):",
                "sisc(c7-b):", "sisc(local-gate):"]
    assert len(subjects) == len(expected), (subjects, expected)
    assert all(x.startswith(y) for x, y in zip(subjects, expected)), (subjects, expected)

    paths = run(["git", "diff", "--name-only", "main...HEAD"]).splitlines()
    allowed_root = "formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/ScientificClosure.lean"
    allowed_src = "formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/ScientificClosure/SISC"
    allowed_docs = "formalization/ueot-core/docs/compression/theory_completion/scientific_closure/"
    allowed_audit = "formalization/ueot-core/scripts/audit_sisc_local.py"
    assert paths
    assert all(p == allowed_root or p.startswith(allowed_src) or
               p.startswith(allowed_docs) or p == allowed_audit for p in paths), paths
    print("PASS: frozen main, ten local stage commits, additive paths, clean tracked state")

    print("VERIFY: exact-head lake build UEOT")
    build = run(["lake", "build", "UEOT"], cwd=CORE)
    assert "Build completed successfully" in build, build[-1500:]
    print("PASS:", [line for line in build.splitlines() if "Build completed" in line][-1])

    names = [
        "response_cannot_identify_sameObject_semantics",
        "certified_unique_successor_of_witness",
        "noisy_admissible_successor_unique",
        "finite_mechanism_derives_directed_coverage",
        "finite_mechanism_to_fbt_continuation",
        "finite_directed_history_with_bound",
        "reject_exact_common_twoD_from_same_jacobian",
        "resource_mechanism_alone_does_not_select_objective",
    ]
    ns = "UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC."
    with tempfile.TemporaryDirectory(prefix="sisc-axioms-") as scratch:
        source = Path(scratch) / "Audit.lean"
        source.write_text("import UEOT\n" + "".join(
            "#print axioms " + ns + name + "\n" for name in names))
        axioms = run(["lake", "env", "lean", str(source)], cwd=CORE)
        assert axioms.count("depends on axioms") + axioms.count("does not depend on any axioms") == len(names)
        assert "sorryAx" not in axioms and "unknown constant" not in axioms
        allowed = {"propext", "Classical.choice", "Quot.sound"}
        for bracket in re.findall(r"depends on axioms: \[([^]]*)\]", axioms):
            assert set(s.strip() for s in bracket.split(",")) <= allowed
    print("PASS: all selected axiom surfaces, standard Lean axioms only")

    manifest = json.loads((RAW / "manifest.json").read_text())
    assert hashlib.sha256((RAW / "events.jsonl").read_bytes()).hexdigest() == manifest["raw_sha256"]
    print("VERIFY: C7 frozen evidence and mutation regression")
    run([sys.executable, str(EVIDENCE / "sisc_c7_sqlite_verify.py"), str(RAW)], output=True)
    run([sys.executable, str(EVIDENCE / "sisc_c7_sqlite_negative_tests.py"), str(RAW)], output=True)
    run([sys.executable, str(EVIDENCE / "sisc_si3_finite_channel_benchmark.py")])

    print("VERIFY: three existing compression / finalization governance regressions")
    for script in ("test_validate_compression_research.py", "test_validate_compression.py",
                   "test_validate_finalization_receipt.py"):
        run([sys.executable, str(CORE / "scripts" / script)], output=True)

    print("LOCAL_GATE_PASS; NO_REMOTE_ACTION; SCIENTIFIC_C7_EXTERNAL_AND_INDEPENDENT_GATES_OPEN")


if __name__ == "__main__":
    main()
