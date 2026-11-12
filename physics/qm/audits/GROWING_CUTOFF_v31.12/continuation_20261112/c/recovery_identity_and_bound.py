#!/usr/bin/env python3
"""Independent recovery review: identity, history and rational bound only.

This does not rerun historical Lean or numerical suites and does not certify
hardware membership. It imports neither the production model nor its checker.
"""
from pathlib import Path
from fractions import Fraction as F
from math import isqrt
from datetime import datetime, timezone
import argparse
import hashlib
import json


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    repo = args.repo.resolve()
    checked = []
    errors = []

    def read(rel):
        return json.loads((repo / rel).read_text())

    def verify_entries(label, entries):
        paths = []
        for item in entries:
            p = repo / item["path"]
            if not p.is_file() or sha(p) != item["sha256"]:
                errors.append(label + ": " + item["path"])
            elif "bytes" in item and p.stat().st_size != item["bytes"]:
                errors.append(label + " size: " + item["path"])
            paths.append(item["path"])
        checked.append({"scope": label, "count": len(entries), "paths": paths})

    proof = read("physics/qm/kernel/evidence/v31.11/source-manifest.json")
    oldrun = read("physics/qm/kernel/evidence/v31.11/runtime/execution_receipt.json")
    newrun = read("physics/qm/kernel/evidence/v31.12/runtime/execution_receipt.json")
    book = read("physics/qm/book/evidence/v3.9/increment-verification.json")
    verify_entries("inherited_proof_config", proof["sources"])
    verify_entries("inherited_runtime_inputs", oldrun["inputs"])
    verify_entries("new_runtime_inputs", newrun["inputs"])
    verify_entries("new_runtime_outputs", newrun["outputs"])
    verify_entries("new_runtime_logs", [c["log"] for c in newrun["commands"]])
    verify_entries("publication_consumed", [
        {"path": p, "sha256": s} for p, s in book["consumed_sha256"].items()
    ])
    verify_entries("paper_and_release_inputs", read(
        "physics/qm/kernel/evidence/v31.12/source-manifest.json")["paper_and_release_inputs"])
    assert len(proof["sources"]) == 158 and len(oldrun["inputs"]) == 13
    assert len(newrun["inputs"]) == 12 and len(newrun["commands"]) == 4
    assert newrun["status"] == "PASS" and all(c["exit_code"] == 0 for c in newrun["commands"])
    assert newrun["execution_context"]["provider"] == "local_python_process"
    assert newrun["execution_context"]["worktree_has_changes"] is True
    assert newrun["new_hardware_data"] is False and newrun["new_lean_execution"] is False

    before = read("physics/qm/book/evidence/v3.9/prior/CHAPTER_DOSSIER.json")
    after = read("physics/qm/book/CHAPTER_DOSSIER.json")
    old_results = [r for c in before["chapters"] for r in c["numbered_results"]]
    new_results = [r for c in after["chapters"] for r in c["numbered_results"]]
    assert len(old_results) == 182 and len(new_results) == 188
    assert new_results[:182] == old_results
    oldclaims = read("physics/qm/status/CLAIM_LEDGER_v31.11.json")["claims"]
    newclaims = read("physics/qm/status/CLAIM_LEDGER_v31.12.json")["claims"]
    assert len(oldclaims) == 105 and len(newclaims) == 111
    assert newclaims[:105] == oldclaims

    # Derive the bound independently with exact rational square-root brackets.
    scale = 10**24
    def sqrt_bounds(x):
        k = isqrt(x.numerator * scale**2 // x.denominator)
        lo = F(k, scale)
        hi = lo if lo*lo == x else F(k+1, scale)
        assert lo*lo <= x <= hi*hi
        return lo, hi
    e = F(1, 4096)
    rlo, rhi = sqrt_bounds(4*e - 3*e*e)
    tlo, thi = sqrt_bounds(F(2))
    lo = F(1,50) + (e+rlo)/2 + tlo/100
    hi = F(1,50) + (e+rhi)/2 + thi/100
    assert hi < F(1,20)
    success = (1-e) * F(37,50)**2
    assert success == F(1121211,2048000)
    # Source and compiled costs use distinct laws.
    qlaw = {"00": F(313,1250), "01": F(312,1250),
            "10": F(312,1250), "11": F(313,1250)}
    assert sum(qlaw.values()) == 1
    assert sum(v*r.count("1") for r,v in qlaw.items()) == 1
    assert qlaw["01"] == F(156,625) > F(1,20)

    report = {
        "schema": "ueot-qm.recovery-c-independent-review/1",
        "status": "PASS" if not errors else "FAIL",
        "reviewed_at_utc": datetime.now(timezone.utc).isoformat(),
        "reviewer": "new native child agent /root/c_robust_evidence",
        "repository_read": str(repo),
        "baseline": "aea2fceef3c62cc8dc749b6cbb1b40a7d89df80d",
        "checked_identity_scopes": checked,
        "identity_errors": errors,
        "historic_result_objects_preserved": 182,
        "historic_claim_objects_preserved": 105,
        "new_result_ids": [r["id"] for r in new_results[182:]],
        "independent_rational_bound": {
            "formula": "1/50+(sqrt(4e-3e^2)+e)/2+sqrt(2)/100; e=1/4096",
            "lower": str(lo), "upper": str(hi),
            "precision": "1/20", "positive_margin_lower": str(F(1,20)-hi),
            "complete_source_attempt_success_lower": str(success),
            "bound_is_not_observed_error": True,
            "compiled_expected_selected_blue_calls": "1",
            "flag_blind_omission_counterexample_distance_lower": str(qlaw["01"]),
        },
        "execution_identity": {
            "inherited_runtime_was_not_rerun": True,
            "new_four_gate_receipt_rehashed_not_reexecuted": True,
            "original_local_dirty_checkout_preserved": True,
            "no_new_lean_execution": True,
            "no_hardware_data": True,
        },
        "reviewed_sources": [
            {"path": p, "sha256": sha(repo/p)} for p in [
                "physics/qm/audits/GROWING_CUTOFF_v31.12/A_OPERATIONAL_GROWTH_BRIDGE.md",
                "physics/qm/audits/GROWING_CUTOFF_v31.12/C_ROBUST_CERTIFICATE_AND_DATA.md",
                "physics/qm/audits/GROWING_CUTOFF_v31.12/SHARED_MODEL.md",
                "physics/qm/growing_cutoff/verify_integration.py",
                "physics/qm/growing_cutoff/exact_checker.py",
                "physics/qm/growing_cutoff/verify_inherited_evidence.py",
                "physics/qm/growing_cutoff/run_verification.py",
                ".github/workflows/ueot-qm.yml",
            ]
        ],
        "publication_entry_finding_at_first_read": {
            "path": "physics/qm/book/evidence/v3.9/local-acceptance.json",
            "status": "missing_at_first_read_reported_to_root_for_completion",
            "existing_valid_receipt": "physics/qm/book/evidence/v3.9/increment-verification.json",
        },
        "scope": "Internal non-author AI review; hashes, rational arithmetic and paper review. No claim of new proof-assistant, hardware or external human peer-review acceptance.",
        "review_script_sha256": sha(Path(__file__)),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, ensure_ascii=False)+"\n")
    print(json.dumps({"status":report["status"], "identity_counts": {x["scope"]:x["count"] for x in checked}, "upper":str(hi), "errors":errors}))
    if errors:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
