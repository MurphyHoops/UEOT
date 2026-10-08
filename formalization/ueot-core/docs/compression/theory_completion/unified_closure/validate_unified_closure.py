#!/usr/bin/env python3
"""Read-only governance validation for UMC contract, frozen counts and typed stage DAG.

Policy = existing immutable Track TC base. This local validator does not grant
new path privileges and cannot promote a mathematical theorem or evidence gate.
"""
import argparse
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
REQUIRED_GATES = {f"G{i}" for i in range(9)}
STAGES = [f"UMC-{i:02}" for i in range(7)]
EXPECTED_GENERATORS = {"M-QD-01", "M-TC-01", "M-PE-01", "M-OI-01"}

def ensure(ok, msg):
    if not ok:
        raise ValueError(msg)

def validate(root: Path, matrix: Path) -> dict:
    m = json.loads(matrix.read_text(encoding="utf-8"))
    ensure(m.get("schema_version") == 1, "schema version mismatch")
    ensure(m.get("tracker_issue") == 302 and m.get("track") == "TC",
           "tracker identity or track mismatch")
    ensure(m.get("state") == "OPEN" and m.get("proof_stage_results") == [],
           "initial frozen contract cannot assert completed proofs")
    ensure(m.get("claim") == "MATHEMATICAL_CONSTRUCTION_UNDER_EXPLICIT_PREMISES",
           "claim upgraded without independent bridge")
    ensure(set(m.get("mandatory_gates", [])) == REQUIRED_GATES,
           "nine scientific gates incomplete or modified")
    ensure(m.get("counted_core_source_theorems") == 106, "Core source count changed")
    ensure(set(m.get("counted_minimal_generators", [])) == EXPECTED_GENERATORS,
           "counted generator set changed")
    ensure((m.get("counted_generated"), m.get("retained_adapter"),
            m.get("retained_boundary")) == (11, 89, 6),
           "Compression final disposition accounting changed")
    ensure(m.get("independent_scientific_evidence") == "UNVERIFIED",
           "external evidence upgraded by mathematics")
    ensure(m.get("historical_theory_completion") ==
           "P0-P12_PROGRAM_CLOSED_P12_PARTIAL_EXPLICIT_BOUNDARY",
           "P12 stronger claim silently introduced")
    stages = m.get("stages", [])
    ensure(len(stages) == 7 and {s.get("id") for s in stages} == set(STAGES),
           "missing, duplicate or extra UMC stage")
    byid = {s["id"]: s for s in stages}
    visited, active = set(), set()
    def visit(node):
        ensure(node not in active, "circular dependency: " + node)
        if node in visited:
            return
        active.add(node)
        for dep in byid[node]["dependencies"]:
            ensure(dep in byid and dep != node, "unknown/self dependency: " + dep)
            visit(dep)
        active.remove(node)
        visited.add(node)
    for node in STAGES:
        visit(node)
    mandatory = {
      "same_source_or_explicit_transport", "assumptions_and_origin",
      "exact_Lean_symbols", "new_implication_or_no_go", "nonvacuous_model",
      "negative_control", "axiom_audit", "conditional_claim_scope"}
    for s in stages:
        sid = s["id"]
        ensure(s["state"] == "OPEN" and
               s["claim_class"] == "CONDITIONAL_THEOREM_OR_BOUNDARY" and
               s["counted_core_impact"] == "NONE",
               f"undocumented stage status/promotion {sid}")
        ensure(s.get("acceptance_criterion") and len(s["acceptance_criterion"]) > 35,
               f"empty or vague criterion {sid}")
        ensure(set(s["must_include"]) == mandatory, f"required proof conditions missing {sid}")
        ensure(len(s["authority_anchors"]) >= 2, f"reused evidence missing {sid}")
        for name in s["authority_anchors"]:
            ensure(name.startswith("formalization/ueot-core/") and
                   ".." not in Path(name).parts,
                   f"unsafe source path: {name}")
            ensure((root/name).is_file(), f"unknown canonical source: {name}")
    # Verify the contract is aligned with the *live* authoritative ledgers.
    coverage = (root/"formalization/ueot-core/docs/V3_COVERAGE_STATUS.md").read_text()
    ensure("**106**" in coverage and "**0**" in coverage and "106/106 FULL-GREEN" in coverage,
           "current frozen Core coverage no longer matches")
    ledger = json.loads((root/"formalization/ueot-core/docs/compression/COMPRESSION_LEDGER.yaml").read_text())
    ensure({key for key, item in ledger["generators"].items()
            if item.get("state") == "counted_generator"} == EXPECTED_GENERATORS,
           "counted ledger generator drift")
    statuses = [v.get("status") for v in ledger["final_dispositions"].values()]
    ensure((statuses.count("generated"), statuses.count("retained_adapter"),
            statuses.count("retained_boundary")) == (11, 89, 6),
           "counted ledger P-ID dispositions drift")
    p12 = (root/"formalization/ueot-core/docs/compression/theory_completion/P12_FINAL_AUTOPOIESIS_AUDIT.md").read_text()
    ensure("PARTIAL / EXPLICIT BOUNDARY" in p12 and
           "no_physicalOnly_synthesizer" in p12,
           "P12 boundary dropped")
    mission = (matrix.parent/"UNIFIED_CLOSURE_MISSION_V1.md")
    ensure(mission.is_file() and "UMC-00" in mission.read_text() and
           "FULL_MATHEMATICAL_CLOSURE" in mission.read_text(),
           "frozen mission contract missing or weakened")
    # Baseline theorem constants: lexical existence does not substitute for a Lean proof.
    checks = {
        "formalization/ueot-core/UEOT/V3/CoreOperationalAssembly.lean": "p_core_01",
        "formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/AutopoiesisClosure.lean":
            "p12_terminal_conditional_finite_lifecycle",
        "formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/ScientificClosure/SISCFutureResponseCore.lean":
            "unique_canonical_future_update"
    }
    for src, symbol in checks.items():
        code = (root/src).read_text()
        ensure(re.search(r"\b(theorem|lemma)\s+" + re.escape(symbol)+r"\b",code) is not None,
               "reused named theorem missing: " + symbol)
    return {"stages":len(stages),"gates":len(REQUIRED_GATES),
            "source_anchors":sum(len(s["authority_anchors"]) for s in stages),
            "source_theorems":106,"generators":4}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo-root", type=Path, default=HERE.parents[5])
    ap.add_argument("--matrix", type=Path,
                    default=HERE/"UNIFIED_CLOSURE_PORT_MATRIX_V1.json")
    args = ap.parse_args()
    try:
        result = validate(args.repo_root.resolve(), args.matrix.resolve())
    except (ValueError, OSError, KeyError, json.JSONDecodeError) as exc:
        print(f"UNIFIED_CLOSURE_GOVERNANCE_FAIL: {exc}",file=sys.stderr)
        return 1
    print("UNIFIED_CLOSURE_GOVERNANCE_PASS", json.dumps(result,sort_keys=True))
    return 0

if __name__=="__main__":
    sys.exit(main())
