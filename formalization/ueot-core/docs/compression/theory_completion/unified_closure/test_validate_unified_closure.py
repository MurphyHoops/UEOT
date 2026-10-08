#!/usr/bin/env python3
"""Finite adversarial controls for UMC immutable mission governance.

The tests edit *temporary* matrix files only; repository source and frozen
ledger are neither changed nor copied. Expected rejections are part of PASS.
"""
from pathlib import Path
import copy
import json
import tempfile
from validate_unified_closure import validate

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[5]
MATRIX=HERE/"UNIFIED_CLOSURE_PORT_MATRIX_V1.json"

def run():
    original=json.loads(MATRIX.read_text())
    ok=validate(ROOT,MATRIX)
    assert ok["stages"] == 7 and ok["source_theorems"] == 106
    checks={
      "closed_without_proof":lambda x:x.update(state="FULL_MATHEMATICAL_CLOSURE"),
      "fake_stage_proof":lambda x:x["stages"][0].update(state="LOCAL_PROVED"),
      "self_cycle":lambda x:x["stages"][0].update(dependencies=["UMC-00"]),
      "missing_stage":lambda x:x["stages"].pop(),
      "counted_core_change":lambda x:x.update(counted_core_source_theorems=105),
      "generator_promotion":lambda x:x["counted_minimal_generators"].append("M-BU-01"),
      "unjustified_empirical_claim":lambda x:x.update(independent_scientific_evidence="VERIFIED"),
      "missing_gate":lambda x:x["mandatory_gates"].remove("G3"),
      "missing_reuse_anchor":lambda x:x["stages"][1].update(authority_anchors=["formalization/ueot-core/MISSING.lean"]),
      "remove_noncircularity":lambda x:x["stages"][2]["must_include"].remove("same_source_or_explicit_transport"),
      "fabricate_proof_results":lambda x:x.update(proof_stage_results=[{"stage":"UMC-01","claim":"FULL"}]),
      "delete_P12_boundary":lambda x:x.update(historical_theory_completion="P0-P12_FULL")
    }
    rejected=0
    with tempfile.TemporaryDirectory(prefix="ueot-umc-governance-") as td:
        for name, mutate in checks.items():
            subject=copy.deepcopy(original)
            mutate(subject)
            path=Path(td)/(name+".json")
            path.write_text(json.dumps(subject))
            try:
                validate(ROOT,path)
            except (ValueError,KeyError):
                rejected+=1
            else:
                raise AssertionError("unsafe matrix mutation was accepted: "+name)
    assert rejected==len(checks)
    print("UNIFIED_CLOSURE_NEGATIVE_CONTROLS_PASS",
          json.dumps({"baseline":1,"expected_rejections":rejected},sort_keys=True))
if __name__=="__main__":
    run()
