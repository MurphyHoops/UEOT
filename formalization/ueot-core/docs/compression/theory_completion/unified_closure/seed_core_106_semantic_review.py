#!/usr/bin/env python3
"""Seed a *source-vs-elaborated-type* human review ledger, never a proof receipt.

The canonical source must be checked independently against its pinned SHA.
This script only joins previous machine atlases and explicitly distinguishes
verified Lean presence from human scientific/semantic validation.
Refuse to overwrite an existing reviewed snapshot.
"""
import json
from pathlib import Path
from collections import Counter

HERE = Path(__file__).resolve().parent
OUT = HERE / "UMC_CORE_106_SEMANTIC_REVIEW_V1.json"
ATLAS = HERE / "UMC_00_SOURCE_ATLAS_V1.json"
DEPS = HERE / "UMC_CORE_106_ELABORATED_DECL_DAG_V1.json"
PINNED_SPEC_SHA256 = "ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303"

def main():
    if OUT.exists():
        raise SystemExit("Review snapshot already exists; refusing to overwrite.")
    atlas = json.loads(ATLAS.read_text())
    deps = json.loads(DEPS.read_text())
    by_pid = {r["pid"]: r for r in deps["records"]}
    reviewed = {
      "P-PER-03": {
        "source_obligation": "Finite controlled PMF deletion stabilizes; winning set for sure-safe infinite viability and preserving stationary selector.",
        "lean_observation": "ViabilitySource.p_per_03 explicitly produces stabilized K, K=winningSet, stationary selector, and genuine all-time trajectory law for an initially K-supported PMF.",
        "remaining_question": "Verify all history-strategy quantifiers, support/measurability interpretation, and paper's implicit finite discrete measurable-space realization."},
      "P-CTL-01": {
        "source_obligation": "Finite nonempty state-dependent actions, bounded reward, 0<beta<1; unique Bellman fixed point, value iteration, greedy global causal optimality.",
        "lean_observation": "p_ctl_01_causal_optimality proves causal upper bound and greedy achievement, with separate Model.fixedPoint_unique and valueIteration_tendsto dependencies.",
        "remaining_question": "Independently trace the causal policy domain and discount/infinite-limit assumptions across dependent source modules."},
      "P-QUO-01": {
        "source_obligation": "Surjective exact action/reward/kernel quotient preserves optimal value and lifts macro optimal policy.",
        "lean_observation": "ExactControlQuotient.p_quo_01 states optimal-value pullback, action-value equality, lifted greedy optimality, and domination of every micro causal policy.",
        "remaining_question": "Audit the ExactControlQuotient structure fields: shared actions/fiber typing, surjectivity, reward and kernel descent, and same beta."},
      "P-ALG-01": {
        "source_obligation": "Finite stable partition coarsest under initial observable/reward partition and controlled Markov lumpability; finite future output-law fidelity.",
        "lean_observation": "PAlg01.p_alg_01 returns terminal stable setoid, coarseness, output/reward/transition preservation, normalized block mass and finite action-word output law agreement.",
        "remaining_question": "Compare exact initialization, refinement termination bound, and all finite-word emission timing against canonical Section 28.5."}
    }
    rows = []
    for src in atlas["records"]:
        pid = src["pid"]
        dep = by_pid[pid]
        note = reviewed.get(pid)
        rows.append({
            "pid": pid,
            "original_section": src["source_chapter"],
            "original_line": src["source_line"],
            "pinned_source_sha256": PINNED_SPEC_SHA256,
            "lean_symbol": dep["name"],
            "lean_decl_source": dep["source"],
            "lean_decl_line": dep["line"],
            "lean_kernel_elaboration_status": "PREVIOUSLY_CHECKED",
            "direct_ueot_constant_count": dep["direct_local_proof_constant_count"],
            "direct_counted_dependencies": dep["direct_counted_pid_deps"],
            "semantic_review_status": "PRELIMINARY_CONTRACT_ALIGNMENT" if note else "NOT_REVIEWED",
            "source_obligation": note["source_obligation"] if note else None,
            "lean_observation": note["lean_observation"] if note else None,
            "remaining_question": note["remaining_question"] if note else "Compare canonical text with unfolded Lean type and all assumptions.",
            "independent_full_semantic_match": False,
        })
    assert len(rows) == 106 and len(set(x["pid"] for x in rows)) == 106
    results = {
        "schema": 1,
        "canonical_source": "UEOT_Core_Mathematics_v3.0_Complete.md",
        "canonical_source_sha256": PINNED_SPEC_SHA256,
        "source_material_available_in_current_conversation_not_in_repository": True,
        "scope": "REVIEW_QUEUE_AND_4_PRELIMINARY_CONTRACT_COMPARISONS_NOT_SEMANTIC_COMPLETION",
        "status_count": dict(Counter(r["semantic_review_status"] for r in rows)),
        "rows": rows,
        "global_full_semantic_validation": "NOT_ESTABLISHED",
        "frozen_counted_ledger_unchanged": True,
    }
    OUT.write_text(json.dumps(results,ensure_ascii=False,indent=2)+"\n")
    print("CORE_106_SEMANTIC_QUEUE_CREATED",results["status_count"])
if __name__=="__main__": main()
