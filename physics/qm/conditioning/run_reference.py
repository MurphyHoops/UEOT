"""Execute the frozen T3 reference and semantic boundary fixtures."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import traceback

import numpy as np
import scipy

from finite_conditioning import (Node, conditioned_reference, full_leaf_law,
    normalized_accepted_law, cq_distance, independent_retry_cost, scaled_filter,
    common_observation_mixture, mass)
from fixtures import t3, singular_one_step, early_stop, out_of_library, deterministic_label, positive_chain
from finite_conditioning import Instrument, repeated_success_tree, expected_action_cost


def run(plan_path=None):
    root = Path(__file__).parent
    plan_path = Path(plan_path) if plan_path else root / "frozen_plan.json"
    instrument, tree, rho = t3(plan_path)
    reference = conditioned_reference(tree, rho)
    original, accepted = full_leaf_law(tree, rho)
    p, target = normalized_accepted_law(original, accepted)
    transformed, _ = full_leaf_law(reference.tree, reference.initial_state)
    residual = cq_distance(target, transformed)
    assert abs(p - 117 / 4096) < 1e-12 and residual < 1e-10
    completeness = []
    def walk(t):
        if isinstance(t, Node):
            completeness.append(float(np.linalg.norm(t.instrument.gram() - np.eye(2))))
            for child in t.children.values():
                walk(child)
    walk(reference.tree)
    filter_instrument, filter_p = scaled_filter(reference.effects[()], rho)
    source_cost = independent_retry_cost(tree, rho)
    sing_tree, sing_rho = singular_one_step()
    sing0 = conditioned_reference(sing_tree, sing_rho, "0")
    sing1 = conditioned_reference(sing_tree, sing_rho, "1")
    sing_law0, _ = full_leaf_law(sing0.tree, sing0.initial_state)
    sing_law1, _ = full_leaf_law(sing1.tree, sing1.initial_state)
    stop_tree, stop_rho = early_stop()
    identity, dephase, flip = out_of_library()
    outside = common_observation_mixture({"x": identity},
        {"dephase": {"x": dephase}, "flip_dephase": {"x": flip}})
    a0, a1 = deterministic_label("0"), deterministic_label("1")
    shared = common_observation_mixture({"x0": a0, "x1": a1},
        {"choose0": {"x0": a0, "x1": a0}, "choose1": {"x0": a1, "x1": a1}})
    assert outside["status"] == shared["status"] == "NUMERICAL_NO_FEASIBLE_MIXTURE"
    pc_source, pc_tree, pc_rho, pc_library = positive_chain()
    pc_ref = conditioned_reference(pc_tree, pc_rho)
    pc_mix = common_observation_mixture({"x": pc_ref.tree.instrument},
                                      {a: {"x": inst} for a, inst in pc_library.items()})
    assert pc_mix["status"] == "NUMERICAL_FEASIBLE_MIXTURE"
    pc_physical = Instrument({o: tuple(k / np.sqrt(2) for a in pc_library.values() for k in a.branches[o])
                              for o in pc_source.branches})
    pc_physical_tree = repeated_success_tree(pc_physical, {"0", "1"}, 3)
    pc_actual, pc_accept = full_leaf_law(pc_physical_tree, pc_rho)
    pc_raw, pc_original_accept = full_leaf_law(pc_tree, pc_rho)
    pc_p, pc_target = normalized_accepted_law(pc_raw, pc_original_accept)
    pc_error = cq_distance(pc_actual, pc_target)
    assert pc_error < 1e-10 and pc_accept == pc_original_accept
    original_only = common_observation_mixture({"x": reference.tree.instrument}, {"source": {"x": instrument}})
    assert original_only["status"] == "NUMERICAL_NO_FEASIBLE_MIXTURE"
    source_names = ["finite_conditioning.py", "fixtures.py", "frozen_plan.json", "positive_chain_plan.json",
                    "exact_witnesses.py", "test_finite_conditioning.py", "run_reference.py"]
    return {
        "schema": "ueot-qm.finite-conditioning-numerical-run/1",
        "status": "PASS_NUMERICAL_REFERENCE_NOT_CERTIFIED_GENERAL_ALGORITHM",
        "executed_at_utc": datetime.now(timezone.utc).isoformat(),
        "versions": {"numpy": np.__version__, "scipy": scipy.__version__},
        "source_sha256": {n: hashlib.sha256((root / n).read_bytes()).hexdigest() for n in source_names},
        "plan_sha256": hashlib.sha256(plan_path.read_bytes()).hexdigest(),
        "t3": {"source_acceptance_probability": p, "accepted_visible_leaves": len(accepted),
               "all_original_visible_leaves": len(original),
               "full_CQ_trace_distance_residual": residual,
               "maximum_completeness_residual": max(completeness),
               "source_early_stop_cost": source_cost,
               "best_scaled_filter_success_probability": filter_p,
               "all_space_implementation_available": "not inferred from formal CPTP legality",
               "original_only_failure_probability_on_I_over_2": mass(instrument.branch("failure", np.eye(2) / 2)),
               "original_only_uniform_failure_lower_bound": float(np.linalg.eigvalsh(instrument.adjoint("failure", np.eye(2))).min()),
               "hidden_kraus_labels_in_records": False},
        "positive_complete_chain": {
            "source_acceptance_probability": pc_p,
            "initial_state_change_residual": float(np.linalg.norm(pc_ref.initial_state - pc_rho)),
            "accepted_visible_records": len(pc_accept),
            "actual_allowed_randomization": pc_mix,
            "implemented_full_CQ_residual": pc_error,
            "source_early_stop_cost": independent_retry_cost(pc_tree, pc_rho),
            "target_actual_Pauli_action_count": expected_action_cost(pc_physical_tree, pc_rho),
            "extra_randomization_cost": "3*r",
            "action_only_advantage_condition": "3*(1+r)<14",
            "all_additional_costs": "unmeasured; no hardware advantage claim"
        },
        "singular_positive_mass": {"p": sing0.acceptance_probability,
            "two_completion_CQ_distance": cq_distance(sing_law0, sing_law1)},
        "variable_early_stop_cost": independent_retry_cost(stop_tree, stop_rho),
        "numerical_library_checks": {"out_of_library": outside, "shared_observation": shared,
                                     "same_T3_original_only": original_only},
        "limits": ["all residuals and LP statuses are numerical, not exact certificates",
                   "the separate exact_witnesses.json contains exact finite symbolic checks",
                   "no universal parser or numerical eigensolver correctness theorem",
                   "preparation, reset, ancilla and calibration costs unmeasured",
                   "no real experiment, external-reference guarantee or new natural-law claim"]
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--plan", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--output-dir", type=Path)
    args = parser.parse_args()
    if args.output and args.output_dir:
        parser.error("choose --output or --output-dir")
    output = args.output or (args.output_dir / "runtime_results.json" if args.output_dir else None)
    try:
        result = run(args.plan)
    except Exception as exc:
        failure = {"status": "NUMERICAL_REFERENCE_FAILED", "error_type": type(exc).__name__,
                   "message": str(exc), "traceback": traceback.format_exc(),
                   "executed_at_utc": datetime.now(timezone.utc).isoformat(),
                   "versions": {"numpy": np.__version__, "scipy": scipy.__version__}}
        if output:
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_text(json.dumps(failure, indent=2) + "\n")
        raise
    if output:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({"status": result["status"], "t3": result["t3"],
                      "output": str(output) if output else None}))
