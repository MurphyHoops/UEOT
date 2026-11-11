#!/usr/bin/env python3
"""Exact probes for the finite UEOT growth-parameter classification.

This file leaves the frozen source and the historical transaction checker intact.
It imports the latter by hash, reweights its literal transactions with each new
primitive probability point, and checks every canonical local request/noise case.
The all-history and arbitrary-horizon claims are written proofs, not consequences
of the finite checks below. No Lean compilation or source modification is made.
"""

from dataclasses import replace
from fractions import Fraction as F
from pathlib import Path
import hashlib
import importlib.util
import json
import sys


BASE_COMMIT_AS_SUPPLIED = "827be44cd14c63d9d13e33493eee07c5f1afa5fe"
SOURCE_RELATIVE = Path("formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure")
TRANSACTION_RELATIVE = Path("mathematics/review/CORE_DEFINITIVE_FREEZE_2026-11-11/boundary_math_check_original.py")
TRANSACTION_SHA256 = "4119e70e968a6b128d464d25ebe4367818fd618df6331b2d89e52a8cc9e1c4a4"
SOURCE_SHA256 = {
    "CoreRegenerativeControlPopulation.lean": "533c9cdedccc2f5016cec438c5fcd9a84f00abd18dcd78c251e21df7ca6441aa",
    "CoreRegenerativeFormation.lean": "daa2b899b5016446bc15a1e9d6df353f1e2703e31a1192a768890aa7c19decd9",
    "CoreRegenerativeOneStep.lean": "dfd341b0a7d381b138cebc98c3725f594d047cc28b234f49506222dfaf97789c",
    "CoreRegenerativePopulation.lean": "b6e62acd425e1c1bc5c2d289836f4d32052a65716715b00e8a24f227801a64f3",
    "CoreRegenerativeQuotient.lean": "9e8965d43f36d27eb36a56d68d2a70fd564bd0a1170b2a7352990eba50666cce",
    "CoreRegenerativeSource.lean": "75e76b0673918186de3aac253e0c4810f9bd4895236f150d408cf27a9a8ed793",
}
ACTIONS = ("care", "bloom", "stop")
HORIZON = 12

# The first five are the requested regimes and exact row-value witnesses.
# Three additional points test ties and the nontrivial subcritical r_H > 1 case.
POINTS = (
    ("old_valid_theta1", (F(3, 4), F(1, 8), F(3, 8), F(1, 4), F(1, 3)),
     (F(9, 8), F(5, 4), F(29, 24)), "old Valid; theta1 uniquely attains the exponent"),
    ("subcritical_bloom_advantage", (F(1, 2), F(1, 8), F(1, 4), F(1, 4), F(1, 3)),
     (F(3, 4), F(7, 8), F(5, 6)), "both internal exponents below the full-menu factor one"),
    ("critical_bloom_advantage", (F(2, 3), F(1, 8), F(1, 4), F(1, 4), F(1, 3)),
     (F(11, 12), F(25, 24), F(1)), "theta1 reaches factor one but loses every finite D horizon"),
    ("reversed_advantage_theta0", (F(3, 4), F(1, 4), F(3, 8), F(1, 8), F(1, 3)),
     (F(9, 8), F(1), F(9, 8)), "theta0 attains; theta1 remains supercritical but is slower"),
    ("care_subcritical_global_supercritical", (F(3, 5), F(1, 10), F(3, 10), F(1, 2), F(1, 5)),
     (F(9, 10), F(13, 10), F(61, 50)), "two-census DP from D is 279/250, not fixed theta1"),
    ("equal_advantage_critical", (F(3, 4), F(1, 8), F(1, 4), F(1, 8), F(1, 3)),
     (F(1), F(1), F(1)), "gamma equals delta; both internal programs attain the critical factor"),
    ("subcritical_with_large_healthy_row", (F(1, 2), F(1, 8), F(1, 4), F(1, 2), F(1, 2)),
     (F(3, 4), F(9, 8), F(15, 16)), "mu below one despite k_star above one; r_H is 9/7"),
    ("equal_advantage_supercritical", (F(3, 4), F(1, 8), F(3, 8), F(1, 8), F(1, 3)),
     (F(9, 8), F(9, 8), F(9, 8)), "gamma equals delta; both internal programs attain above one"),
)


def locate_repository():
    for ancestor in Path(__file__).resolve().parents:
        for candidate in (ancestor, ancestor / "ueot-review"):
            if ((candidate / TRANSACTION_RELATIVE).is_file()
                    and all((candidate / SOURCE_RELATIVE / name).is_file() for name in SOURCE_SHA256)):
                return candidate
    raise FileNotFoundError("Cannot locate the repository and frozen transaction checker from script ancestors")


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_transaction_checker(repo):
    path = repo / TRANSACTION_RELATIVE
    assert sha256(path) == TRANSACTION_SHA256, "The historical transaction checker changed"
    spec = importlib.util.spec_from_file_location("ueot_frozen_transaction_checker", path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    previous_bytecode_setting = sys.dont_write_bytecode
    sys.dont_write_bytecode = True
    try:
        spec.loader.exec_module(module)
    finally:
        sys.dont_write_bytecode = previous_bytecode_setting
    return module


def basic_valid(p):
    s, delta, b, gamma, q = p
    return 0 < delta < s < 1 and b > 0 and gamma > 0 and b + gamma < 1 and 0 < q < 1


def noise_weight(p, z):
    s, delta, b, gamma, q = p
    u, v, dr, db = z
    return ((1 - s, delta, s - delta)[u]
            * (1 - b - gamma, gamma, b)[v]
            * (q if dr else 1 - q) * (q if db else 1 - q))


def dot(x, y):
    return sum((a * b for a, b in zip(x, y)), F(0))


def advance(population_means, matrix):
    return tuple(sum((population_means[i] * matrix[i][j] for i in (0, 1)), F(0))
                 for j in (0, 1))


def expected_rows(p):
    s, delta, b, gamma, q = p
    kc, kb = s + b, s - delta + b + gamma
    care, bloom = (kc * (1 - q), kc * q), (kb * (1 - q), kb * q)
    return {
        False: {"care": care, "bloom": bloom, "stop": (F(0), F(0))},
        True: {"care": care, "bloom": (F(0), F(1)), "stop": (F(0), F(0))},
    }


def check_literal_transactions(source, p, rows):
    weights = {z: noise_weight(p, z) for z in source.NOISE}
    assert len(weights) == 36 and all(w > 0 for w in weights.values())
    assert sum(weights.values()) == 1
    local_cases = program_cases = 0
    for theta in (False, True):
        for kind in (False, True):
            for tag in (False, True):
                body = replace(source.program_body(theta, kind), tag=tag)
                for action in ACTIONS:
                    mean = [F(0), F(0)]
                    rejected_results = set()
                    for z, w in weights.items():
                        local_cases += 1
                        r = source.step(body, action, z)
                        outputs = [x for x in (r.retained, r.newborn) if x is not None]
                        assert len(outputs) <= 2
                        assert r.repair_paid + r.operation_paid + len(outputs) + r.refund == 6
                        if action == "stop":
                            assert (r.retained, r.newborn, r.repair_paid, r.operation_paid,
                                    r.refund, r.status) == (None, None, 0, 0, 6, "stopped")
                        elif kind and action == "bloom":
                            assert (r.retained, r.newborn, r.repair_paid, r.operation_paid,
                                    r.refund, r.status) == (body, None, 0, 0, 5, "rejected")
                            rejected_results.add(r)
                        else:
                            assert r.status == "executed"
                            assert r.repair_paid == (3 if kind else 0)
                            assert r.operation_paid == (1 if action == "care" else 2)
                        for output in outputs:
                            assert (source.majority(output.row_h), source.majority(output.row_d)) == (theta, False)
                            assert output.tag == tag
                            mean[int(source.diagnostic(output))] += w
                    assert tuple(mean) == rows[kind][action]
                    if kind and action == "bloom":
                        assert len(rejected_results) == 1  # no raw-noise dependence
                for z in source.NOISE:
                    program_cases += 1
                    r = source.program_step(body, z)
                    assert r == source.step(body, source.request_of(body), z)
                    assert r.status == "executed"
                    assert r.repair_paid == (3 if kind else 0)
                    assert source.request_cap(body, source.request_of(body)) <= 6
    return {"local_menu_cases": local_cases, "internal_program_cases": program_cases,
            "all_36_noise_weights_positive_and_sum_one": True,
            "full_menu_rows_from_literal_transactions": True,
            "rejection_is_noise_independent_same_body_with_refund_five": True}


def finite_dp(rows, horizon):
    values = [(F(1), F(1))]
    decisions = [None]
    for _ in range(horizon):
        previous = values[-1]
        next_values, next_decisions = [], {}
        for kind, label in ((False, "H"), (True, "D")):
            candidates = {a: dot(rows[kind][a], previous) for a in ACTIONS}
            best = max(candidates.values())
            next_values.append(best)
            next_decisions[label] = [a for a in ACTIONS if candidates[a] == best]
        values.append(tuple(next_values))
        decisions.append(next_decisions)
    return values, decisions


def point_probe(source, name, p, expected_rates, purpose):
    assert basic_valid(p)
    s, delta, b, gamma, q = p
    kc, kb = s + b, s - delta + b + gamma
    k = max(kc, kb)
    a = 1 - q
    mu, lam0, lam1 = a * k + q * kc, kc, a * kb + q * kc
    rho = max(F(1), mu)
    assert (kc, kb, mu) == expected_rates
    assert mu == max(lam0, lam1)
    assert rho == max(F(1), lam0, lam1)
    if mu >= 1:
        r = (k, kc)
        d_action = "care"
    else:
        assert 0 < 1 - a * k
        r = (k * q / (1 - a * k), F(1))
        d_action = "bloom"  # the real rejected request; not accepted bloom
    assert min(r) > 0
    h_action = "care" if kc >= kb else "bloom"
    rows = expected_rows(p)
    literal = check_literal_transactions(source, p, rows)
    matrix = (rows[False][h_action], rows[True][d_action])
    row_gaps = {label: {action: rho * r[int(kind)] - dot(row, r)
                        for action, row in rows[kind].items()}
                for kind, label in ((False, "H"), (True, "D"))}
    assert all(gap >= 0 for by_action in row_gaps.values() for gap in by_action.values())
    assert dot(matrix[0], r) == rho * r[0]
    assert dot(matrix[1], r) == rho * r[1]

    # An explicitly correlated joint request law: its two request coordinates
    # do not factor. The universal real-kernel result uses written linearity.
    correlation_gap = (F(1, 3) * (row_gaps["H"]["bloom"] + row_gaps["D"]["care"])
                       + F(2, 3) * (row_gaps["H"]["care"] + row_gaps["D"]["bloom"]))
    assert correlation_gap >= 0
    starts = {"one_H": (F(1), F(0)), "one_D": (F(0), F(1)),
              "mixed_2H_1D": (F(2), F(1)), "empty": (F(0), F(0))}
    trajectories = {}
    for label, initial in starts.items():
        current = initial
        value0 = dot(initial, r)
        path = []
        for T in range(HORIZON + 1):
            population = sum(current)
            weighted = dot(current, r)
            assert weighted == value0 * rho ** T
            assert value0 / max(r) * rho ** T <= population <= value0 / min(r) * rho ** T
            path.append(population)
            current = advance(current, matrix)
        trajectories[label] = path

    internal = {}
    for theta in (0, 1):
        lam = lam0 if theta == 0 else lam1
        internal_matrix = (rows[False]["care" if theta == 0 else "bloom"], rows[True]["care"])
        state = (F(0), F(1))
        series = [F(1)]
        for T in range(1, HORIZON + 1):
            state = advance(state, internal_matrix)
            assert sum(state) == kc * lam ** (T - 1)
            series.append(sum(state))
        condition = (gamma <= delta and kc >= 1) if theta == 0 else (gamma >= delta and lam1 >= 1)
        assert (lam == rho) == condition
        internal[f"theta{theta}"] = {"growth_factor": lam, "attains_rho": condition,
                                     "mean_population_from_D_T0_to_T12": series}

    dp, decisions = finite_dp(rows, HORIZON)
    for T, value in enumerate(dp):
        for kind in (False, True):
            assert trajectories["one_D" if kind else "one_H"][T] <= value[int(kind)]
            assert value[int(kind)] <= r[int(kind)] / min(r) * rho ** T
    if mu <= 1:
        alpha = a * k
        assert 0 < alpha < 1
        rejection_rh = k * q / (1 - alpha)
        for T, value in enumerate(dp):
            assert value == (rejection_rh + (1 - rejection_rh) * alpha ** T, F(1))
    elif kc >= 1:
        assert all(dp[T] == (trajectories["one_H"][T], trajectories["one_D"][T])
                   for T in range(HORIZON + 1))

    # A paid first care transaction followed by the attaining external selector.
    # This witnesses why a finite repair prefix cannot be used to claim a
    # general incompatibility between repair and the optimal asymptotic exponent.
    first_repair_weight = dot(rows[True]["care"], r)
    assert first_repair_weight > 0
    repaired = rows[True]["care"]
    prefix_path = []
    for T in range(1, HORIZON + 1):
        assert dot(repaired, r) == first_repair_weight * rho ** (T - 1)
        assert first_repair_weight / max(r) * rho ** (T - 1) <= sum(repaired)
        prefix_path.append(sum(repaired))
        repaired = advance(repaired, matrix)

    return {
        "name": name, "purpose": purpose, "p_s_delta_b_gamma_q": p,
        "basic_probability_region": True,
        "old_Valid_region": delta < gamma and kc > 1,
        "kc": kc, "kb": kb, "k_star": k, "mu": mu, "rho": rho,
        "lambda0": lam0, "lambda1": lam1,
        "positive_potential_H_D": r,
        "attaining_external_selector": {"H": h_action, "D": d_action,
                                         "D_bloom_means_rejected": d_action == "bloom"},
        "full_request_rows_H_D": {"H": rows[False], "D": rows[True]},
        "row_super_eigen_gaps": row_gaps,
        "correlated_joint_request_gap": correlation_gap,
        "literal_checks": literal,
        "stationary_expected_population_T0_to_T12": trajectories,
        "internal_programs": internal,
        "finite_dp": [{"T": T, "value_H_D": dp[T], "optimal_next_requests": decisions[T]}
                      for T in range(HORIZON + 1)],
        "paid_care_once_then_external_selector": {
            "first_repair_paid": 3, "first_request_cap": 6,
            "positive_weight_after_first_care": first_repair_weight,
            "expected_population_T1_to_T12": prefix_path,
            "same_optimal_growth_factor_by_written_bounds": rho,
        },
    }


def jsonable(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): jsonable(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [jsonable(v) for v in value]
    return value


def main():
    repo = locate_repository()
    source_hashes = {name: sha256(repo / SOURCE_RELATIVE / name) for name in SOURCE_SHA256}
    assert source_hashes == SOURCE_SHA256, "Bound source bytes changed"
    source = load_transaction_checker(repo)
    probes = [point_probe(source, *point) for point in POINTS]
    by_name = {p["name"]: p for p in probes}
    required = by_name["care_subcritical_global_supercritical"]
    assert required["finite_dp"][2]["value_H_D"][1] == F(279, 250)
    assert required["internal_programs"]["theta1"]["mean_population_from_D_T0_to_T12"][2] == F(549, 500)
    assert F(279, 250) - F(549, 500) == F(9, 500)
    critical = by_name["critical_bloom_advantage"]
    assert all(x == F(11, 12) for x in critical["internal_programs"]["theta1"]["mean_population_from_D_T0_to_T12"][1:])
    assert all(v["value_H_D"][1] == 1 for v in critical["finite_dp"])
    result = {
        "status": "passed",
        "bound_source_commit_as_supplied_by_coordinator": BASE_COMMIT_AS_SUPPLIED,
        "remote_git_identity_independently_checked_by_this_script": False,
        "source_sha256": source_hashes,
        "historical_transaction_checker": {"repository_relative_path": str(TRANSACTION_RELATIVE),
                                            "sha256": TRANSACTION_SHA256, "modified": False},
        "check_script_sha256": sha256(Path(__file__)),
        "point_count": len(probes), "requested_point_count": 5,
        "tested_horizons": list(range(HORIZON + 1)),
        "exact_arithmetic": "fractions.Fraction; no floating-point comparisons",
        "local_menu_cases_total": sum(p["literal_checks"]["local_menu_cases"] for p in probes),
        "internal_program_cases_total": sum(p["literal_checks"]["internal_program_cases"] for p in probes),
        "required_two_tick_counterexample": {
            "finite_optimum_from_D": F(279, 250), "fixed_theta1_from_D": F(549, 500),
            "difference": F(9, 500), "rho": F(61, 50),
        },
        "critical_counterexample": {
            "rho": F(1), "fixed_theta1_from_D_all_positive_T": F(11, 12),
            "reject_D_population_pathwise_all_T": F(1),
        },
        "probes": probes,
        "proof_status": {
            "finite_checks": "Exact at the listed points and horizons; complete local menu at each point.",
            "general_history_real_kernel_bounds": "Written row inequality, linearity, and finite-history induction; not established by enumerating policies.",
            "all_T_and_all_basic_parameters": "Written proof in BOUNDARY_REVIEW.md; finite numerical probes are only witnesses.",
            "new_Lean_proof_or_compilation": False,
            "empirical_validation": False,
            "old_Valid_or_frozen_source_modified": False,
        },
    }
    print(json.dumps(jsonable(result), indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
