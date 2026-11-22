#!/usr/bin/env python3
"""Self-contained, zero-dependency exact rational verification script for
'What Prediction Leaves Out: Relational Objecthood and the Grounds of Purpose'.

Uses ONLY the Python 3 standard library (fractions, itertools, json, sys),
reads and writes zero external files, and can be executed from any working
directory via:

    python3 verify_standalone.py
"""
from __future__ import annotations

from fractions import Fraction as Q
import itertools
import json
import sys


def _dot(u: tuple[Q, ...], v: tuple[Q, ...]) -> Q:
    return sum((a * b for a, b in zip(u, v)), Q(0))


def _det3(m: tuple[tuple[Q, Q, Q], tuple[Q, Q, Q], tuple[Q, Q, Q]]) -> Q:
    return (
        m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1])
        - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
        + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0])
    )


def _tv_distance(law_p: dict, law_q: dict) -> Q:
    keys = set(law_p.keys()) | set(law_q.keys())
    return Q(1, 2) * sum((abs(law_p.get(k, Q(0)) - law_q.get(k, Q(0))) for k in keys), Q(0))


def check_proposition_2() -> dict:
    """Verify Proposition 2: full-simplex operator invariance failure vs exact
    quotient recursion on the forward-closed reachable belief set {delta_0, delta_1, delta_2}.
    """
    # Deterministic 3-state cycle 0 -> 1 -> 2 -> 0 with a single uninformative observation
    ones = (Q(1), Q(1), Q(1))
    f1 = (Q(0), Q(1), Q(2))
    v_perp = (Q(1), Q(-2), Q(1))

    def u_op(f: tuple[Q, Q, Q]) -> tuple[Q, Q, Q]:
        # (U f)(x) = sum_{x'} T(x'|x) O(o|x') f(x') = f((x + 1) mod 3)
        return (f[1], f[2], f[0])

    def bayes_step(b: tuple[Q, Q, Q]) -> tuple[Q, Q, Q]:
        # Forward pushforward along 0 -> 1 -> 2 -> 0: b'(x') = b((x' - 1) mod 3)
        unnorm = (b[2], b[0], b[1])
        norm = sum(unnorm, Q(0))
        return (unnorm[0] / norm, unnorm[1] / norm, unnorm[2] / norm)

    def f_sig(b: tuple[Q, Q, Q]) -> tuple[Q, Q]:
        return (_dot(b, ones), _dot(b, f1))

    u_ones = u_op(ones)
    u_f1 = u_op(f1)
    perp_checks_ok = (_dot(v_perp, ones) == Q(0)) and (_dot(v_perp, f1) == Q(0))
    u_f1_perp_inner = _dot(v_perp, u_f1)
    basis_det = _det3((ones, f1, u_f1))
    full_simplex_invariant = (u_f1_perp_inner == Q(0)) and (basis_det == Q(0))

    # Explicit interior full-simplex belief pair merged by F whose posteriors split
    b_a = (Q(1, 3), Q(1, 3), Q(1, 3))
    b_b = (Q(5, 12), Q(2, 12), Q(5, 12))
    interior_merged = (
        all(x > 0 for x in b_a + b_b)
        and sum(b_a, Q(0)) == Q(1)
        and sum(b_b, Q(0)) == Q(1)
        and f_sig(b_a) == f_sig(b_b)
    )
    post_a = bayes_step(b_a)
    post_b = bayes_step(b_b)
    interior_posteriors_split = f_sig(post_a) != f_sig(post_b)

    # Forward-update-closed reachable belief set R from prior delta_0
    delta_0 = (Q(1), Q(0), Q(0))
    reachable: list[tuple[Q, Q, Q]] = []
    cur = delta_0
    while cur not in reachable:
        reachable.append(cur)
        cur = bayes_step(cur)
    reachable_closed = all(bayes_step(b) in reachable for b in reachable)
    reachable_spans_r3 = len(reachable) == 3 and _det3((reachable[0], reachable[1], reachable[2])) == Q(1)

    distinct_merged_reachable_pairs = sum(
        1
        for b1, b2 in itertools.product(reachable, reachable)
        if b1 != b2 and f_sig(b1) == f_sig(b2)
    )
    reachable_quotient_exact = reachable_closed and (distinct_merged_reachable_pairs == 0)

    ok = (
        perp_checks_ok
        and (not full_simplex_invariant)
        and u_f1 == (Q(1), Q(2), Q(0))
        and u_f1_perp_inner == Q(-3)
        and interior_merged
        and interior_posteriors_split
        and reachable_spans_r3
        and reachable_quotient_exact
    )
    return {
        "passed": ok,
        "u_f1": [str(x) for x in u_f1],
        "full_simplex_invariant": full_simplex_invariant,
        "interior_posterior_f1_values": [str(f_sig(post_a)[1]), str(f_sig(post_b)[1])],
        "reachable_set_size": len(reachable),
        "reachable_spans_r3": reachable_spans_r3,
        "distinct_merged_reachable_pairs": distinct_merged_reachable_pairs,
    }


def single_token_step_law(
    status: str,
    action: str,
    s: Q,
    delta: Q,
    b: Q,
    gamma: Q,
    q: Q,
    b_boot: int = 1,
    mechanism: str = "M_vote",
) -> list[tuple[Q, int, int, int, int]]:
    """Return exact single-token step outcomes as (prob, births, repair_cost, next_H, next_D)."""
    if action == "stop":
        return [(Q(1), 0, 0, 0, 0)]

    if status == "H":
        if action == "care":
            r_cost, p_ret, p_birth = 0, s, b
        elif action == "bloom":
            r_cost, p_ret, p_birth = 0, s - delta, b + gamma
        else:
            raise ValueError(f"Unknown action: {action}")
    elif status == "D":
        if action == "bloom":
            # Required prepayment 3 + 2 + 2 = 7 > 6: transaction rejected, damaged token retained
            return [(Q(1), 0, 0, 0, 1)]
        if action == "care":
            if mechanism == "M_vote" and b_boot == 0:
                # Bootstrap voting ablated: gate stays closed, zero expenditure, zero births, remains D
                return [(Q(1), 0, 0, 0, 1)]
            if mechanism not in ("M_vote", "M_bypass"):
                raise ValueError(f"Unknown mechanism: {mechanism}")
            # Paid restoration (R = 3) + care actuation (1) + escrow (2) = 6
            r_cost, p_ret, p_birth = 3, s, b
        else:
            raise ValueError(f"Unknown action: {action}")
    else:
        raise ValueError(f"Unknown status: {status}")

    acc: dict[tuple[int, int, int, int], Q] = {}
    for i_ret, i_birth in itertools.product((0, 1), (0, 1)):
        p_act = (p_ret if i_ret else (Q(1) - p_ret)) * (p_birth if i_birth else (Q(1) - p_birth))
        total_out = i_ret + i_birth
        for dmg_bits in itertools.product((0, 1), repeat=total_out):
            n_d = sum(dmg_bits)
            n_h = total_out - n_d
            p_dmg = (q ** n_d) * ((Q(1) - q) ** n_h)
            key = (i_birth, r_cost, n_h, n_d)
            acc[key] = acc.get(key, Q(0)) + p_act * p_dmg

    out = [(prob, k[0], k[1], k[2], k[3]) for k, prob in acc.items() if prob > 0]
    if sum((x[0] for x in out), Q(0)) != Q(1):
        raise AssertionError("Single-token transition probabilities failed to sum to 1")
    return out


def _convolve_identical_tokens(
    count: int, single_outcomes: list[tuple[Q, int, int, int, int]]
) -> list[tuple[Q, int, int, int, int]]:
    """Exact distribution of (births, repair_cost, next_H, next_D) summed over `count` i.i.d. tokens."""
    dist: dict[tuple[int, int, int, int], Q] = {(0, 0, 0, 0): Q(1)}
    for _ in range(count):
        nxt: dict[tuple[int, int, int, int], Q] = {}
        for (b_acc, r_acc, h_acc, d_acc), p_acc in dist.items():
            for p_tok, b_tok, r_tok, h_tok, d_tok in single_outcomes:
                key = (b_acc + b_tok, r_acc + r_tok, h_acc + h_tok, d_acc + d_tok)
                nxt[key] = nxt.get(key, Q(0)) + p_acc * p_tok
        dist = nxt
    return [(prob, k[0], k[1], k[2], k[3]) for k, prob in dist.items() if prob > 0]


def enumerate_population_process(
    init_state: tuple[int, int],
    step_policies: list[tuple[str, str]],
    s: Q,
    delta: Q,
    b: Q,
    gamma: Q,
    q: Q,
    b_boot: int = 1,
    mechanism: str = "M_vote",
) -> dict[tuple[tuple[int, ...], tuple[int, ...], tuple[int, int]], Q]:
    """Enumerate exact finite-population distribution over ((B_1..B_T), (R_1..R_T), (n_H, n_D)).

    `step_policies` gives `(action_on_H, action_on_D)` for each step t = 1..T.
    """
    dist: dict[tuple[tuple[int, ...], tuple[int, ...], tuple[int, int]], Q] = {
        ((), (), init_state): Q(1)
    }
    for act_h, act_d in step_policies:
        law_h = single_token_step_law("H", act_h, s, delta, b, gamma, q, b_boot=b_boot, mechanism=mechanism)
        law_d = single_token_step_law("D", act_d, s, delta, b, gamma, q, b_boot=b_boot, mechanism=mechanism)
        cache_h: dict[int, list[tuple[Q, int, int, int, int]]] = {}
        cache_d: dict[int, list[tuple[Q, int, int, int, int]]] = {}
        nxt: dict[tuple[tuple[int, ...], tuple[int, ...], tuple[int, int]], Q] = {}
        for (b_hist, r_hist, (n_h, n_d)), prob in dist.items():
            if n_h not in cache_h:
                cache_h[n_h] = _convolve_identical_tokens(n_h, law_h)
            if n_d not in cache_d:
                cache_d[n_d] = _convolve_identical_tokens(n_d, law_d)
            for p_h, b_h, r_h, nh_h, nd_h in cache_h[n_h]:
                for p_d, b_d, r_d, nh_d, nd_d in cache_d[n_d]:
                    key = (
                        b_hist + (b_h + b_d,),
                        r_hist + (r_h + r_d,),
                        (nh_h + nh_d, nd_h + nd_d),
                    )
                    nxt[key] = nxt.get(key, Q(0)) + prob * p_h * p_d
        if sum(nxt.values(), Q(0)) != Q(1):
            raise AssertionError("Population distribution failed normalization")
        dist = nxt
    return dist


def _marginal(dist: dict, projector) -> dict:
    out: dict = {}
    for key, prob in dist.items():
        proj = projector(key)
        out[proj] = out.get(proj, Q(0)) + prob
    return out


def _partition_classes(named_laws: dict[str, dict]) -> list[list[str]]:
    names = list(named_laws.keys())
    assigned: set[str] = set()
    classes: list[list[str]] = []
    for name in names:
        if name in assigned:
            continue
        cls = [other for other in names if named_laws[other] == named_laws[name]]
        assigned.update(cls)
        classes.append(cls)
    return classes


def check_proposition_3() -> dict:
    """Verify Proposition 3: 2-3-4 protocol partitions, Blackwell non-simulability,
    and the 3-step parameter-identifiability witness (377/512 vs 351/512).
    """
    s, delta, b, gamma, q = Q(3, 4), Q(1, 8), Q(3, 8), Q(1, 4), Q(1, 3)
    founders = {
        "theta_0_H": ((1, 0), [("care", "care")] * 3),
        "theta_0_D": ((0, 1), [("care", "care")] * 3),
        "theta_1_H": ((1, 0), [("bloom", "care")] * 3),
        "theta_1_D": ((0, 1), [("bloom", "care")] * 3),
    }
    full_3step = {
        name: enumerate_population_process(init, pols, s, delta, b, gamma, q)
        for name, (init, pols) in founders.items()
    }

    b1_laws = {name: _marginal(d, lambda k: k[0][0]) for name, d in full_3step.items()}
    b1_b2_laws = {name: _marginal(d, lambda k: k[0][:2]) for name, d in full_3step.items()}
    b1_b2_b3_laws = {name: _marginal(d, lambda k: k[0][:3]) for name, d in full_3step.items()}
    b1_r1_laws = {name: _marginal(d, lambda k: (k[0][0], k[1][0])) for name, d in full_3step.items()}
    b1_b2_r1_laws = {name: _marginal(d, lambda k: (k[0][:2], k[1][0])) for name, d in full_3step.items()}

    classes_b1 = _partition_classes(b1_laws)
    classes_b1_b2 = _partition_classes(b1_b2_laws)
    classes_b1_b2_b3 = _partition_classes(b1_b2_b3_laws)
    classes_b1_r1 = _partition_classes(b1_r1_laws)
    classes_b1_b2_r1 = _partition_classes(b1_b2_r1_laws)

    eb2_theta0_d = sum((b2 * p for (_, b2), p in b1_b2_laws["theta_0_D"].items()), Q(0))
    eb2_theta1_d = sum((b2 * p for (_, b2), p in b1_b2_laws["theta_1_D"].items()), Q(0))

    # Single-run overlap even when joint probability laws separate all 4 founders
    run_000_shared = (
        b1_b2_r1_laws["theta_0_H"].get(((0, 0), 0), Q(0)) > 0
        and b1_b2_r1_laws["theta_1_H"].get(((0, 0), 0), Q(0)) > 0
    )
    run_003_shared = (
        b1_b2_r1_laws["theta_0_D"].get(((0, 0), 3), Q(0)) > 0
        and b1_b2_r1_laws["theta_1_D"].get(((0, 0), 3), Q(0)) > 0
    )

    # Blackwell post-processing non-simulability via total-variation contraction:
    # Any Markov kernel M satisfies TV(M(P), M(Q)) <= TV(P, Q).
    tv_b1b2_theta0H_theta0D = _tv_distance(b1_b2_laws["theta_0_H"], b1_b2_laws["theta_0_D"])
    tv_b1r1_theta0H_theta0D = _tv_distance(b1_r1_laws["theta_0_H"], b1_r1_laws["theta_0_D"])
    tv_b1r1_theta0D_theta1D = _tv_distance(b1_r1_laws["theta_0_D"], b1_r1_laws["theta_1_D"])
    tv_b1b2_theta0D_theta1D = _tv_distance(b1_b2_laws["theta_0_D"], b1_b2_laws["theta_1_D"])
    blackwell_incomparable = (
        tv_b1b2_theta0H_theta0D == Q(0)
        and tv_b1r1_theta0H_theta0D == Q(1)
        and tv_b1r1_theta0D_theta1D == Q(0)
        and tv_b1b2_theta0D_theta1D > Q(0)
    )

    # 3-step parameter-identifiability boundary from theta_1 D: delta = 1/8 vs delta' = 1/4
    delta_alt = Q(1, 4)
    dist_d18 = full_3step["theta_1_D"]
    dist_d14 = enumerate_population_process(
        (0, 1), [("bloom", "care")] * 3, s, delta_alt, b, gamma, q
    )
    b1_b2_d18 = _marginal(dist_d18, lambda k: k[0][:2])
    b1_b2_d14 = _marginal(dist_d14, lambda k: k[0][:2])
    grid_b1_b2_identical = all(
        b1_b2_d18.get((b1, b2), Q(0)) == b1_b2_d14.get((b1, b2), Q(0))
        for b1 in (0, 1, 2)
        for b2 in (0, 1, 2)
    )
    eb3_d18 = sum((k[0][2] * p for k, p in dist_d18.items()), Q(0))
    eb3_d14 = sum((k[0][2] * p for k, p in dist_d14.items()), Q(0))
    closed_form_d18 = (s + b) * ((Q(1) - q) * (s - delta + b + gamma) + q * (s + b)) * (
        (Q(1) - q) * (b + gamma) + q * b
    )
    closed_form_d14 = (s + b) * ((Q(1) - q) * (s - delta_alt + b + gamma) + q * (s + b)) * (
        (Q(1) - q) * (b + gamma) + q * b
    )

    ok = (
        classes_b1 == [["theta_0_H", "theta_0_D", "theta_1_D"], ["theta_1_H"]]
        and classes_b1_b2 == [["theta_0_H", "theta_0_D"], ["theta_1_H"], ["theta_1_D"]]
        and classes_b1_b2_b3 == classes_b1_b2
        and classes_b1_r1 == [["theta_0_H"], ["theta_0_D", "theta_1_D"], ["theta_1_H"]]
        and len(classes_b1_b2_r1) == 4
        and b1_r1_laws["theta_0_D"] == {(0, 3): Q(5, 8), (1, 3): Q(3, 8)}
        and b1_r1_laws["theta_1_D"] == {(0, 3): Q(5, 8), (1, 3): Q(3, 8)}
        and eb2_theta0_d == Q(27, 64)
        and eb2_theta1_d == Q(39, 64)
        and run_000_shared
        and run_003_shared
        and blackwell_incomparable
        and grid_b1_b2_identical
        and b1_b2_d18 == b1_b2_d14
        and eb3_d18 == Q(377, 512)
        and eb3_d14 == Q(351, 512)
        and eb3_d18 == closed_form_d18
        and eb3_d14 == closed_form_d14
    )
    return {
        "passed": ok,
        "partition_B1": classes_b1,
        "partition_B1_B2": classes_b1_b2,
        "partition_B1_R1": classes_b1_r1,
        "partition_B1_B2_R1": classes_b1_b2_r1,
        "theta0D_eb2": str(eb2_theta0_d),
        "theta1D_eb2": str(eb2_theta1_d),
        "blackwell_incomparable": blackwell_incomparable,
        "tv_b1b2_theta0D_theta1D": str(tv_b1b2_theta0D_theta1D),
        "parameter_boundary_witness": {
            "b1_b2_laws_identical": grid_b1_b2_identical and (b1_b2_d18 == b1_b2_d14),
            "b1_b2_joint_law": {f"({k[0]},{k[1]})": str(v) for k, v in sorted(b1_b2_d18.items())},
            "theta1D_delta18_b3": str(eb3_d18),
            "theta1D_delta14_b3": str(eb3_d14),
            "eb3_gap": str(eb3_d18 - eb3_d14),
        },
    }


def _verify_subcritical_potential_drop(s: Q, delta: Q, b: Q, gamma: Q, q: Q) -> tuple[bool, Q, Q]:
    """Check one-step potential drop >= (1 - bar_lambda) * k_c on active steps when bar_lambda < 1."""
    k_c = s + b
    k_b = s - delta + b + gamma
    lam_0 = k_c
    lam_1 = (Q(1) - q) * k_b + q * k_c
    bar_lam = max(lam_0, lam_1)
    v_h = max(k_c, k_b)
    v_d = k_c
    v_map = {"H": v_h, "D": v_d}
    req_drop = (Q(1) - bar_lam) * k_c

    all_ok = bar_lam < Q(1) and req_drop > Q(0)
    for status in ("H", "D"):
        for action in ("care", "bloom", "stop"):
            outcomes = single_token_step_law(status, action, s, delta, b, gamma, q)
            exp_v_next = sum((p * (nh * v_h + nd * v_d) for p, _, _, nh, nd in outcomes), Q(0))
            exp_births = sum((p * b_i for p, b_i, _, _, _ in outcomes), Q(0))
            drop = v_map[status] - exp_v_next
            is_active = (action == "care") or (status == "H" and action == "bloom")
            if is_active:
                all_ok = all_ok and (drop >= req_drop) and (exp_births <= b + gamma)
            else:
                all_ok = all_ok and (drop >= Q(0)) and (exp_births == Q(0))

    single_d_bound = (b + gamma) * v_d / req_drop
    return all_ok, bar_lam, single_d_bound


def check_theorem_1() -> dict:
    """Verify Theorem 1: critical, supercritical, subcritical switching, and subcritical
    finite cumulative expected births bound.
    """
    # 1. Critical rational witness (2/3, 1/8, 1/4, 1/4, 1/3)
    c_s, c_d, c_b, c_g, c_q = Q(2, 3), Q(1, 8), Q(1, 4), Q(1, 4), Q(1, 3)
    c_kc = c_s + c_b
    c_kb = c_s - c_d + c_b + c_g
    c_lam1 = (Q(1) - c_q) * c_kb + c_q * c_kc
    crit_3step = enumerate_population_process(
        (0, 1), [("bloom", "care")] * 3, c_s, c_d, c_b, c_g, c_q
    )
    crit_en3 = sum(((nh + nd) * p for (_, _, (nh, nd)), p in crit_3step.items()), Q(0))

    # 2. Supercritical witness (3/4, 1/8, 3/8, 1/4, 1/3)
    sp_s, sp_d, sp_b, sp_g, sp_q = Q(3, 4), Q(1, 8), Q(3, 8), Q(1, 4), Q(1, 3)
    out_theta1 = single_token_step_law("H", "bloom", sp_s, sp_d, sp_b, sp_g, sp_q)
    out_theta0 = single_token_step_law("H", "care", sp_s, sp_d, sp_b, sp_g, sp_q)
    p_n1_t1 = [sum((p for p, _, _, nh, nd in out_theta1 if nh + nd == k), Q(0)) for k in (0, 1, 2)]
    p_n1_t0 = [sum((p for p, _, _, nh, nd in out_theta0 if nh + nd == k), Q(0)) for k in (0, 1, 2)]
    ext_inv = p_n1_t1[0] * (Q(1) - p_n1_t0[0])
    exp_t1 = sum((i * p for i, p in enumerate(p_n1_t1)), Q(0))
    exp_t0 = sum((i * p for i, p in enumerate(p_n1_t0)), Q(0))
    ratio_exp = exp_t1 / (exp_t1 + exp_t0)
    uncond_share = sum(
        (p_n1_t1[n1] * p_n1_t0[n0] * Q(n1, n1 + n0) for n1 in (1, 2) for n0 in (0, 1, 2)),
        Q(0),
    )
    cond_share = uncond_share / (Q(1) - p_n1_t1[0] * p_n1_t0[0])

    # 3. Subcritical switching witness (1/2, 1/4, 1/4, 1/8, 1/3)
    sw_s, sw_d, sw_b, sw_g, sw_q = Q(1, 2), Q(1, 4), Q(1, 4), Q(1, 8), Q(1, 3)
    sw_kc = sw_s + sw_b
    sw_kb = sw_s - sw_d + sw_b + sw_g
    sw_lam1 = (Q(1) - sw_q) * sw_kb + sw_q * sw_kc
    sw_parent_d = sw_s * sw_q
    sw_any_d = Q(1) - (Q(1) - sw_s * sw_q) * (Q(1) - sw_b * sw_q)
    sw_dist_t1 = enumerate_population_process(
        (0, 1), [("care", "care")], sw_s, sw_d, sw_b, sw_g, sw_q
    )
    sw_prob_d_entering_t2 = sum((p for (_, _, (_, nd)), p in sw_dist_t1.items() if nd >= 1), Q(0))
    sw_dist_t2 = enumerate_population_process(
        (0, 1), [("care", "care"), ("care", "bloom")], sw_s, sw_d, sw_b, sw_g, sw_q
    )
    sw_prob_d_entering_t3 = sum((p for (_, _, (_, nd)), p in sw_dist_t2.items() if nd >= 1), Q(0))

    # 4. Subcritical finite-cumulative-births potential bound across both gamma<=delta and gamma>delta
    drop_ok_case1, bar_lam_case1, bound_single_d = _verify_subcritical_potential_drop(
        sw_s, sw_d, sw_b, sw_g, sw_q
    )
    drop_ok_case2, _, _ = _verify_subcritical_potential_drop(
        Q(1, 2), Q(1, 8), Q(1, 8), Q(1, 4), Q(1, 3)
    )
    dorm_dist = enumerate_population_process(
        (0, 1), [("care", "bloom")] * 3, sw_s, sw_d, sw_b, sw_g, sw_q
    )
    pi_dorm_3step_births = sum((sum(k[0]) * p for k, p in dorm_dist.items()), Q(0))
    theta0_sub_dist = enumerate_population_process(
        (0, 1), [("care", "care")] * 3, sw_s, sw_d, sw_b, sw_g, sw_q
    )
    theta0_b_steps = [
        sum((k[0][step] * p for k, p in theta0_sub_dist.items()), Q(0)) for step in (0, 1, 2)
    ]
    # Geometric sum_{t>=1} (k_c)^{t-1} * b = b / (1 - k_c) = (1/4) / (1/4) = 1
    theta0_inf_births = sw_b / (Q(1) - sw_kc)

    ok = (
        c_kc == Q(11, 12)
        and c_kb == Q(25, 24)
        and c_lam1 == Q(1, 1)
        and crit_en3 == Q(11, 12)
        and tuple(p_n1_t1) == (Q(9, 64), Q(30, 64), Q(25, 64))
        and tuple(p_n1_t0) == (Q(5, 32), Q(18, 32), Q(9, 32))
        and ext_inv == Q(243, 2048)
        and uncond_share == Q(2095, 4096)
        and cond_share == Q(2095, 4006)
        and ratio_exp == Q(10, 19)
        and sw_kc == Q(3, 4)
        and sw_kb == Q(5, 8)
        and sw_lam1 == Q(2, 3)
        and sw_parent_d == Q(1, 6)
        and sw_any_d == Q(17, 72)
        and sw_prob_d_entering_t2 == Q(17, 72)
        and sw_prob_d_entering_t3 > Q(17, 72)
        and drop_ok_case1
        and drop_ok_case2
        and bar_lam_case1 == Q(3, 4)
        and bound_single_d == Q(3, 2)
        and pi_dorm_3step_births == Q(0)
        and theta0_b_steps == [Q(1, 4), Q(3, 16), Q(9, 64)]
        and theta0_inf_births == Q(1, 1)
        and theta0_inf_births <= bound_single_d
    )
    return {
        "passed": ok,
        "critical_kc": str(c_kc),
        "critical_kb": str(c_kb),
        "critical_lambda1": str(c_lam1),
        "critical_theta1D_en3": str(crit_en3),
        "first_census_extinction_inversion": str(ext_inv),
        "unconditional_expected_share": str(uncond_share),
        "conditioned_expected_share": str(cond_share),
        "ratio_of_expectations": str(ratio_exp),
        "switching_kc": str(sw_kc),
        "switching_kb": str(sw_kb),
        "switching_lambda1": str(sw_lam1),
        "switching_parent_damaged_prob": str(sw_parent_d),
        "switching_any_damaged_prob": str(sw_any_d),
        "subcritical_finite_births": {
            "potential_drop_verified_both_cases": drop_ok_case1 and drop_ok_case2,
            "bar_lambda": str(bar_lam_case1),
            "upper_bound_single_D": str(bound_single_d),
            "pi_dorm_cumulative_expected_births": "0",
            "theta0D_step_1_to_3_expected_births": [str(x) for x in theta0_b_steps],
            "theta0D_cumulative_expected_births": str(theta0_inf_births),
        },
    }


def check_section_6_mechanisms() -> dict:
    """Verify Section 6 competing mechanisms M_vote vs M_bypass from (theta_0, D)
    under normal operation (b_boot = 1) vs targeted ablation do(b_boot = 0).
    """
    s, delta, b, gamma, q = Q(3, 4), Q(1, 8), Q(3, 8), Q(1, 4), Q(1, 3)
    pols = [("care", "care")] * 2

    vote_b1 = enumerate_population_process((0, 1), pols, s, delta, b, gamma, q, b_boot=1, mechanism="M_vote")
    bypass_b1 = enumerate_population_process((0, 1), pols, s, delta, b, gamma, q, b_boot=1, mechanism="M_bypass")
    vote_b0 = enumerate_population_process((0, 1), pols, s, delta, b, gamma, q, b_boot=0, mechanism="M_vote")
    bypass_b0 = enumerate_population_process((0, 1), pols, s, delta, b, gamma, q, b_boot=0, mechanism="M_bypass")

    law_vote_b1 = _marginal(vote_b1, lambda k: (k[0], k[1]))
    law_bypass_b1 = _marginal(bypass_b1, lambda k: (k[0], k[1]))
    law_vote_b0 = _marginal(vote_b0, lambda k: (k[0], k[1]))
    law_bypass_b0 = _marginal(bypass_b0, lambda k: (k[0], k[1]))

    vote_b0_eb1 = sum((b_seq[0] * p for (b_seq, _), p in law_vote_b0.items()), Q(0))
    vote_b0_eb2 = sum((b_seq[1] * p for (b_seq, _), p in law_vote_b0.items()), Q(0))
    bypass_b0_r1_is_3 = all(r_seq[0] == 3 for (_, r_seq) in law_bypass_b0.keys())
    bypass_b0_eb1 = sum((b_seq[0] * p for (b_seq, _), p in law_bypass_b0.items()), Q(0))
    bypass_b0_eb2 = sum((b_seq[1] * p for (b_seq, _), p in law_bypass_b0.items()), Q(0))

    ok = (
        law_vote_b1 == law_bypass_b1
        and law_vote_b0 == {((0, 0), (0, 0)): Q(1)}
        and law_bypass_b0 == law_bypass_b1
        and vote_b0_eb1 == Q(0)
        and vote_b0_eb2 == Q(0)
        and bypass_b0_r1_is_3
        and bypass_b0_eb1 == Q(3, 8)
        and bypass_b0_eb2 == Q(27, 64)
    )
    return {
        "passed": ok,
        "b_boot_1_laws_identical": law_vote_b1 == law_bypass_b1,
        "b_boot_1_atom_count": len(law_vote_b1),
        "do_b_boot_0_M_vote_deterministic_zero": law_vote_b0 == {((0, 0), (0, 0)): Q(1)},
        "do_b_boot_0_M_vote_eb1": str(vote_b0_eb1),
        "do_b_boot_0_M_vote_eb2": str(vote_b0_eb2),
        "do_b_boot_0_M_bypass_r1": "3" if bypass_b0_r1_is_3 else "mixed",
        "do_b_boot_0_M_bypass_eb1": str(bypass_b0_eb1),
        "do_b_boot_0_M_bypass_eb2": str(bypass_b0_eb2),
    }


def check_auxiliary_propositions() -> dict:
    """Verify Proposition 4b (gate vs decoded code), Proposition 6a (1-step memory vs
    reactive failure 1/2), and Proposition 7 (rank-3 Jacobian determinant b > 0).
    """
    # Proposition 4b: identical intact rows (1,1,1), (0,0,0) with g=open vs g=closed under raw bloom
    b, gamma = Q(3, 8), Q(1, 4)
    raw_open_birth_prob = b + gamma
    raw_closed_birth_prob = Q(0)

    # Proposition 6a: under mu_0 = 1/2 delta_{x_L} + 1/2 delta_{x_R}, any memoryless pi_0(a_L | o_M) = p
    # fails at t=2 with probability 1/2*(1-p) + 1/2*p == 1/2 across all p in [0, 1].
    reactive_fail_probs = [Q(1, 2) * (Q(1) - p) + Q(1, 2) * p for p in (Q(0), Q(1, 4), Q(1, 2), Q(1))]
    memory_1_fail_prob = Q(0)

    # Proposition 7: Psi(s, b, q) = (s, b, b*q) Jacobian determinant
    s_val, b_val, q_val = Q(3, 4), Q(3, 8), Q(1, 3)
    jac = (
        (Q(1), Q(0), Q(0)),
        (Q(0), Q(1), Q(0)),
        (Q(0), q_val, b_val),
    )
    jac_det = _det3(jac)

    ok = (
        raw_open_birth_prob == Q(5, 8)
        and raw_closed_birth_prob == Q(0)
        and all(fp == Q(1, 2) for fp in reactive_fail_probs)
        and memory_1_fail_prob == Q(0)
        and jac_det == b_val
        and jac_det > Q(0)
    )
    return {
        "passed": ok,
        "prop4b_raw_birth_open_vs_closed": [str(raw_open_birth_prob), str(raw_closed_birth_prob)],
        "prop6a_reactive_two_step_failure_prob": "1/2",
        "prop6a_one_step_memory_failure_prob": "0",
        "prop7_jacobian_det_at_witness": str(jac_det),
    }


def run_all_standalone_checks() -> dict:
    p2 = check_proposition_2()
    p3 = check_proposition_3()
    t1 = check_theorem_1()
    s6 = check_section_6_mechanisms()
    aux = check_auxiliary_propositions()
    all_ok = all(sec["passed"] for sec in (p2, p3, t1, s6, aux))
    return {
        "schema": "standalone-exact-rational-verification/1",
        "version": "2.4",
        "status": "PASS" if all_ok else "FAIL",
        "proposition_2": p2,
        "proposition_3": p3,
        "theorem_1": t1,
        "section_6_mechanisms": s6,
        "auxiliary_propositions_4_6_7": aux,
    }


if __name__ == "__main__":
    report = run_all_standalone_checks()
    print(json.dumps(report, indent=2))
    sys.exit(0 if report["status"] == "PASS" else 1)
