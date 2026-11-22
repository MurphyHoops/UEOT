#!/usr/bin/env python3
"""Standalone, zero-dependency exact numerical & algorithmic verifier for:
'Pure-Kernel Verified Controller Synthesis, Fixed-Sample Impossibility, and
Calibrated Post-Selection Risk under Partial Observation' (Version 1.2).

Uses ONLY the Python 3 standard library (`fractions`, `itertools`, `math`, `random`, `time`)
and reads/writes NO external files, so referees can run it from any directory:

    python3 verify_standalone.py

What this script verifies independently from scratch:
  1. Theorem 5 (3-state Lean witness, N=4096): Exact integer binomial summation
     (`math.comb` + `fractions.Fraction`, distinguished explicitly from decimal display)
     across theta in {1/4, 1/5, 17/100, 1/8} at fixed u=1/20 (N=4096) and scaled u=1/40 (N=16384).
  2. Section 4.3 (12-state, 3-action, T=4 non-trivial multi-abstraction benchmark):
     Synthesizes finite-memory support controllers across non-identity coarse sensors
     q_pool (|Y|=3), q_coarse (|Y|=4), q_fine (|Y|=5), and full-state q_id (|Y|=12);
     compares macro-reference vs. microscopic-reference verification paths and runtimes;
     and evaluates acceptance & abstention causes across 100 deterministic seeded datasets.
  3. Theorem 7 (Prepaid {S, G} fault-mechanism POMDP): Solves the full 7-action, 4-receipt
     rational POMDP dynamic program from scratch at H=2 and H=3, verifying V_S*(2)=V_G*(2)=13/16,
     V_S*(3)=41/32, V_G*(3)=5/4, V_dual*(3)=5/4, cross-payoffs 37/32 and 5/4, and R* = 3/128 < 1/32.
"""
from __future__ import annotations

from fractions import Fraction as Q
from typing import Optional
import itertools
import json
import math
import random
import sys
import time


# ===========================================================================
# PART 1: Exact Integer Binomial Verifier for 3-State Witness (Theorem 5)
# ===========================================================================
def exact_accepted_k_range(n: int, u: Q, tau: Q, beta: Q) -> tuple[int, int]:
    """Return exact [k_min, k_max] accepted by NoisyFiniteRiskOracleWitness."""
    ks = [
        k for k in range(n + 1)
        if ((1 - Q(k, n)) - 2 * u > tau) and ((1 - Q(k, n)) ** 2 + 2 * u <= beta)
    ]
    return min(ks), max(ks)


def exact_binomial_prob(n: int, theta: Q, k_lo: int, k_hi: int) -> Q:
    """Compute exact rational probability sum_{k=k_lo}^{k_hi} C(n,k) theta^k (1-theta)^(n-k)
    using exact arbitrary-precision Python integers (no floating-point logs).
    """
    if k_lo > k_hi:
        return Q(0)
    p_num, p_den = theta.numerator, theta.denominator
    q_num = p_den - p_num
    denom = p_den ** n
    term = math.comb(n, k_lo) * (p_num ** k_lo) * (q_num ** (n - k_lo))
    numer = term
    for k in range(k_lo, k_hi):
        term = (term * (n - k) * p_num) // ((k + 1) * q_num)
        numer += term
    assert term == math.comb(n, k_hi) * (p_num ** k_hi) * (q_num ** (n - k_hi))
    return Q(numer, denom)


def format_sci_from_fraction(val: Q, sig: int = 5) -> str:
    """Decimal display helper for an already-computed exact Fraction `val`."""
    if val == 0:
        return "0"
    # Use exact integer log10 scaling so even 10^-300 never underflows float!
    num, den = val.numerator, val.denominator
    exp10 = (len(str(num)) - 1) - (len(str(den)) - 1)
    # Adjust exp10 so 1 <= val * 10^(-exp10) < 10
    if exp10 >= 0:
        scaled = Q(num, den * (10 ** exp10))
    else:
        scaled = Q(num * (10 ** (-exp10)), den)
    while scaled >= 10:
        scaled /= 10
        exp10 += 1
    while scaled < 1:
        scaled *= 10
        exp10 -= 1
    digits = int(round(float(scaled) * (10 ** (sig - 1))))
    if digits >= 10 ** sig:
        digits //= 10
        exp10 += 1
    s = str(digits)
    mant = f"{s[0]}.{s[1:]}"
    return f"{mant}e{exp10:+d}"


def verify_part1_witness_binomial() -> dict:
    k_lo, k_hi = exact_accepted_k_range(4096, Q(1, 20), Q(1, 8), Q(7, 10))
    assert (k_lo, k_hi) == (924, 3174)

    # Boundary record k=820 inside good event G_{1/20} at theta=1/4
    assert abs(Q(820, 4096) - Q(1, 4)) == Q(51, 1024) <= Q(1, 20)
    k820_budget = (1 - Q(820, 4096)) ** 2 + Q(1, 10)
    assert Q(739, 1000) < k820_budget < Q(740, 1000)

    points_4096 = {}
    for label, th in [
        ("1/4", Q(1, 4)),
        ("1/5", Q(1, 5)),
        ("17/100", Q(17, 100)),
        ("1/8", Q(1, 8)),
    ]:
        p_exact = exact_binomial_prob(4096, th, k_lo, k_hi)
        true_risk = (1 - th) ** 2
        points_4096[label] = {
            "true_risk_exact": str(true_risk),
            "true_risk_decimal": round(float(true_risk), 6),
            "accept_prob_numerator_digits": len(str(p_exact.numerator)),
            "accept_prob_denominator_power": f"{th.denominator}^4096",
            "accept_prob_decimal_display": format_sci_from_fraction(p_exact, 5),
        }

    # Verify exact decimal displays match referee's independent integer-binomial check
    assert points_4096["1/4"]["accept_prob_decimal_display"] == "9.9988e-1"
    assert points_4096["1/5"]["accept_prob_decimal_display"] == "2.9491e-5"
    assert points_4096["17/100"]["accept_prob_decimal_display"] == "4.6100e-20"
    assert points_4096["1/8"]["accept_prob_decimal_display"] == "5.9748e-71"

    # Scaled u_N = 1/40 at N = 16384 (keeping N * u_N^2 = 512/50 = 10.24 and alpha = 48*e^(-512/25) fixed!)
    k16_lo, k16_hi = exact_accepted_k_range(16384, Q(1, 40), Q(1, 8), Q(7, 10))
    assert (k16_lo, k16_hi) == (3175, 13516)
    p_fifth_16384 = exact_binomial_prob(16384, Q(1, 5), k16_lo, k16_hi)
    dec_fifth_16384 = round(float(p_fifth_16384), 4)
    assert 0.975 <= dec_fifth_16384 <= 0.980

    return {
        "n4096_accepted_k_range": [k_lo, k_hi],
        "n4096_exact_binomial_curve": points_4096,
        "n16384_u0025_accepted_k_range": [k16_lo, k16_hi],
        "n16384_u0025_theta_one_fifth_accept_decimal": dec_fifth_16384,
    }


# ===========================================================================
# PART 2: 12-State, 3-Action, T=4 Multi-Abstraction Selection Benchmark
# ===========================================================================
STATES_12 = list(range(12))
SAFE_K_12 = set(range(11))
TARGET_G_12 = {8, 9, 10}
ACTIONS_12 = ["boost", "steady", "hazard"]


def build_12state_plant() -> dict[tuple[int, str], dict[int, Q]]:
    P: dict[tuple[int, str], dict[int, Q]] = {}
    for x in STATES_12:
        for a in ACTIONS_12:
            if x == 11:
                P[(x, a)] = {11: Q(1)}
            elif x in {9, 10}:
                if a == "hazard":
                    P[(x, a)] = {9: Q(4, 5), 11: Q(1, 5)}
                else:
                    P[(x, a)] = {9: Q(1, 2), 10: Q(1, 2)}
            elif x in {0, 1, 2, 3}:  # Stage S_A: both boost and steady safe
                eps = Q(1, 100) if x in {2, 3} else Q(0)
                if a == "boost":
                    stay = Q(3, 10) + eps
                    g_main = Q(3, 5) - eps
                    P[(x, a)] = {
                        0: stay / 4, 1: stay / 4, 2: stay / 4, 3: stay / 4,
                        8: Q(1, 10), 9: g_main / 2, 10: g_main / 2,
                    }
                elif a == "steady":
                    stay = Q(1, 2) + eps
                    g_main = Q(2, 5) - eps
                    P[(x, a)] = {
                        0: stay / 4, 1: stay / 4, 2: stay / 4, 3: stay / 4,
                        8: Q(1, 10), 9: g_main / 2, 10: g_main / 2,
                    }
                else:
                    P[(x, a)] = {0: Q(1, 2), 11: Q(1, 2)}
            elif x in {4, 5, 6, 7, 8}:  # Stage S_B ({4..7}) and quiet goal G_buf ({8})
                eps = Q(1, 100) if x in {6, 7, 8} else Q(0)
                if a == "boost":
                    P[(x, a)] = {4: Q(1, 4) + eps, 5: Q(1, 4) - eps, 11: Q(1, 2)}
                elif a == "steady":
                    stay = Q(2, 5) + eps
                    g_main = Q(12, 25) - eps
                    P[(x, a)] = {
                        4: stay / 4, 5: stay / 4, 6: stay / 4, 7: stay / 4,
                        8: Q(3, 25), 9: g_main / 2, 10: g_main / 2,
                    }
                else:
                    P[(x, a)] = {4: Q(1, 2), 11: Q(1, 2)}
    return P


def q_pool3(x: int) -> int:
    return 0 if x <= 8 else (1 if x <= 10 else 2)


def q_coarse4(x: int) -> int:
    return 0 if x <= 3 else (1 if x <= 8 else (2 if x <= 10 else 3))


def q_fine5(x: int) -> int:
    return 0 if x <= 3 else (1 if x <= 7 else (2 if x == 8 else (3 if x <= 10 else 4)))


def q_id12(x: int) -> int:
    return x


def synthesize_support_controller(P, p0, q):
    obs_vals = sorted({q(x) for x in STATES_12})
    I0 = {x for x, v in p0.items() if v > 0}
    cert = {
        (x, a): all(z in SAFE_K_12 for z, pr in P[(x, a)].items() if pr > 0)
        for x in STATES_12 for a in ACTIONS_12
    }
    fibers = {y: [x for x in STATES_12 if q(x) == y] for y in obs_vals}
    arena: set[frozenset[int]] = set()
    for xs in fibers.values():
        for r in range(1, len(xs) + 1):
            for comb in itertools.combinations(xs, r):
                arena.add(frozenset(comb))
    W = set(arena)
    while True:
        W_next = set()
        for s in W:
            for a in ACTIONS_12:
                if all(cert[(x, a)] for x in s):
                    if all(
                        (not nxt) or (nxt in W)
                        for y2 in obs_vals
                        for nxt in [frozenset(z for x in s for z, pr in P[(x, a)].items() if pr > 0 and q(z) == y2)]
                    ):
                        W_next.add(s)
                        break
        if W_next == W:
            break
        W = W_next
    init_supports = {y: frozenset(x for x in I0 if q(x) == y) for y in obs_vals}
    for s0 in init_supports.values():
        if s0 and s0 not in W:
            return None

    def pick_action(s: frozenset[int]) -> str:
        for a in ACTIONS_12:
            if all(cert[(x, a)] for x in s):
                if all(
                    (not nxt) or (nxt in W)
                    for y2 in obs_vals
                    for nxt in [frozenset(z for x in s for z, pr in P[(x, a)].items() if pr > 0 and q(z) == y2)]
                ):
                    return a
        return ACTIONS_12[0]

    def update_mem(s: frozenset[int], a: str, y2: int) -> frozenset[int]:
        nxt = frozenset(z for x in s for z, pr in P[(x, a)].items() if pr > 0 and q(z) == y2)
        return nxt if nxt else s

    reach = {s for s in init_supports.values() if s}
    queue = list(reach)
    while queue:
        cur = queue.pop()
        act = pick_action(cur)
        for y2 in obs_vals:
            nxt = frozenset(z for x in cur for z, pr in P[(x, act)].items() if pr > 0 and q(z) == y2)
            if nxt and nxt not in reach:
                reach.add(nxt)
                queue.append(nxt)
    return {
        "obs_vals": obs_vals,
        "reachable_mem_states": len(reach),
        "init": init_supports,
        "act": pick_action,
        "upd": update_mem,
    }


def tv_rows_12(r1: dict[int, Q], r2: dict[int, Q]) -> Q:
    return Q(1) - sum(min(r1.get(z, Q(0)), r2.get(z, Q(0))) for z in STATES_12)


def fiber_discrepancy_12(K_rows: dict[tuple[int, str], dict[int, Q]], q) -> Q:
    mx = Q(0)
    for x in STATES_12:
        for xp in STATES_12:
            if x < xp and q(x) == q(xp):
                for a in ACTIONS_12:
                    d = tv_rows_12(K_rows[(x, a)], K_rows[(xp, a)])
                    if d > mx:
                        mx = d
    return mx


def eval_micro_traj_risk(K_rows, p0, q, prog, T: int) -> tuple[Q, int, float]:
    t0 = time.perf_counter()
    total_bad = Q(0)
    traj_count = 0
    for x0, w0 in p0.items():
        if w0 == 0:
            continue
        m0 = prog["init"][q(x0)]

        def dfs(step: int, x: int, mem: frozenset[int], prob: Q):
            nonlocal total_bad, traj_count
            if step == T:
                traj_count += 1
                if x not in TARGET_G_12:
                    total_bad += prob
                return
            a = prog["act"](mem)
            for z, pz in K_rows[(x, a)].items():
                if pz > 0:
                    dfs(step + 1, z, prog["upd"](mem, a, q(z)), prob * pz)

        dfs(0, x0, m0, w0)
    dt_ms = (time.perf_counter() - t0) * 1000.0
    return total_bad, traj_count, dt_ms


def eval_macro_hist_risk(K_rows, p0, q, prog, bad_obs_set: set[int], T: int) -> tuple[Q, int, float]:
    t0 = time.perf_counter()
    obs_vals = prog["obs_vals"]
    rep = {y: min(x for x in STATES_12 if q(x) == y) for y in obs_vals}
    Kq = {}
    for y in obs_vals:
        rx = rep[y]
        for a in ACTIONS_12:
            row_y: dict[int, Q] = {}
            for z, pz in K_rows[(rx, a)].items():
                if pz > 0:
                    row_y[q(z)] = row_y.get(q(z), Q(0)) + pz
            Kq[(y, a)] = row_y
    p0_y: dict[int, Q] = {}
    for x, px in p0.items():
        if px > 0:
            p0_y[q(x)] = p0_y.get(q(x), Q(0)) + px
    total_bad = Q(0)
    hist_count = 0
    for y0, py0 in p0_y.items():
        m0 = prog["init"][y0]

        def dfs_y(step: int, y: int, mem: frozenset[int], prob: Q):
            nonlocal total_bad, hist_count
            if step == T:
                hist_count += 1
                if y in bad_obs_set:
                    total_bad += prob
                return
            a = prog["act"](mem)
            for y2, py2 in Kq[(y, a)].items():
                if py2 > 0:
                    dfs_y(step + 1, y2, prog["upd"](mem, a, y2), prob * py2)

        dfs_y(0, y0, m0, py0)
    dt_ms = (time.perf_counter() - t0) * 1000.0
    return total_bad, hist_count, dt_ms


def sample_12state_kernel(P, rng: random.Random, N: int) -> dict[tuple[int, str], dict[int, Q]]:
    K_hat: dict[tuple[int, str], dict[int, Q]] = {}
    for (x, a), row in P.items():
        zs = sorted(row.keys())
        cum = []
        acc = 0.0
        for z in zs:
            acc += float(row[z])
            cum.append(acc)
        counts = {z: 0 for z in zs}
        for _ in range(N):
            r = rng.random()
            for idx, c in enumerate(cum):
                if r <= c or idx == len(cum) - 1:
                    counts[zs[idx]] += 1
                    break
        K_hat[(x, a)] = {z: Q(c, N) for z, c in counts.items() if c > 0}
    return K_hat


def verify_part2_multi_abstraction_benchmark() -> dict:
    P = build_12state_plant()
    p0 = {x: (Q(1, 8) if x in range(8) else Q(0)) for x in STATES_12}
    T = 4

    candidates = [
        ("q_pool3", q_pool3, {1}),
        ("q_coarse4", q_coarse4, {2}),
        ("q_fine5", q_fine5, {2, 3}),
        ("q_id12", q_id12, {8, 9, 10}),
    ]
    structural_summary = {}
    progs = {}
    for name, q_fn, good_obs in candidates:
        prog = synthesize_support_controller(P, p0, q_fn)
        assert prog is not None
        progs[name] = prog
        bad_obs = set(prog["obs_vals"]) - good_obs
        disc = fiber_discrepancy_12(P, q_fn)
        true_r, micro_paths, micro_ms = eval_micro_traj_risk(P, p0, q_fn, prog, T)
        macro_r, macro_paths, macro_ms = eval_macro_hist_risk(P, p0, q_fn, prog, bad_obs, T)
        structural_summary[name] = {
            "sensor_classes": len(prog["obs_vals"]),
            "reachable_memory_states": prog["reachable_mem_states"],
            "true_fiber_discrepancy": str(disc),
            "true_risk_decimal": round(float(true_r), 5),
            "macro_ref_risk_decimal": round(float(macro_r), 5),
            "envelope_slack_decimal": round(float(macro_r - true_r), 5),
            "macro_positive_histories": macro_paths,
            "micro_positive_trajectories": micro_paths,
            "macro_eval_ms": round(macro_ms, 3),
            "micro_eval_ms": round(micro_ms, 3),
        }

    assert structural_summary["q_pool3"]["reachable_memory_states"] == 3
    assert structural_summary["q_coarse4"]["reachable_memory_states"] == 5
    assert structural_summary["q_fine5"]["reachable_memory_states"] == 4
    assert structural_summary["q_id12"]["reachable_memory_states"] == 11
    assert structural_summary["q_coarse4"]["macro_positive_histories"] == 20
    assert structural_summary["q_fine5"]["macro_positive_histories"] == 62
    assert structural_summary["q_coarse4"]["micro_positive_trajectories"] == 8248
    assert structural_summary["q_pool3"]["true_risk_decimal"] == 0.07836
    assert structural_summary["q_coarse4"]["true_risk_decimal"] == 0.04469
    assert structural_summary["q_fine5"]["true_risk_decimal"] == 0.04469

    # 100 deterministic seeded training datasets at N=2500, u=1/40 (0.025)
    rng = random.Random(20261122)
    N = 2500
    u = Q(1, 40)
    datasets = [sample_12state_kernel(P, rng, N) for _ in range(100)]

    def run_menu_trials(tau_val: Q, beta_val: Q) -> dict:
        res = {
            "menu_coarse_first_accept": 0,
            "menu_coarse_first_abstain_fiber_ambig": 0,
            "menu_coarse_first_abstain_env_slack": 0,
            "menu_coarse_first_abstain_u_margin": 0,
            "menu_fine_first_accept": 0,
            "menu_fine_first_abstain_fiber_ambig": 0,
            "menu_fine_first_abstain_u_margin": 0,
        }
        for K_hat in datasets:
            # q_pool3 is always cleanly rejected (delta_hat - 2u > tau)
            d0 = fiber_discrepancy_12(K_hat, q_pool3)
            assert d0 - 2 * u > tau_val

            d1 = fiber_discrepancy_12(K_hat, q_coarse4)
            r1, _, _ = eval_macro_hist_risk(K_hat, p0, q_coarse4, progs["q_coarse4"], {0, 1, 3}, T)
            b1 = min(Q(1), r1 + T * min(Q(1), u + d1))

            d2 = fiber_discrepancy_12(K_hat, q_fine5)
            r2, _, _ = eval_macro_hist_risk(K_hat, p0, q_fine5, progs["q_fine5"], {0, 1, 4}, T)
            b2 = min(Q(1), r2 + T * min(Q(1), u + d2))

            # Menu A: [q_pool3, q_coarse4, q_fine5]
            if d1 + 2 * u <= tau_val:
                if b1 <= beta_val:
                    res["menu_coarse_first_accept"] += 1
                else:
                    # Separate envelope-slack abstention (where q_fine5 would pass at same d1!) from u+delta margin
                    r1_no_env_slack = r2
                    if r1_no_env_slack + T * min(Q(1), u + d1) <= beta_val:
                        res["menu_coarse_first_abstain_env_slack"] += 1
                    else:
                        res["menu_coarse_first_abstain_u_margin"] += 1
            else:
                res["menu_coarse_first_abstain_fiber_ambig"] += 1

            # Menu B: [q_pool3, q_fine5]
            if d2 + 2 * u <= tau_val:
                if b2 <= beta_val:
                    res["menu_fine_first_accept"] += 1
                else:
                    res["menu_fine_first_abstain_u_margin"] += 1
            else:
                res["menu_fine_first_abstain_fiber_ambig"] += 1
        return res

    reg_generous = run_menu_trials(Q(1, 8), Q(19, 50))    # tau=0.125, beta=0.38
    reg_tight_beta = run_menu_trials(Q(1, 8), Q(17, 50))  # tau=0.125, beta=0.34
    reg_tight_tau = run_menu_trials(Q(19, 200), Q(19, 50))# tau=0.095, beta=0.38

    assert reg_generous["menu_coarse_first_accept"] == 96
    assert reg_generous["menu_fine_first_accept"] == 99
    assert reg_tight_beta["menu_coarse_first_accept"] == 56
    assert reg_tight_beta["menu_fine_first_accept"] == 75
    assert reg_tight_tau["menu_coarse_first_abstain_fiber_ambig"] == 51
    assert reg_tight_tau["menu_fine_first_abstain_fiber_ambig"] == 41

    # Also check Microscopic-Reference evaluation on first 10 datasets at tight beta=0.20
    micro_accept_10 = 0
    for K_hat in datasets[:10]:
        r_m, _, _ = eval_micro_traj_risk(K_hat, p0, q_coarse4, progs["q_coarse4"], T)
        if r_m + T * u <= Q(1, 5):
            micro_accept_10 += 1
    assert micro_accept_10 == 10

    return {
        "structural_summary": structural_summary,
        "trials_100_tau0125_beta038": reg_generous,
        "trials_100_tau0125_beta034": reg_tight_beta,
        "trials_100_tau0095_beta038": reg_tight_tau,
        "micro_reference_accept_at_beta020_first10": f"{micro_accept_10}/10",
    }


# ===========================================================================
# PART 3: Exact-Rational 7-Action POMDP Dynamic Program for Theorem 7
# ===========================================================================
Action7 = Optional[tuple[bool, Optional[bool]]]
Obs2 = tuple[bool, bool]
Store = tuple[Optional[bool], ...]
World = tuple[str, Store, bool]

ALL_ACTIONS_7: list[Action7] = [
    None,
    (False, None),
    (True, None),
    (False, False),
    (False, True),
    (True, False),
    (True, True),
]
ALL_OBS_4: list[Obs2] = [(False, False), (False, True), (True, False), (True, True)]


def action_cap(a: Action7) -> int:
    return 0 if a is None else (1 if a[1] is not None else 0)


def step_world(w: World, a: Action7, mode_normal: bool) -> tuple[Obs2, World]:
    mech, store, stopped = w
    idx, write_op = (0, None) if (stopped or a is None) else ((1 if a[0] else 0), a[1])
    lookup = store[idx] if idx < len(store) else None
    if lookup is None:
        obs: Obs2 = (False, False)
        u_store: Store = store + (None,)
    else:
        eff_bit = lookup if write_op is None else write_op
        post_bit = eff_bit if mode_normal else False
        child: Optional[bool] = True if (mode_normal and eff_bit is True) else None
        obs = (child is not None, bool(mode_normal and write_op is not None))
        u_store = store[:idx] + (post_bit,) + store[idx + 1:] + (child,)
    if mech == "G" and not mode_normal:
        u_store = tuple((False if slot is not None else None) for slot in u_store)
    return obs, (mech, u_store, stopped or (a is None))


def step_gain(o: Obs2) -> Q:
    return (Q(1) if o[0] else Q(0)) - (Q(1, 4) if o[1] else Q(0))


def solve_exact_pomdp(horizon: int, belief: dict[World, Q], bal: int):
    if horizon == 0:
        return Q(0), ("halt",)
    scored = []
    for a in [act for act in ALL_ACTIONS_7 if action_cap(act) <= bal]:
        total = Q(0)
        children = {}
        for o in ALL_OBS_4:
            unnorm: dict[World, Q] = {}
            obs_mass = Q(0)
            for w, prob in belief.items():
                for mode in (True, False):
                    o_out, w_next = step_world(w, a, mode)
                    if o_out == o:
                        mass = prob * Q(1, 2)
                        obs_mass += mass
                        unnorm[w_next] = unnorm.get(w_next, Q(0)) + mass
            next_bal = bal - (1 if o[1] else 0)
            if obs_mass == 0:
                children[o] = ("halt_zero", next_bal)
            else:
                post = {wn: m / obs_mass for wn, m in unnorm.items()}
                sub_val, sub_tree = solve_exact_pomdp(horizon - 1, post, next_bal)
                total += obs_mass * (step_gain(o) + sub_val)
                children[o] = sub_tree
        scored.append((total, ("node", a, children)))
    best_val, best_tree = scored[-1]
    for val, tree in reversed(scored[:-1]):
        if not (val < best_val):
            best_val, best_tree = val, tree
    return best_val, best_tree


def eval_policy_tree(tree, w: World) -> Q:
    if tree[0] == "halt":
        return Q(0)
    _, a, children = tree
    acc = Q(0)
    for mode in (True, False):
        o_out, w_next = step_world(w, a, mode)
        acc += Q(1, 2) * (step_gain(o_out) + eval_policy_tree(children[o_out], w_next))
    return acc


def verify_part3_pomdp_regret() -> dict:
    wS: World = ("S", (False,), False)
    wG: World = ("G", (False,), False)
    h2_S_val, h2_S_tree = solve_exact_pomdp(2, {wS: Q(1)}, 2)
    h2_G_val, _ = solve_exact_pomdp(2, {wG: Q(1)}, 2)
    assert h2_S_val == Q(13, 16) and h2_G_val == Q(13, 16)
    assert eval_policy_tree(h2_S_tree, wG) == Q(13, 16)

    v_S, tree_S = solve_exact_pomdp(3, {wS: Q(1)}, 2)
    v_G, tree_G = solve_exact_pomdp(3, {wG: Q(1)}, 2)
    v_dual, _ = solve_exact_pomdp(3, {wS: Q(3, 4), wG: Q(1, 4)}, 2)
    j_G_piS = eval_policy_tree(tree_S, wG)
    j_S_piG = eval_policy_tree(tree_G, wS)

    assert v_S == Q(41, 32) and v_G == Q(5, 4) and v_dual == Q(5, 4)
    assert j_G_piS == Q(37, 32) and j_S_piG == Q(5, 4)
    dual_lb = Q(3, 4) * v_S + Q(1, 4) * v_G - v_dual
    j_S_rho = Q(1, 4) * v_S + Q(3, 4) * j_S_piG
    j_G_rho = Q(1, 4) * j_G_piS + Q(3, 4) * v_G
    assert dual_lb == Q(3, 128)
    assert v_S - j_S_rho == Q(3, 128) and v_G - j_G_rho == Q(3, 128)

    return {
        "h2_common_opt_exact": str(h2_S_val),
        "h3_v_S_exact": str(v_S),
        "h3_v_G_exact": str(v_G),
        "h3_v_dual_exact": str(v_dual),
        "h3_cross_j_G_piS_exact": str(j_G_piS),
        "h3_cross_j_S_piG_exact": str(j_S_piG),
        "h3_minimax_regret_exact": str(dual_lb),
        "h3_deterministic_barrier_exact": str(v_S - v_G),
    }


def run_all_standalone_checks() -> dict:
    p1 = verify_part1_witness_binomial()
    p2 = verify_part2_multi_abstraction_benchmark()
    p3 = verify_part3_pomdp_regret()
    return {
        "status": "PASS",
        "part1_exact_integer_binomial_witness": p1,
        "part2_multi_abstraction_12state_benchmark": p2,
        "part3_exact_rational_7action_pomdp": p3,
    }


if __name__ == "__main__":
    summary = run_all_standalone_checks()
    print(json.dumps(summary, indent=2))
    sys.exit(0)
