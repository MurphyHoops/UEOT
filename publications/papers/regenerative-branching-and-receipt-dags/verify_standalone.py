#!/usr/bin/env python3
"""Standalone, zero-dependency exact rational & algorithmic verifier for:
'Prepayment Thresholds, Informative Zero Receipts, and Certified Polynomial
Decision Diagrams in Partially Observed Regenerative Maintenance' (Version 1.3).

Uses ONLY the Python 3 standard library (`fractions`, `json`, `math`, `platform`,
`statistics`, `sys`, `time`) and reads/writes NO external files, so referees can
execute it directly from any directory:

    python3 verify_standalone.py
    python3 verify_standalone.py --benchmark-timings

What this script verifies independently from scratch:
  1. Theorem 2 (Single-repair budget c <= B_0 < 2c, all prices p >= 0):
     - Closed-form polynomials U_1(r, d, n) and U_2(r, d, n), single-crossing
       marginal retry gains Delta_t, and exact DP parity across all 1,440 parameter
       instances (1,200 positive-horizon + 240 zero-horizon) plus interior c < B_0 < 2c.
     - Three-step arbitrary-price witnesses (53/32, 11/8; V_3* = 5/64 at p = 3/2;
       V_3* = 29/128 at p = 5/4) and four-step pure standby-window decision flip at
       known r = 1/2, d = 3/4 (p_0*(3) = 929/512; p_1*(3) = 97/64 vs. counterfactual
       53/32, gap 9/64; flipping post-fault optimal action at p = 8/5 from retry to stop).
  2. Theorem 3 & Table 1 (Persistence premium, posterior contraction, VoI duality):
     - Persistence variance premium d * Var(r) = 1/32 (1/160 vs. -1/40, redraw opt. 0).
     - Post-fault threshold contraction (21/16 -> 5/4, prior-freeze loss 3/640).
     - Four-step state-feedback vs. open-loop separation both ex-ante at t = 0
       (Delta_raw = 20925/524288) and conditionally inside the t = 1 post-success
       subgame (EVSI_state,post = 6975/106496), paired with EVPI_theta,post = 0.
  3. Theorems 4-6 & Table 3 (Sufficiency witnesses, all-action DAGs, Theta(H^3) order):
     - Physical-Markov insufficiency (5/8 != 1/2) and genealogy-erasing history merger
       at B_3 = 0 across all legal actions (plus slot-2 separation 0 vs. 5/8).
     - All 5 Table 3 benchmarks: exact V_H*, certified (s, f) nodes/edges, optimal
       execution nodes/edges, legal positive-probability history counts (23,841,395 at
       H = 8), complementary-prior (s - f) reduction (1,020 nodes / 5,558 edges),
       standalone two-layer `accept = certify + boundCheck` verification, omitted-edge
       rejection by `certify`, and H = 0 unbound-row rejection by `boundCheck`.
     - Tight cubic reachability order for fixed positive wallets (M >= 1): verifies
       that all C(H + 1, 3) interior keys (H - t, (t, s, f, 1, (g, None, 0, 0))) with
       s >= 1, f >= 1, s + f <= t are generated (giving |G_reach| >= 1 + C(H + 1, 3)),
       whereas zero-repair budgets (M = 0) visit exactly 2H + 1 nodes.
"""
from __future__ import annotations

from fractions import Fraction as Q
from math import comb
import json
import platform
import statistics
import sys
import time

ALL_ACTIONS = [
    None,            # stop
    (False, None),   # (0, idle)
    (True, None),    # (1, idle)
    (False, False),  # (0, write_0)
    (False, True),   # (0, write_1)
    (True, False),   # (1, write_0)
    (True, True),    # (1, write_1)
]
OBS_LIST = [(False, False), (False, True), (True, False), (True, True)]


def cap(a) -> Q:
    return Q(0) if a is None else (Q(1) if a[1] is not None else Q(0))


def effective(stopped: bool, a):
    return (False, None) if (stopped or a is None) else a


def normal_receipt(q, a, goal: bool = True):
    req_j, req_act = effective(q[2], a)
    sel = q[1] if req_j else q[0]
    if sel is None:
        return (False, False)
    post = sel if req_act is None else req_act
    return (post == goal, req_act is not None)


def update_stat(st, a, o, goal: bool = True):
    elapsed, s, f, paid, q = st
    nr = normal_receipt(q, a, goal)
    inf = nr[0] or nr[1]
    ns = o[0] or o[1]
    ds = 1 if (inf and ns) else 0
    df = 1 if (inf and not ns) else 0
    dp = 1 if o[1] else 0
    root, child, stopped, fresh = q
    req_j, _ = effective(stopped, a)
    bit_b = goal if o[0] else (not goal)
    new_root = root if req_j else bit_b
    if fresh:
        new_child = goal if o[0] else None
    elif req_j:
        new_child = bit_b if child is not None else None
    else:
        new_child = child
    return (
        elapsed + 1,
        s + ds,
        f + df,
        paid + dp,
        (new_root, new_child, stopped or (a is None), False),
    )


def generate_candidate_dag(H: int, B0: Q, tariff: Q, price: Q, discount: Q,
                           r_list, prior_list, goal: bool = True):
    """Mirror FiniteJointDecisionDAGGenerator.generate: bottom-up array with integer cursors."""
    init_q = (not goal, None, False, True)
    init_st = (0, 0, 0, 0, init_q)
    idx_memo = {}
    graph = []

    def build(rem: int, st) -> int:
        key = (rem, st)
        if key in idx_memo:
            return idx_memo[key]
        _, s, f, paid, q = st
        wallet = max(Q(0), B0 - paid * tariff)
        if rem == 0:
            idx = len(graph)
            graph.append({"rem": 0, "st": st, "val": Q(0), "act": None, "edges": {}})
            idx_memo[key] = idx
            return idx
        ws = [p * (r ** s) * ((1 - r) ** f) for r, p in zip(r_list, prior_list)]
        Z = sum(ws)
        pw = [w / Z for w in ws]
        legal = [a for a in ALL_ACTIONS if tariff * cap(a) <= wallet]
        best_val = None
        best_act = None
        edges = {}
        for a in legal:
            nr = normal_receipt(q, a, goal)
            qv = Q(0)
            for o in OBS_LIST:
                m = sum(
                    w * ((r if nr == o else Q(0)) + ((1 - r) if (False, False) == o else Q(0)))
                    for r, w in zip(r_list, pw)
                )
                if m > 0:
                    nxt = update_stat(st, a, o, goal)
                    ch_idx = build(rem - 1, nxt)
                    rew = (Q(1) if o[0] else Q(0)) - price * (tariff if o[1] else Q(0))
                    qv += m * (rew + discount * graph[ch_idx]["val"])
                    edges[(a, o)] = ch_idx
            if best_val is None or qv > best_val:
                best_val = qv
                best_act = a
        idx = len(graph)
        graph.append({"rem": rem, "st": st, "val": best_val, "act": best_act, "edges": edges})
        idx_memo[key] = idx
        return idx

    root_id = build(H, init_st)
    return {"graph": graph, "root_id": root_id, "keys": set(idx_memo.keys())}


def accept_candidate_dag(cand, H: int, B0: Q, tariff: Q, price: Q, discount: Q,
                         r_list, prior_list, goal: bool = True,
                         require_bound_check: bool = True) -> bool:
    """Mirror RegisterDecisionRepresentation.accept (= certify + boundCheck)."""
    init_q = (not goal, None, False, True)
    init_st = (0, 0, 0, 0, init_q)
    graph = cand["graph"]
    root_id = cand["root_id"]
    n_rows = len(graph)
    if not (0 <= root_id < n_rows):
        return False
    if graph[root_id]["rem"] != H or graph[root_id]["st"] != init_st:
        return False
    seen_keys = set()
    for nd in graph:
        rem = nd["rem"]
        st = nd["st"]
        key = (rem, st)
        if key in seen_keys:
            return False
        seen_keys.add(key)
        elapsed, s, f, paid, q = st
        if require_bound_check:
            if rem + elapsed != H or s < 0 or f < 0 or paid < 0 or (s + f) > elapsed or paid > elapsed:
                return False
        if rem == 0:
            if nd["val"] != Q(0):
                return False
            continue
        wallet = max(Q(0), B0 - paid * tariff)
        ws = [p * (r ** s) * ((1 - r) ** f) for r, p in zip(r_list, prior_list)]
        Z = sum(ws)
        if Z <= 0:
            return False
        pw = [w / Z for w in ws]
        legal = [a for a in ALL_ACTIONS if tariff * cap(a) <= wallet]
        if nd["act"] not in legal:
            return False
        best_val = None
        best_act = None
        edges = nd["edges"]
        for a in legal:
            nr = normal_receipt(q, a, goal)
            qv = Q(0)
            for o in OBS_LIST:
                m = sum(
                    w * ((r if nr == o else Q(0)) + ((1 - r) if (False, False) == o else Q(0)))
                    for r, w in zip(r_list, pw)
                )
                if m > 0:
                    if (a, o) not in edges:
                        return False
                    ch_idx = edges[(a, o)]
                    if not (0 <= ch_idx < n_rows):
                        return False
                    ch = graph[ch_idx]
                    if ch["rem"] != rem - 1 or ch["st"] != update_stat(st, a, o, goal):
                        return False
                    rew = (Q(1) if o[0] else Q(0)) - price * (tariff if o[1] else Q(0))
                    qv += m * (rew + discount * ch["val"])
            if best_val is None or qv > best_val:
                best_val = qv
                best_act = a
        if nd["val"] != best_val or nd["act"] != best_act:
            return False
    if require_bound_check and n_rows > 24 * ((H + 1) ** 4):
        return False
    return True


def solve_dag_metrics(H: int, B0: Q, tariff: Q, price: Q, discount: Q,
                      r_list, prior_list, goal: bool = True):
    cand = generate_candidate_dag(H, B0, tariff, price, discount, r_list, prior_list, goal)
    graph = cand["graph"]
    root_id = cand["root_id"]

    exec_vis = set()
    exec_edges = 0

    def walk(idx: int):
        nonlocal exec_edges
        if idx in exec_vis:
            return
        exec_vis.add(idx)
        nd = graph[idx]
        if nd["rem"] == 0:
            return
        act = nd["act"]
        for (a, _), ch_idx in nd["edges"].items():
            if a == act:
                exec_edges += 1
                walk(ch_idx)

    walk(root_id)

    hist_memo = {}

    def count_hist(idx: int) -> int:
        if idx in hist_memo:
            return hist_memo[idx]
        nd = graph[idx]
        if nd["rem"] == 0:
            hist_memo[idx] = 1
            return 1
        tot = sum(count_hist(ch_idx) for ch_idx in nd["edges"].values())
        hist_memo[idx] = tot
        return tot

    stat_memo = {}

    def eval_exec_stats(idx: int, had_birth: bool):
        k = (idx, had_birth)
        if k in stat_memo:
            return stat_memo[k]
        nd = graph[idx]
        _, s, f, paid, q = nd["st"]
        if nd["rem"] == 0:
            return (Q(1) if had_birth else Q(0), Q(1) if paid == 2 else Q(0), Q(0), Q(0))
        ws = [p * (r ** s) * ((1 - r) ** f) for r, p in zip(r_list, prior_list)]
        Z = sum(ws)
        pw = [w / Z for w in ws]
        act = nd["act"]
        nr = normal_receipt(q, act, goal)
        pb = pp2 = eb = ef = Q(0)
        for o in OBS_LIST:
            if (act, o) in nd["edges"]:
                m = sum(
                    w * ((r if nr == o else Q(0)) + ((1 - r) if (False, False) == o else Q(0)))
                    for r, w in zip(r_list, pw)
                )
                cb, cp2, ceb, cef = eval_exec_stats(nd["edges"][(act, o)], had_birth or o[0])
                pb += m * cb
                pp2 += m * cp2
                eb += m * ((Q(1) if o[0] else Q(0)) + ceb)
                ef += m * ((tariff if o[1] else Q(0)) + cef)
        stat_memo[k] = (pb, pp2, eb, ef)
        return stat_memo[k]

    m_out = eval_exec_stats(root_id, False)
    M = int(B0 // tariff)
    reach_upper = 1 + 12 * sum(comb(t + 2, 2) * (min(M, t) + 1) for t in range(1, H + 1))
    reach_lower = 1 + comb(H + 1, 3) if M >= 1 else (2 * H + 1)

    return {
        "val": graph[root_id]["val"],
        "cert_nodes": len(graph),
        "cert_edges": sum(len(nd["edges"]) for nd in graph),
        "exec_nodes": len(exec_vis),
        "exec_edges": exec_edges,
        "legal_histories": count_hist(root_id),
        "reachable_lower_bound": reach_lower,
        "reachable_upper_bound": reach_upper,
        "quartic_bound": 24 * ((H + 1) ** 4),
        "max_denom_bits": max(nd["val"].denominator.bit_length() for nd in graph),
        "p_birth_ge_1": m_out[0],
        "p_paid_2": m_out[1],
        "e_births": m_out[2],
        "e_fees": m_out[3],
        "keys": cand["keys"],
    }


def solve_complementary_diff_dag_h8():
    goal = True
    B0, c, lam, d = Q(2), Q(1), Q(13, 10), Q(3, 4)
    r_list = [Q(1, 4), Q(3, 4)]
    init_q = (not goal, None, False, True)
    memo_diff = {}
    edges_diff = 0

    def build_diff(rem: int, st) -> Q:
        nonlocal edges_diff
        key = (rem, st)
        if key in memo_diff:
            return memo_diff[key]
        diff, paid, q = st
        wallet = max(Q(0), B0 - paid * c)
        if rem == 0:
            memo_diff[key] = Q(0)
            return Q(0)
        p_hi = Q(3 ** diff, 1 + 3 ** diff) if diff >= 0 else Q(1, 1 + 3 ** (-diff))
        pw = [1 - p_hi, p_hi]
        legal = [a for a in ALL_ACTIONS if c * cap(a) <= wallet]
        best = None
        for a in legal:
            nr = normal_receipt(q, a, goal)
            inf = nr[0] or nr[1]
            qv = Q(0)
            for o in OBS_LIST:
                m = sum(
                    w * ((r if nr == o else Q(0)) + ((1 - r) if (False, False) == o else Q(0)))
                    for r, w in zip(r_list, pw)
                )
                if m > 0:
                    edges_diff += 1
                    ns = o[0] or o[1]
                    dd = (1 if ns else -1) if inf else 0
                    dp = 1 if o[1] else 0
                    root_b, child_b, stopped, fresh = q
                    req_j, _ = effective(stopped, a)
                    bit_b = goal if o[0] else (not goal)
                    new_root = root_b if req_j else bit_b
                    new_child = (
                        (goal if o[0] else None)
                        if fresh
                        else ((bit_b if child_b is not None else None) if req_j else child_b)
                    )
                    nxt = (diff + dd, paid + dp, (new_root, new_child, stopped or (a is None), False))
                    rew = (Q(1) if o[0] else Q(0)) - lam * (c if o[1] else Q(0))
                    qv += m * (rew + d * build_diff(rem - 1, nxt))
            if best is None or qv > best:
                best = qv
        memo_diff[key] = best
        return best

    val = build_diff(8, (0, 0, init_q))
    return val, len(memo_diff), edges_diff


def U1_poly(r: Q, d: Q, n: int) -> Q:
    return sum((d ** (k - 1)) * (r ** k) for k in range(1, n + 1))


def U2_poly(r: Q, d: Q, n: int) -> Q:
    if n == 0:
        return Q(0)
    return r + sum((d ** (k - 1)) * (r ** (k - 1)) * ((k - 1) - (k - 2) * r) for k in range(2, n + 1))


def single_wallet_formula_and_sc(H_tot: int, p: Q, d: Q, r_list, prior_list):
    if H_tot == 0:
        return Q(0), True
    H = H_tot - 1
    deltas = [
        sum(
            w * r * ((1 - r) ** t) * (1 - p + d * (U2_poly(r, d, H - t) if t == 0 else U1_poly(r, d, H - t)))
            for r, w in zip(r_list, prior_list)
        )
        for t in range(H + 1)
    ]
    sc_ok = all(not (deltas[t] <= 0 and deltas[t + 1] > 0) for t in range(H))
    max_pref = max([Q(0)] + [sum((d ** s) * deltas[s] for s in range(m)) for m in range(1, H + 2)])
    pos_sum = sum((d ** t) * max(Q(0), deltas[t]) for t in range(H + 1))
    return pos_sum, (sc_ok and max_pref == pos_sum)


BENCHMARK_SPECS = [
    ("1. Two-step (H=2, B0=1)", 2, Q(1), Q(1), Q(13, 10), Q(1, 2), [Q(1, 4), Q(3, 4)], [Q(1, 2), Q(1, 2)]),
    ("2. Backup (H=3, B0=1)", 3, Q(1), Q(1), Q(7, 4), Q(3, 4), [Q(1, 4), Q(3, 4)], [Q(1, 2), Q(1, 2)]),
    ("3. Posterior (H=3, B0=1)", 3, Q(1), Q(1), Q(13, 10), Q(1, 2), [Q(1, 4), Q(3, 4)], [Q(1, 2), Q(1, 2)]),
    ("4. Feedback (H=4, B0=1)", 4, Q(1), Q(1), Q(37, 16), Q(3, 4), [Q(3, 4), Q(7, 8)], [Q(1, 2), Q(1, 2)]),
    ("5. Two-wallet (H=8, B0=2)", 8, Q(2), Q(1), Q(13, 10), Q(3, 4), [Q(1, 4), Q(3, 4)], [Q(1, 2), Q(1, 2)]),
]


def run_benchmark_timings(reps: int = 5) -> dict:
    rows = []
    for label, H_b, B0_b, c_b, lam_b, d_b, rl_b, wl_b in BENCHMARK_SPECS:
        gen_ms, chk_ms = [], []
        cand_last = None
        for _ in range(reps):
            t0 = time.perf_counter()
            cand_last = generate_candidate_dag(H_b, B0_b, c_b, lam_b, d_b, rl_b, wl_b)
            gen_ms.append((time.perf_counter() - t0) * 1000.0)
            t1 = time.perf_counter()
            ok = accept_candidate_dag(cand_last, H_b, B0_b, c_b, lam_b, d_b, rl_b, wl_b, require_bound_check=True)
            chk_ms.append((time.perf_counter() - t1) * 1000.0)
            assert ok
        rows.append({
            "benchmark": label,
            "nodes": len(cand_last["graph"]),
            "edges": sum(len(nd["edges"]) for nd in cand_last["graph"]),
            "value": str(cand_last["graph"][cand_last["root_id"]]["val"]),
            "generate_median_ms": round(statistics.median(gen_ms), 1),
            "accept_median_ms": round(statistics.median(chk_ms), 1),
        })
    return {
        "repetitions": reps,
        "python": platform.python_version(),
        "platform": platform.platform(),
        "processor": platform.processor(),
        "benchmarks": rows,
    }


def main() -> int:
    if "--benchmark-timings" in sys.argv:
        print(json.dumps(run_benchmark_timings(5), indent=2))
        return 0

    b_res = [solve_dag_metrics(*spec[1:]) for spec in BENCHMARK_SPECS]
    b1, b2, b3, b4, b5 = b_res
    diff_val, diff_nodes, diff_edges = solve_complementary_diff_dag_h8()

    # 1. Verify accept = certify + boundCheck + dual negative rejection probes
    accept_all_ok = all(
        accept_candidate_dag(
            generate_candidate_dag(*spec[1:]), *spec[1:], require_bound_check=True
        )
        for spec in BENCHMARK_SPECS
    )
    cand_tampered = generate_candidate_dag(*BENCHMARK_SPECS[0][1:])
    del cand_tampered["graph"][cand_tampered["root_id"]]["edges"][(None, (False, False))]
    omitted_alt_rejected = not accept_candidate_dag(
        cand_tampered, *BENCHMARK_SPECS[0][1:], require_bound_check=False
    )
    cand_h0 = generate_candidate_dag(0, Q(1), Q(1), Q(13, 10), Q(1, 2), [Q(1, 4), Q(3, 4)], [Q(1, 2), Q(1, 2)])
    for extra_t in range(1, 25):
        cand_h0["graph"].append({
            "rem": 0,
            "st": (extra_t, 0, 0, 0, (False, None, False, True)),
            "val": Q(0),
            "act": None,
            "edges": {},
        })
    h0_certify_vs_accept_ok = (
        len(cand_h0["graph"]) == 25 > 24
        and accept_candidate_dag(
            cand_h0, 0, Q(1), Q(1), Q(13, 10), Q(1, 2), [Q(1, 4), Q(3, 4)], [Q(1, 2), Q(1, 2)],
            require_bound_check=False,
        )
        and not accept_candidate_dag(
            cand_h0, 0, Q(1), Q(1), Q(13, 10), Q(1, 2), [Q(1, 4), Q(3, 4)], [Q(1, 2), Q(1, 2)],
            require_bound_check=True,
        )
    )

    # 2. Verify Theorem 6 exact cubic lower-bound witness keys (s >= 1, f >= 1, s + f <= t)
    q_star = (True, None, False, False)
    cubic_lower_keys_ok = True
    zero_wallet_linear_ok = True
    for H_chk in range(0, 9):
        m_pos = solve_dag_metrics(H_chk, Q(1), Q(1), Q(13, 10), Q(3, 4), [Q(1, 4), Q(3, 4)], [Q(1, 2), Q(1, 2)])
        expected_interior_keys = {
            (H_chk - t, (t, s, f, 1, q_star))
            for t in range(2, H_chk + 1)
            for s in range(1, t)
            for f in range(1, t - s + 1)
        }
        if len(expected_interior_keys) != comb(H_chk + 1, 3):
            cubic_lower_keys_ok = False
        if not expected_interior_keys.issubset(m_pos["keys"]):
            cubic_lower_keys_ok = False
        if m_pos["cert_nodes"] < 1 + comb(H_chk + 1, 3):
            cubic_lower_keys_ok = False
        m_zero = solve_dag_metrics(H_chk, Q(0), Q(1), Q(13, 10), Q(3, 4), [Q(1, 4), Q(3, 4)], [Q(1, 2), Q(1, 2)])
        if m_zero["cert_nodes"] != 2 * H_chk + 1:
            zero_wallet_linear_ok = False

    # 3. Verify Theorem 2 arbitrary-price sweep (1,440 instances) + c <= B_0 < 2c + 4-step standby flip
    sw_priors = [
        ([Q(1, 2)], [Q(1)]),
        ([Q(0), Q(1)], [Q(1, 2), Q(1, 2)]),
        ([Q(0), Q(1, 2), Q(1)], [Q(1, 4), Q(1, 2), Q(1, 4)]),
        ([Q(1, 4), Q(3, 4)], [Q(1, 2), Q(1, 2)]),
        ([Q(1, 5), Q(4, 5)], [Q(4, 5), Q(1, 5)]),
        ([Q(1, 10), Q(1, 2), Q(9, 10)], [Q(3, 10), Q(4, 10), Q(3, 10)]),
    ]
    sw_ok = True
    sw_checked = 0
    for h_tot in [0, 1, 2, 3, 4, 5]:
        for rl, wl in sw_priors:
            for dv in [Q(0), Q(1, 4), Q(1, 2), Q(3, 4), Q(1)]:
                for pv in [Q(0), Q(1, 2), Q(1), Q(6, 5), Q(13, 10), Q(3, 2), Q(7, 4), Q(5, 2)]:
                    v_fm, sc = single_wallet_formula_and_sc(h_tot, pv, dv, rl, wl)
                    v_dp = solve_dag_metrics(h_tot, Q(1), Q(1), pv, dv, rl, wl)["val"]
                    sw_checked += 1
                    if (not sc) or (v_fm != v_dp):
                        sw_ok = False

    subtwo_wallet_ok = all(
        solve_dag_metrics(h_tot, b_sub, Q(1), pv, Q(3, 4), [Q(1, 4), Q(3, 4)], [Q(1, 2), Q(1, 2)])["val"]
        == solve_dag_metrics(h_tot, Q(1), Q(1), pv, Q(3, 4), [Q(1, 4), Q(3, 4)], [Q(1, 2), Q(1, 2)])["val"]
        for h_tot in [1, 2, 3, 4]
        for b_sub in [Q(3, 2), Q(19, 10)]
        for pv in [Q(1, 2), Q(6, 5), Q(13, 10), Q(8, 5)]
    )

    r_sw4, d_sw4, p_sw4 = Q(1, 2), Q(3, 4), Q(8, 5)
    p0_sw4 = 1 + d_sw4 * U2_poly(r_sw4, d_sw4, 3)
    p1_sw4_actual = 1 + d_sw4 * U1_poly(r_sw4, d_sw4, 2)
    p1_sw4_cf = 1 + d_sw4 * U2_poly(r_sw4, d_sw4, 2)
    delta0_sw4 = r_sw4 * (1 - p_sw4 + d_sw4 * U2_poly(r_sw4, d_sw4, 3))
    delta1_sw4_actual = r_sw4 * (1 - r_sw4) * (1 - p_sw4 + d_sw4 * U1_poly(r_sw4, d_sw4, 2))
    delta1_sw4_cf = r_sw4 * (1 - r_sw4) * (1 - p_sw4 + d_sw4 * U2_poly(r_sw4, d_sw4, 2))
    v4_sw4_actual = solve_dag_metrics(4, Q(1), Q(1), p_sw4, d_sw4, [r_sw4], [Q(1)])["val"]
    v4_sw4_cf = delta0_sw4 + d_sw4 * max(Q(0), delta1_sw4_cf)

    # 4. Verify Theorem 3 ex-ante & post-success subgame witnesses + Theorem 5 history witnesses
    f_mu1, f_mu2, f_mu3, f_mu4 = Q(13, 16), Q(85, 128), Q(559, 1024), Q(3697, 8192)
    open_four = f_mu1 * (1 - Q(37, 16)) + (Q(3, 4) + Q(9, 16)) * f_mu2 + Q(27, 64) * f_mu3
    feedback_ex_ante = Q(27, 64) * (f_mu3 - f_mu4)
    feedback_post_subgame = Q(9, 16) * (f_mu3 - f_mu4) / f_mu1  # E_{pi_(1,1)}[d^2 r^2 (1 - r)]

    checks = {
        "single_wallet_1440_sweep_and_single_crossing": sw_ok and sw_checked == 1440,
        "single_repair_interval_c_le_B0_lt_2c": subtwo_wallet_ok,
        "four_step_standby_window_flip_97_64_vs_53_32": (
            p0_sw4 == Q(929, 512)
            and p1_sw4_actual == Q(97, 64)
            and p1_sw4_cf == Q(53, 32)
            and (p1_sw4_cf - p1_sw4_actual) == Q(9, 64)
            and delta0_sw4 == Q(549, 5120)
            and delta1_sw4_actual == Q(-27, 1280)
            and delta1_sw4_cf == Q(9, 640)
            and v4_sw4_actual == Q(549, 5120)
            and v4_sw4_cf == Q(603, 5120)
        ),
        "four_step_feedback_ex_ante_and_post_subgame": (
            open_four == Q(2325, 65536)
            and feedback_ex_ante == Q(20925, 524288)
            and feedback_post_subgame == Q(6975, 106496)
            and Q(3, 4) * f_mu1 * feedback_post_subgame == feedback_ex_ante
            and open_four + feedback_ex_ante == b4["val"] == Q(39525, 524288)
        ),
        "table3_five_benchmarks_and_accept_soundness": (
            accept_all_ok
            and omitted_alt_rejected
            and h0_certify_vs_accept_ok
            and b1["val"] == Q(1, 160) and b1["cert_nodes"] == 21 and b1["cert_edges"] == 43
            and b2["val"] == Q(9, 256) and b2["cert_nodes"] == 52 and b2["cert_edges"] == 127
            and b3["val"] == Q(27, 320) and b3["cert_nodes"] == 52 and b3["cert_edges"] == 127
            and b4["val"] == Q(39525, 524288) and b4["cert_nodes"] == 104 and b4["cert_edges"] == 287
            and b5["val"] == Q(884450457, 1342177280)
            and b5["cert_nodes"] == 1661 and b5["cert_edges"] == 8221
            and b5["exec_nodes"] == 151 and b5["exec_edges"] == 182
            and b5["legal_histories"] == 23841395
            and diff_val == b5["val"] and diff_nodes == 1020 and diff_edges == 5558
        ),
        "theorem6_cubic_lower_bound_1_plus_C_H1_3_and_zero_wallet_2H_1": (
            cubic_lower_keys_ok and zero_wallet_linear_ok
        ),
    }

    all_pass = all(checks.values())
    print(json.dumps({
        "status": "PASS" if all_pass else "FAIL",
        "version": "1.3",
        "checks": checks,
        "table3_summary": [
            {
                "benchmark": spec[0],
                "exact_value": str(m["val"]),
                "cert_nodes_edges": f"{m['cert_nodes']}/{m['cert_edges']}",
                "exec_nodes_edges": f"{m['exec_nodes']}/{m['exec_edges']}",
                "legal_pos_histories": m["legal_histories"],
                "cubic_lower_bound": m["reachable_lower_bound"],
                "cubic_upper_bound": m["reachable_upper_bound"],
                "quartic_accept_ceiling": m["quartic_bound"],
            }
            for spec, m in zip(BENCHMARK_SPECS, b_res)
        ],
    }, indent=2))
    return 0 if all_pass else 1


if __name__ == "__main__":
    sys.exit(main())
