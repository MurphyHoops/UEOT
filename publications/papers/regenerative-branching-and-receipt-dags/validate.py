#!/usr/bin/env python3
"""Validate standalone Master Edition, INFORMS MOR double-anonymous package,
99-entry bibliography parity, and live exact-rational recomputation of all
closed-form boundaries, 4-step standby-window witnesses, and certified DAG benchmarks.

Run `python3 validate.py --benchmark-timings` to measure standalone median wall-clock
times (over 5 runs) for untrusted memoized synthesis (`generate`) versus standalone
all-action rational certificate verification (`accept = certify + boundCheck`).
"""
from fractions import Fraction as Q
from pathlib import Path
import datetime
import hashlib
import json
import os
import platform
import re
import statistics
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
MOR_DIR = ROOT / "submissions" / "mor"
ENV = os.environ.copy()
ENV["PATH"] = ":".join([
    str(Path.home() / "Library/TinyTeX/bin/universal-darwin"),
    str(Path.home() / ".TinyTeX/bin/universal-darwin"),
    "/Library/TeX/texbin",
    "/opt/homebrew/bin",
    "/usr/local/bin",
    ENV.get("PATH", ""),
])


def sha(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


# --- 1. Live exact-rational dynamic program over sigma = (t, q, s, f, k) ---
ALL_ACTIONS = [
    None,
    (False, None),
    (True, None),
    (False, False),
    (False, True),
    (True, False),
    (True, True),
]
OBS_LIST = [(False, False), (False, True), (True, False), (True, True)]


def solve_dag(H, B0, tariff, price, discount, r_list, prior_list, goal=True):
    init_q = (not goal, None, False, True)
    init_st = (0, 0, 0, 0, init_q)

    def cap(a):
        return Q(0) if a is None else (Q(1) if a[1] is not None else Q(0))

    def effective(stopped, a):
        return (False, None) if (stopped or a is None) else a

    def normal_receipt(q, a):
        req_j, req_act = effective(q[2], a)
        sel = q[1] if req_j else q[0]
        if sel is None:
            return (False, False)
        post = sel if req_act is None else req_act
        return (post == goal, req_act is not None)

    def update_stat(st, a, o):
        elapsed, s, f, paid, q = st
        nr = normal_receipt(q, a)
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
        return (elapsed + 1, s + ds, f + df, paid + dp,
                (new_root, new_child, stopped or (a is None), False))

    memo = {}
    edges_count = 0

    def build(rem, st):
        nonlocal edges_count
        key = (rem, st)
        if key in memo:
            return memo[key]
        _, s, f, paid, q = st
        wallet = max(Q(0), B0 - paid * tariff)
        if rem == 0:
            memo[key] = {"val": Q(0), "act": None, "succ": {}}
            return memo[key]
        ws = [p * (r ** s) * ((1 - r) ** f) for r, p in zip(r_list, prior_list)]
        Z = sum(ws)
        pw = [w / Z for w in ws]
        legal = [a for a in ALL_ACTIONS if tariff * cap(a) <= wallet]
        best_val = None
        best_idx = None
        all_succ = {}
        for idx, a in enumerate(legal):
            nr = normal_receipt(q, a)
            qv = Q(0)
            asucc = []
            for o in OBS_LIST:
                m = sum(w * ((r if nr == o else Q(0)) + ((1 - r) if (False, False) == o else Q(0)))
                        for r, w in zip(r_list, pw))
                if m > 0:
                    edges_count += 1
                    nxt = update_stat(st, a, o)
                    ch = build(rem - 1, nxt)
                    rew = (Q(1) if o[0] else Q(0)) - price * (tariff if o[1] else Q(0))
                    qv += m * (rew + discount * ch["val"])
                    asucc.append((o, m, nxt))
            all_succ[idx] = asucc
            if best_val is None or qv > best_val:
                best_val = qv
                best_idx = idx
        memo[key] = {"val": best_val, "act": best_idx, "succ": all_succ}
        return memo[key]

    root = build(H, init_st)
    exec_vis = set()
    exec_edges = 0

    def walk(rem, st):
        nonlocal exec_edges
        k = (rem, st)
        if k in exec_vis:
            return
        exec_vis.add(k)
        if rem == 0:
            return
        nd = memo[k]
        for o, m, nxt in nd["succ"][nd["act"]]:
            exec_edges += 1
            walk(rem - 1, nxt)

    walk(H, init_st)

    stat_memo = {}

    def eval_metrics(rem, st, had_birth):
        k = (rem, st, had_birth)
        if k in stat_memo:
            return stat_memo[k]
        if rem == 0:
            return (Q(1) if had_birth else Q(0), Q(1) if st[3] == 2 else Q(0), Q(0), Q(0))
        nd = memo[(rem, st)]
        pb = pp2 = eb = ef = Q(0)
        for o, m, nxt in nd["succ"][nd["act"]]:
            cb, cp2, ceb, cef = eval_metrics(rem - 1, nxt, had_birth or o[0])
            pb += m * cb
            pp2 += m * cp2
            eb += m * ((Q(1) if o[0] else Q(0)) + ceb)
            ef += m * ((tariff if o[1] else Q(0)) + cef)
        stat_memo[k] = (pb, pp2, eb, ef)
        return stat_memo[k]

    m_out = eval_metrics(H, init_st, False)

    hist_memo = {}

    def count_hist(rem, st):
        k = (rem, st)
        if k in hist_memo:
            return hist_memo[k]
        if rem == 0:
            hist_memo[k] = 1
            return 1
        nd = memo[k]
        tot = sum(count_hist(rem - 1, nxt) for asucc in nd["succ"].values() for _, _, nxt in asucc)
        hist_memo[k] = tot
        return tot

    from math import comb
    M = int(B0 // tariff)
    reach_bound = 1 + 12 * sum(comb(t + 2, 2) * (min(M, t) + 1) for t in range(1, H + 1))
    max_den_bits = max(v["val"].denominator.bit_length() for v in memo.values())

    return {
        "val": root["val"],
        "cert_nodes": len(memo),
        "cert_edges": edges_count,
        "exec_nodes": len(exec_vis),
        "exec_edges": exec_edges,
        "legal_histories": count_hist(H, init_st),
        "reachable_bound": reach_bound,
        "quartic_bound": 24 * ((H + 1) ** 4),
        "max_denom_bits": max_den_bits,
        "p_birth_ge_1": m_out[0],
        "p_paid_2": m_out[1],
        "e_births": m_out[2],
        "e_fees": m_out[3],
    }


def solve_diff_dag_h8():
    goal = True
    B0 = Q(2)
    c = Q(1)
    lam = Q(13, 10)
    d = Q(3, 4)
    r_list = [Q(1, 4), Q(3, 4)]
    init_q = (not goal, None, False, True)
    memo_diff = {}
    edges_diff = 0

    def cap(a):
        return Q(0) if a is None else (Q(1) if a[1] is not None else Q(0))

    def effective(stopped, a):
        return (False, None) if (stopped or a is None) else a

    def normal_receipt(q, a):
        req_j, req_act = effective(q[2], a)
        sel = q[1] if req_j else q[0]
        if sel is None:
            return (False, False)
        post = sel if req_act is None else req_act
        return (post == goal, req_act is not None)

    def build_diff(rem, st):
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
            nr = normal_receipt(q, a)
            inf = nr[0] or nr[1]
            qv = Q(0)
            for o in OBS_LIST:
                m = sum(w * ((r if nr == o else Q(0)) + ((1 - r) if (False, False) == o else Q(0)))
                        for r, w in zip(r_list, pw))
                if m > 0:
                    edges_diff += 1
                    ns = o[0] or o[1]
                    dd = (1 if ns else -1) if inf else 0
                    dp = 1 if o[1] else 0
                    root_b, child_b, stopped, fresh = q
                    req_j, _ = effective(stopped, a)
                    bit_b = goal if o[0] else (not goal)
                    new_root = root_b if req_j else bit_b
                    new_child = (goal if o[0] else None) if fresh else ((bit_b if child_b is not None else None) if req_j else child_b)
                    nxt = (diff + dd, paid + dp, (new_root, new_child, stopped or (a is None), False))
                    rew = (Q(1) if o[0] else Q(0)) - lam * (c if o[1] else Q(0))
                    qv += m * (rew + d * build_diff(rem - 1, nxt))
            if best is None or qv > best:
                best = qv
        memo_diff[key] = best
        return best

    val = build_diff(8, (0, 0, init_q))
    return val, len(memo_diff), edges_diff


def U1_poly(r, d, n):
    return sum((d ** (k - 1)) * (r ** k) for k in range(1, n + 1))


def U2_poly(r, d, n):
    if n == 0:
        return Q(0)
    return r + sum((d ** (k - 1)) * (r ** (k - 1)) * ((k - 1) - (k - 2) * r) for k in range(2, n + 1))


def single_wallet_formula_and_sc(H_tot, p, d, r_list, prior_list):
    if H_tot == 0:
        return Q(0), True
    H = H_tot - 1
    deltas = []
    for t in range(H + 1):
        rem = H - t
        deltas.append(sum(
            w * r * ((1 - r) ** t) * (1 - p + d * (U2_poly(r, d, rem) if t == 0 else U1_poly(r, d, rem)))
            for r, w in zip(r_list, prior_list)
        ))
    sc_ok = all(not (deltas[t] <= 0 and deltas[t + 1] > 0) for t in range(H))
    max_pref = max([Q(0)] + [sum((d ** s) * deltas[s] for s in range(m)) for m in range(1, H + 2)])
    pos_sum = sum((d ** t) * max(Q(0), deltas[t]) for t in range(H + 1))
    return pos_sum, (sc_ok and max_pref == pos_sum)


def generate_candidate_dag(H, B0, tariff, price, discount, r_list, prior_list, goal=True):
    """Mirror FiniteJointDecisionDAGGenerator.generate: bottom-up array with integer cursors."""
    init_q = (not goal, None, False, True)
    init_st = (0, 0, 0, 0, init_q)

    def cap(a):
        return Q(0) if a is None else (Q(1) if a[1] is not None else Q(0))

    def effective(stopped, a):
        return (False, None) if (stopped or a is None) else a

    def normal_receipt(q, a):
        req_j, req_act = effective(q[2], a)
        sel = q[1] if req_j else q[0]
        if sel is None:
            return (False, False)
        post = sel if req_act is None else req_act
        return (post == goal, req_act is not None)

    def update_stat(st, a, o):
        elapsed, s, f, paid, q = st
        nr = normal_receipt(q, a)
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
        return (elapsed + 1, s + ds, f + df, paid + dp,
                (new_root, new_child, stopped or (a is None), False))

    idx_memo = {}
    graph = []

    def build(rem, st):
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
            nr = normal_receipt(q, a)
            qv = Q(0)
            for o in OBS_LIST:
                m = sum(w * ((r if nr == o else Q(0)) + ((1 - r) if (False, False) == o else Q(0)))
                        for r, w in zip(r_list, pw))
                if m > 0:
                    nxt = update_stat(st, a, o)
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
    return {"graph": graph, "root_id": root_id}


def accept_candidate_dag(cand, H, B0, tariff, price, discount, r_list, prior_list,
                         goal=True, require_bound_check=True):
    """Mirror RegisterDecisionRepresentation.accept (= certify + boundCheck when require_bound_check=True)."""
    init_q = (not goal, None, False, True)
    init_st = (0, 0, 0, 0, init_q)
    graph = cand["graph"]
    root_id = cand["root_id"]
    n_rows = len(graph)
    if not (0 <= root_id < n_rows):
        return False
    if graph[root_id]["rem"] != H or graph[root_id]["st"] != init_st:
        return False

    def cap(a):
        return Q(0) if a is None else (Q(1) if a[1] is not None else Q(0))

    def effective(stopped, a):
        return (False, None) if (stopped or a is None) else a

    def normal_receipt(q, a):
        req_j, req_act = effective(q[2], a)
        sel = q[1] if req_j else q[0]
        if sel is None:
            return (False, False)
        post = sel if req_act is None else req_act
        return (post == goal, req_act is not None)

    def update_stat(st, a, o):
        elapsed, s, f, paid, q = st
        nr = normal_receipt(q, a)
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
        return (elapsed + 1, s + ds, f + df, paid + dp,
                (new_root, new_child, stopped or (a is None), False))

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
            nr = normal_receipt(q, a)
            qv = Q(0)
            for o in OBS_LIST:
                m = sum(w * ((r if nr == o else Q(0)) + ((1 - r) if (False, False) == o else Q(0)))
                        for r, w in zip(r_list, pw))
                if m > 0:
                    if (a, o) not in edges:
                        return False
                    ch_idx = edges[(a, o)]
                    if not (0 <= ch_idx < n_rows):
                        return False
                    ch = graph[ch_idx]
                    if ch["rem"] != rem - 1 or ch["st"] != update_stat(st, a, o):
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


BENCHMARK_SPECS = [
    ("1. Two-step (H=2, B0=1)", 2, Q(1), Q(1), Q(13, 10), Q(1, 2), [Q(1, 4), Q(3, 4)], [Q(1, 2), Q(1, 2)]),
    ("2. Backup (H=3, B0=1)", 3, Q(1), Q(1), Q(7, 4), Q(3, 4), [Q(1, 4), Q(3, 4)], [Q(1, 2), Q(1, 2)]),
    ("3. Posterior (H=3, B0=1)", 3, Q(1), Q(1), Q(13, 10), Q(1, 2), [Q(1, 4), Q(3, 4)], [Q(1, 2), Q(1, 2)]),
    ("4. Feedback (H=4, B0=1)", 4, Q(1), Q(1), Q(37, 16), Q(3, 4), [Q(3, 4), Q(7, 8)], [Q(1, 2), Q(1, 2)]),
    ("5. Two-wallet (H=8, B0=2)", 8, Q(2), Q(1), Q(13, 10), Q(3, 4), [Q(1, 4), Q(3, 4)], [Q(1, 2), Q(1, 2)]),
]

if "--benchmark-timings" in sys.argv:
    reps = 5
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
    print(json.dumps({
        "repetitions": reps,
        "python": platform.python_version(),
        "platform": platform.platform(),
        "processor": platform.processor(),
        "benchmarks": rows,
    }, indent=2))
    sys.exit(0)


b1 = solve_dag(2, Q(1), Q(1), Q(13, 10), Q(1, 2), [Q(1, 4), Q(3, 4)], [Q(1, 2), Q(1, 2)])
b2 = solve_dag(3, Q(1), Q(1), Q(7, 4), Q(3, 4), [Q(1, 4), Q(3, 4)], [Q(1, 2), Q(1, 2)])
b3 = solve_dag(3, Q(1), Q(1), Q(13, 10), Q(1, 2), [Q(1, 4), Q(3, 4)], [Q(1, 2), Q(1, 2)])
b4 = solve_dag(4, Q(1), Q(1), Q(37, 16), Q(3, 4), [Q(3, 4), Q(7, 8)], [Q(1, 2), Q(1, 2)])
b5 = solve_dag(8, Q(2), Q(1), Q(13, 10), Q(3, 4), [Q(1, 4), Q(3, 4)], [Q(1, 2), Q(1, 2)])
diff_val, diff_nodes, diff_edges = solve_diff_dag_h8()

# Standalone accept = certify + boundCheck verification + negative boundary probes (Theorem 6)
accept_all_ok = all(
    accept_candidate_dag(
        generate_candidate_dag(H_b, B0_b, c_b, lam_b, d_b, rl_b, wl_b),
        H_b, B0_b, c_b, lam_b, d_b, rl_b, wl_b, require_bound_check=True,
    )
    for _, H_b, B0_b, c_b, lam_b, d_b, rl_b, wl_b in BENCHMARK_SPECS
)
cand_b1_tampered = generate_candidate_dag(2, Q(1), Q(1), Q(13, 10), Q(1, 2), [Q(1, 4), Q(3, 4)], [Q(1, 2), Q(1, 2)])
del cand_b1_tampered["graph"][cand_b1_tampered["root_id"]]["edges"][(None, (False, False))]
omitted_alt_rejected = not accept_candidate_dag(
    cand_b1_tampered, 2, Q(1), Q(1), Q(13, 10), Q(1, 2), [Q(1, 4), Q(3, 4)], [Q(1, 2), Q(1, 2)],
    require_bound_check=False,
)
cand_h0_padded = generate_candidate_dag(0, Q(1), Q(1), Q(13, 10), Q(1, 2), [Q(1, 4), Q(3, 4)], [Q(1, 2), Q(1, 2)])
for extra_t in range(1, 25):
    cand_h0_padded["graph"].append({
        "rem": 0, "st": (extra_t, 0, 0, 0, (False, None, False, True)),
        "val": Q(0), "act": None, "edges": {},
    })
h0_certify_vs_accept_ok = (
    len(cand_h0_padded["graph"]) == 25 > 24
    and accept_candidate_dag(
        cand_h0_padded, 0, Q(1), Q(1), Q(13, 10), Q(1, 2), [Q(1, 4), Q(3, 4)], [Q(1, 2), Q(1, 2)],
        require_bound_check=False,
    )
    and not accept_candidate_dag(
        cand_h0_padded, 0, Q(1), Q(1), Q(13, 10), Q(1, 2), [Q(1, 4), Q(3, 4)], [Q(1, 2), Q(1, 2)],
        require_bound_check=True,
    )
)

# Arbitrary-price single-wallet witness & sweep verification (Theorem 2 strengthened, c <= B0 < 2c)
wit_p32 = solve_dag(3, Q(1), Q(1), Q(3, 2), Q(3, 4), [Q(1, 2)], [Q(1)])["val"]
wit_p54 = solve_dag(3, Q(1), Q(1), Q(5, 4), Q(3, 4), [Q(1, 2)], [Q(1)])["val"]
wit_p65 = solve_dag(3, Q(1), Q(1), Q(6, 5), Q(1, 2), [Q(1, 4), Q(3, 4)], [Q(1, 2), Q(1, 2)])["val"]

# 4-step standby-window comparison witness (H+1 = 4, r = 1/2, d = 3/4, p = 8/5)
r_sw4, d_sw4 = Q(1, 2), Q(3, 4)
p0_sw4 = 1 + d_sw4 * U2_poly(r_sw4, d_sw4, 3)
p1_sw4_actual = 1 + d_sw4 * U1_poly(r_sw4, d_sw4, 2)
p1_sw4_cf = 1 + d_sw4 * U2_poly(r_sw4, d_sw4, 2)
p1_sw4_gap = p1_sw4_cf - p1_sw4_actual
p_sw4_test = Q(8, 5)
delta0_sw4 = r_sw4 * (1 - p_sw4_test + d_sw4 * U2_poly(r_sw4, d_sw4, 3))
delta1_sw4_actual = r_sw4 * (1 - r_sw4) * (1 - p_sw4_test + d_sw4 * U1_poly(r_sw4, d_sw4, 2))
delta1_sw4_cf = r_sw4 * (1 - r_sw4) * (1 - p_sw4_test + d_sw4 * U2_poly(r_sw4, d_sw4, 2))
v4_sw4_actual = solve_dag(4, Q(1), Q(1), p_sw4_test, d_sw4, [r_sw4], [Q(1)])["val"]
v4_sw4_cf = delta0_sw4 + d_sw4 * max(Q(0), delta1_sw4_cf)

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
                v_dp = solve_dag(h_tot, Q(1), Q(1), pv, dv, rl, wl)["val"]
                sw_checked += 1
                if (not sc) or (v_fm != v_dp):
                    sw_ok = False

subtwo_wallet_ok = all(
    solve_dag(h_tot, b_sub, Q(1), pv, Q(3, 4), [Q(1, 4), Q(3, 4)], [Q(1, 2), Q(1, 2)])["val"]
    == solve_dag(h_tot, Q(1), Q(1), pv, Q(3, 4), [Q(1, 4), Q(3, 4)], [Q(1, 2), Q(1, 2)])["val"]
    for h_tot in [1, 2, 3, 4]
    for b_sub in [Q(3, 2), Q(19, 10)]
    for pv in [Q(1, 2), Q(6, 5), Q(13, 10), Q(8, 5)]
)

# Exact analytical witness checks (Theorems 2-5)
mu1 = Q(1, 2)
mu2 = Q(5, 16)
mu3 = Q(7, 32)
redraw_two = mu1 * (1 - Q(13, 10)) + Q(1, 2) * (mu1 ** 2)
var_premium = b1["val"] - redraw_two
p_prior_thresh = 1 + Q(1, 2) * (mu2 / mu1)
p_fault_thresh = 1 + Q(1, 2) * ((mu2 - mu3) / (mu1 - mu2))
post_fault_retry = ((mu1 - mu2) / (1 - mu1)) * (1 - Q(13, 10)) + Q(1, 2) * ((mu2 - mu3) / (1 - mu1))
prior_freeze_three = b3["val"] + (1 - mu1) * Q(1, 2) * post_fault_retry
root_only_three = mu1 * (1 - Q(7, 4)) + Q(3, 4) * mu2 + Q(9, 16) * mu3

f_mu1 = Q(13, 16)
f_mu2 = Q(85, 128)
f_mu3 = Q(559, 1024)
f_mu4 = Q(3697, 8192)
open_four = f_mu1 * (1 - Q(37, 16)) + (Q(3, 4) + Q(9, 16)) * f_mu2 + Q(27, 64) * f_mu3
feedback_gap_four = Q(27, 64) * (f_mu3 - f_mu4)
feedback_post_subgame = Q(9, 16) * (f_mu3 - f_mu4) / f_mu1

from math import comb
cubic_lower_ok = all(
    solve_dag(h_c, Q(1), Q(1), Q(13, 10), Q(3, 4), [Q(1, 4), Q(3, 4)], [Q(1, 2), Q(1, 2)])["cert_nodes"] >= 1 + comb(h_c + 1, 3)
    and solve_dag(h_c, Q(0), Q(1), Q(13, 10), Q(3, 4), [Q(1, 4), Q(3, 4)], [Q(1, 2), Q(1, 2)])["cert_nodes"] == 2 * h_c + 1
    for h_c in range(0, 9)
)

mass_hA = Q(1, 2) * (Q(1, 4)**2 * Q(3, 4) + Q(3, 4)**2 * Q(1, 4))
mass_hB = Q(1, 2) * (Q(1, 4) * Q(3, 4) + Q(3, 4) * Q(1, 4))
post_hA_low = (Q(1, 2) * Q(1, 4)**2 * Q(3, 4)) / mass_hA
post_hB_low = (Q(1, 2) * Q(1, 4) * Q(3, 4)) / mass_hB
next_birth_hA = post_hA_low * Q(1, 4) + (1 - post_hA_low) * Q(3, 4)
next_birth_hB = post_hB_low * Q(1, 4) + (1 - post_hB_low) * Q(3, 4)

arithmetic_ok = (
    sw_ok and sw_checked == 1440 and subtwo_wallet_ok
    and accept_all_ok and omitted_alt_rejected and h0_certify_vs_accept_ok
    and p0_sw4 == Q(929, 512) and p1_sw4_actual == Q(97, 64) and p1_sw4_cf == Q(53, 32)
    and p1_sw4_gap == Q(9, 64) and p1_sw4_gap == (d_sw4 ** 2) * r_sw4 * (1 - r_sw4)
    and delta0_sw4 == Q(549, 5120) and delta1_sw4_actual == Q(-27, 1280) and delta1_sw4_cf == Q(9, 640)
    and v4_sw4_actual == Q(549, 5120) and v4_sw4_cf == Q(603, 5120)
    and wit_p32 == Q(5, 64) and wit_p54 == Q(29, 128) and wit_p65 == Q(89, 640)
    and b1["val"] == Q(1, 160) and b1["cert_nodes"] == 21 and b1["exec_nodes"] == 6
    and b1["legal_histories"] == 70 and b1["reachable_bound"] == 217
    and b2["val"] == Q(9, 256) and b2["cert_nodes"] == 52 and b2["exec_nodes"] == 11
    and b2["legal_histories"] == 502 and b2["reachable_bound"] == 457
    and b3["val"] == Q(27, 320) and b3["cert_nodes"] == 52 and b3["exec_nodes"] == 11
    and b3["legal_histories"] == 502 and b3["reachable_bound"] == 457
    and b4["val"] == Q(39525, 524288) and b4["cert_nodes"] == 104 and b4["exec_nodes"] == 16
    and b4["legal_histories"] == 3466 and b4["reachable_bound"] == 817
    and b5["val"] == Q(884450457, 1342177280)
    and b5["cert_nodes"] == 1661 and b5["cert_edges"] == 8221
    and b5["exec_nodes"] == 151 and b5["exec_edges"] == 182
    and b5["legal_histories"] == 23841395 and b5["reachable_bound"] == 5869
    and b5["max_denom_bits"] == 31
    and b5["cert_nodes"] <= b5["reachable_bound"] <= b5["quartic_bound"] == 157464
    and diff_val == b5["val"] and diff_nodes == 1020 and diff_edges == 5558
    and b5["p_birth_ge_1"] == Q(215, 256)
    and b5["p_paid_2"] == Q(1233, 4096)
    and b5["e_births"] == Q(57313, 16384)
    and b5["e_fees"] == Q(4673, 4096)
    and redraw_two == Q(-1, 40) and var_premium == Q(1, 32)
    and p_prior_thresh == Q(21, 16) and p_fault_thresh == Q(5, 4)
    and post_fault_retry == Q(-3, 160)
    and prior_freeze_three == Q(51, 640) and b3["val"] - prior_freeze_three == Q(3, 640)
    and root_only_three == Q(-9, 512)
    and open_four == Q(2325, 65536) and feedback_gap_four == Q(20925, 524288)
    and feedback_post_subgame == Q(6975, 106496) and Q(3, 4) * f_mu1 * feedback_post_subgame == feedback_gap_four
    and open_four + feedback_gap_four == b4["val"]
    and cubic_lower_ok
    and mass_hA == Q(3, 32) and mass_hB == Q(3, 16)
    and post_hA_low == Q(1, 4) and post_hB_low == Q(1, 2)
    and next_birth_hA == Q(5, 8) and next_birth_hB == Q(1, 2)
)

# --- 2. Editorial, standalone, and BibTeX parity checks ---
text = (ROOT / "manuscript.md").read_text(encoding="utf-8")
bib = (ROOT / "references.bib").read_text(encoding="utf-8")

abstract = text.split("abstract: |", 1)[1].split("keywords:", 1)[0].strip()
keywords_line = re.search(r'^keywords:\s*"([^"]+)"', text, re.M).group(1)
keywords = [k.strip() for k in keywords_line.split(";") if k.strip()]
body = text[text.index("# Introduction:"):text.index("# Appendix:")]
appendix = text[text.index("# Appendix:"):text.index("# Declarations")]

keys = re.findall(r"@\w+\{([^,\s]+),", bib)
cited = set(re.findall(r"(?<!\w)@([A-Za-z0-9_:-]+)", text))
missing = sorted(cited - set(keys))
unused = sorted(set(keys) - cited)
duplicates = sorted({x for x in keys if keys.count(x) > 1})

forbidden_insider_tokens = [
    "UEOT", "qianOriginal", "qianPhilosophy", "qianMathematics",
    "ueotSource", "ueotGrowth", "ueotStatus", "GOD", "GOA",
    "P-ID", "CSX-", "N-TEL", "MurphyHoops",
]
insider_hits = [tok for tok in forbidden_insider_tokens if tok in text or tok in bib]

required = [
    "manuscript.md", "manuscript.tex", "manuscript.pdf", "references.bib",
    "ABSTRACT_ZH.md", "CLAIM_MATRIX.md", "README.md", "COPYRIGHT_AND_LICENSE.md",
    "BUILD_RECEIPT.json", "template.tex", "layout.lua", "generate_figures.py",
    "verify_standalone.py", "build.py", "validate.py",
    "figures/fig1_architecture_and_thresholds.pdf",
    "figures/fig2_informative_counts_and_sufficiency.pdf",
    "figures/fig3_dag_compression_and_scaling.pdf",
    "submissions/mor/mor_blinded_manuscript.pdf",
    "submissions/mor/mor_title_page.pdf",
    "submissions/mor/verify_standalone.py",
    "submissions/mor/generate_figures.py",
    "submissions/mor/cover_letter.md",
    "submissions/mor/SUBMISSION_GUIDE_AND_MANIFEST.md",
]
absent = [n for n in required if not (ROOT / n).is_file()]

build = json.loads((ROOT / "BUILD_RECEIPT.json").read_text(encoding="utf-8"))
hash_errors = [
    n for group in ["inputs", "outputs"]
    for n, h in build[group].items()
    if sha(ROOT / n) != h
]

(ROOT / "build").mkdir(exist_ok=True)
subprocess.run(["pdftotext", "-layout", "manuscript.pdf", "build/final-extracted.txt"], cwd=ROOT, env=ENV, check=True)
pdftext = (ROOT / "build/final-extracted.txt").read_text(errors="replace")
unresolved_pdf = "??" in pdftext or "[?]" in pdftext

info = subprocess.run(["pdfinfo", "manuscript.pdf"], cwd=ROOT, env=ENV, capture_output=True, text=True, check=True).stdout
pages = int(re.search(r"^Pages:\s+(\d+)", info, re.M).group(1))

# --- 3. Double-anonymous MOR submission package validation ---
subprocess.run(
    ["pdftotext", "-layout", "mor_blinded_manuscript.pdf", "build/mor-extracted.txt"],
    cwd=MOR_DIR, env=ENV, check=True,
)
mor_text = (MOR_DIR / "build" / "mor-extracted.txt").read_text(errors="replace")
mor_info = subprocess.run(
    ["pdfinfo", "mor_blinded_manuscript.pdf"],
    cwd=MOR_DIR, env=ENV, capture_output=True, text=True, check=True,
).stdout
mor_pages = int(re.search(r"^Pages:\s+(\d+)", mor_info, re.M).group(1))
mor_log = (MOR_DIR / "build" / "mor_blinded_manuscript.log").read_text(errors="replace")
mor_blg = (MOR_DIR / "build" / "mor_blinded_manuscript.blg").read_text(errors="replace")
master_blg = (ROOT / "build" / "manuscript.blg").read_text(errors="replace")
mor_tex_errors = re.findall(
    r"^!.*$|^.*(?:undefined citations|Citation .* undefined|Reference .* undefined|\(author\?\)).*$",
    mor_log, re.M,
)
mor_bib_warnings = re.findall(r"^Warning--.*$", mor_blg, re.M)
master_bib_warnings = re.findall(r"^Warning--.*$", master_blg, re.M)
mor_missing_glyphs = re.findall(r"^Missing character:.*$", mor_log, re.M)
mor_overfull = re.findall(r"^Overfull.*$", mor_log, re.M)

mor_page_splits = mor_text.split("\x0c")
ref_page_idx = next(
    (idx for idx, pg in enumerate(mor_page_splits) if re.search(r"^\s*(?:\d+\s+)?References\s*$", pg, re.M)),
    mor_pages,
)
mor_pages_excl_references = ref_page_idx  # 0-based index of first References page = count of preceding pages
abstract_on_page_2 = len(mor_page_splits) >= 2 and ("Abstract." in mor_page_splits[1])

mor_verify_txt = (MOR_DIR / "verify_standalone.py").read_text(encoding="utf-8") if (MOR_DIR / "verify_standalone.py").is_file() else ""
mor_genfig_txt = (MOR_DIR / "generate_figures.py").read_text(encoding="utf-8") if (MOR_DIR / "generate_figures.py").is_file() else ""
standalone_run = subprocess.run(
    [sys.executable, str(MOR_DIR / "verify_standalone.py")],
    cwd="/tmp", env=ENV, capture_output=True, text=True, check=True,
)
standalone_verifier_pass = json.loads(standalone_run.stdout).get("status") == "PASS"

anonymity_leaks = [
    tok for tok in [
        "Degui", "Qian", "MurphyHoops", "24433585", "24433584",
        "Single-authored", "sole author", "UEOT",
    ]
    if tok in mor_text or tok in mor_info or tok in mor_verify_txt or tok in mor_genfig_txt
]
ai_disclosure_in_blinded_manuscript = (
    "Generative AI and reproducibility disclosure" in mor_text
    and "Gemini 4 Carbon" in mor_text
    and "ChatGPT 6 Astra" in mor_text
    and "verify_standalone.py" in mor_text
)

mor_title_info = subprocess.run(
    ["pdfinfo", "mor_title_page.pdf"],
    cwd=MOR_DIR, env=ENV, capture_output=True, text=True, check=True,
).stdout
mor_title_pages = int(re.search(r"^Pages:\s+(\d+)", mor_title_info, re.M).group(1))

mor_record = {
    "journal": "Mathematics of Operations Research (INFORMS)",
    "review_mode": "double-anonymous (two-file split: mor_title_page.pdf + mor_blinded_manuscript.pdf)",
    "status": "PASS" if (
        not anonymity_leaks and ai_disclosure_in_blinded_manuscript and standalone_verifier_pass
        and mor_title_pages == 1
        and not mor_tex_errors and not mor_bib_warnings
        and not mor_missing_glyphs and not mor_overfull
        and abstract_on_page_2 and mor_pages_excl_references <= 40
        and 100 <= len(abstract.split()) <= 150
        and "$" not in abstract and "@" not in abstract and 3 <= len(keywords) <= 5
    ) else "FAIL",
    "abstract_words": len(abstract.split()),
    "abstract_target": "<= 150 words (official INFORMS MOR limit), on Page 2 following blinded Title Page, 0 equations, 0 citations",
    "abstract_on_page_2": abstract_on_page_2,
    "equations_or_citations_in_abstract": ("$" in abstract) or ("@" in abstract),
    "keyword_count": len(keywords),
    "keyword_target": "3-5 keywords",
    "msc2020_present": "MSC 2020" in mor_text,
    "orms_present": "OR/MS" in mor_text,
    "ai_disclosure_in_blinded_manuscript": ai_disclosure_in_blinded_manuscript,
    "standalone_verifier_pass": standalone_verifier_pass,
    "title_page_pages": mor_title_pages,
    "pdf_pages": mor_pages,
    "pdf_pages_excl_references": mor_pages_excl_references,
    "page_ceiling_excl_references": 40,
    "bibliography_entries": len(keys),
    "bibtex_warnings": mor_bib_warnings,
    "anonymity_leaks": anonymity_leaks,
    "tex_errors": mor_tex_errors,
    "missing_glyphs": mor_missing_glyphs,
    "overfull_boxes": mor_overfull,
}
(MOR_DIR / "VALIDATION_MOR.json").write_text(json.dumps(mor_record, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

errors = []
if not 6500 <= len(body.split()) <= 12000:
    errors.append(f"Main body word count {len(body.split())} outside 6,500-12,000 target")
if not 100 <= len(abstract.split()) <= 150:
    errors.append(f"Abstract word count {len(abstract.split())} outside <= 150 MOR target")
if master_bib_warnings:
    errors.append(f"Master BibTeX warnings: {master_bib_warnings}")
if "$" in abstract or "@" in abstract:
    errors.append("Abstract contains equations or citations")
if not 3 <= len(keywords) <= 5:
    errors.append(f"Keyword count {len(keywords)} outside 3-5 MOR target")
if len(keys) < 75:
    errors.append("Bibliography has fewer than 75 external works")
if missing or unused or duplicates:
    errors.append(f"Citation-key mismatch: missing={missing}, unused={unused}, dup={duplicates}")
if insider_hits:
    errors.append(f"Non-standalone insider tokens found: {insider_hits}")
if absent:
    errors.append(f"Missing deliverables: {absent}")
if hash_errors:
    errors.append(f"Build hash mismatch: {hash_errors}")
if unresolved_pdf or build["undefined_references_or_tex_errors"] or build["missing_glyphs"] or build["overfull_boxes"]:
    errors.append("Master PDF/TeX validation issue")
if mor_record["status"] != "PASS":
    errors.append(f"MOR blinded package validation failed: {mor_record}")
if pages != build["pages"]:
    errors.append("Page count mismatch")
if not arithmetic_ok:
    errors.append("Live rational dynamic-programming arithmetic mismatch")

record = {
    "schema": "standalone-mor-editorial-validation/3",
    "version": "1.3",
    "checked_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "status": "PASS" if not errors else "FAIL",
    "errors": errors,
    "body_words": len(body.split()),
    "appendix_words": len(appendix.split()),
    "abstract_words": len(abstract.split()),
    "keyword_count": len(keywords),
    "full_markdown_words": len(text.split()),
    "bibliography_entries": len(keys),
    "cited_keys": len(cited),
    "external_scholarly_works": len(keys),
    "unpublished_internal_self_citations": 0,
    "insider_tokens_found": insider_hits,
    "missing_citations": missing,
    "unused_entries": unused,
    "duplicate_keys": duplicates,
    "missing_required_files": absent,
    "build_hash_mismatches": hash_errors,
    "pdf_pages": pages,
    "mor_blinded_pages": mor_pages,
    "mor_validation_status": mor_record["status"],
    "unresolved_markers_in_pdf": unresolved_pdf,
    "live_rational_benchmarks": {
        "two_step": {k: str(v) for k, v in b1.items()},
        "three_backup": {k: str(v) for k, v in b2.items()},
        "three_posterior": {k: str(v) for k, v in b3.items()},
        "four_feedback": {k: str(v) for k, v in b4.items()},
        "eight_two_wallet": {k: str(v) for k, v in b5.items()},
    },
    "printed_arithmetic_status": "PASS" if arithmetic_ok else "FAIL",
    "manuscript_sha256": sha(ROOT / "manuscript.md"),
    "pdf_sha256": sha(ROOT / "manuscript.pdf"),
}
(ROOT / "VALIDATION.json").write_text(json.dumps(record, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

sha_files = sorted([
    str(p.relative_to(ROOT))
    for p in ROOT.rglob("*")
    if p.is_file()
    and "build" not in p.parts
    and p.name not in {".gitignore", "SHA256SUMS", ".DS_Store"}
])
sha_lines = [f"{sha(ROOT / f)}  {f}" for f in sha_files]
(ROOT / "SHA256SUMS").write_text("\n".join(sha_lines) + "\n", encoding="utf-8")

print(json.dumps({
    k: record[k]
    for k in [
        "status", "errors", "abstract_words", "body_words", "appendix_words",
        "bibliography_entries", "unpublished_internal_self_citations",
        "pdf_pages", "mor_blinded_pages", "mor_validation_status",
    ]
}, indent=2))
sys.exit(bool(errors))
