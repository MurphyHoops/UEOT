#!/usr/bin/env python3
"""Independent exact check of THIS returned policy and native execution.

Only Python's standard library is imported. Neither the production/native
adapter nor any supplied solver recursion is imported. The independent
transaction below uses dictionaries; the full-menu check propagates joint
UNNORMALIZED history masses and maximizes their remaining contribution.
Formal all-real-randomized bounds remain the responsibility of the Lean proof.
"""
from __future__ import annotations
import argparse
from collections import defaultdict
from copy import deepcopy
from fractions import Fraction as F
from functools import lru_cache
import hashlib
from itertools import product
import json
from pathlib import Path

ACTION = {"stop": None, "root_idle": (0, None), "child1_idle": (1, None),
          "root_write_false": (0, False), "root_write_true": (0, True),
          "child1_write_false": (1, False), "child1_write_true": (1, True)}
NAMES = tuple(ACTION)
OBS = tuple(product((False, True), repeat=2))


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def dictionary_transaction(store, request, normal, label):
    after = deepcopy(store)
    clock, parent = len(store), request[0]
    obj = store[parent] if parent < len(store) else None
    if obj is None:
        return after + [None], [False, False], F(0), None
    bit = (obj["physical"] if request[1] is None else request[1]) if normal else False
    birth = normal and bit == obj["program"]
    fee = F(int(normal and request[1] is not None))
    after[parent]["physical"] = bit
    after[parent]["clock"] = clock + 1
    child = {"physical": bit, "program": obj["program"],
             "history": obj["history"] + [label],
             "identity": obj["identity"] + [[clock, label]], "clock": 0} if birth else None
    after.append(child)
    record = {"tick": clock, "request_parent": parent, "executed": normal,
              "mode": normal, "label": label, "parent_identity": obj["identity"],
              "parent_clock": clock + 1, "child_slot": clock if birth else None,
              "child_identity": child["identity"] if child else None,
              "expenditure": str(fee)}
    return after, [bool(birth), bool(fee)], fee, record


def check_trace(trace, policy, packed):
    seed, mechanism = trace["seed"], trace["mechanism"]
    rows = policy["components"]["S" if seed == 0 else "G"]["rows"]
    table = {tuple(map(tuple, row["history"])): row["action"] for row in rows}
    store = [{"physical": False, "program": True, "history": [],
              "identity": [[0, False]], "clock": 0}]
    balance, cost, payoff, births, stopped = F(2), F(0), F(0), 0, False
    history, names, receipts = (), [], []
    assert len(trace["world_events"]) == len(trace["ledger"]) == 3
    for t in range(3):
        name = table[history]
        requested = ACTION[name]
        cap = F(requested is not None and requested[1] is not None)
        assert cap <= balance, "unaffordable request, even if upcoming fault is free"
        request = (0, None) if stopped or requested is None else requested
        stopped = stopped or requested is None
        normal, label = trace["modes"][t], trace["labels"][t]
        event, ledger = trace["world_events"][t], trace["ledger"][t]
        assert event["store_before"] == store
        assert event["source_clock"] == len(store) and event["tick"] == t
        assert event["request"] == list(request)
        assert (event["mode"], event["label"]) == (normal, label)
        after, receipt, fee, record = dictionary_transaction(store, request, normal, label)
        assert event["transaction"] == record
        assert event["store_after_transaction"] == after
        damaged = []
        if mechanism == "G" and not normal:
            damaged = [j for j, obj in enumerate(after) if obj is not None]
            for obj in after:
                if obj is not None:
                    obj["physical"] = False
        assert event["common_fault_damaged_slots"] == damaged
        assert event["store_after"] == after
        assert trace["controller_history"][t] == {
            "action": name, "receipt": receipt, "wallet": str(balance - fee)}
        assert ledger == {"prefix": t + 1, "request_cap": str(cap),
                          "balance_before": str(balance), "actual_fee": str(fee),
                          "balance_after": str(balance - fee)}
        balance -= fee
        cost += fee
        births += int(receipt[0])
        payoff += int(receipt[0]) - fee / 4
        history += (tuple(receipt),)
        names.append(name)
        receipts.append(receipt)
        store = after
        assert balance >= 0 and balance == 2 - cost
    assert trace["final_store"] == store and len(store) == 4
    assert trace["committed_stop"] == stopped
    assert trace["receipts"] == receipts and trace["births"] == births
    assert F(trace["J_path"]) == payoff
    assert F(trace["actual_fee"]) == cost and F(trace["final_wallet"]) == balance
    assert packed["actions"] == names and packed["receipts"] == receipts
    assert packed["final_store"] == [None if o is None else o["physical"] for o in store]
    assert packed["stopped"] == stopped and F(packed["J_path"]) == payoff
    return payoff, cost, births


def scalar_step(world, name, normal):
    mechanism, slots, stopped = world
    requested = ACTION[name]
    parent, write = (0, None) if stopped or requested is None else requested
    current = slots[parent] if parent < len(slots) else None
    after = list(slots)
    if current is None:
        receipt = (False, False)
        after.append(None)
    else:
        bit = (current if write is None else write) if normal else False
        receipt = (bool(normal and bit), bool(normal and write is not None))
        after[parent] = bit
        after.append(True if receipt[0] else None)
    if mechanism == "G" and not normal:
        after = [None if bit is None else False for bit in after]
    return (mechanism, tuple(after), stopped or requested is None), receipt


def freeze(atoms):
    return tuple(sorted(((w, p) for w, p in atoms.items() if p), key=lambda x: repr(x[0])))


def branches(atoms, name):
    groups = {o: defaultdict(F) for o in OBS}
    for world, weight in atoms:
        for normal in (False, True):
            nxt, obs = scalar_step(world, name, normal)
            groups[obs][nxt] += weight / 2
    return [(obs, freeze(group)) for obs, group in groups.items() if any(group.values())]


def legal(wallet):
    return [name for name, a in ACTION.items() if a is None or a[1] is None or wallet >= 1]


@lru_cache(None)
def independent_all_menu(atoms, wallet, remaining, objective="J"):
    if remaining == 0:
        if objective == "J":
            return F(0)
        masses = {m: sum(p for (kind, _, _), p in atoms if kind == m) for m in ("S", "G")}
        return abs(masses["S"] - masses["G"]) / 2
    scores = []
    for name in legal(wallet):
        score = F(0)
        for obs, group in branches(atoms, name):
            mass = sum(p for _, p in group)
            immediate = mass * (int(obs[0]) - F(int(obs[1]), 4)) if objective == "J" else F(0)
            score += immediate + independent_all_menu(group, wallet - int(obs[1]), remaining - 1, objective)
        scores.append(score)
    return max(scores)


def key(t):
    return t["mechanism"], t["seed"], tuple(t["modes"]), tuple(t["labels"])


def verify_all(policy, native):
    expected = {(m, s, modes, labels) for m in ("S", "G") for s in range(4)
                for modes in product((False, True), repeat=3)
                for labels in product((False, True), repeat=3)}
    traces = native["traces"]
    packed = {key(t): t for t in policy["packed_runs"]}
    assert len(traces) == len(policy["packed_runs"]) == len(packed) == len(expected) == 512
    assert {key(t) for t in traces} == set(packed) == expected
    assert all(F(t["conditional_mass"]) == F(1, 256) for t in traces)
    values = {m: F(0) for m in ("S", "G")}
    components = {s: {m: F(0) for m in ("S", "G")} for s in range(4)}
    for t in traces:
        value, _, _ = check_trace(t, policy, packed[key(t)])
        values[t["mechanism"]] += value / 256
        components[t["seed"]][t["mechanism"]] += value / 64
    assert values == {"S": F(161, 128), "G": F(157, 128)}
    assert components[0] == {"S": F(41, 32), "G": F(37, 32)}
    assert all(components[s] == {"S": F(5, 4), "G": F(5, 4)} for s in (1, 2, 3))
    assert {m: F(x) for m, x in native["values"].items()} == values
    return values


def expect_rejection(test):
    try:
        test()
    except (AssertionError, KeyError):
        return True
    raise AssertionError("negative audit mutation was accepted")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--policy", type=Path, required=True)
    parser.add_argument("--native", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    policy, native = json.loads(args.policy.read_text()), json.loads(args.native.read_text())
    assert native["policy_sha256"] == digest(args.policy)
    assert policy["parameters"] == {"goal": True, "r": "1/2", "horizon": 3,
        "initial_wallet": "2", "write_tariff": "1", "price": "1/4", "discount": "1", "terminal": "0"}
    assert policy["private_seed"] == {"size": 4, "mass_each": "1/4",
        "component_S_seeds": [0], "component_G_seeds": [1, 2, 3]}
    assert policy["dual_witness"]["weights"] == ["3/4", "1/4"]
    assert native["zero_wallet_actual_controller_request_rejected_before_outcome"] is True
    values = verify_all(policy, native)
    optima = {}
    for label, weights in (("S", (F(1), F(0))), ("G", (F(0), F(1))),
                           ("dual", (F(3, 4), F(1, 4)))):
        atoms = freeze({(m, (False,), False): w for m, w in zip(("S", "G"), weights)})
        optima[label] = independent_all_menu(atoms, 2, 3)
    assert optima == {"S": F(41, 32), "G": F(5, 4), "dual": F(5, 4)}
    assert F(policy["components"]["S"]["solver_value"]) == optima["S"]
    assert F(policy["components"]["G"]["solver_value"]) == optima["G"]
    assert F(policy["dual_witness"]["solver_value"]) == optima["dual"]
    lower = F(3, 4) * optima["S"] + F(1, 4) * optima["G"] - optima["dual"]
    regrets = {m: optima[m] - values[m] for m in ("S", "G")}
    assert lower == regrets["S"] == regrets["G"] == F(3, 128)
    tv_atoms = freeze({(m, (False,), False): F(1) for m in ("S", "G")})
    tv = independent_all_menu(tv_atoms, 2, 3, "TV")
    assert tv == F(1, 8)
    # These mutations address specific source/interface risks; they are not a
    # substitute for the universal native or admissibility theorems.
    bad = deepcopy(native)
    bad["traces"][0]["conditional_mass"] = "1/128"
    seed_rejected = expect_rejection(lambda: verify_all(policy, bad))
    bad = deepcopy(native)
    changed = False
    for t in bad["traces"]:
        for e in t["world_events"]:
            if t["mechanism"] == "G" and not e["mode"]:
                for j, obj in enumerate(e["store_after_transaction"]):
                    if obj is not None and obj["physical"] and j != e["request"][0]:
                        e["store_after"][j]["physical"] = True
                        changed = True
                        break
            if changed: break
        if changed: break
    assert changed
    damage_rejected = expect_rejection(lambda: verify_all(policy, bad))
    assert "root_write_true" not in legal(F(0))
    report = {"schema": "UEOT/MECHANISM_INDEPENDENT_CHECK/V1", "status": "PASS",
              "policy_sha256": digest(args.policy), "native_sha256": digest(args.native),
              "checker_sha256": digest(Path(__file__)), "native_paths_checked": 512,
              "all_prefixes_checked": 1536, "complete_enumeration": True,
              "values": {m: str(x) for m, x in values.items()},
              "independent_all_menu_values": {m: str(x) for m, x in optima.items()},
              "lower_witness": {"weights": ["3/4", "1/4"], "lower": str(lower)},
              "actual_achiever_regrets": {m: str(x) for m, x in regrets.items()},
              "independent_max_TV": str(tv), "equal_prior_classification_error": str((1-tv)/2),
              "negative_checks": {"seed_noise_mass_mutation_rejected": seed_rejected,
                                  "missed_unselected_G_damage_rejected": damage_rejected,
                                  "zero_wallet_write_rejected_before_outcome": True},
              "independent_recursion": "unnormalized joint history mass; no solver imports",
              "empirical_support": "UNVERIFIED"}
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
