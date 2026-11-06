#!/usr/bin/env python3
"""Execute THIS exported controller on the original full Store plus G damage.

No planning recursion is called. The original PR441 native_step is reused for
the literal transaction; G is applied afterward to the resulting full Store.
The controller receives only its private seed, its own actions and receipts.
The complete world audit is retained separately from those controller inputs.
"""
from __future__ import annotations
import argparse
from dataclasses import asdict, replace
from fractions import Fraction as Q
import hashlib
import importlib.util
from itertools import product
import json
from pathlib import Path
import sys

OLD_SHA = "b81f62cbe65c3d01d32b2d74910db0e6999b144f249d79e93a8367a2fa9cad5f"
ACTIONS = {
    "stop": None,
    "root_idle": (0, None), "child1_idle": (1, None),
    "root_write_false": (0, False), "root_write_true": (0, True),
    "child1_write_false": (1, False), "child1_write_true": (1, True),
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def original_native(path):
    assert sha(path) == OLD_SHA, "original native adapter identity changed"
    spec = importlib.util.spec_from_file_location("ueot_original_native", path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


class Controller:
    """The constructor and request/receive APIs have no world-side argument."""
    def __init__(self, artifact, seed):
        assert seed in range(4)
        component = "S" if seed == 0 else "G"
        self.table = {tuple(tuple(o) for o in row["history"]): row["action"]
                      for row in artifact["components"][component]["rows"]}
        self.history = []
        self.receipts = ()
        self.wallet = Q(artifact["parameters"]["initial_wallet"])
        self.tariff = Q(artifact["parameters"]["write_tariff"])

    def request(self):
        name = self.table[self.receipts]
        action = ACTIONS[name]
        cap = self.tariff if action is not None and action[1] is not None else Q(0)
        assert cap <= self.wallet, "request cap must pass before world outcome"
        return name, action, cap

    def receive(self, name, receipt):
        fee = self.tariff * int(receipt[1])
        self.wallet -= fee
        assert self.wallet >= 0
        self.receipts += (tuple(receipt),)
        self.history.append({"action": name, "receipt": list(receipt),
                             "wallet": str(self.wallet)})


def store_json(store):
    return [None if p is None else asdict(p) for p in store]


def run(artifact, old, mechanism, seed, modes, labels):
    controller = Controller(artifact, seed)
    p = artifact["parameters"]
    assert p["goal"] is True and Q(p["r"]) == Q(1, 2)
    store = (old.Organism(False, True, (), ((0, False),), 0),)
    committed = False
    receipts, events, ledgers = [], [], []
    total, births, fees = Q(0), 0, Q(0)
    for t in range(p["horizon"]):
        before = store
        balance_before = controller.wallet
        name, action, cap = controller.request()  # no mode or label read yet
        request = (0, None) if committed or action is None else action
        committed = committed or action is None
        mode, label = modes[t], labels[t]
        existed = request[0] < len(store) and store[request[0]] is not None
        store, receipt, fee, record = old.native_step(
            store, request, mode, label, Q(p["write_tariff"]))
        post_transaction = store
        damaged = []
        if mechanism == "G" and not mode:
            damaged = [j for j, obj in enumerate(store) if obj is not None]
            store = tuple(None if obj is None else replace(obj, physical=False)
                          for obj in store)
        controller.receive(name, receipt)
        assert fee == balance_before - controller.wallet
        births += int(receipt[0])
        fees += fee
        total += Q(p["discount"]) ** t * (int(receipt[0]) - Q(p["price"]) * fee)
        receipts.append(list(receipt))
        events.append({
            "tick": t, "source_clock": len(before), "request": list(request),
            "mode": mode, "label": label,
            "transaction": record if existed else None,
            "store_before": store_json(before),
            "store_after_transaction": store_json(post_transaction),
            "common_fault_damaged_slots": damaged,
            "store_after": store_json(store),
        })
        ledgers.append({"prefix": t + 1, "request_cap": str(cap),
                        "balance_before": str(balance_before), "actual_fee": str(fee),
                        "balance_after": str(controller.wallet)})
    assert len(store) == 4
    return {"mechanism": mechanism, "seed": seed,
            "conditional_mass": "1/256", "modes": list(modes), "labels": list(labels),
            "controller_history": controller.history, "receipts": receipts,
            "world_events": events, "ledger": ledgers, "final_store": store_json(store),
            "births": births, "actual_fee": str(fees), "J_path": str(total),
            "final_wallet": str(controller.wallet), "committed_stop": committed}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--policy", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--original-native", type=Path)
    args = parser.parse_args()
    old_path = args.original_native or (Path(__file__).resolve().parents[2] /
        "joint_decision_closure_v1/native_protocol/exact_reference.py")
    old = original_native(old_path)
    artifact = json.loads(args.policy.read_text())
    # Exercise the actual request API, before any world/noise API is called.
    unaffordable = Controller(artifact, 0)
    unaffordable.wallet = Q(0)
    rejected = False
    try:
        unaffordable.request()
    except AssertionError:
        rejected = True
    assert rejected, "THIS first write must fail request-cap with a zero wallet"
    traces = [run(artifact, old, m, seed, modes, labels)
              for m in ("S", "G") for seed in range(4)
              for modes in product((False, True), repeat=3)
              for labels in product((False, True), repeat=3)]
    values = {m: sum(Q(t["conditional_mass"]) * Q(t["J_path"])
                     for t in traces if t["mechanism"] == m) for m in ("S", "G")}
    component_values = {component: {m: sum(Q(t["J_path"]) / 64
        for t in traces if t["mechanism"] == m and t["seed"] == seed)
        for m in ("S", "G")} for component, seed in (("S", 0), ("G", 1))}
    result = {"schema": "UEOT/MECHANISM_NATIVE_EXECUTION/V1",
              "policy_sha256": sha(args.policy), "driver_sha256": sha(Path(__file__)),
              "original_native_sha256": sha(old_path),
              "complete_enumeration": True, "native_paths": len(traces),
              "joint_seed_noise_mass_given_mechanism": "1/256",
              "private_seed_independent_of_fixed_mechanism_and_world_noise": True,
              "zero_wallet_actual_controller_request_rejected_before_outcome": rejected,
              "values": {k: str(v) for k, v in values.items()},
              "component_values": {k: {m: str(v) for m, v in row.items()}
                                   for k, row in component_values.items()},
              "min_prefix_balance": str(min(Q(l["balance_after"]) for t in traces for l in t["ledger"])),
              "empirical_support": "UNVERIFIED", "traces": traces}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "traces"}, indent=2))


if __name__ == "__main__":
    main()
