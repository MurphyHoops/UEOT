"""Run the *fixed* sharp experiment against the registered complete-Store adapter.

The existing driver has one frozen RNG mass field for the four-seed consumer.
This diagnostic is deterministic: its probability model is separately fixed
at one atom of mass 1/64 for each full (mode,label) triple in each mechanism.
We compare the executed histories, records and ledger; no seed-mass field of
the other consumer is used.
"""
import argparse
from collections import Counter
from fractions import Fraction as Q
import hashlib
from importlib import util
from itertools import product
import json
from pathlib import Path
import sys


def adapter_at(path):
    spec = util.spec_from_file_location("sg_h3_registered_native", path)
    adapter = util.module_from_spec(spec)
    sys.modules[spec.name] = adapter
    spec.loader.exec_module(adapter)
    return adapter


def main():
    ap = argparse.ArgumentParser()
    for flag in ("packed", "adapter", "original-native", "output"):
        ap.add_argument("--" + flag, type=Path, required=True)
    args = ap.parse_args()
    packed = json.loads(args.packed.read_bytes())
    assert packed["schema"] == "UEOT/H3_SHARP_EXPERIMENT/V1"
    assert tuple(packed[k] for k in ("budget", "tariff", "r")) == ("1", "1", "1/2")
    adapter = adapter_at(args.adapter)
    old = adapter.original_native(args.original_native)
    # All four receipt branches at a level have the same action, as in separationTable.
    observations = tuple(product((False, True), repeat=2))
    word = ("root_write_true", "root_idle", "child1_idle")
    rows = [{"history": list(h), "action": a}
            for k, a in enumerate(word) for h in product(observations, repeat=k)]
    policy = {"parameters": {"goal": True, "r": "1/2", "horizon": 3,
                             "initial_wallet": "1", "write_tariff": "1",
                             "price": "1/4", "discount": "1"},
              "components": {"S": {"rows": rows}, "G": {"rows": rows}}}
    counts = {m: Counter() for m in ("S", "G")}
    paid = {m: Counter() for m in counts}
    samples, keys = [], set()
    canonical = hashlib.sha256()
    exclusive = ((True, True), (False, False), (True, False))
    for p in packed["atoms"]:
        m, modes, labels = p["mechanism"], tuple(p["modes"]), tuple(p["labels"])
        key = (m, modes, labels)
        assert key not in keys
        keys.add(key)
        native = adapter.run(policy, old, m, 0, modes, labels)
        receipts = tuple(map(tuple, native["receipts"]))
        assert native["committed_stop"] is False
        assert p["exclusive"] == (receipts == exclusive)
        assert (receipts == exclusive) == (m == "S" and modes == (True, False, True))
        assert list(word) == [x["action"] for x in native["controller_history"]]
        assert len(p["ledger"]) == len(native["ledger"]) == 3
        for k, (pl, nl) in enumerate(zip(p["ledger"], native["ledger"])):
            assert pl["prepaid"] and Q(pl["balance_before"]) >= Q(pl["cap"])
            assert pl["action"] == word[k] and tuple(pl["receipt"]) == receipts[k]
            for lk, rk in (("cap", "request_cap"), ("balance_before", "balance_before"),
                           ("fee", "actual_fee"), ("balance_after", "balance_after")):
                assert Q(pl[lk]) == Q(nl[rk]), (m, modes, labels, lk)
        assert Q(native["final_wallet"]) == 1 - int(receipts[0][1])
        counts[m][receipts] += 1
        paid[m][native["actual_fee"]] += 1
        record = {"mechanism": m, "modes": modes, "labels": labels,
                  "ledger": native["ledger"], "world_events": native["world_events"]}
        canonical.update(json.dumps(record, sort_keys=True, separators=(",", ":")).encode()+b"\n")
        if labels == (False, False, False) and modes in ((True, False, True), (False, False, False)):
            samples.append(record)
    triples = tuple(product((False, True), repeat=3))
    assert keys == set(product(counts, triples, triples))
    hists = set(counts["S"]) | set(counts["G"])
    tv = Q(sum(abs(counts["S"][h]-counts["G"][h]) for h in hists),128)
    risk = Q((64-counts["S"][exclusive])+counts["G"][exclusive],128)
    assert (tv, risk) == (Q(1,8), Q(7,16))
    assert paid == {m: {"0": 32, "1": 32} for m in counts}
    def hist_name(h):
        return "/".join("".join(str(int(b)) for b in o) for o in h)
    def sha(path):
        return hashlib.sha256(path.read_bytes()).hexdigest()
    report = {"schema":"UEOT/NATIVE_H3_SHARP_CHECK/V1", "status":"PASS",
              "packed_sha256":sha(args.packed), "adapter_sha256":sha(args.adapter),
              "original_native_sha256":sha(args.original_native), "horizon":3,
              "tariff":"1", "initial_wallet":"1", "rate":"1/2",
              "absolute_parameters":"fixed mechanism; one deterministic shared table",
              "packed_native_atoms":len(keys), "conditional_mass_each":"1/64",
              "prepaid_tick_checks":len(keys)*3, "induced_histograms":{
                  m: {hist_name(h):n for h,n in sorted(counts[m].items())} for m in counts},
              "paid_fee_histograms":paid, "exclusive_count":{m:counts[m][exclusive] for m in counts},
              "tv":str(tv), "equal_prior_error":str(risk),
              "all_native_world_ledger_sha256":canonical.hexdigest(),
              "complete_Store_examples":samples}
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True)+"\n")
    print(json.dumps({k:report[k] for k in ("status","packed_native_atoms","prepaid_tick_checks",
                                             "exclusive_count","tv","equal_prior_error")},sort_keys=True))


if __name__ == "__main__":
    main()
