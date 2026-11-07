#!/usr/bin/env python3
"""Independently check actual NativeSourceRun JSON against the physical interpreter.

A PASS requires reading a real Lean export.  It is never inferred from a mock,
source-only inspection, or the internal mutation checks.  All probability
arithmetic is exact Fraction arithmetic; no successful-run conditioning is used.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from copy import deepcopy
from dataclasses import replace
from fractions import Fraction as F
from hashlib import sha256
from importlib.util import module_from_spec, spec_from_file_location
from itertools import product
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent


def require(ok, label):
    if not ok:
        raise AssertionError(label)


def equal(actual, expected, label):
    if actual != expected:
        raise AssertionError(f"{label}: actual={actual!r}, expected={expected!r}")


def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()


def jsonable(x):
    if isinstance(x, F):
        return str(x)
    if isinstance(x, dict):
        return {str(k): jsonable(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return [jsonable(v) for v in x]
    return x


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("native", nargs="?", type=Path, default=HERE / "lean_native_execution.json")
    ap.add_argument("--prototype", type=Path, default=HERE / "source-prototype.py")
    ap.add_argument("--source-lean", type=Path, default=HERE / "CoreRegenerativeSource.lean")
    ap.add_argument("--population-lean", type=Path, default=HERE / "CoreRegenerativePopulation.lean")
    ap.add_argument("--runner-lean", type=Path, default=HERE / "NativeSourceRun.lean")
    ap.add_argument("--output", type=Path, default=HERE / "native_source_check.json")
    args = ap.parse_args()
    data = json.loads(args.native.read_text())
    equal(data["schema"], "UEOT/CORE_REGENERATIVE_LEAN_EXECUTION/V1", "schema")

    spec = spec_from_file_location("ueot_independent_physical_interpreter", args.prototype)
    src = module_from_spec(spec)
    sys.modules[spec.name] = src
    spec.loader.exec_module(src)
    p = src.Parameters(F(3, 4), F(1, 8), F(3, 8), F(1, 4), F(1, 3))
    p.validate()
    require(p.survival + p.common_birth > 1, "public supercritical positive class")
    atom_law = dict(src.atoms(p))
    equal(len(atom_law), 36, "primitive atom support")
    equal(sum(atom_law.values()), F(1), "primitive normalization")
    require(all(w > 0 for w in atom_law.values()), "nonzero source noise")

    def body(b):
        return {"code": [list(row) for row in b.code], "gate": b.gate,
                "bootstrap": b.bootstrap, "tag": b.tag}

    def identity(i):
        if i is None:
            return None
        equal(i[0][0], 0, "identity founder time")
        require(all(slot == 0 for _, slot in i[1:]), "single actual newborn slot")
        return {"founder": i[0][1], "births": [t for t, _ in i[1:]]}

    def member(x, ancestry):
        return {"identity": identity(x.identity), "parent": identity(x.parent),
                "born_at": x.born_at, "age": x.age, "body": body(x.body),
                "wallet": x.wallet, "ancestry": ancestry}

    def lift(t, old, receipt, history):
        answer = []
        for out in receipt["outputs"]:
            newborn = out.identity != old.identity
            edge = {"census": t + 1, "source_id": identity(old.identity),
                    "target_id": identity(out.identity), "newborn": newborn,
                    "source_kind": src.damaged(old.body), "target_kind": src.damaged(out.body)}
            answer.append((out, history + [edge]))
        return answer

    def result(old, receipt):
        retained = [x for x in receipt["outputs"] if x.identity == old.identity]
        newborn = [x for x in receipt["outputs"] if x.identity != old.identity]
        require(len(retained) <= 1 and len(newborn) <= 1, "two actual output slots")
        return {"retained": body(retained[0].body) if retained else None,
                "newborn": body(newborn[0].body) if newborn else None,
                "repair_paid": receipt["repair_fee"],
                "operation_paid": receipt["operation_fee"],
                "output_capital": len(receipt["outputs"]),
                "refund": receipt["returned_to_environment"], "status": receipt["status"]}

    def prefix_balances(old, receipt):
        available = old.wallet + receipt["source_inflow"]
        balances = [available]
        balances.append(balances[-1] - receipt["repair_fee"])
        balances.append(balances[-1] - receipt["operation_fee"])
        for out in receipt["outputs"]:
            balances.append(balances[-1] - out.wallet)
        balances.append(balances[-1] - receipt["returned_to_environment"])
        require(min(balances) >= 0 and balances[-1] == 0, "actual payment prefixes")
        if receipt["status"] == "executed":
            require(receipt["request_cap"] <= available, "cap paid before outcome")
            equal(receipt["noise_used"], True, "executed transaction consumes atom")
        elif receipt["status"] == "rejected":
            equal(receipt["outputs"], [old], "rejection preserves exact old body and wallet")
            equal(receipt["noise_used"], False, "rejection does not inspect random atom")
            equal(receipt["actual_fee"], 0, "rejection pays no execution fee")
        else:
            equal(receipt["outputs"], [], "stop has no retained or newborn output")
            equal(receipt["noise_used"], False, "stop does not inspect random atom")
        return balances

    def check_record(record, is_program):
        theta, kind, tag = record["theta"], record["kind"], record["tag"]
        require(all(type(x) is bool for x in [theta, kind, tag]), "physical selectors are booleans")
        equal(record["program"], is_program, "dispatch mode")
        atom = tuple(record["noise"])
        require(atom in atom_law and type(atom[2]) is bool and type(atom[3]) is bool,
                "declared primitive atom")
        old = src.founder(theta, kind, 0, tag)
        equal(record["before"], member(old, []), "complete input member")
        equal(record["diagnostic"], src.damaged(old.body), "allowed physical diagnostic")
        request = record["request"]
        require(request in ("care", "bloom", "stop"), "actual request alphabet")
        if is_program:
            equal(request, src.program_request(old.body), "request read from actual physical code")
        receipt = src.tick(p, old, 0, atom, request=None if is_program else request)
        equal(record["cap"], receipt["request_cap"], "pre-outcome request cap")
        equal(record["raw_before"], src.raw_execute(old.body, src.damaged(old.body)), "raw damaged execution")
        restored, _, _ = src.repair(old.body)
        equal(record["raw_restored"], src.raw_execute(restored, src.damaged(old.body)), "restored physical execution")
        equal(record["result"], result(old, receipt), "complete local result")
        equal(record["outputs"], [member(x, h) for x, h in lift(0, old, receipt, [])],
              "complete output bodies, identities, parents, ages and marked ancestry")
        for out in receipt["outputs"]:
            equal(src.decode(out.body), (theta, False), "faithful actual inherited code")
        return receipt, prefix_balances(old, receipt)

    equal(data["port_count"], 864, "declared port count")
    equal(data["program_count"], 288, "declared program count")
    equal(len(data["ports"]), 864, "all port records exist")
    equal(len(data["programs"]), 288, "all program records exist")
    expected_ports = set(product((False, True), (False, True), (False, True),
                                 ("care", "bloom", "stop"), atom_law))
    expected_programs = set(product((False, True), (False, True), (False, True), atom_law))
    seen_ports, seen_programs = set(), set()
    rows = defaultdict(lambda: {"L": [F(0), F(0)], "B": [F(0), F(0)]})
    distributions = defaultdict(lambda: defaultdict(F))
    statuses = defaultdict(int)
    prefix_count = 0
    minimum_balance = 6
    for is_program, records in [(False, data["ports"]), (True, data["programs"])]:
        for record in records:
            receipt, balances = check_record(record, is_program)
            prefix_count += len(balances)
            minimum_balance = min(minimum_balance, min(balances))
            statuses[receipt["status"]] += 1
            theta, kind, tag = record["theta"], record["kind"], record["tag"]
            atom = tuple(record["noise"])
            key = (theta, kind, tag, atom) if is_program else (theta, kind, tag, record["request"], atom)
            seen = seen_programs if is_program else seen_ports
            require(key not in seen, "no duplicate record substitutes for missing Cartesian case")
            seen.add(key)
            if is_program:
                weight = atom_law[atom]
                row = rows[theta, kind, tag]
                for output in record["outputs"]:
                    j = int(not output["body"]["gate"] or any(len(set(r)) != 1 for r in output["body"]["code"]))
                    target = "L" if output["identity"] == record["before"]["identity"] else "B"
                    row[target][j] += weight
                if not kind and not tag:
                    distributions[theta][len(record["outputs"])] += weight
    equal(seen_ports, expected_ports, "full seven-coordinate request coverage")
    equal(seen_programs, expected_programs, "full physical program coverage")

    nu = [1 - p.damage, p.damage]
    for (theta, kind, tag), row in rows.items():
        a = "bloom" if theta and not kind else "care"
        survival = p.survival - (p.care_only_survival if a == "bloom" else 0)
        births = p.common_birth + (p.bloom_only_birth if a == "bloom" else 0)
        equal(row["L"], [survival * x for x in nu], "actual source retained mean row")
        equal(row["B"], [births * x for x in nu], "actual source newborn mean row")
        row["M"] = [x + y for x, y in zip(row["L"], row["B"])]
    rates = [sum(rows[theta, False, False]["M"]) * nu[0]
             + sum(rows[theta, True, False]["M"]) * nu[1] for theta in (False, True)]
    equal(rates, [F(9, 8), F(29, 24)], "same returned-program growth rates")
    equal(dict(distributions[False]), {0: F(5, 32), 1: F(9, 16), 2: F(9, 32)}, "native care count law")
    equal(dict(distributions[True]), {0: F(9, 64), 1: F(15, 32), 2: F(25, 64)}, "native bloom count law")

    zero = ratio = expected_n = expected_upper = best_lost = F(0)
    for a, pa in distributions[False].items():
        for b, pb in distributions[True].items():
            weight, total = pa * pb, a + b
            zero += weight * (total == 0)
            best_lost += weight * (b == 0 and a > 0)
            expected_n += weight * total
            expected_upper += weight * b
            if total:
                ratio += weight * F(b, total)
    equal((zero, best_lost, ratio, ratio / (1-zero), expected_upper / expected_n),
          (F(45,2048), F(243,2048), F(2095,4096), F(2095,4006), F(10,19)),
          "native-derived exact finite-population boundaries")

    two = data["two_round"]
    population = [(src.founder(True, True, 0, False), []),
                  (src.founder(False, False, 1, True), [])]
    equal(two["start"], [member(x,h) for x,h in population], "two-round actual start")
    round_finance = []
    for t, field, noise_field in [(0,"after_first","noise_first"),(1,"after_second","noise_second")]:
        atom = tuple(two[noise_field])
        require(atom in atom_law, "two-round primitive atom")
        next_population = []
        fees = refunds = output_wallets = 0
        for old, history in population:
            receipt = src.tick(p, old, t, atom)
            balances = prefix_balances(old, receipt)
            prefix_count += len(balances)
            minimum_balance = min(minimum_balance, min(balances))
            next_population.extend(lift(t, old, receipt, history))
            fees += receipt["actual_fee"]
            refunds += receipt["returned_to_environment"]
            output_wallets += sum(x.wallet for x in receipt["outputs"])
        equal(two[field], [member(x,h) for x,h in next_population], "two-round complete census and ancestry")
        equal(len(next_population), 2 * len(population), "newborns act only in following census")
        require(len({x.identity for x,_ in next_population}) == len(next_population), "unique actual identities")
        equal(len(population) * 6, fees + refunds + output_wallets, "round resource conservation")
        round_finance.append({"old_members":len(population),"source_inflow":5*len(population),
                              "fees":fees,"refunds":refunds,"output_wallets":output_wallets})
        population = next_population

    cuts = {c["name"]:c for c in data["cuts"]}
    equal(set(cuts), {"bootstrap","main_gate","active_code","erasure"}, "causal cut coverage")
    original = src.founder(True, True)
    boot = replace(original, body=replace(original.body, bootstrap=False))
    receipt = src.tick(p, boot, 0, (2,2,False,False))
    equal(cuts["bootstrap"]["body"], body(boot.body), "bootstrap cut physical state")
    equal(cuts["bootstrap"]["step"], result(boot, receipt), "bootstrap cut really blocks repair")
    healthy = src.founder(True, False).body
    gate = replace(healthy, gate=False)
    equal(cuts["main_gate"], {"name":"main_gate","body":body(gate),"raw":src.raw_execute(gate,False)}, "gate causal cut")
    row = healthy.code[0]
    wrong = replace(healthy, code=((not row[0],row[1],row[2]),healthy.code[1]))
    equal(cuts["active_code"], {"name":"active_code","body":body(wrong),"raw":src.raw_execute(wrong,False)}, "active-code causal cut")
    erased = replace(healthy, code=((False,False,False),(False,False,False)), gate=False)
    restored, _, _ = src.repair(erased)
    equal(cuts["erasure"], {"name":"erasure","body":body(erased),"restored":body(restored)}, "erasure nonidentifiability")
    require(src.decode(restored) != (True,False), "erased original program not invented by repair")

    # These source checks have a narrowly stated scope: runtime entry points
    # take physical bodies and allowed diagnostics, never a hidden program label
    # or source expectation.  Complete 1152-record equality checks the semantics.
    lean = args.source_lean.read_text()
    def declaration(name):
        m = re.search(r"^(?:noncomputable\s+)?def " + re.escape(name) + r"\b[^\n]*(?:\n[ \t]+[^\n]*)*", lean, re.M)
        require(m is not None, f"actual runtime declaration {name}")
        return m.group(0)
    controls = {name:declaration(name) for name in ["requestOf","rawExecute","restore","programStep"]}
    forbidden = re.compile(r"\b(theta|growthRate|eventMean|fitness|sourceValue)\b|\.tag\b")
    for name, text in controls.items():
        require(not forbidden.search(text), f"oracle-free physical runtime {name}")
    equal(" ".join(controls["programStep"].split()),
          "def programStep (x : Body) (z : Noise) : LocalResult := "
          "if canExecute x (requestOf x) then "
          "match rawExecute (restore x) (diagnostic x) with "
          "| some actual => executedResult x actual z "
          "| none => ⟨some x, none, 0, 0, 5, .rejected⟩ "
          "else ⟨some x, none, 0, 0, 5, .rejected⟩",
          "actual restored-code execution; private noise does not select request or code")
    require("requestOf (x : Body) : Action" in controls["requestOf"], "controller has only physical input")
    require("majority" in controls["restore"] and "active" in controls["rawExecute"], "real repair and raw execution")
    parameter_decl = declaration("concreteParameters")
    equal(re.sub(r"\s+", "", parameter_decl),
          "noncomputabledefconcreteParameters:Parameters:=⟨3/4,1/8,3/8,1/4,1/3⟩", "same primitive probability parameters")
    pop_text = args.population_lean.read_text()
    require("programStep old.body w.1" in pop_text and "treeCount T old.body w" in pop_text,
            "identity wrapper consumes same programStep/treeCount")
    require("old.births" not in controls["requestOf"], "ancestry is not a controller oracle")
    runner = args.runner_lean.read_text()
    require("programStep old.body z else step old.body a z" in runner,
            "native exporter calls real program or real request port")

    mutations = []
    def rejects(name, record, program=False):
        try:
            check_record(record, program)
        except AssertionError:
            mutations.append(name)
            return
        raise AssertionError(f"checker failed to reject mutation {name}")
    rec = deepcopy(data["programs"][0]); rec["cap"] += 1
    rejects("unpaid_request_cap", rec, True)
    rec = deepcopy(next(r for r in data["programs"] if r["result"]["newborn"] is not None))
    rec["outputs"][-1]["parent"] = None
    rejects("fabricated_newborn_parent", rec, True)
    rec = deepcopy(next(r for r in data["ports"] if r["result"]["status"] == "rejected"))
    rec["outputs"][0]["age"] += 1
    rejects("rejection_advances_execution_age", rec)
    rec = deepcopy(next(r for r in data["programs"] if r["outputs"]))
    rec["outputs"][0]["body"]["code"][0][0] = not rec["outputs"][0]["body"]["code"][0][0]
    rejects("wrong_physical_inherited_code", rec, True)
    rec = deepcopy(next(r for r in data["programs"] if r["outputs"]))
    rec["outputs"][0]["ancestry"][0]["newborn"] = not rec["outputs"][0]["ancestry"][0]["newborn"]
    rejects("conflated_retention_birth_mark", rec, True)

    report = {"schema":"UEOT/CORE_REGENERATIVE_NATIVE_CHECK/V1", "status":"PASS",
              "empirical_support":"UNVERIFIED",
              "input":{"native_sha256":digest(args.native),"native_bytes":args.native.stat().st_size,
                       "prototype_sha256":digest(args.prototype),"source_lean_sha256":digest(args.source_lean),
                       "population_lean_sha256":digest(args.population_lean),"runner_lean_sha256":digest(args.runner_lean),
                       "checker_sha256":digest(Path(__file__))},
              "checked_ports":864,"checked_program_paths":288,
              "complete_cartesian_coverage":True,"full_store_identity_parent_ancestry_checks":True,
              "payment_prefixes_checked":prefix_count,"minimum_prefix_balance":minimum_balance,
              "statuses":dict(statuses),"actual_program_rows":dict(rows),"growth_rates":rates,
              "two_round_finance":round_finance,"two_round_final_count":len(population),
              "oracle_free_runtime_inspection":list(controls),"causal_cuts_checked":list(cuts),
              "negative_mutations_rejected":mutations,
              "same_source_counterexamples":{"zero_population":zero,"best_extinct_inferior_nonzero":best_lost,
                 "expected_ratio_zero_extension":ratio,"expected_ratio_given_nonzero":ratio/(1-zero),
                 "ratio_expected_counts":expected_upper/expected_n},
              "limits":["Exact native-source verification, not empirical support",
                        "No inference of permanent survival from a positive first-round count",
                        "Cohort concentration requires separately funded independent source tapes"]}
    args.output.write_text(json.dumps(jsonable(report), ensure_ascii=False, indent=2) + "\n")
    print(json.dumps(jsonable(report), ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
