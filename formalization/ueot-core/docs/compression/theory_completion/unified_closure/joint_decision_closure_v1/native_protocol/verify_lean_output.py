#!/usr/bin/env python3
"""Verify THIS Lean-serialized table by independent full Store replay.

The caller freezes source/proof/input/output identities around Lean execution.
This verifier binds the exact received output bytes and interprets its rows,
rather than substituting the independent Python planner's returned policy.
"""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import argparse
import hashlib
import json
import sys
import time

import exact_reference as ref

OBS = ((False,False),(False,True),(True,False),(True,True))
ACTION = {
    "stop": None, "root_idle": (0,None), "child1_idle": (1,None),
    "root_write_false": (0,False), "root_write_true": (0,True),
    "child1_write_false": (1,False), "child1_write_true": (1,True),
}

class InvalidInput(Exception):
    pass

class ResourceUnknown(Exception):
    pass

def no_duplicate_keys(pairs):
    result = {}
    for key,value in pairs:
        if key in result:
            raise InvalidInput("duplicate JSON object key: "+str(key))
        result[key] = value
    return result

def read_rational(value, name):
    if not isinstance(value,str):
        raise InvalidInput(name+" must be an exact rational string")
    try:
        return Q(value)
    except (ValueError,ZeroDivisionError):
        raise InvalidInput(name+" is not a valid rational")

def parse_output(raw, max_horizon, max_tapes):
    try:
        data = json.loads(raw,object_pairs_hook=no_duplicate_keys)
    except (ValueError,UnicodeDecodeError) as exc:
        raise InvalidInput("malformed JSON: "+str(exc))
    if not isinstance(data,dict):
        raise InvalidInput("top-level JSON must be an object")
    if data.get("schema") != "UEOT/JOINT_DECISION_RETURN/V1":
        raise InvalidInput("unsupported output schema")
    h = data.get("horizon")
    if type(h) is not int or h < 0:
        raise InvalidInput("horizon must be a natural number")
    if not isinstance(data.get("normal_probabilities"),list) or not isinstance(data.get("prior"),list):
        raise InvalidInput("normal probabilities and prior must be arrays")
    rs = tuple(read_rational(x,"normal probability") for x in data["normal_probabilities"])
    prior = tuple(read_rational(x,"prior") for x in data["prior"])
    if not rs or len(rs) != len(prior):
        raise InvalidInput("finite source/prior lengths do not match")
    if any(r < 0 or r > 1 for r in rs) or any(w < 0 for w in prior) or sum(prior) != 1:
        raise InvalidInput("invalid probabilities")
    tariff = read_rational(data.get("tariff"),"tariff")
    price = read_rational(data.get("price"),"price")
    d = read_rational(data.get("discount"),"discount")
    budget = read_rational(data.get("wallet"),"wallet")
    value = read_rational(data.get("value"),"value")
    if tariff <= 0 or price < 0 or not 0 <= d <= 1 or budget < 0:
        raise InvalidInput("invalid tariff/price/discount/wallet")
    if data.get("goal") is not True or data.get("initial_damaged") is not True:
        raise ResourceUnknown("this independent checker covers the registered known-true-goal damaged founder family")
    if h > max_horizon or len(rs)*(4**h) > max_tapes:
        raise ResourceUnknown("registered exact replay resource bound exceeded; no infeasibility claim")
    rows = {}
    raw_rows = data.get("rows")
    if not isinstance(raw_rows,list):
        raise InvalidInput("rows must be a complete array")
    for row in raw_rows:
        if not isinstance(row,dict) or set(row) != {"history","action"}:
            raise InvalidInput("each row must contain only history and action")
        if not isinstance(row["action"],str) or row["action"] not in ACTION:
            raise InvalidInput("unknown action")
        if not isinstance(row["history"],list):
            raise InvalidInput("history must be an observation list")
        history = []
        for obs in row["history"]:
            if not isinstance(obs,list) or len(obs) != 2 or any(type(x) is not bool for x in obs):
                raise InvalidInput("receipt must be exactly [birth_bool,paid_write_bool]")
            history.append(tuple(obs))
        history = tuple(history)
        if history in rows:
            raise InvalidInput("duplicate decision history")
        rows[history] = row["action"]
    expected_histories = {t for n in range(h) for t in product(OBS,repeat=n)}
    if set(rows) != expected_histories:
        raise InvalidInput("serialized rows are not exactly the complete finite table")
    return data,h,rs,prior,tariff,price,d,budget,value,rows

def verify_bytes(raw, max_horizon=8, max_tapes=1000000):
    started = time.perf_counter()
    data,h,rs,prior,cost,price,d,budget,declared,rows = parse_output(raw,max_horizon,max_tapes)
    # This checks the exact total menu used by the Lean solver, including
    # impossible receipt branches. Off-support wallet updates deliberately
    # use the registered clamp; supported native paths below never need it.
    for history,name in rows.items():
        row_balance = budget
        for obs in history:
            row_balance = max(Q(0),row_balance-(cost if obs[1] else Q(0)))
        action = ACTION[name]
        demand = cost if action is not None and action[1] is not None else Q(0)
        assert demand <= row_balance, "THIS serialized row violates the prepaid menu"
    planner = ref.Planner(rs,prior,price,d,cost)
    reference_value = planner.solve(h,prior,(False,),budget)[0]
    founder = ref.Organism(False,True,(),((0,False),),0)
    total = value = success = mean_births = mean_fee = Q(0)
    minimum_balance = budget
    histories = {}
    traces = []
    for theta,theta_mass in enumerate(prior):
        for modes in product((False,True),repeat=h):
            mode_mass = theta_mass
            for mode in modes:
                mode_mass *= rs[theta] if mode else 1-rs[theta]
            for labels in product((False,True),repeat=h):
                mass = mode_mass/(2**h)
                if not mass:
                    continue
                store,balance,committed,belief = (founder,),budget,False,prior
                history = ()
                births,fees,payoff,records = 0,Q(0),Q(0),[]
                for t,(mode,label) in enumerate(zip(modes,labels)):
                    name = rows[history]
                    action = ACTION[name]
                    projected = tuple(None if item is None else item.physical for item in store)
                    demand = cost if action is not None and action[1] is not None else Q(0)
                    # The original public menu tests the selected request's cap.
                    # This is checked BEFORE this hidden outcome is consulted.
                    if demand > balance:
                        raise AssertionError("THIS table requests an unaffordable action")
                    info = (belief,projected,balance,committed)
                    if history in histories:
                        assert histories[history] == info, "permitted history is not sufficient for replay information"
                    else:
                        histories[history] = info
                        branches = planner.branches(belief,projected,balance,committed,action)
                        assert branches is not None
                        action_bound = sum(m * (int(o[0])-price*(balance-b) +
                            d*planner.solve(h-t-1,post,nxt,b,flag)[0])
                            for o,m,post,nxt,b,flag in branches)
                        optimal = planner.solve(h-t,belief,projected,balance,committed)[0]
                        assert action_bound == optimal, "THIS reachable row is not an optimal action"
                    request = (0,None) if committed or action is None else action
                    committed_next = committed or action is None
                    store,obs,fee,record = ref.native_step(store,request,mode,label,cost)
                    matches = [branch for branch in planner.branches(
                        belief,projected,balance,committed,action) if branch[0] == obs]
                    assert len(matches) == 1
                    _,_,belief,nxt,b,flag = matches[0]
                    balance -= fee
                    assert balance == b and balance >= 0 and flag == committed_next
                    assert tuple(None if item is None else item.physical for item in store) == nxt
                    committed = committed_next
                    minimum_balance = min(minimum_balance,balance)
                    births += int(obs[0])
                    fees += fee
                    payoff += d**t*(int(obs[0])-price*fee)
                    record["requested_action"] = name
                    record["effective_parent"] = request[0]
                    record["effective_action"] = request[1]
                    record["receipt"] = obs
                    record["balance"] = ref.rat(balance)
                    records.append(record)
                    history += (obs,)
                assert balance == budget-fees and len(store) == 1+h
                child_ids = [r["child_slot"] for r in records if r["child_slot"] is not None]
                assert len(child_ids) == len(set(child_ids))
                assert all(r["tick"] == t+1 for t,r in enumerate(records))
                total += mass
                value += mass*payoff
                success += mass*int(births > 0)
                mean_births += mass*births
                mean_fee += mass*fees
                traces.append({"theta":theta,"mass":ref.rat(mass),"modes":modes,
                    "labels":labels,"records":records,"payoff":ref.rat(payoff),
                    "final_balance":ref.rat(balance)})
    assert total == 1, "native path mass is not one"
    assert value == declared, "THIS full native replay disagrees with Lean declared value"
    assert value == reference_value, "THIS native replay disagrees with independent full-history optimum"
    summary = {
        "status":"PASS", "case":data.get("case"),
        "scope":"THIS exact Lean rows; independent original Store replay and finite optimum comparison",
        "lean_output_sha256":hashlib.sha256(raw).hexdigest(),
        "verifier_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "reference_source_sha256":hashlib.sha256(Path(ref.__file__).read_bytes()).hexdigest(),
        "horizon":h, "full_serialized_rows":len(rows),
        "reachable_decision_histories":len(histories),
        "zero_probability_decision_rows":len(rows)-len(histories),
        "complete_table_rows_checked":True,
        "all_serialized_rows_prepaid_menu_checked":True,
        "reachable_row_optimality_checked":True,
        "original_labels_failures_none_retained":True,
        "source_index_draws":1,
        "declared_value":ref.rat(declared),
        "actual_native_value":ref.rat(value),
        "independent_optimal_value":ref.rat(reference_value),
        "probability_mass":ref.rat(total),
        "at_least_one_birth":ref.rat(success),
        "expected_total_births":ref.rat(mean_births),
        "expected_total_fee":ref.rat(mean_fee),
        "minimum_prefix_balance":ref.rat(minimum_balance),
        "positive_full_tapes":len(traces),
        "seconds":time.perf_counter()-started,
        "qualification":"Optimality of all finite same-information randomized policies is the Lean theorem; this executable check covers the supplied finite rational instance and actual bytes."
    }
    return summary,traces

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--lean-output",type=Path,action="append",required=True)
    parser.add_argument("--output",type=Path,required=True)
    parser.add_argument("--max-horizon",type=int,default=8)
    parser.add_argument("--max-full-tapes",type=int,default=1000000)
    args = parser.parse_args()
    args.output.mkdir(parents=True,exist_ok=True)
    summaries = []
    exit_code = 0
    for index,path in enumerate(args.lean_output):
        raw = path.read_bytes()
        try:
            summary,traces = verify_bytes(raw,args.max_horizon,args.max_full_tapes)
            trace_raw = json.dumps(traces,ensure_ascii=False,indent=2).encode()
            trace_name = f"{index:02d}-{summary['case']}.THIS_LEAN_NATIVE_TRACES.json"
            (args.output/trace_name).write_bytes(trace_raw)
            summary["full_traces_file"] = trace_name
            summary["full_traces_sha256"] = hashlib.sha256(trace_raw).hexdigest()
        except (InvalidInput,ResourceUnknown,AssertionError) as exc:
            status = "INVALID_INPUT" if isinstance(exc,InvalidInput) else (
                "UNKNOWN" if isinstance(exc,ResourceUnknown) else "FAIL")
            summary = {"status":status,"reason":str(exc),
                "lean_output_sha256":hashlib.sha256(raw).hexdigest()}
            exit_code = 2 if status == "UNKNOWN" else 1
        summary["lean_output_file"] = str(path.resolve())
        summaries.append(summary)
    report = {"schema":"UEOT/THIS_LEAN_TABLE_CHECK/V1","results":summaries}
    (args.output/"THIS_LEAN_TABLE_CHECK.json").write_text(
        json.dumps(report,ensure_ascii=False,indent=2)+"\n")
    print(json.dumps(report,ensure_ascii=False,indent=2))
    return exit_code

if __name__ == "__main__":
    sys.exit(main())

