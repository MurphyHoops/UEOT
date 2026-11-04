#!/usr/bin/env python3
"""Independent exact finite Register check, with a separate full-record replay.

Planning observes only (birth, paid-write). Theta is drawn once. Full replay
retains program, history, true identity, clocks, hidden labels and None slots.
This check does not replace the general Lean optimality and source proofs.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from pathlib import Path
import argparse, hashlib, json, time

STOP = None
ACTIONS = (STOP, (0,None), (1,None), (0,False), (0,True), (1,False), (1,True))

def rat(x):
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"

def action_json(a):
    return {"kind":"stop"} if a is STOP else {"kind":"dispatch","parent":a[0],"action":a[1]}

def projected_step(store, request, mode):
    parent, action = request
    new = list(store)
    if parent >= len(store) or store[parent] is None:
        return tuple(new + [None]), (False,False)
    post = (store[parent] if action is None else action) if mode else False
    born, paid = bool(mode and post), bool(mode and action is not None)
    new[parent] = post
    return tuple(new + [True if born else None]), (born,paid)

@dataclass(frozen=True)
class Organism:
    physical: bool
    program: bool
    history: tuple
    identity: tuple
    clock: int

def native_step(store, request, mode, label, cost):
    """Original modeRecordStep -> timestamp step -> Store.next."""
    parent, action = request
    clock, new = len(store), list(store)
    current = store[parent] if parent < len(store) else None
    if current is None:
        new.append(None)
        return tuple(new),(False,False),Q(0),{
            "tick":clock,"request_parent":parent,"executed":False,
            "mode":mode,"label":label,"parent_identity":None,
            "parent_clock":None,"child_slot":None,"child_identity":None,"expenditure":"0"}
    post = (current.physical if action is None else action) if mode else False
    after = Organism(post,current.program,current.history,current.identity,clock+1)
    born = bool(mode and post == current.program)
    child = Organism(post,current.program,current.history+(label,),
        current.identity+((clock,label),),0) if born else None
    fee = cost if mode and action is not None else Q(0)
    new[parent] = after
    new.append(child)
    return tuple(new),(born,fee != 0),fee,{
        "tick":clock,"request_parent":parent,"executed":bool(mode),
        "mode":mode,"label":label,"parent_identity":current.identity,
        "parent_clock":after.clock,"child_slot":clock if born else None,
        "child_identity":child.identity if child else None,"expenditure":rat(fee)}

class Planner:
    def __init__(self, rs, prior, price, discount, cost=Q(1)):
        assert len(rs) == len(prior) and sum(prior) == 1
        assert all(0 <= r <= 1 for r in rs) and all(w >= 0 for w in prior)
        assert cost > 0 and price >= 0 and 0 <= discount <= 1
        self.rs,self.prior = tuple(rs),tuple(prior)
        self.price,self.discount,self.cost = price,discount,cost

    def branches(self, belief, store, budget, stopped, action):
        request = (0,None) if stopped or action is STOP else action
        committed = stopped or action is STOP
        if (self.cost if request[1] is not None else Q(0)) > budget:
            return None
        groups = {}
        for j,weight in enumerate(belief):
            for mode in (False,True):
                mass = weight*(self.rs[j] if mode else 1-self.rs[j])
                if not mass:
                    continue
                nxt,receipt = projected_step(store,request,mode)
                fee = self.cost if receipt[1] else Q(0)
                if receipt not in groups:
                    groups[receipt] = [nxt,budget-fee,[Q(0)]*len(belief)]
                # This known-goal projection follows from delivered receipts.
                assert groups[receipt][0] == nxt and groups[receipt][1] == budget-fee
                groups[receipt][2][j] += mass
        return tuple((obs,sum(ws),tuple(w/sum(ws) for w in ws),nxt,b,committed)
            for obs,(nxt,b,ws) in sorted(groups.items()))

    @lru_cache(None)
    def solve(self, h, belief, store, budget, stopped=False):
        if h == 0:
            return Q(0),STOP
        best = None
        for action in ((STOP,) if stopped else ACTIONS):
            branches = self.branches(belief,store,budget,stopped,action)
            if branches is None:
                continue
            value = Q(0)
            for obs,mass,post,nxt,b,flag in branches:
                reward = Q(int(obs[0]))-self.price*(budget-b)
                value += mass*(reward+self.discount*self.solve(h-1,post,nxt,b,flag)[0])
            if best is None or value > best[0]:
                best = value,action
        assert best is not None
        return best

    def make_table(self, h, budget):
        nodes,assigned = [],{}
        def add(k,belief,store,b,stopped):
            key = (k,belief,store,b,stopped)
            if key in assigned:
                return assigned[key]
            idx = len(nodes)
            assigned[key] = idx
            nodes.append(None)
            value,action = self.solve(k,belief,store,b,stopped)
            node = {"id":idx,"remaining":k,"value":rat(value),"budget":rat(b),
                "action":action_json(action),"committed_stop":stopped,"branches":{}}
            if k:
                for obs,mass,post,nxt,b1,flag in self.branches(belief,store,b,stopped,action):
                    child = add(k-1,post,nxt,b1,flag)
                    node["branches"][f"{int(obs[0])},{int(obs[1])}"] = {
                        "probability":rat(mass),"next":child}
            nodes[idx] = node
            return idx
        add(h,self.prior,(False,),budget,False)
        return nodes

    def replay_table(self, h, budget, table):
        value = success = births_mean = fee_mean = total = Q(0)
        min_balance,traces = budget,[]
        founder = Organism(False,True,(),((0,False),),0)
        for theta,prior_mass in enumerate(self.prior):
            for modes in product((False,True),repeat=h):
                mode_mass = prior_mass
                for mode in modes:
                    mode_mass *= self.rs[theta] if mode else 1-self.rs[theta]
                for labels in product((False,True),repeat=h):
                    mass = mode_mass/(2**h)
                    if mass == 0:
                        continue
                    store,balance,node_id,committed = (founder,),budget,0,False
                    records,receipts,births,fees,payoff = [],[],0,Q(0),Q(0)
                    for t,(mode,label) in enumerate(zip(modes,labels)):
                        node = table[node_id]
                        encoded = node["action"]
                        request = (0,None) if committed or encoded["kind"] == "stop" else (
                            encoded["parent"],encoded["action"])
                        committed = committed or encoded["kind"] == "stop"
                        demand = self.cost if request[1] is not None else Q(0)
                        assert demand <= balance  # checked before using mode/label
                        store,obs,fee,record = native_step(store,request,mode,label,self.cost)
                        balance -= fee
                        assert balance >= 0
                        min_balance = min(min_balance,balance)
                        births += int(obs[0])
                        fees += fee
                        payoff += self.discount**t*(int(obs[0])-self.price*fee)
                        records.append(record)
                        receipts.append(obs)
                        node_id = node["branches"][f"{int(obs[0])},{int(obs[1])}"]["next"]
                    assert len(store) == 1+h and len(records) == h
                    ids = [r["child_slot"] for r in records if r["child_slot"] is not None]
                    assert len(ids) == len(set(ids))
                    total += mass
                    value += mass*payoff
                    success += mass*int(births > 0)
                    births_mean += mass*births
                    fee_mean += mass*fees
                    traces.append({"theta":theta,"mass":rat(mass),"modes":modes,
                        "labels":labels,"receipts":receipts,"records":records,
                        "payoff":rat(payoff),"balance":rat(balance)})
        assert total == 1 and value == self.solve(h,self.prior,(False,),budget)[0]
        return {"value":rat(value),"mass":rat(total),"at_least_one_birth":rat(success),
            "mean_births":rat(births_mean),"mean_fee":rat(fee_mean),
            "min_prefix_balance":rat(min_balance),"positive_full_tapes":len(traces)},traces

    def fixed_sequence_value(self, sequence, budget):
        value = Q(0)
        for theta,prior in enumerate(self.prior):
            for modes in product((False,True),repeat=len(sequence)):
                mass = prior
                for mode in modes:
                    mass *= self.rs[theta] if mode else 1-self.rs[theta]
                if mass == 0:
                    continue
                store,balance,payoff = (False,),budget,Q(0)
                for t,(action,mode) in enumerate(zip(sequence,modes)):
                    if action[1] is not None and balance < self.cost:
                        return None
                    store,obs = projected_step(store,action,mode)
                    fee = self.cost if obs[1] else Q(0)
                    balance -= fee
                    payoff += self.discount**t*(int(obs[0])-self.price*fee)
                value += mass*payoff
        return value

    def best_fixed(self, h, budget):
        best = None
        for sequence in product(ACTIONS[1:],repeat=h):
            value = self.fixed_sequence_value(sequence,budget)
            if value is not None and (best is None or value > best[0]):
                best = value,sequence
        return best

def run_case(name,rs,prior,price,discount,horizon,budget):
    started = time.perf_counter()
    p = Planner(rs,prior,price,discount)
    table = p.make_table(horizon,budget)
    replay,traces = p.replay_table(horizon,budget,table)
    fixed = p.best_fixed(horizon,budget)
    mu = {k:sum(w*r**k for w,r in zip(prior,rs)) for k in range(1,5)}
    out = {"case":name,"rs":list(map(rat,rs)),"prior":list(map(rat,prior)),
        "priced_write":rat(price),"write_cost":"1","discount":rat(discount),
        "horizon":horizon,"budget":rat(budget),
        "observation":["birth_bool","paid_write_bool"],"source_index_draws":1,
        "label_probability":"1/2","moments":{str(k):rat(v) for k,v in mu.items()},
        "optimal":replay,"returned_table_nodes":len(table),"best_fixed_value":rat(fixed[0]),
        "best_fixed_sequence":list(map(action_json,fixed[1])),
        "joint_minus_fixed":rat(Q(replay["value"])-fixed[0]),
        "shortsighted_value_from_damaged_start":"0" if price >= 1 else None,
        "seconds":time.perf_counter()-started,"planner_cache":p.solve.cache_info()._asdict()}
    if horizon == 2:
        candidate = max(Q(0),mu[1]*(1-price)+discount*mu[2])
        out["persistent_two_step_formula"] = rat(candidate)
        out["incorrect_redrawn_theta_repair_value"] = rat(mu[1]*(1-price)+discount*mu[1]**2)
        if budget >= 1 and price >= 1:
            assert candidate == Q(replay["value"])
    if horizon == 3 and price >= 1+discount and budget == 1:
        candidate = max(Q(0),mu[1]*(1-price)+(discount+discount**2)*mu[2])
        out["population_three_step_formula"] = rat(candidate)
        out["root_only_repair_value"] = rat(mu[1]*(1-price)+discount*mu[2]+discount**2*mu[3])
        assert candidate == Q(replay["value"])
    if horizon == 4 and price >= 1+discount+discount**2 and budget == 1:
        raw = mu[1]*(1-price)+(discount+discount**2)*mu[2]+discount**3*(2*mu[3]-mu[4])
        out["population_four_step_formula"] = rat(max(Q(0),raw))
        out["feedback_raw_gain_over_alternating_fixed"] = rat(discount**3*(mu[3]-mu[4]))
        assert max(Q(0),raw) == Q(replay["value"])
    return out,table,traces

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output",type=Path,required=True)
    parser.add_argument("--full-traces",action="store_true")
    args = parser.parse_args()
    args.output.mkdir(parents=True,exist_ok=True)
    cases = [
        ("persistent_theta_two_step",[Q(1,4),Q(3,4)],[Q(1,2),Q(1,2)],Q(13,10),Q(1,2),2,Q(1)),
        ("population_backup_three_step",[Q(1,4),Q(3,4)],[Q(1,2),Q(1,2)],Q(7,4),Q(3,4),3,Q(1)),
        ("receipt_feedback_four_step",[Q(3,4),Q(7,8)],[Q(1,2),Q(1,2)],Q(37,16),Q(3,4),4,Q(1)),
        ("zero_horizon",[Q(1,4),Q(3,4)],[Q(1,2),Q(1,2)],Q(13,10),Q(1,2),0,Q(1)),
        ("zero_budget",[Q(1,4),Q(3,4)],[Q(1,2),Q(1,2)],Q(13,10),Q(1,2),2,Q(0)),
        ("insufficient_prepay",[Q(1,4),Q(3,4)],[Q(1,2),Q(1,2)],Q(13,10),Q(1,2),2,Q(3,4)),
        ("all_fault",[Q(0)],[Q(1)],Q(13,10),Q(1,2),2,Q(1)),
        ("known_reliable_source",[Q(1)],[Q(1)],Q(13,10),Q(1,2),2,Q(1)),
    ]
    results = []
    for case in cases:
        out,table,traces = run_case(*case)
        prefix = args.output/case[0]
        raw = json.dumps(table,ensure_ascii=False,indent=2).encode()
        prefix.with_suffix(".table.json").write_bytes(raw)
        out["table_sha256"] = hashlib.sha256(raw).hexdigest()
        if args.full_traces:
            raw = json.dumps(traces,ensure_ascii=False,indent=2).encode()
            prefix.with_suffix(".traces.json").write_bytes(raw)
            out["full_traces_sha256"] = hashlib.sha256(raw).hexdigest()
        results.append(out)
    result = {"scope":"independent exact finite reference; original labels and failures retained",
        "source_contract":"known goal; one initial theta; single prepaid wallet; prefix birth/fee receipt; no parent/program oracle",
        "source_script_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),"results":results}
    (args.output/"REFERENCE_RESULTS.json").write_text(json.dumps(result,ensure_ascii=False,indent=2)+"\n")
    print(json.dumps(result,ensure_ascii=False,indent=2))

if __name__ == "__main__":
    main()
