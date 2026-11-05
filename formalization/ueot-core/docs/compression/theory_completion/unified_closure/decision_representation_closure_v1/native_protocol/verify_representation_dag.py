#!/usr/bin/env python3
"""Independent checker and original-Store executor for THIS exported Lean DAG.

Every legal alternative is checked, not only the chosen execution graph. The
prior PR441 memo result is read as independent reference evidence; its policy
is never substituted and its solver is never called by this checker.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import argparse
import hashlib
import json
import resource
import sys
import time

from representation_reference import load_reference

ACTION = {
    "stop": None, "root_idle": (0,None), "child1_idle": (1,None),
    "root_write_false": (0,False), "root_write_true": (0,True),
    "child1_write_false": (1,False), "child1_write_true": (1,True),
}
OBS = ((False,False),(False,True),(True,False),(True,True))


class InvalidInput(Exception):
    pass


class ResourceUnknown(Exception):
    pass


def require(condition, reason):
    if not condition:
        raise AssertionError(reason)


def rational(value):
    if not isinstance(value,str):
        raise InvalidInput("rational quantities must be strings")
    try:
        return Q(value)
    except (ValueError,ZeroDivisionError) as exc:
        raise InvalidInput("invalid rational string") from exc


def nat(value):
    if type(value) is not int or value < 0:
        raise InvalidInput("natural-number field has an invalid value")
    return value


def boolean(value):
    if type(value) is not bool:
        raise InvalidInput("boolean field has an invalid value")
    return value


def no_duplicate_keys(pairs):
    result = {}
    for key,value in pairs:
        if key in result:
            raise InvalidInput("duplicate JSON key: "+str(key))
        result[key] = value
    return result


@dataclass(frozen=True)
class State:
    elapsed: int
    s: int
    f: int
    paid: int
    root: bool
    child: bool | None
    stopped: bool
    fresh: bool


def state_of(raw):
    if not isinstance(raw,dict) or set(raw) != {"elapsed","s","f","paidCount","q"}:
        raise InvalidInput("unexpected statistic fields")
    q = raw["q"]
    if not isinstance(q,dict) or set(q) != {"root","child","stopped","fresh"}:
        raise InvalidInput("unexpected local-state fields")
    child = q["child"]
    if child is not None:
        boolean(child)
    return State(nat(raw["elapsed"]),nat(raw["s"]),nat(raw["f"]),nat(raw["paidCount"]),
        boolean(q["root"]),child,boolean(q["stopped"]),boolean(q["fresh"]))


def request(st, action):
    return (0,None) if st.stopped or action is None else action


def normal_receipt(st, action, goal):
    parent, bit = request(st,action)
    old = st.root if parent == 0 else st.child
    if old is None:
        return False,False
    return (old if bit is None else bit) == goal, bit is not None


def update(st, action, obs, goal):
    parent,_ = request(st,action)
    bit = goal if obs[0] else not goal
    root = st.root if parent else bit
    child = (goal if obs[0] else None) if st.fresh else (
        bit if parent and st.child is not None else st.child)
    informative = any(normal_receipt(st,action,goal))
    seen = any(obs)
    return State(st.elapsed+1,st.s+int(informative and seen),
        st.f+int(informative and not seen),st.paid+int(obs[1]),
        root,child,st.stopped or action is None,False)


class Source:
    def __init__(self,data):
        self.H = nat(data["horizon"])
        self.rs = tuple(map(rational,data["normal_probabilities"]))
        self.prior = tuple(map(rational,data["prior"]))
        self.c,self.price,self.d,self.B = map(rational,
            (data["tariff"],data["price"],data["discount"],data["wallet"]))
        self.goal = boolean(data["goal"])
        if not self.rs or len(self.rs)!=len(self.prior) or sum(self.prior)!=1:
            raise InvalidInput("invalid finite source/prior")
        if any(not 0<=r<=1 for r in self.rs) or any(w<0 for w in self.prior):
            raise InvalidInput("invalid probability")
        if self.c<=0 or self.price<0 or self.B<0 or not 0<=self.d<=1:
            raise InvalidInput("invalid cost, wallet or discount")
        if data.get("initial_damaged") is not True or not self.goal:
            raise ResourceUnknown("independent native adapter covers the registered known-true-goal damaged founder")
        self.posteriors = {}

    def posterior(self,st):
        key = st.s,st.f
        if key not in self.posteriors:
            weights = tuple(w*r**st.s*(1-r)**st.f for w,r in zip(self.prior,self.rs))
            total = sum(weights)
            require(total>0,"positive generated graph contains a zero count normalizer")
            self.posteriors[key] = tuple(w/total for w in weights)
        return self.posteriors[key]

    def balance(self,st):
        return self.B-self.c*st.paid

    def menu(self,st):
        balance = max(Q(0),self.balance(st))
        # Original REQUESTED cap, including requests made after committed stop.
        return tuple(name for name,a in ACTION.items()
            if (self.c if a is not None and a[1] is not None else Q(0)) <= balance)

    def branches(self,st,name):
        action=ACTION[name]
        normal=normal_receipt(st,action,self.goal)
        mean=sum(w*r for w,r in zip(self.posterior(st),self.rs))
        probs={}
        probs[normal]=probs.get(normal,Q(0))+mean
        probs[(False,False)]=probs.get((False,False),Q(0))+1-mean
        return {o:(p,update(st,action,o,self.goal)) for o,p in probs.items() if p>0}


def validate_graph(raw,reference,max_nodes):
    data=json.loads(raw,object_pairs_hook=no_duplicate_keys)
    if data.get("schema")!="UEOT/DECISION_REPRESENTATION_DAG/V1":
        raise InvalidInput("unexpected DAG schema")
    require(data.get("checks",{}).get("bellman") is True,
        "the actual Lean producer did not report a successful exact Bellman certificate")
    require(data.get("checks",{}).get("node_bounds") is True,
        "the actual Lean producer did not report a successful all-row bound check")
    source=Source(data)
    rows=data.get("nodes")
    if not isinstance(rows,list) or not rows:
        raise InvalidInput("empty or invalid node array")
    if len(rows)>max_nodes:
        raise ResourceUnknown("registered independent checker node resource limit exceeded")
    root=nat(data["root_id"])
    require(root<len(rows),"invalid root index")
    states,values,keys=[],[],set()
    for index,row in enumerate(rows):
        require(nat(row["id"])==index,"node IDs must be the actual array positions")
        st=state_of(row["state"])
        remaining=nat(row["remaining"])
        require(remaining+st.elapsed==source.H,"remaining/elapsed horizon mismatch")
        require(st.s+st.f<=st.elapsed and st.paid<=st.elapsed,"source count bound violated")
        require(source.balance(st)>=0,"a positive graph state has overspent the wallet")
        require(st.fresh==(st.elapsed==0),"first-allocation phase is inconsistent with elapsed time")
        source.posterior(st)
        key=(remaining,st)
        require(key not in keys,"duplicate stored canonical node key")
        keys.add(key)
        states.append(st)
        values.append(rational(row["value"]))
    require(states[root]==State(0,0,0,0,not source.goal,None,False,True),"root is not the frozen initial statistic")
    require(rational(data["value"])==values[root],"declared root value differs from THIS root row")
    edge_maps={}
    proof_edges=0
    for index,row in enumerate(rows):
        choice=row["chosen_action"]
        if choice not in ACTION:
            raise InvalidInput("unknown chosen action")
        alternatives=row["alternatives"]
        if row["remaining"]==0:
            require(values[index]==0 and alternatives==[],"terminal value/alternatives are not zero/empty")
            continue
        menu=source.menu(states[index])
        require(tuple(a["action"] for a in alternatives)==menu,"certificate omits/reorders a legal original-menu alternative")
        scores=[]
        for alternative in alternatives:
            name=alternative["action"]
            expected=source.branches(states[index],name)
            edges={}
            q=Q(0)
            for edge in alternative["edges"]:
                obs=tuple(map(boolean,edge["obs"]))
                require(len(obs)==2 and obs in OBS,"invalid receipt pair")
                require(obs not in edges,"duplicate positive receipt edge")
                target=nat(edge["next"])
                require(target<len(rows),"edge points outside THIS graph")
                prob=rational(edge["prob"])
                require(obs in expected and prob==expected[obs][0],"edge is not the exact positive source receipt mass")
                require(states[target]==expected[obs][1],"edge target statistic is not the actual receipt update")
                require(rows[target]["remaining"]+1==row["remaining"],"edge does not reduce the finite horizon")
                require(source.c*int(obs[1])<=source.balance(states[index]),"positive source edge cannot pay its literal fee")
                q+=prob*(int(obs[0])-source.price*source.c*int(obs[1])+source.d*values[target])
                edges[obs]=(prob,target)
            require(set(edges)==set(expected),"certificate omits a positive successor of a legal alternative")
            require(q==rational(alternative["q"]),"declared alternative Q differs from its complete exact source sum")
            edge_maps[index,name]=edges
            proof_edges+=len(edges)
            scores.append(q)
        best=max(scores)
        expected_choice=menu[scores.index(best)]
        require(choice==expected_choice,"choice fails the original earlier-action tie order")
        require(values[index]==best,"node value is not the all-action maximum")
    # Count the actual proof graph, not just a quotient of a larger copied array.
    reached={root}
    frontier=[root]
    while frontier:
        index=frontier.pop()
        for alt in rows[index]["alternatives"]:
            for _,target in edge_maps[index,alt["action"]].values():
                if target not in reached:
                    reached.add(target)
                    frontier.append(target)
    require(len(reached)==len(rows),"artifact contains extra rows outside the generated positive all-action graph")
    require(len(rows)<=24*(source.H+1)**4,"actual stored graph violates the proved conservative source bound")
    metrics=data.get("metrics",{})
    if "node_count" in metrics:
        require(nat(metrics["node_count"])==len(rows),"declared actual node count differs from the array")
    if "proof_edges" in metrics:
        require(nat(metrics["proof_edges"])==proof_edges,"declared proof-edge count differs from all action edges")
    for counter in ("computed_nodes","memo_entries"):
        if counter in metrics:
            require(nat(metrics[counter])==len(rows),"declared storage counter differs from the actual node array: "+counter)
    if "node_bound" in metrics:
        require(nat(metrics["node_bound"])==24*(source.H+1)**4,"declared bound differs from the proved source bound")
    rp=reference["parameters"]
    require(reference["status"]=="PASS","reference attempt was not successful")
    require(reference["case"]==data["case"],"reference and THIS case identities differ")
    require((tuple(map(Q,rp["r"])),tuple(map(Q,rp["prior"])),rp["H"],Q(rp["B"]),Q(rp["c"]),Q(rp["price"]),Q(rp["d"]))==
        (source.rs,source.prior,source.H,source.B,source.c,source.price,source.d),"reference and THIS public inputs differ")
    require(values[root]==Q(reference["value"]),"THIS exact value disagrees with the preserved independent memo baseline")
    return data,source,rows,states,values,edge_maps,proof_edges


def execution_graph_metrics(source,rows,states,edge_maps,root):
    reachable={root}
    frontier=[root]
    edges=0
    while frontier:
        j=frontier.pop()
        if not rows[j]["remaining"]:
            continue
        for _,k in edge_maps[j,rows[j]["chosen_action"]].values():
            edges+=1
            if k not in reachable:
                reachable.add(k); frontier.append(k)
    event,births,fees,payments={},{},{},{}
    for j in sorted(reachable,key=lambda j:rows[j]["remaining"]):
        if not rows[j]["remaining"]:
            event[j]=births[j]=fees[j]=Q(0); payments[j]={0:Q(1)}
            continue
        event[j]=births[j]=fees[j]=Q(0); distribution={}
        for o,(p,k) in edge_maps[j,rows[j]["chosen_action"]].items():
            event[j]+=p*(1 if o[0] else event[k])
            births[j]+=p*(int(o[0])+births[k])
            fees[j]+=p*(source.c*int(o[1])+fees[k])
            for count,mass in payments[k].items():
                new_count=count+int(o[1])
                distribution[new_count]=distribution.get(new_count,Q(0))+p*mass
        payments[j]=distribution
    return {"node_count":len(reachable),"edge_count":edges,
        "at_least_one_birth":str(event[root]),"expected_total_births":str(births[root]),
        "expected_total_fee":str(fees[root]),
        "minimum_prefix_balance":str(min(source.balance(states[j]) for j in reachable)),
        "total_paid_count_distribution":{str(k):str(v) for k,v in sorted(payments[root].items())}}


def replay_one(ref,source,rows,states,edge_maps,root,theta,modes,labels):
    store=(ref.Organism(False,True,(),((0,False),),0),)
    j,balance,stopped,s,f,paid=root,source.B,False,0,0,0
    records=[]; payoff=Q(0); births=0
    for t,(mode,label) in enumerate(zip(modes,labels)):
        st=states[j]
        local_child=None if len(store)<2 or store[1] is None else store[1].physical
        require(st==State(t,s,f,paid,store[0].physical,local_child,stopped,len(store)==1),
            "THIS node statistic disagrees with the hidden native execution")
        name=rows[j]["chosen_action"]; action=ACTION[name]
        demand=source.c if action is not None and action[1] is not None else Q(0)
        require(demand<=balance,"THIS native execution cannot prepay the selected request")
        effective=(0,None) if stopped or action is None else action
        parent,bit=effective
        current=store[parent] if parent<len(store) else None
        # The audit uses hidden fields to check the observer; they never enter
        # action selection, which has already read THIS indexed graph row.
        informative=current is not None and (bit is not None or current.physical==current.program)
        s+=int(informative and mode); f+=int(informative and not mode)
        stopped=stopped or action is None
        store,obs,fee,record=ref.native_step(store,effective,mode,label,source.c)
        balance-=fee; paid+=int(obs[1]); births+=int(obs[0])
        require(balance>=0,"literal native subtraction is negative")
        require(obs in edge_maps[j,name],"actual positive native receipt is absent from THIS graph")
        _,nxt=edge_maps[j,name][obs]
        payoff+=source.d**t*(int(obs[0])-source.price*fee)
        record.update(node=j,next=nxt,requested_action=name,receipt=list(obs),balance=str(balance),
            informative=informative,informative_normal_count=s,informative_fault_count=f)
        records.append(record);j=nxt
    require(rows[j]["remaining"]==0 and len(store)==source.H+1,"THIS driver did not consume exactly the finite protocol ticks")
    require(balance==source.B-source.c*paid,"native payment count and literal ledger disagree")
    return {"theta":theta,"modes":list(modes),"labels":list(labels),"records":records,
        "payoff":str(payoff),"births":births,"paid_count":paid,"final_balance":str(balance),
        "final_store":[None if x is None else x.physical for x in store],
        "final_stopped":stopped}


def check_direct_packed_runs(ref,data,source,rows,states,edge_maps,root):
    runs=data.get("direct_packed_runs")
    require(isinstance(runs,list),"actual Lean indexed executions are missing")
    seen=set(); checked=[]
    for run in runs:
        theta=nat(run["theta"])
        require(theta<len(source.prior) and source.prior[theta]>0,
            "direct execution uses an unsupported initial source index")
        require(theta not in seen,"duplicate direct source-index execution")
        seen.add(theta)
        noise=run["noise"]
        require(isinstance(noise,list) and len(noise)==source.H,"direct execution noise word has wrong length")
        for z in noise:
            require(isinstance(z,list) and len(z)==2,"invalid mode/label pair")
            boolean(z[0]); boolean(z[1])
        modes=tuple(z[0] for z in noise); labels=tuple(z[1] for z in noise)
        mass=source.prior[theta]
        for mode in modes:
            mass*=(source.rs[theta] if mode else 1-source.rs[theta])/2
        require(mass>0 and rational(run["source_mass"])==mass,
            "direct execution word is not positive with its declared full source mass")
        native=replay_one(ref,source,rows,states,edge_maps,root,theta,modes,labels)
        require(run["requests"]==[r["requested_action"] for r in native["records"]],
            "Lean direct indexed requests differ from THIS native controller")
        require(run["receipts"]==[r["receipt"] for r in native["records"]],
            "Lean direct indexed receipts differ from the original native source")
        require(rational(run["payoff"])==Q(native["payoff"]),
            "Lean direct payoff differs from actual full native fees and births")
        require(isinstance(run["final_store"],list),"invalid direct final physical store")
        for bit in run["final_store"]:
            if bit is not None:
                boolean(bit)
        require(run["final_store"]==native["final_store"] and
            boolean(run["final_stopped"])==native["final_stopped"],
            "Lean direct final packed world differs from original native execution")
        checked.append({"theta":theta,"source_mass":str(mass),"payoff":native["payoff"],
            "paid_count":native["paid_count"],"final_balance":native["final_balance"]})
    require(seen=={i for i,p in enumerate(source.prior) if p>0},
        "a positive initial source index lacks its direct Lean indexed execution")
    return {"status":"PASS","checked_runs":checked,
        "scope":"Actual Lean packedRun output checked against the same THIS graph executed by the original full-record interpreter"}


def native_checks(ref,source,rows,states,values,edge_maps,root):
    traces=[]; total=value=success=Q(0)
    full=source.H<=4
    if full:
        patterns=list(product((False,True),repeat=source.H))
        labels_list=list(product((False,True),repeat=source.H))
    else:
        h=source.H
        patterns=list(dict.fromkeys([
            tuple([True]*h),tuple([False]*h),tuple(t%2==0 for t in range(h)),
            tuple(t%2==1 for t in range(h)),tuple(t<2 for t in range(h)),
            tuple(t==0 or t>=3 for t in range(h)),tuple(t!=1 for t in range(h)),
            tuple(t<4 or t==h-1 for t in range(h))]))
        labels_list=[tuple([False]*h),tuple(t%2==0 for t in range(h))]
    for theta,prior in enumerate(source.prior):
        for modes in patterns:
            mass=prior
            for mode in modes:
                mass*=source.rs[theta] if mode else 1-source.rs[theta]
            for labels in labels_list:
                path_mass=mass/Q(2**source.H)
                if not path_mass:
                    continue
                trace=replay_one(ref,source,rows,states,edge_maps,root,theta,modes,labels)
                trace["mass"]=str(path_mass); traces.append(trace)
                total+=path_mass;value+=path_mass*Q(trace["payoff"])
                success+=path_mass*int(trace["births"]>0)
    if full:
        require(total==1 and value==values[root],"complete THIS native tape replay differs from the certified root value")
    return {"complete_enumeration":full,"native_paths":len(traces),
        "enumerated_mass":str(total),
        "actual_value":str(value) if full else None,
        "at_least_one_birth":str(success) if full else None,
        "max_paid_count_on_checked_paths":max((x["paid_count"] for x in traces),default=0),
        "qualification": "Complete mode/label/source replay" if full else
            "Fixed distinguishing native paths only; exact all-action certificate and general source theorem carry the long-instance value claim"},traces


def merger_checks(source,rows,states,edge_maps,root):
    if source.H<3:
        return {"applicable":False,"reason":"horizon is shorter than the registered three-tick witnesses"}
    def follow(history):
        j=root
        for name,o in history:
            edges=edge_maps.get((j,name),{})
            if o not in edges:
                return None
            j=edges[o][1]
        return j
    a=follow([("root_write_true",(True,True)),("root_idle",(False,False)),("child1_idle",(True,False))])
    b=follow([("root_write_true",(True,True)),("child1_idle",(True,False)),("root_idle",(False,False))])
    if a is None or b is None:
        return {"applicable":False,"reason":"a witness history has zero source mass or unavailable prepaid action"}
    require(a==b,"the two genuine equal-summary histories were stored as different graph nodes")
    ia=follow([("root_write_true",(True,True)),("root_idle",(True,False)),("root_idle",(False,False))])
    ib=follow([("root_write_true",(True,True)),("root_idle",(False,False)),("root_idle",(False,False))])
    require(ia is not None and ib is not None,"positive insufficient-summary witness is missing")
    require(states[ia]!=states[ib] and states[ia].s==2 and states[ib].s==1 and states[ia].f==states[ib].f==1,
        "the summary has forgotten the informative-count distinction")
    return {"applicable":True,"merge_history_a_node":a,"merge_history_b_node":b,
        "actual_same_node":True,"insufficient_summary_history_a_node":ia,
        "insufficient_summary_history_b_node":ib,
        "qualification":"Paths traverse the all-action proof graph; they need not both follow its chosen policy."}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--dag-output",type=Path,required=True)
    parser.add_argument("--reference-result",type=Path,required=True)
    parser.add_argument("--reference-source",type=Path,required=True)
    parser.add_argument("--output",type=Path,required=True)
    parser.add_argument("--max-nodes",type=int,default=1000000)
    args=parser.parse_args()
    args.output.mkdir(parents=True,exist_ok=True)
    if (args.output/"THIS_DAG_CHECK.json").exists():
        parser.error("use a fresh directory to preserve prior attempts")
    start=time.perf_counter()
    raw=args.dag_output.read_bytes();reference_raw=args.reference_result.read_bytes()
    report={"schema":"UEOT/THIS_REPRESENTATION_DAG_CHECK/V1",
        "dag_output_sha256":hashlib.sha256(raw).hexdigest(),
        "reference_result_sha256":hashlib.sha256(reference_raw).hexdigest(),
        "checker_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    try:
        ref,ref_hash=load_reference(args.reference_source)
        report["native_reference_source_sha256"]=ref_hash
        reference=json.loads(reference_raw)
        loading=time.perf_counter()
        data,source,rows,states,values,edge_maps,proof_edges=validate_graph(raw,reference,args.max_nodes)
        report["all_action_certificate_seconds"]=time.perf_counter()-loading
        root=data["root_id"]
        policy_metrics=execution_graph_metrics(source,rows,states,edge_maps,root)
        mergers=merger_checks(source,rows,states,edge_maps,root)
        native_start=time.perf_counter()
        native,traces=native_checks(ref,source,rows,states,values,edge_maps,root)
        direct_runs=check_direct_packed_runs(ref,data,source,rows,states,edge_maps,root)
        report["native_check_seconds"]=time.perf_counter()-native_start
        trace_raw=json.dumps(traces,ensure_ascii=False,indent=2).encode()
        (args.output/"THIS_NATIVE_TRACES.json").write_bytes(trace_raw)
        report.update(status="PASS",case=data["case"],root_value=str(values[root]),
            actual_graph_nodes=len(rows),actual_proof_edges=proof_edges,
            conservative_node_bound=24*(source.H+1)**4,
            all_original_menu_alternatives_checked=True,
            earlier_action_tie_order_preserved=True,all_rows_reachable_in_proof_graph=True,
            execution_graph=policy_metrics,actual_merge=mergers,native=native,
            direct_lean_execution=direct_runs,
            traces_sha256=hashlib.sha256(trace_raw).hexdigest(),
            traces_bytes=len(trace_raw),dag_bytes=len(raw),
            peak_process_rss_bytes=int(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)*(1 if sys.platform=="darwin" else 1024),
            total_seconds=time.perf_counter()-start,
            qualification="THIS indexed Lean artifact is checked and executed. Existing memo reference uses STOP as a justified representative after committed stop; THIS certificate checks the unreduced original requested-action menu. No old Lean observation tree was recomputed.")
        code=0
    except (InvalidInput,ResourceUnknown,AssertionError,KeyError,ValueError,TypeError) as exc:
        status="UNKNOWN" if isinstance(exc,ResourceUnknown) else ("FAIL" if isinstance(exc,AssertionError) else "INVALID_INPUT")
        report.update(status=status,reason=str(exc),total_seconds=time.perf_counter()-start)
        code=2 if status=="UNKNOWN" else 1
    (args.output/"THIS_DAG_CHECK.json").write_text(json.dumps(report,ensure_ascii=False,indent=2)+"\n")
    print(json.dumps(report,ensure_ascii=False,indent=2))
    return code


if __name__=="__main__":
    sys.exit(main())
