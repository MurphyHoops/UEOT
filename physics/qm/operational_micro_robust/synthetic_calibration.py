"""Synthetic-only calibration and held-out complete-record pipeline.

Generation has explicit synthetic theta; analysis consumes only recorded
flags and frozen settings, never the generating theta. This finite record
tester does not measure quantum terminal states or certify a device model.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import random


RECORDS=("f","0f","1f","00","01","10","11")


def synthetic_flag(rng):
    """Exact ideal q=1/2,s=3/4 distribution from an integer random draw."""
    n=rng.randrange(8)
    return "0" if n<3 else "1" if n<6 else "f"


def generate(model, out):
    out.mkdir(parents=True,exist_ok=True)
    rng=random.Random(model["calibration"]["synthetic_seed"])
    flags="".join(synthetic_flag(rng) for _ in range(model["calibration"]["shots"]))
    # Index is the complete logical order. No fictitious physical timestamps.
    (out/"synthetic_calibration_flags.txt").write_text(flags+"\n")
    rng=random.Random(model["holdout"]["source_seed"])
    raw=[]
    for _ in range(model["holdout"]["shots_per_protocol"]):
        a=synthetic_flag(rng)
        raw.append(a if a=="f" else a+synthetic_flag(rng))
    (out/"synthetic_source_holdout.txt").write_text("\n".join(raw)+"\n")
    rng=random.Random(model["holdout"]["compiled_seed"])
    compiled=[]
    for _ in range(model["holdout"]["shots_per_protocol"]):
        a=str(rng.randrange(2))
        probability=F(model["adaptive_second_label1_given_"+a])
        b="1" if rng.randrange(probability.denominator)<probability.numerator else "0"
        compiled.append(a+b)
    (out/"synthetic_compiled_holdout.txt").write_text("\n".join(compiled)+"\n")
    provenance={"classification":"SYNTHETIC_ONLY", "new_hardware_data":False,
                "generating_model":{"q":"1/2","s":"3/4"},
                "calibration_seed":model["calibration"]["synthetic_seed"],
                "source_holdout_seed":model["holdout"]["source_seed"],
                "compiled_holdout_seed":model["holdout"]["compiled_seed"],
                "record_order":"character/line order is logical shot order; physical time not simulated",
                "assumptions":["iid source flags", "fixed parameters", "ideal preparation/readout",
                               "known fresh source state per run", "no leakage in ideal model"],
                "real_world_absences":["physical timestamps", "hardware gate identities",
                                      "measured energy", "measured costs", "terminal-state tomography"]}
    (out/"synthetic_provenance.json").write_text(json.dumps(provenance,indent=2)+"\n")


def calibration_from_flags(path, n_expected, radius, design):
    flags=path.read_text().strip()
    if len(flags)!=n_expected or set(flags)-set("01f"):
        raise ValueError("Missing, extra or illegal calibration records; do not silently discard them")
    counts={k:flags.count(k) for k in "01f"}
    qhat=F(2*counts["f"],len(flags))
    lo=max(F(0),qhat-radius); hi=min(F(1),qhat+radius)
    nonempty=lo<=hi
    contained=nonempty and design[0]<=lo<=hi<=design[1]
    return {"counts":counts,"shots":len(flags),"qhat":str(qhat),
            "q_confidence_interval":[str(lo),str(hi)],"nonempty":nonempty,
            "joint_set":"C_q x allowed phase x allowed exchange; s=1-q/2",
            "phase_exchange_identified":False,"gate_matching_calibrated":False,
            "deployment_status":"CERTIFIED_MODEL_BOUND" if contained else "INSUFFICIENT_CERTIFICATE",
            "claim":"coverage conditional on iid fixed-q ideal-flag model; not hardware model validation",
            "minimax_claim":"design-region policy reused conservatively; not optimized for this narrower interval"}


def mul_interval(*intervals):
    # All factors below are nonnegative. This outer bound is conservative and
    # does not posit separate independent physical values for repeated q.
    low=F(1); high=F(1)
    for a,b in intervals:low*=a;high*=b
    return low,high


def source_probability_outer_bounds(lo,hi):
    p=(lo,hi); qbar=(1-hi,1-lo); s=(1-hi/2,1-lo/2); fail=(lo/2,hi/2)
    return {"f":fail,"0f":mul_interval(s,qbar,fail),"1f":mul_interval(s,p,fail),
            "00":mul_interval(s,s,qbar,qbar),"01":mul_interval(s,s,p,qbar),
            "10":mul_interval(s,s,p,qbar),"11":mul_interval(s,s,p,p)}


def holdout(path,n_expected,predicted,radius):
    records=path.read_text().splitlines()
    if len(records)!=n_expected or set(records)-set(RECORDS):
        raise ValueError("Incomplete/invalid held-out record contract")
    count=Counter(records)
    cells=[]
    for r in RECORDS:
        frequency=F(count[r],len(records)); lo,hi=predicted[r]
        distance=max(lo-frequency,frequency-hi,F(0))
        cells.append({"record":r,"count":count[r],"frequency":str(frequency),
                      "predicted_probability_outer_interval":[str(lo),str(hi)],
                      "distance_to_interval":str(distance),"within_frozen_radius":distance<=radius})
    return {"shots":len(records),"all_records_retained":True,"cells":cells,
            "status":"NOT_REJECTED_BY_FINITE_RECORD_TESTERS" if all(c["within_frozen_radius"] for c in cells)
                     else "REJECTED_BY_FROZEN_RECORD_TESTER",
            "classification":"synthetic record-law check, not empirical verification or full-CQ tomography",
            "limitations":"cell intervals are conservative images of one shared-q set; passing is not joint model identification"}


def analyze(model,out):
    design=tuple(map(F,model["q_interval"]))
    cal=calibration_from_flags(out/"synthetic_calibration_flags.txt",model["calibration"]["shots"],
                               F(model["calibration"]["q_confidence_radius"]),design)
    lo,hi=map(F,cal["q_confidence_interval"])
    if not cal["nonempty"]:raise ValueError("Empty calibration confidence set")
    source_pred=source_probability_outer_bounds(lo,hi)
    a=F(model["adaptive_first_label1_weight"])
    p0=F(model["adaptive_second_label1_given_0"]);p1=F(model["adaptive_second_label1_given_1"])
    words={"00":(1-a)*(1-p0),"01":(1-a)*p0,"10":a*(1-p1),"11":a*p1}
    compiled_pred={r:(words.get(r,F(0)),)*2 for r in RECORDS}
    n=model["holdout"]["shots_per_protocol"]
    rad=F(model["holdout"]["cell_frequency_radius"])
    result={"classification":"SYNTHETIC_ONLY","new_hardware_data":False,
            "calibration":cal,
            "source_holdout":holdout(out/"synthetic_source_holdout.txt",n,source_pred,rad),
            "compiled_holdout":holdout(out/"synthetic_compiled_holdout.txt",n,compiled_pred,rad),
            "fixed_error_allocation":{"calibration":"<=1/20", "record_testers":"<=1/20",
                                      "union_total":"<=1/10 conditional on correct model"},
            "resource_counts":{"calibration_flag_shots":model["calibration"]["shots"],
                               "source_holdout_attempts":n,"compiled_holdout_attempts":n,
                               "cost_units":"counts only; no measured time/energy/money"},
            "dependent_shot_failure_control":{"construction":"One latent flag repeated for all 80000 shots",
                                              "same_marginals":True,
                                              "coverage_at_q_one_half":"0",
                                              "reason":"marginals alone do not imply iid concentration"},
            "source_action_mismatch_control":{"calibrated_by_flag_counts":False,
                                              "status":"UNVERIFIED_PHYSICAL_PREMISE"},
            "raw_data_hashes":{p.name:hashlib.sha256(p.read_bytes()).hexdigest()
                               for p in sorted(out.glob("synthetic_*holdout.txt"))}}
    result["raw_data_hashes"]["synthetic_calibration_flags.txt"]=hashlib.sha256((out/"synthetic_calibration_flags.txt").read_bytes()).hexdigest()
    return result


def main():
    p=argparse.ArgumentParser()
    p.add_argument("--model",type=Path,default=Path(__file__).with_name("frozen_model.json"))
    p.add_argument("--output-dir",type=Path,default=Path(__file__).with_name("synthetic_output"))
    p.add_argument("--analyze-only",action="store_true")
    a=p.parse_args();model=json.loads(a.model.read_text())
    if not a.analyze_only:generate(model,a.output_dir)
    result=analyze(model,a.output_dir)
    result["analysis_source_sha256"]=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    result["model_sha256"]=hashlib.sha256(a.model.read_bytes()).hexdigest()
    (a.output_dir/"synthetic_analysis.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({"classification":result["classification"],"calibration":result["calibration"],
                      "source_holdout":result["source_holdout"]["status"],
                      "compiled_holdout":result["compiled_holdout"]["status"]}))


if __name__=="__main__":main()
