"""Produce rational certificates for the frozen complete-record model.

This is a small sufficient-certificate producer, not a general quantum solver.
The independent checker derives the source and validates every reported bound.
No hardware calibration or empirical full-CQ claim is produced.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path


def decision(upper, precision, lower=None):
    if upper is not None and upper <= precision:
        return "CERTIFIED_FEASIBLE"
    if lower is not None and lower > precision:
        return "CERTIFIED_INFEASIBLE"
    return "INSUFFICIENT_CERTIFICATE"


def tagged_word_law(first, second0, second1):
    return {"00": (1-first)*(1-second0), "01": (1-first)*second0,
            "10": first*(1-second1), "11": first*second1}


def tv(p, q):
    return sum(abs(p.get(k,F(0))-q.get(k,F(0))) for k in p.keys()|q.keys())/2


def produce(model):
    lo, hi = map(F, model["q_interval"])
    middle = (lo+hi)/2
    delta = (hi-lo)/2
    if middle != F(1,2) or not 0 <= delta <= F(1,2):
        raise ValueError("This analytic certificate requires its declared symmetric interval")
    wm = F(model["memoryless_label1_weight"])
    if wm != middle:
        raise ValueError("memoryless producer requires the frozen central weight")
    adaptive = tagged_word_law(F(model["adaptive_first_label1_weight"]),
                              F(model["adaptive_second_label1_given_0"]),
                              F(model["adaptive_second_label1_given_1"]))
    expected = {"00": F(1,4)+delta**2, "11": F(1,4)+delta**2,
                "01": F(1,4)-delta**2, "10": F(1,4)-delta**2}
    if adaptive != expected:
        raise ValueError("proposed adaptive policy is not the analytic minimax construction")
    tail = F(model["analytic_energy_budget"])/(model["analytic_cutoff_N"]+1)
    # This frozen example is chosen to give an exact rational square root.
    from math import isqrt
    rn, rd = isqrt(tail.numerator), isqrt(tail.denominator)
    if rn*rn != tail.numerator or rd*rd != tail.denominator:
        raise ValueError("nonrational square root needs an interval certificate")
    cut = F(rn,rd)
    prep = cut+tail
    e_mem = delta*(1+delta)
    e_adapt = delta
    eps = F(model["required_full_output_precision"])
    smin = 1-hi/2
    # All results derived here are candidates for the independent checker.
    out = {
        "schema": "ueot-qm.micro-robust-candidate/1",
        "scope": "complete tagged CQ, all declared finite references and inputs; exact shared gates",
        "optimization_scope": "minimax/lower bounds over frozen design interval, not every narrower realized calibration interval",
        "new_hardware_data": False,
        "policy_word_weights": {k:str(v) for k,v in sorted(adaptive.items())},
        "memoryless_error": str(e_mem),
        "adaptive_error": str(e_adapt),
        "uniform_policy_lower_bound": str(delta),
        "source_acceptance_lower": str(smin*smin),
        "tail_mass_upper": str(tail),
        "normalized_truncation_upper": str(cut),
        "complete_preparation_upper": str(prep),
        "memoryless_full_output_upper": str(prep+e_mem),
        "adaptive_full_output_upper": str(prep+e_adapt),
        "remaining_unmeasured_physical_error_margin": str(eps-prep-e_adapt),
        "required_precision": str(eps),
        "classification": {
            "adaptive_model": decision(prep+e_adapt, eps),
            "memoryless_model": decision(prep+e_mem, eps),
            "design_region_uniform_precision_1_over_100": decision(None,F(1,100),delta),
            "singleton_zero_action_precision_1_over_100": decision(None,F(1,100),lo),
            "generic_insufficient_bound": decision(F(1,5),F(1,20)),
            "maximum_distance_bound": decision(F(1),F(1,20))
        },
        "generic_triangle_example": {
            "r_nominal": "1/100", "eta_T": "1/200",
            "weights": ["1/3","2/3"], "eta_actions": ["1/100","1/50"],
            "derived_upper": str(F(1,100)+F(1,200)+F(1,3)*F(1,100)+F(2,3)*F(1,50))
        },
        "not_certified": ["actual device membership in this model", "actual gate matching",
                          "measured full-CQ distance", "measured resource advantage"]
    }
    return out


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--model", type=Path, default=Path(__file__).with_name("frozen_model.json"))
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("candidate.json"))
    args=parser.parse_args()
    out=produce(json.loads(args.model.read_text()))
    out["model_sha256"]=hashlib.sha256(args.model.read_bytes()).hexdigest()
    out["producer_sha256"]=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    args.output.write_text(json.dumps(out,indent=2,ensure_ascii=False)+"\n")
    print(json.dumps({"output":str(args.output),"classification":out["classification"]}))


if __name__ == "__main__":
    main()
