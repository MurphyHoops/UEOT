#!/usr/bin/env python3
"""Independent B-side checks of C's fixed candidate, without importing C code."""
from fractions import Fraction as F
from pathlib import Path
import argparse
import hashlib
import json


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--c-dir", type=Path, default=Path(__file__).parent.parent/"research_c")
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("C_INDEPENDENT_CHECK.json"))
    args = parser.parse_args()
    root = args.c_dir
    model = json.loads((root/"frozen_model.json").read_text())
    candidate = json.loads((root/"candidate.json").read_text())
    lo, hi = map(F, model["q_interval"])
    delta = (hi-lo)/2
    Q = {k: F(v) for k, v in candidate["policy_word_weights"].items()}
    def law(q):
        return {"00": (1-q)**2, "01": q*(1-q), "10": q*(1-q), "11": q*q}
    def tv(a, b):
        return sum(abs(a[k]-b[k]) for k in a)/2
    checks = []
    def check(name, condition):
        assert condition, name
        checks.append({"name": name, "pass": True})
    check("actual_controller_law", Q == {"00": F(313,1250), "01": F(156,625),
                                        "10": F(156,625), "11": F(313,1250)})
    check("full_design_endpoint_lower_bound", tv(law(lo),law(hi)) == 2*delta)
    check("endpoints_attained", tv(law(lo),Q) == tv(law(hi),Q) == delta)
    check("center_has_smaller_positive_error", tv(law(F(1,2)),Q) == 2*delta*delta)
    check("source_success_lower", F(candidate["source_acceptance_lower"]) == (1-hi/2)**2)
    check("physical_failure_added", F(candidate["adaptive_full_output_upper"]) == F(1,64)+F(1,4096)+delta)
    check("joint_full_output_precision", F(candidate["adaptive_full_output_upper"]) < F(1,20))
    # This independently exposes the forbidden transfer of a design-region
    # lower bound to a narrower accepted calibration set.
    dsmall = F(1,100)
    Qsmall = {"00": F(1,4)+dsmall*dsmall, "11": F(1,4)+dsmall*dsmall,
              "01": F(1,4)-dsmall*dsmall, "10": F(1,4)-dsmall*dsmall}
    check("calibration_lower_bound_nontransfer_counterexample",
          tv(law(F(49,100)),Qsmall) == tv(law(F(51,100)),Qsmall) == dsmall and dsmall < delta)
    check("revised_candidate_scope", "not every narrower realized calibration interval" in candidate["optimization_scope"])
    out = {"reviewer": "native research agent B", "date": "2026-11-11",
           "baseline": "16a89154183c22030d4526413167d095d94e6890",
           "scope": "independent exact arithmetic and a design/calibration quantifier counterexample; no empirical data",
           "checks": checks, "passed": True, "not_a_universal_numerical_proof": True,
           "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
           "paper_upper_bound_argument": "For x=|q-1/2|<=d and u=d^2-x^2, TV=max(x,u)+u; d-(x+u)=(d-x)(1-d-x)>=0; d-2u=d(1-2d)+2x^2>=0.",
           "reviewed_inputs": {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                               for p in [root/"frozen_model.json", root/"candidate.json", root/"C_ROBUST_CALIBRATION.md"]}}
    args.output.write_text(json.dumps(out,indent=2)+"\n")
    print(json.dumps({"pass": True, "checks": len(checks),
                      "adaptive_full_output_upper": str(F(candidate["adaptive_full_output_upper"])),
                      "source_sha256": out["source_sha256"]}))


if __name__ == "__main__":
    main()
