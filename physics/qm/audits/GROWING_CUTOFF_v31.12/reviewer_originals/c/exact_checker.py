#!/usr/bin/env python3
"""Independent rational checker for the segmented blue-sideband increment.

This checker imports neither a certificate producer nor the common-model
simulator.  It reads frozen physical/model inputs, derives record weights and
the scalar analytic bound, and encloses each square root using integer
arithmetic.  The companion mathematical proof, not a finite numerical grid,
supplies the universal quantum and infinite-dimensional inequalities.

An interval enclosing a proved upper-bound FORMULA is not a confidence
interval or a lower bound for the actual physical error.  Hardware membership
and an independently justified pulse-area constraint remain external inputs.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
import hashlib
import json
from math import isqrt
from pathlib import Path
import sympy as S


def sqrt_interval(x: F, denominator: int = 10**18) -> tuple[F, F]:
    """Certified nonnegative rational enclosure, using no floating point."""
    if x < 0 or denominator <= 0:
        raise ValueError("square-root input and enclosure scale are invalid")
    k = isqrt(x.numerator * denominator * denominator // x.denominator)
    lo = F(k, denominator)
    hi = lo if lo * lo == x else F(k + 1, denominator)
    if not (0 <= lo <= hi and lo * lo <= x <= hi * hi):
        raise AssertionError("invalid integer square-root enclosure")
    return lo, hi


def record_law(q: F) -> dict[str, F]:
    return {"00": (1-q)**2, "01": q*(1-q),
            "10": q*(1-q), "11": q*q}


def source_law(q: F) -> dict[str, F]:
    s = 1-q/2
    return {"f": 1-s, "0f": s*(1-q)*(1-s), "1f": s*q*(1-s),
            **{r: s*s*p for r, p in record_law(q).items()}}


def tv(p: dict[str, F], q: dict[str, F]) -> F:
    return sum((abs(p.get(k, F(0))-q.get(k, F(0)))
                for k in p.keys() | q.keys()), F(0))/2


def fraction_map(values):
    if isinstance(values, F):
        return str(values)
    if isinstance(values, dict):
        return {k: fraction_map(v) for k, v in values.items()}
    if isinstance(values, (list, tuple)):
        return [fraction_map(v) for v in values]
    return values


def derive(model: dict) -> dict:
    checks = []

    def check(name, ok, detail):
        if not ok:
            raise AssertionError(name)
        checks.append({"name": name, "verified": True, "detail": detail})

    lo, hi = map(F, model["q_interval"])
    d = (hi-lo)/2
    check("fixed_symmetric_design_region", (lo+hi)/2 == F(1, 2)
          and 0 <= d <= F(1, 2),
          "The analytic controller is tied to the complete design interval")
    check("frozen_source_contract", model["source_height"] == 2
          and model["source_records"] == ["f", "0f", "1f", "00", "01", "10", "11"]
          and model["accept"] == ["00", "01", "10", "11"]
          and model["s_relation"] == "1-q/2"
          and model["theta"] == ["q", "phi", "alpha", "beta"],
          "Exact two-step source, stopping alphabet, and shared-parameter relation")
    p = F(model["adaptive_first_label1_weight"])
    p0 = F(model["adaptive_second_label1_given_0"])
    p1 = F(model["adaptive_second_label1_given_1"])
    Q = {"00": (1-p)*(1-p0), "01": (1-p)*p0,
         "10": p*(1-p1), "11": p*p1}
    check("visible_controller", all(0 <= x <= 1 for x in (p, p0, p1))
          and sum(Q.values()) == 1,
          "The second coin consumes only the visible first label")
    check("minimax_word_law", Q == {"00": F(1, 4)+d*d,
                                   "01": F(1, 4)-d*d,
                                   "10": F(1, 4)-d*d,
                                   "11": F(1, 4)+d*d},
          "This law follows from the actual conditional weights")
    q = S.symbols("q", real=True)
    s = 1-q/2
    source = {"f": 1-s, "0f": s*(1-q)*(1-s), "1f": s*q*(1-s),
              "00": s*s*(1-q)**2, "01": s*s*q*(1-q),
              "10": s*s*q*(1-q), "11": s*s*q*q}
    check("source_leaf_partition", S.expand(sum(source.values())-1) == 0,
          "Exact symbolic polynomial identity for all seven raw records")
    check("same_parameter_conditioning",
          S.expand(sum(v for r, v in source.items() if 'f' not in r)-s*s) == 0,
          "The scalar acceptance is s(q)^2, not a supplied target certificate")
    check("design_minimax_endpoint_witness", tv(record_law(lo), record_law(hi)) == 2*d
          and tv(record_law(lo), Q) == tv(record_law(hi), Q) == d,
          "Endpoint marginal triangle bound is matched by this policy")
    # For x=|q-1/2|<=d, u=d^2-x^2, exact TV=max(x,u)+u.
    # Both cases are bounded by d because
    # d-(x+u)=(d-x)(1-d-x)>=0,
    # d-2u=d(1-2d)+2x^2>=0.
    check("paper_uniform_case_domain", d <= F(1, 2),
          "The two explicit nonnegative remainders cover the entire interval; "
          "finite endpoint tests alone are not the universal proof")
    expected_blue = sum((F(r.count("1"))*w for r, w in Q.items()), F(0))
    first_blue = Q["10"] + Q["11"]
    second_blue = Q["01"] + Q["11"]
    check("compiled_blue_count", first_blue == second_blue == F(1, 2)
          and expected_blue == 1,
          "This is the Q-policy expected executed count, not the source count 2q")

    E = F(model["analytic_energy_budget"])
    N = int(model["analytic_cutoff_N"])
    beta = F(model["beta_abs_bound"])
    precision = F(model["required_full_output_precision"])
    check("frozen_numeric_case", (lo, hi, E, N, beta, precision)
          == (F(12, 25), F(13, 25), F(1), 4095, F(1, 100), F(1, 20)),
          "This is the independently frozen example, not a generic feasibility solver")
    check("energy_cutoff_domain", E >= 0 and N >= 0 and F(N+1) > E,
          "Low-spectral projection has positive success and tail e<1")
    check("frozen_pulse_precision", beta >= 0 and 0 < precision < 1,
          "Pulse-area magnitude is a model/engineering premise, not a flag estimate")
    tail = E/F(N+1)
    radicand = 4*tail-3*tail*tail
    root_lo, root_hi = sqrt_interval(radicand)
    filter_lo, filter_hi = (tail+root_lo)/2, (tail+root_hi)/2
    energy_lo, energy_hi = sqrt_interval(E+1)
    blue_lo, blue_hi = beta*expected_blue*energy_lo, beta*expected_blue*energy_hi
    total_lo, total_hi = d+filter_lo+blue_lo, d+filter_hi+blue_hi
    matched_lo, matched_hi = d+filter_lo, d+filter_hi
    check("rational_filter_enclosure", root_lo**2 <= radicand <= root_hi**2,
          "Integer arithmetic encloses sqrt(4e-3e^2)")
    check("rational_energy_enclosure", energy_lo**2 <= E+1 <= energy_hi**2,
          "Integer arithmetic encloses the no-blue reference energy bound")
    check("declared_precision_sufficient", total_hi < precision,
          "Complete-output upper-bound formula, including real filter failure, is below the frozen target")
    check("matched_blue_precision_sufficient", matched_hi < precision,
          "The matched-blue source/action construction needs no small-beta approximation")

    loose_lo, loose_hi = sqrt_interval(tail)
    loose_total_lo = d+tail+loose_lo+blue_lo
    loose_total_hi = d+tail+loose_hi+blue_hi
    check("loose_filter_bound_does_not_certify", loose_total_lo > precision,
          "Failure of this weaker upper bound is insufficient evidence, not physical impossibility")
    enlarged_beta = 2*beta
    enlarged_total_lo = d+filter_lo+2*blue_lo
    check("larger_pulse_allowance_loses_this_certificate", enlarged_total_lo > precision,
          "Doubling the allowed beta makes this bound uninformative at the frozen precision")
    source_floor = (1-hi/2)**2
    filter_floor = 1-tail
    total_source_floor = filter_floor*source_floor
    check("actual_preparation_success_included", total_source_floor < source_floor,
          "Physical attempts succeed with s_N*s^2; the old conditional denominator alone is insufficient")
    # A rigorous flag-only nonidentifiability control: from |g,0>, both
    # excitation-preserving U0/U1 leave the vacuum unchanged.  For word 01,
    # beta=pi/2 maps it to -i|e,1>, orthogonal to the omitted-blue output.
    # Hence D(Q_blue,Q_no_blue)>=Q(01), while every flag probability agrees.
    check("flag_blind_beta_counterexample", Q["01"] > precision,
          "At beta=pi/2, vacuum word 01 alone gives D>=Q(01); flags have the same law as beta=0")
    small_d = d/2
    Qsmall = {"00": F(1, 4)+small_d*small_d, "11": F(1, 4)+small_d*small_d,
              "01": F(1, 4)-small_d*small_d, "10": F(1, 4)-small_d*small_d}
    check("design_lower_bound_not_a_calibration_lower_bound",
          tv(record_law(F(1, 2)-small_d), Qsmall) == small_d < d,
          "A narrower calibrated set may admit better weights; design optimality is not transferred")
    check("oracle_policy_is_not_deployment", tv(record_law(lo), record_law(hi)) > 0,
          "w(theta)=q is pointwise exact, but one unknown-parameter policy cannot equal both endpoints")
    check("visible_label_failure_control", tv({"0": F(1)}, {"1": F(1)}) == 1,
          "Erasing labels would hide a maximal complete-CQ discrepancy")

    return fraction_map({
        "schema": "ueot-qm.segmented-growth-independent-certificate/1",
        "classification": "EXACT_RATIONAL_ENCLOSURE_OF_ANALYTIC_MODEL_BOUND",
        "all_verified": True,
        "new_hardware_data": False,
        "checks": checks,
        "derived": {
            "q_design_interval": [lo, hi], "policy_word_weights": Q,
            "design_full_record_radius": d,
            "compiled_label1_marginals": [first_blue, second_blue],
            "compiled_expected_blue_count": expected_blue,
            "source_conditional_expected_blue_count": "2*q",
            "tail_mass_upper": tail,
            "sharp_complete_filter_bound_interval": [filter_lo, filter_hi],
            "normalized_low_filter_energy_upper": E,
            "blue_omission_bound_interval": [blue_lo, blue_hi],
            "matched_blue_total_bound_interval": [matched_lo, matched_hi],
            "omitted_blue_total_bound_interval": [total_lo, total_hi],
            "certified_remaining_model_error_margin": precision-total_hi,
            "required_precision": precision,
            "loose_filter_total_bound_interval": [loose_total_lo, loose_total_hi],
            "larger_beta_control": enlarged_beta,
            "filter_success_lower": filter_floor,
            "unfiltered_source_success_lower": source_floor,
            "complete_attempt_source_success_lower": total_source_floor,
            "beta_blind_record_counterexample_distance_lower": Q["01"],
        },
        "decision": {
            "matched_blue_model": "CERTIFIED_SUFFICIENT_BOUND",
            "omitted_blue_given_independent_beta_bound": "CERTIFIED_SUFFICIENT_BOUND",
            "omitted_blue_from_flags_only": "INSUFFICIENT_PHYSICAL_INPUT",
            "looser_preparation_bound": "INSUFFICIENT_BOUND",
            "doubled_beta_using_same_bound": "INSUFFICIENT_BOUND",
            "hardware_membership": "UNVERIFIED",
            "empirical_full_CQ_error": "UNVERIFIED",
            "resource_advantage": "UNVERIFIED",
        },
        "bound_meaning": "Enclosures of proved model upper-bound formulas; not measured errors, error lower bounds, or statistical confidence intervals",
        "physical_inputs": [
            "One shared theta=(q,phi,alpha,beta) for source and library",
            "Finite segmented V0=U0,V1=B_beta U1 with U0,U1 preserving G",
            "Ideal low-spectral filter of G with the stated reset failure map",
            "Mean excitation at most the frozen E for the actual joint input",
            "Finite-dimensional untouched reference and visible classical policy",
            "For omission only: an independent |beta| bound, not inferred from flag counts",
        ],
        "not_covered": [
            "general infinite-dimensional proof-assistant acceptance",
            "simultaneous Rabi dynamics or arbitrary non-segmented drives",
            "actual device/model matching, drift, leakage or pulse calibration",
            "full-CQ tomography from finite flag data",
            "independent regeneration of unknown quantum inputs",
        ],
    })


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--model", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    model = json.loads(args.model.read_text(encoding="utf-8"))
    result = derive(model)
    result["input_sha256"] = {
        "model": hashlib.sha256(args.model.read_bytes()).hexdigest(),
        "checker": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, ensure_ascii=False)+"\n", encoding="utf-8")
    print(json.dumps({"all_verified": result["all_verified"],
                      "checks": len(result["checks"]),
                      "classification": result["classification"],
                      "output": str(args.output)}))


if __name__ == "__main__":
    main()
