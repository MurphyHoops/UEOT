"""Calibration-only estimator. This module does not open simulation truth or holdout."""
from __future__ import annotations
import datetime, math
from fractions import Fraction
import numpy as np
from mpmath import iv
from common_c import BASE, decimal_string, digest, dump_json, load_json, outward_fraction

iv.dps=60

def ivq(q):
    q=Fraction(q)
    return iv.mpf(q.numerator)/q.denominator

def main():
    contract=load_json(BASE/"CALIBRATION_CONTRACT.json")
    freeze=load_json(BASE/"FROZEN_CALIBRATION_IDENTITY.json")
    if digest(BASE/"CALIBRATION_CONTRACT.json") != freeze["contract_sha256"]:
        raise RuntimeError("contract changed")
    receipt=load_json(BASE/"calibration_generation_receipt.json")
    if receipt["data_sha256"] != digest(BASE/"calibration_shots.npz"):
        raise RuntimeError("calibration data identity changed")
    alpha=Fraction(contract["calibration"]["alpha"])
    generation_allowance=Fraction(contract["calibration"]["synthetic_generation_probability_allowance"])
    # The generator receipt is used only to bind bytes, not to read its model probabilities.
    observed=np.load(BASE/"calibration_shots.npz")
    intervals=[]; counts=[]
    for setting in contract["calibration"]["settings"]:
        samples=observed[setting["id"]]
        n=len(samples); k=int(samples.sum())
        if n != setting["shots"] or not np.all((samples==0)|(samples==1)):
            raise RuntimeError("invalid binary data")
        r=iv.sqrt(iv.ln(ivq(4/alpha))/(2*n))+ivq(generation_allowance)
        mean=ivq(Fraction(2*k,n)-1)
        lower=outward_fraction(mean-2*r,False)
        upper=outward_fraction(mean+2*r,True)
        intervals.append((lower,upper))
        counts.append({"id":setting["id"],"n":n,"plus":k,"mean":str(Fraction(2*k,n)-1),
                       "expectation_interval":[decimal_string(lower),decimal_string(upper)]})
    eta_l=max(Fraction(".9"),intervals[0][0]); eta_u=min(Fraction(1),intervals[0][1])
    y_l,y_u=intervals[1]
    if eta_l > eta_u or y_l <= 0:
        raise RuntimeError("empty or nonpositive calibration: no logarithmic certificate")
    t=Fraction("3/2")
    a=4*((1-iv.cos(ivq(t)))+ivq(Fraction(4,25))*(1-iv.cos(ivq(Fraction(3,2)*t))))
    q_l=-iv.ln(ivq(y_u/eta_l))/a
    q_u=-iv.ln(ivq(y_l/eta_u))/a
    lam_l=max(Fraction(".2"),outward_fraction(iv.sqrt(q_l),False))
    lam_u=min(Fraction(".4"),outward_fraction(iv.sqrt(q_u),True))
    if lam_l > lam_u:
        raise RuntimeError("empty calibration joint set")
    lam_hat=Fraction(decimal_string((lam_l+lam_u)/2))
    factor=iv.exp(a*ivq(lam_hat**2))
    eta_section_l=max(eta_l,outward_fraction(ivq(y_l)*factor,True))
    eta_section_u=min(eta_u,outward_fraction(ivq(y_u)*factor,False))
    if eta_section_l > eta_section_u:
        raise RuntimeError("failed nominal-section construction")
    eta_hat=Fraction(decimal_string((eta_section_l+eta_section_u)/2))
    predicted=ivq(eta_hat)*iv.exp(-a*ivq(lam_hat**2))
    p_low=outward_fraction(predicted,False); p_up=outward_fraction(predicted,True)
    feasible=eta_l <= eta_hat <= eta_u and y_l <= p_low <= p_up <= y_u
    if not feasible:
        raise RuntimeError("nominal witness not interval-certified feasible")
    lambda_radius=max(abs(lam_hat-lam_l),abs(lam_u-lam_hat))
    eta_radius=max(abs(eta_hat-eta_l),abs(eta_u-eta_hat))
    param=Fraction(51,10)*lambda_radius
    trunc=Fraction(contract["error_certificate"]["analytic_galerkin_error_upper"])
    data={"schema":"calibration-only-nominal/1","created_at":datetime.datetime.now(datetime.timezone.utc).isoformat(),
          "contract_sha256":freeze["contract_sha256"],"data_sha256":digest(BASE/"calibration_shots.npz"),
          "estimator_sha256":digest(__file__),"input_files_read":["CALIBRATION_CONTRACT.json","FROZEN_CALIBRATION_IDENTITY.json","calibration_generation_receipt.json (identity fields only)","calibration_shots.npz"],
          "lambda_hat":decimal_string(lam_hat),"eta_hat":decimal_string(eta_hat),
          "lambda_projection_outer":[decimal_string(lam_l),decimal_string(lam_u)],
          "eta_projection_outer":[decimal_string(eta_l),decimal_string(eta_u)],
          "joint_set":"box domain intersected with both observed expectation inequalities; the displayed rectangle is an outer set, not the exact confidence set",
          "nonempty_witness_interval_verified":feasible,"alpha":str(alpha),"counts":counts,
          "lambda_max_error":decimal_string(lambda_radius),"eta_max_error":decimal_string(eta_radius),
          "all_input_ideal_nominal_CQ_error_upper":decimal_string(param),
          "all_input_ideal_Galerkin_CQ_error_upper":decimal_string(param+trunc),
          "fixed_tester_readout_error_addition":decimal_string(eta_radius/2),
          "implementation_numerical_error":"PENDING_INDEPENDENT_ENCLOSURE", "hardware_status":"NOT_CERTIFIED",
          "scope":"conditional analytical source certificate; no unstructured arbitrary-channel tomography and no hardware claim"}
    dump_json(BASE/"NOMINAL_MODEL.json",data)
    dump_json(BASE/"FROZEN_HOLDOUT_PLAN.json",{
      "schema":"frozen-before-holdout/1","created_at":data["created_at"],"contract_sha256":freeze["contract_sha256"],
      "nominal_sha256":digest(BASE/"NOMINAL_MODEL.json"),"maximum_lambda_mesh":contract["error_certificate"]["holdout_lambda_mesh_max"],
      "prediction_set":"outer lambda/eta rectangle; eta endpoints and lambda covering grid; per-event margin 5.1*mesh/2 plus independently certified numerical error",
      "multiple_testing_cells":96,"alpha":"1/100","rule":"reject a family if at least one simultaneous holdout interval is disjoint from its entire calibration-permitted probability enclosure",
      "no_post_holdout_refit":True})
    print({"lambda_hat":data["lambda_hat"],"eta_hat":data["eta_hat"],"lambda_interval":data["lambda_projection_outer"],"ideal_CQ_bound":data["all_input_ideal_nominal_CQ_error_upper"]})

if __name__ == "__main__":
    main()
