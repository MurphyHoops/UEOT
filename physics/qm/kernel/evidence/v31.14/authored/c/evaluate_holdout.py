"""Read frozen calibration and holdout bytes; never access simulation truth."""
from __future__ import annotations
import datetime, math, time
from fractions import Fraction
import numpy as np
from mpmath import iv
from common_c import BASE, decimal_string, digest, dump_json, dynamics, event_probabilities, load_json, outward_fraction, rational
from interval_source import moments, q

def main():
    start=time.perf_counter(); cpu=time.process_time()
    contract=load_json(BASE/"CALIBRATION_CONTRACT.json")
    nominal=load_json(BASE/"NOMINAL_MODEL.json")
    frozen=load_json(BASE/"FROZEN_HOLDOUT_PLAN.json")
    if frozen["nominal_sha256"] != digest(BASE/"NOMINAL_MODEL.json"):
        raise RuntimeError("nominal changed after holdout freeze")
    receipt=load_json(BASE/"holdout_generation_receipt.json")
    if receipt["data_sha256"] != digest(BASE/"holdout_shots.npz") or receipt["nominal_sha256"] != frozen["nominal_sha256"]:
        raise RuntimeError("holdout bytes or nominal binding changed")
    samples=np.load(BASE/"holdout_shots.npz")
    lower,upper=map(Fraction,nominal["lambda_projection_outer"])
    el,eu=map(Fraction,nominal["eta_projection_outer"])
    spacing_limit=Fraction(frozen["maximum_lambda_mesh"])
    steps=math.ceil((upper-lower)/spacing_limit)
    mesh=(upper-lower)/steps
    grid=[lower+(upper-lower)*Fraction(j,steps) for j in range(steps+1)]
    covering=Fraction(51,10)*mesh/2
    n=contract["holdout"]["shots_per_setting"]
    alpha=Fraction(contract["holdout"]["alpha"])
    r=iv.sqrt(iv.ln(q(Fraction(2*frozen["multiple_testing_cells"])/alpha))/(2*n))
    data_radius=outward_fraction(r,True)+Fraction(contract["holdout"]["synthetic_generation_probability_allowance"])
    dyn,source_path=dynamics()
    lambda_hat=rational(nominal["lambda_hat"]); eta_hat=rational(nominal["eta_hat"])
    family_results={}; cached_envelopes={}; numeric_checks=[]; observed_cost=0
    for family in contract["holdout"]["families"]:
        times=tuple(family["times"])
        if times not in cached_envelopes:
            bounds={obs:[[Fraction(1),Fraction(0)] for _ in range(8)] for obs in contract["holdout"]["observables"]}
            for lam in grid:
                vals=moments(lam,times)
                for oi,obs in enumerate(bounds):
                    for ri,record in enumerate(("f","pf","ppf","ppp")):
                        w,m=vals[record][0],vals[record][oi+1]
                        for si,sign in enumerate((-1,1)):
                            index=2*ri+si
                            for eta in (el,eu):
                                p=(w+sign*q(eta)*m)/2
                                bounds[obs][index][0]=min(bounds[obs][index][0],outward_fraction(p,False))
                                bounds[obs][index][1]=max(bounds[obs][index][1],outward_fraction(p,True))
            for obs in bounds:
                for pair in bounds[obs]:
                    pair[0]=max(Fraction(0),pair[0]-covering)
                    pair[1]=min(Fraction(1),pair[1]+covering)
            cached_envelopes[times]=bounds
        envelope=cached_envelopes[times]
        float_times=[rational(t) for t in times]
        nominal_blocks=dyn.exact_output(lambda_hat,times=float_times)
        reset_blocks=dyn.reset_bath_output(lambda_hat,times=float_times)
        baseline_start=time.perf_counter()
        baseline_blocks=dyn.galerkin_output(lambda_hat,times=float_times,cutoff=20)
        baseline_seconds=time.perf_counter()-baseline_start
        observed_cost+=4*n
        settings=[]; rejected=False; reset_disagreements=[]
        for obs in contract["holdout"]["observables"]:
            key=family["id"]+"__"+obs
            raw=samples[key]
            if len(raw)!=n or np.any(raw>7):
                raise RuntimeError("invalid complete-record data")
            counts=np.bincount(raw,minlength=8)
            freq=[Fraction(int(k),n) for k in counts]
            measured=[[max(Fraction(0),x-data_radius),min(Fraction(1),x+data_radius)] for x in freq]
            failures=[j for j,(a,b) in enumerate(zip(measured,envelope[obs])) if a[1]<b[0] or b[1]<a[0]]
            rejected |= bool(failures)
            npred=event_probabilities(nominal_blocks,eta_hat,obs)
            bpred=event_probabilities(baseline_blocks,eta_hat,obs)
            rpred=event_probabilities(reset_blocks,eta_hat,obs)
            # This reset comparison is a nominal ablation diagnostic, not a composite-model rejection proof.
            reset_fail=[j for j,a in enumerate(measured) if float(a[1]) < rpred[j] or rpred[j] < float(a[0])]
            reset_disagreements+= [(obs,j) for j in reset_fail]
            settings.append({"observable":obs,"counts":counts.tolist(),"shots":n,
              "empirical_event_intervals":[[decimal_string(x),decimal_string(y)] for x,y in measured],
              "calibration_prediction_envelope":[[decimal_string(x),decimal_string(y)] for x,y in envelope[obs]],
              "disjoint_event_indices":failures,"nominal_prediction":npred.tolist(),"standard_joint_prediction":bpred.tolist(),
              "max_float_backend_probability_discrepancy":float(np.max(abs(npred-bpred))),
              "reset_nominal_prediction":rpred.tolist(),"reset_nominal_disjoint_event_indices":reset_fail})
        family_results[family["id"]]={"status":"REJECTED_MODEL_CONTRACT" if rejected else "NOT_REJECTED_FROZEN_HOLDOUT",
          "times":list(times),"all_records_retained":True,"settings":settings,
          "standard_backend_CQ_float_discrepancy":dyn.cq_distance(nominal_blocks,baseline_blocks),
          "standard_backend_wall_seconds":baseline_seconds,
          "reset_bath_CQ_float_difference":dyn.cq_distance(nominal_blocks,reset_blocks),
          "reset_nominal_disagreements":reset_disagreements}
    result={"schema":"persistent-bath-heldout-classification/1","created_at":datetime.datetime.now(datetime.timezone.utc).isoformat(),
      "contract_sha256":digest(BASE/"CALIBRATION_CONTRACT.json"),"nominal_sha256":frozen["nominal_sha256"],
      "data_sha256":digest(BASE/"holdout_shots.npz"),"classifier_sha256":digest(__file__),"interval_source_sha256":digest(BASE/"interval_source.py"),
      "dynamics_sha256":digest(source_path),"truth_file_read":False,"holdout_refit":False,
      "grid_points":len(grid),"grid_spacing_exact":str(mesh),"per_event_covering_error":decimal_string(covering),
      "per_event_hoeffding_radius_plus_generation_allowance":decimal_string(data_radius),
      "calibration_coverage_failure_upper":".01","heldout_simultaneous_failure_upper":".01",
      "false_rejection_probability_upper_under_frozen_model":".02 (union bound; conditional assumptions apply)",
      "families":family_results,"method_gain":"EQUIVALENT_NO_ADDED_GAIN",
      "method_gain_basis":"same physical quantum map and same estimator/error rule as the strong standard process; independent finite joint backend verifies implementation agreement but is not proof of a new UEOT advantage",
      "hardware_status":"NOT_CERTIFIED","matching_raw_device_data":False,
      "resources":{"heldout_shots_consumed":observed_cost,"wall_seconds":time.perf_counter()-start,"cpu_seconds":time.process_time()-cpu}}
    dump_json(BASE/"HOLDOUT_RESULTS.json",result)
    print({family:r["status"] for family,r in family_results.items()})

if __name__ == "__main__":
    main()
