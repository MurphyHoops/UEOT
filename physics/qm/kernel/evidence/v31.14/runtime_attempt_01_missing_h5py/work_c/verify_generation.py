"""Generator audit, separate from estimation and holdout decisions.

This verification is allowed to see the generator's inputs. It proves that the
serialized sampling probabilities lie within the declared numerical allowance
of the independently evaluated ideal model for every generated setting.
"""
from __future__ import annotations
from fractions import Fraction
from mpmath import iv
from common_c import BASE, digest, dump_json, iv_endpoint_fraction, load_json
from interval_source import probabilities,q

def max_distance(x,interval):
    x=Fraction.from_float(float(x))
    lo=iv_endpoint_fraction(interval,False);hi=iv_endpoint_fraction(interval,True)
    return max(abs(x-lo),abs(x-hi))

def main():
    contract=load_json(BASE/"CALIBRATION_CONTRACT.json")
    truth=load_json(BASE/"SYNTHETIC_TRUTH.json")
    lam=Fraction(truth["lambda"]);eta=Fraction(truth["eta"])
    cal=load_json(BASE/"calibration_generation_receipt.json")
    hold=load_json(BASE/"holdout_generation_receipt.json")
    distances=[]
    for setting,receipt in zip(contract["calibration"]["settings"],cal["settings"]):
        t=q(setting["time"])
        a=4*((1-iv.cos(t))+q("4/25")*(1-iv.cos(q("3/2")*t)))
        p=(1+q(eta)*iv.exp(-a*q(lam)**2))/2
        distances.append(max_distance(receipt["generator_probability_plus"],p))
    receipt_lookup={r["setting_id"]:r for r in hold["settings"]}
    for family in contract["holdout"]["families"]:
        e=Fraction(truth["detector_violation_eta"]) if family["id"]=="detector_violation" else eta
        predicted=probabilities(lam,e,tuple(family["times"]))
        for obs,values in predicted.items():
            r=receipt_lookup[family["id"]+"__"+obs]
            for sampled,p in zip(r["generator_probabilities"],values):
                distances.append(max_distance(sampled,p))
    limit=Fraction(contract["calibration"]["synthetic_generation_probability_allowance"])
    maximum=max(distances)
    assert maximum < limit
    result={"schema":"synthetic-generator-probability-verification/1","contract_sha256":digest(BASE/"CALIBRATION_CONTRACT.json"),
            "verifier_sha256":digest(__file__),"interval_source_sha256":digest(BASE/"interval_source.py"),
            "generator_truth_read_for_audit_only":True,"estimator_and_classifier_truth_access":False,
            "event_probabilities_checked":len(distances),"maximum_interval_enclosed_probability_deviation_upper_float":float(maximum),
            "declared_allowance":str(limit),"status":"ALL_GENERATION_PROBABILITIES_WITHIN_ALLOWANCE",
            "coverage_status":"the stated coverage is the mathematical iid-trial guarantee; one fixed pseudo-random synthetic execution is not an empirical validation of coverage"}
    dump_json(BASE/"GENERATOR_PROBABILITY_CHECK.json",result)
    print(result["status"],float(maximum))

if __name__ == "__main__":main()
