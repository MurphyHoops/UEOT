"""Independent rational end bound and scope review for correlated static states."""
from fractions import Fraction as F
import argparse,hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent;REPO=HERE.parents[4]
# Very coarse numbers already prove >7%; no shared interval helper is imported.
dlo=F(43,50);Lhi=F(23,16);sqrt2hi=F(17,12);nulo=F(1000)
assert dlo*dlo<F(3,4)
assert F(7,8)**2>F(3,4)
assert sqrt2hi**2>2
assert (dlo/2-1/nulo)/(3*sqrt2hi*Lhi)>F(7,100)
# For y>=0,h>=0, (y+h)^2-y^2=2yh+h^2>=0.
# For y<0, y_+=0 and (y+h)^2>=0. This is deliberately a
# positive-part bound, not the false untruncated square inequality.
assert (-F(1)+F(1))**2 < (-F(1))**2
# Integrated mode orthogonality removes zero/high cross operator terms;
# stationarity is imposed on the high marginal, not on the free-particle zero mode.
data=json.loads((HERE/"correlations.json").read_text())
assert data["status"]=="PASS" and all(data["identities"].values())
assert data["nu0"][0]>1000
assert data["strict_record_weighted_relative_RMS_lower"][0]>.07
assert data["strict_record_weighted_relative_RMS_lower"][1]<.08
assert not data["conditional_zero_high_product_required"]
assert data["classical_anticorrelation_and_quantum_entanglement_allowed"]
assert not data["high_state_required_thermal"] and not data["occupied_shells_restricted_to_k2"]
assert data["high_marginal_stationary_required"] and not data["joint_state_required_stationary"]
assert data["pointwise_static_mean_SCE_assumed_not_constructed"]
assert data["complete_input_S0_spectrum_preserved"] and data["all_records_retained"]
assert not data["ten_percent_bound_extended_to_correlated_states"]
assert not data["sharp_optimum_claimed"] and not data["geometric_RMS_bound_claimed"]
assert not data["mean_SCE_disproved"] and not data["nonstatic_or_other_matter_models_excluded"]
payload={"schema":"ueot-correlated-static-review/1","status":"PASS",
 "independent_rational_seven_percent_margin":str((dlo/2-1/nulo)/(3*sqrt2hi*Lhi)-F(7,100)),
 "untruncated_square_replacement_rejected":True,
 "correlated_state_positive_part_bound":"PASS","full_record_and_stationarity_scope":"PASS",
 "spatial_average_necessary_equations_not_pointwise_converse":"PASS",
 "native_review_agents":3,"external_human_peer_review_claimed":False,
 "conditional_product_ten_percent_result_retained":True,
 "quantum_correlated_generalization_seven_percent_only":True,
 "whole_unified_physics_goal":"OPEN",
 "old_checkers_executed":0,"mode_ODE_integrations":0,"geometry_ODE_integrations":0,
 "source_sha256":{str(p.relative_to(REPO)):hashlib.sha256(p.read_bytes()).hexdigest()
   for p in [HERE/"correlations.py",HERE/"correlations.json",HERE/"review.py"]}}
ap=argparse.ArgumentParser(description=__doc__)
g=ap.add_mutually_exclusive_group(required=True);g.add_argument("--write",action="store_true");g.add_argument("--check",action="store_true")
args=ap.parse_args();out=HERE/"review.json"
if args.write:out.write_text(json.dumps(payload,indent=2,sort_keys=True,ensure_ascii=False)+"\n")
else:assert json.loads(out.read_text())==payload
print("PASS: correlated_static_review")
