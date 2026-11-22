"""Certify the changed sign preparation and an all-mode Weyl readout.

The old source's X-symmetry restriction is intentionally changed. No old mode
integration is rerun. Full response/state equivalence is restricted to explicitly
parity-covariant instruments. Ideal X readout of a linear controlled-Weyl gate
is parity covariant and distinguishes the old/new amplitude laws, not the new
internal signs. A Y quadrature (or nonzero phase offset) can access odd effects.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
from mpmath import iv, mp
import sympy as sp

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[5]
BASE="d6ec9eda409ba78d1d7993d7648ba26b5a34374d"
TL="physics/qm/null_source/timelike/"
INPUTS=[
    "physics/qm/null_source/FINITE_WINDOW.md",
    TL+"continuation/SOURCE.md",
    TL+"instrument/CONTRACT.md",
    TL+"instrument/instrument.py",
    TL+"instrument/joint_bound.py",
    TL+"instrument/result.json",
    TL+"compatibility/CONTRACT.md",
    TL+"compatibility/constraints/result.json",
    TL+"compatibility/review.json",
]
LAMBDA=8192
iv.dps=78
mp.dps=100

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def I(x):return iv.mpf(x.numerator)/x.denominator if isinstance(x,F) else iv.mpf(x)
def end(x,j):return mp.make_mpf(x._mpi_[j])
def rat(x):
    sign,man,power,_=x._mpf_
    return F((-1 if sign else 1)*man)*F(2)**power
def pair(x):return [str(rat(end(x,j))) for j in (0,1)]
def box(a,b):return iv.mpf([end(I(a),0),end(I(b),1)])
def parse(v):return box(F(v[0]),F(v[1]))
def upper(x):return I(end(x,1))
def probability_box(x):
    return box(max(F(0),F(pair(x)[0])),min(F(1),F(pair(x)[1])))

def frozen_inputs():
    manifest={}
    for rel in INPUTS:
        path=REPO/rel
        prior=subprocess.check_output(["git","show",BASE+":"+rel],cwd=REPO)
        assert path.read_bytes()==prior,("Changed inherited input",rel)
        manifest[rel]=sha(path)
    source=HERE/"check.py"
    manifest[str(source.relative_to(REPO))]=sha(source)
    return manifest

def symbolic():
    y,x,m,t,f,Q,B=sp.symbols("y x m t f Q B",real=True)
    p=(1+m)/2
    new=lambda poly:sp.expand(p*poly.subs(y,1)+(1-p)*poly.subs(y,-1))
    assert new(y)==m and new(y*y)==1
    assert new(y**4)-new(y*y)**2==0
    moments={}
    for s in (-1,1):
        old=lambda poly:sp.simplify((poly.subs(y,sp.Rational(s,2)+sp.sqrt(3)/2)+
                                     poly.subs(y,sp.Rational(s,2)-sp.sqrt(3)/2))/2)
        old_values=[old(y**n) for n in range(5)]
        new_values=[new(y**n).subs(m,sp.Rational(s,2)) for n in range(5)]
        assert old_values[:3]==new_values[:3]
        assert old_values[3]==sp.Rational(5*s,4)
        assert new_values[3]==sp.Rational(s,2)
        assert old_values[4]==sp.Rational(7,4) and new_values[4]==1
        assert sp.expand(old((y-sp.Rational(s,2))**3))==0
        centered_third=new((y-sp.Rational(s,2))**3).subs(m,sp.Rational(s,2))
        assert centered_third==-sp.Rational(3*s,4)
        mean_old=old(Q+B*y+f*y*y)
        mean_new=new(Q+B*y+f*y*y).subs(m,sp.Rational(s,2))
        assert sp.expand(mean_old-mean_new)==0
        # This conditional mean polynomial is used with B=0 for a centered reference.
        assert sp.expand((old((Q+f*y*y)**2)-old(Q+f*y*y)**2)-sp.Rational(3,4)*f*f)==0
        assert sp.expand((new((Q+f*y*y)**2)-new(Q+f*y*y)**2))==0
        old_re=sp.cos(t/2)*sp.cos(sp.sqrt(3)*t/2)
        old_im=sp.sin(s*t/2)*sp.cos(sp.sqrt(3)*t/2)
        new_re=sp.cos(t)
        new_im=sp.Rational(s,2)*sp.sin(t)
        assert sp.simplify(sp.diff(new_im-old_im,t,3).subs(t,0))==sp.Rational(3*s,4)
        assert sp.simplify(sp.diff(new_re-old_re,t,4).subs(t,0))==-sp.Rational(3,4)
        moments[str(s)]={
            "old_moments_0_through_4":[str(v) for v in old_values],
            "new_moments_0_through_4":[str(v) for v in new_values],
            "new_plus_probability":str(p.subs(m,sp.Rational(s,2))),
            "new_minus_probability":str((1-p).subs(m,sp.Rational(s,2))),
            "new_centered_third_moment":str(centered_third),
        }
    assert sp.simplify(sp.cos(t)**2+m*m*sp.sin(t)**2-
                       (1-(1-m*m)*sp.sin(t)**2))==0
    # A finite algebra sanity check; the general parity statement is the
    # automorphism proof in README, not an extrapolation from these monomials.
    parity_checks=[]
    for degree in range(7):
        polynomial=x**degree
        assert sp.expand(polynomial.subs(x,-x+f)-
                         polynomial.subs(x,-x).subs(x,x-f))==0
        parity_checks.append(degree)
    failure,probability=sp.symbols("failure probability",real=True)
    records=[failure,(1-failure)*probability,(1-failure)*(1-probability)]
    assert sp.expand(sum(records))==1
    return {
        "fixed_mean_second_moment":{
            "admissible_mean":"-1 <= m <= 1",
            "minimum_Var_Y_squared":"0",
            "zero_variance_support_subset":["-1","1"],
            "plus_weight":"(1+m)/2","minus_weight":"(1-m)/2",
            "proof":"E[(Y^2-1)^2]>=0; equality iff Y^2=1 a.s.; first moment fixes both weights",
        },
        "moments":moments,
        "old_characteristic":"exp(i*s*t/2)*cos(sqrt(3)*t/2)",
        "new_characteristic":"cos(t)+i*s*sin(t)/2",
        "old_and_new_one_and_two_point_functions_equal":True,
        "old_and_new_full_states_equal":False,
        "old_X_symmetry_preserved":False,
        "new_X_second_moment":"3/4",
        "stress_variance_removed_exact":"(3/4)*A_f^2 for centered quasifree reference",
        "parity_theorem":{
            "reference_assumption":"gamma-invariant centered quasifree Hadamard reference",
            "state_relation":"omega_- = omega_+ composed with gamma",
            "even_algebra_restriction":"all biased +/-f mixtures equal omega_+ on gamma(A)=A",
            "stress_n_point_scope":"products of separately smooth compactly smeared Wick stress tensors in their common domain",
            "finite_adaptive_instrument_condition":"every Heisenberg branch map commutes with gamma with record labels fixed; all terminal accessible effects are even",
            "record_conclusion":"all finite adaptive complete record probabilities agree for +f, -f and any sign weights",
            "odd_field_access_allowed_in_this_conclusion":False,
            "actual_gravity_dynamics_selected_by_this_theorem":False,
        },
        "finite_parity_algebra_sanity_degrees":parity_checks,
        "complete_record_normalization":"failure+(1-failure)*p+(1-failure)*(1-p)=1",
    }

def reference_variance_bound():
    a0=iv.sqrt(3)
    aL=iv.sqrt(3*iv.cos(I(F(1,4))))
    aR=iv.sqrt(3*iv.cos(I(F(1,8))))
    aT=iv.sqrt(3*iv.cos(I(F(3,8))))
    variation=(a0+aR-2*aL)/aL+iv.log(a0/aR)+iv.log(a0/aT)
    assert F(pair(variation)[1])<F(1,8)
    assert F(pair(aT*aT)[0])>F(27,10)
    R=I(F(1,100))
    # Positive normalized radial bump. Its denominator is bounded by the
    # chi<=R/2 ball and sin(chi)>=chi*(1-R^2/24).
    l2=6*iv.exp(I(F(1,3)))/(iv.pi*R**3*(1-R**2/24)**2)
    nonzero=iv.exp(I(F(1,4)))*l2/(2*I(F(27,10))*iv.sqrt(3))
    # q(eta)=q_seed+p_seed*J; the seed has zero symmetric qp covariance.
    J=I(F(25,216))
    zero=(I(F(1,6))+I(F(3,2))*J**2)/(2*iv.pi**2)
    total=upper(nonzero+zero)
    assert F(1,50)<F(1,32)
    assert F(1,100)+F(3,16)<F(1,4)
    assert F(pair(iv.sin(I(F(1,100)+F(3,16))))[1])<F(pair(1/iv.sqrt(3))[0])
    return {
        "spatial_radius_chi":"1/100",
        "time_window_eta":["5/32","3/16"],
        "w_and_F":"nonnegative C-infinity compactly supported; integral w deta=integral F dOmega3=1",
        "base_smearing":"J=w(eta)*F(chi)/a(eta)^4",
        "preparation_total_log_variation_upper":pair(upper(variation)),
        "convenient_log_variation_cap":"1/8",
        "scale_squared_lower":"27/10",
        "spatial_L2_squared_upper":pair(upper(l2)),
        "all_nonzero_modes_variance_upper":pair(upper(nonzero)),
        "regular_zero_mode_variance_upper":pair(upper(zero)),
        "full_base_smeared_field_variance_upper":pair(total),
        "amplitude_bound":"|u_k|^2 <= exp(2*r)/(2*a^2*sqrt(k^2-1))",
        "zero_mode_J_upper":"25/216",
        "uses_Parseval_without_mode_cutoff":True,
        "new_mode_integrations":0,
        "coordinate_support_within_inner_domain":True,
        "aperture_diameter_less_than_window_width":True,
        "support_reports_reach_center_before_eta":"1/4",
        "these_coordinate_checks_prove_a_physical_detector":False,
    }

def readout(variance):
    data=json.loads((REPO/(TL+"instrument/result.json")).read_text(),parse_float=str)
    means=data["joint_certificate"]["mean_intervals_outward"][1]
    mu=box(F(means[0]),F(means[1]))
    constraints=json.loads((REPO/(TL+"compatibility/constraints/result.json")).read_text())
    source=next(row for row in constraints["tuned_sources"] if str(row["lambda"])==str(LAMBDA))
    M2=parse(source["M2_interval"])
    M2hat=F(source["explicit_rational_approximation"]["M2"])
    assert F(source["M2_interval"][0])<=M2hat<=F(source["M2_interval"][1])
    amplitude=iv.sqrt(M2/(27*LAMBDA**4))
    gain=box(F(199,200),F(201,200))
    phase=box(F(-1,100),F(1,100))
    theta=10*gain*amplitude*mu
    V=parse(variance["full_base_smeared_field_variance_upper"])
    vis_min=iv.exp(-2*(I(5)/LAMBDA*I(F(201,200)))**2*V)
    visibility=iv.mpf([end(vis_min,0),1])
    contrast=box(F(99,100),1)
    bias=box(F(-1,1000),F(1,1000))
    old_re=iv.cos(theta/2)*iv.cos(iv.sqrt(3)*theta/2)
    old_im=box(-1,1)*iv.sin(theta/2)*iv.cos(iv.sqrt(3)*theta/2)
    new_re=iv.cos(theta)
    new_im=box(F(-1,2),F(1,2))*iv.sin(theta)
    old_rotated=iv.cos(phase)*old_re-iv.sin(phase)*old_im
    new_rotated=iv.cos(phase)*new_re-iv.sin(phase)*new_im
    old_p=probability_box((1+contrast*visibility*old_rotated)/2+bias)
    new_p=probability_box((1+contrast*visibility*new_rotated)/2+bias)
    failure=box(0,F(1,100))
    old_full=(1-failure)*old_p
    new_full=(1-failure)*new_p
    assert F(pair(old_full)[0])>F(9,20)
    assert F(pair(new_full)[1])<F(3,20)
    risk=iv.exp(-I(F(288,25)))
    assert F(pair(risk)[1])<F(1,100000)
    assert F(1,100)+2*F(1,4)-F(5,32)<F(1,2)
    a_read=iv.sqrt(3*iv.cos(I(F(1,2))))
    added_energy=upper((5*I(F(201,200)))**2*parse(variance["spatial_L2_squared_upper"])/(2*LAMBDA**3*a_read**3))
    assert F(pair(added_energy)[1])<F(1,50000)
    old_mean=json.loads((REPO/(TL+"compatibility/review.json")).read_text())["physical_models"]
    for key in ["exact_correlated_source","explicit_rational_source"]:
        for field in ["uniform_density_relative_defect_upper","uniform_pressure_relative_defect_upper"]:
            assert F(old_mean[key][field])<F(1,100)
    return {
        "lambda":LAMBDA,
        "new_aperture_and_gain_are_declared_not_old_probabilities_reused":True,
        "dual_smearing":"J_lambda=lambda^-3*J",
        "nominal_gain_gamma":"5/lambda relative to dual smearing J_lambda=lambda^-3*J",
        "equivalent_normal_clock_gain":"g_physical=lambda*gamma=5, multiplying (w/a_lambda)*Z*integral F*Phi",
        "equivalent_unit_normalized_smearing":"J_normalized_lambda=lambda^-4*J with gain g_physical=5",
        "allowed_instrument":"one logical controlled-Weyl interaction, then complete qubit X readout",
        "ideal_X_effects":"(I +/- cos(2*gamma*Phi(J_lambda)))/2 are parity even",
        "ideal_X_Kraus":"cos(gamma*Phi), -i*sin(gamma*Phi); each CP branch is parity covariant",
        "ideal_X_distinguishes":"old amplitude law versus new sign law; not the two internal signs of the new law",
        "odd_quadrature_access":"Y reads sin(2*gamma*Phi); nonzero phase offset can also add an odd component",
        "calibration_intervals_cover_both_fixed_sign_labels":True,
        "probe_initial_state":"+X",
        "source_phase":"theta=10*(actual_gain/nominal_gain)*sqrt(M2/(27*lambda^4))*mu",
        "mean_phi_window_interval":pair(mu),
        "source_amplitude_ratio":pair(amplitude),
        "source_phase_interval":pair(theta),
        "reference_visibility_lower":pair(vis_min)[0],
        "reference_variance_includes_infinite_field":True,
        "calibration_contract":{
            "actual_to_nominal_gain_interval":["199/200","201/200"],
            "phase_error_interval":["-1/100","1/100"],
            "additional_readout_contrast_interval":["99/100","1"],
            "additive_probability_error_interval":["-1/1000","1/1000"],
            "flagged_startup_failure_probability_interval":["0","1/100"],
            "prepared_candidate_is_conditional_on_success":True,
            "failure_semantics":"heralded preparation failure before interrogation; successful preparation satisfies the candidate state and calibration contract; not arbitrary selective mid-protocol loss",
            "actual_calibration_performed":False,
        },
        "ideal_success_probability":"[1+visibility*Re(chi(theta))]/2",
        "calibrated_success_probability":"[1+contrast*visibility*Re(exp(i*phase_error)*chi(theta))]/2 + probability_error",
        "old_success_plus_interval":pair(old_p),
        "new_success_plus_interval":pair(new_p),
        "old_all_launch_plus_interval":pair(old_full),
        "new_all_launch_plus_interval":pair(new_full),
        "complete_record_probabilities":{
            "flagged_failure":"f","plus":"(1-f)*p","minus":"(1-f)*(1-p)",
            "these_three_entries_are_correlated":True,
        },
        "fixed_sample_theorem":{
            "independent_fresh_launches":256,
            "score":"1 for plus; 0 for minus or flagged failure; keep all three raw labels",
            "decision_threshold":"3/10",
            "decision":"old if empirical plus frequency >=3/10; new otherwise",
            "certified_minimum_distance_to_threshold":"3/20",
            "per_hypothesis_error_upper":pair(risk)[1],
            "two_separate_arms_if_both_candidates_tested":512,
            "calibration_preparation_drive_and_geometry_costs_included_in_256":False,
            "launches_actually_executed":0,
        },
        "fixed_background_instrument_field_energy":{
            "readout_eta":"1/4",
            "retarded_support_chi_at_readout":"83/800",
            "retarded_support_chi_plus_eta_at_readout":"283/800",
            "within_original_inner_conformal_patch":True,
            "extends_mean_or_geometric_response_certificate_past_3_over_16":False,
            "gain_upper":"201/40",
            "new_nonselective_field_energy_upper":pair(added_energy),
            "bound_formula":"g_physical^2*norm(F)^2/(2*lambda^3*(3*cos(1/2))^(3/2))",
            "proof":"Etilde=a_lambda^3*E; on the contracting interval d sqrt(2*Etilde)/deta <= abs(g)*w*norm(F)",
            "full_field_and_regular_zero_mode_included":True,
            "pointer_initial_Z_mean":"0",
            "probe_and_drive_stress_included":False,
            "pointwise_geometric_feedback_certified":False,
        },
        "source_mean_certificates_apply_before_or_without_interrogation":True,
        "same_source_mean_certificate_holds_in_each_sign_branch":True,
        "mean_equation_certificates_reused_by_exact_two_point_identity":{
            "exact_correlated_source":old_mean["exact_correlated_source"],
            "explicit_rational_source":old_mean["explicit_rational_source"],
        },
        "physical_local_detector_and_drive_stress_constructed":False,
        "exact_nonlinear_semiclassical_solution_proved":False,
    }

def calculate():
    if not __debug__:raise RuntimeError("Proof assertions require Python without -O")
    manifest=frozen_inputs()
    algebra=symbolic()
    variance=reference_variance_bound()
    protocol=readout(variance)
    assert all(sha(REPO/rel)==h for rel,h in manifest.items()),"Input changed during calculation"
    self_path=str((HERE/"check.py").relative_to(REPO))
    return {
        "schema":"ueot-response-preparation/1",
        "reviewed_base":BASE,
        "status":"ZERO_CLASSICAL_MIXTURE_NOISE_WITH_PRESERVED_MEAN_AND_CERTIFIED_CHANGED_READOUT",
        "symbolic":algebra,"reference_variance":variance,"readout":protocol,
        "inherited_input_sha256":{p:h for p,h in manifest.items() if p!=self_path},
        "source_sha256":{self_path:manifest[self_path]},
        "new_mode_integrations":0,"new_hardware_data":False,
        "general_parity_and_uniqueness_proofs":"README mathematical proof; finite symbolic checks are supplementary",
    }

if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write",action="store_true")
    parser.add_argument("--check",action="store_true")
    args=parser.parse_args()
    result=calculate()
    text=json.dumps(result,indent=2,sort_keys=True,ensure_ascii=False)+"\n"
    target=HERE/"result.json"
    if args.write:target.write_text(text)
    if args.check:assert target.read_text()==text,"Preparation receipt mismatch"
    p=result["readout"]
    print("old all-launch +:",[float(F(v)) for v in p["old_all_launch_plus_interval"]])
    print("new all-launch +:",[float(F(v)) for v in p["new_all_launch_plus_interval"]])
    print("reference visibility >=",float(F(p["reference_visibility_lower"])))
    print("PASS: preserved first/two-point functions, changed parity preparation, all-mode readout and complete-record sample bound.")
