"""Independent algebra and common-scale integration of the full noise certificate.

Consumes the independently reviewed all-mode C0 enclosure. Recomputes the
mean defect, geometry comparison, calibrated Weyl records and field-energy
budget at that SAME exact-correlated-source scale; no mode ODE is executed.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
from mpmath import iv,mp
import sympy as sp

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[4]
TL="physics/qm/null_source/timelike/"
BASE="29d49e3eee6299e2085492b0e061288b8166b5fa"
mp.dps=90
iv.dps=78

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def I(x):return iv.mpf(x.numerator)/x.denominator if isinstance(x,F) else iv.mpf(x)
def endpoint(x,j):return mp.make_mpf(x._mpi_[j])
def rational(x):
    sign,mant,power,_=x._mpf_
    return F((-1 if sign else 1)*mant)*F(2)**power
def pair(x):return [str(rational(endpoint(x,j))) for j in (0,1)]
def box(a,b):return iv.mpf([endpoint(I(a),0),endpoint(I(b),1)])
def parse(x):
    assert isinstance(x,(list,tuple)) and len(x)==2,"Expected an interval pair"
    return box(F(x[0]),F(x[1]))
def upper(x):return I(endpoint(x,1))
def absolute(x):return I(max(abs(endpoint(x,0)),abs(endpoint(x,1))))
def sinh(x):return (iv.exp(x)-iv.exp(-x))/2
def cosh(x):return (iv.exp(x)+iv.exp(-x))/2
def probability(x):return box(max(F(0),F(pair(x)[0])),min(F(1),F(pair(x)[1])))

def canonical_algebra():
    # Multiplication represents independent interval choices, not a square.
    interval_product=box(-1,1)*box(-1,1)
    assert pair(interval_product)==["-1","1"]
    # Exact finite canonical algebra is an independent normalization check.
    # The continuum passage and all-mode bound remain separate proof inputs.
    O=sp.diag(sp.Matrix([[0,1],[-1,0]]),sp.Matrix([[0,1],[-1,0]]))
    V=sp.diag(sp.Rational(1,2),sp.Rational(1,2),sp.Rational(1,6),sp.Rational(3,2))
    C=V+sp.I*O/2
    f=sp.Matrix([1,2,3,4])
    H=sp.diag(3,1,2,4)
    K=sp.Matrix([[1,2,0,1],[2,3,1,0],[0,1,4,2],[1,0,2,1]])
    assert H==H.T and K==K.T
    def d(A):return (f.T*A*f)[0]/2
    def base(A,B):return sp.trace(A*C*B*C.T)/2
    def connected(A,B,variance_y2):
        return sp.simplify(base(A,B)+(f.T*A*C*B*f)[0]+variance_y2*d(A)*d(B))
    new=connected(H,K,0);old=connected(H,K,sp.Rational(3,4))
    assert sp.simplify(old-new-sp.Rational(3,4)*d(H)*d(K))==0
    assert sp.simplify(sp.im(old)-sp.im(new))==0
    J=H*O*K-K*O*H
    full_second=V+f*f.T
    assert sp.simplify(new-sp.conjugate(new)-sp.I*sp.trace(J*full_second)/2)==0
    # Shared canonical evolution and a common quadratic observable retain
    # equality of means even when both change with the metric parameter.
    t=sp.symbols("t",real=True)
    S=sp.diag(sp.Matrix([[1,t],[0,1]]),sp.Matrix([[1,0],[t,1]]))
    assert S*O*S.T==O
    Hg=H+t*K;fg=S*f;Vg=S*V*S.T
    mean=sp.simplify((sp.trace(Hg*Vg)+(fg.T*Hg*fg)[0])/2)
    for sign in [-1,1]:
        m=sp.Rational(sign,2)
        old_values=[m-sp.sqrt(3)/2,m+sp.sqrt(3)/2]
        old_second=sp.simplify(sum(y*y for y in old_values)/2)
        new_second=sp.simplify((1+m)/2+(1-m)/2)
        assert old_second==new_second==1
        old_mean=(sp.trace(Hg*Vg)+old_second*(fg.T*Hg*fg)[0])/2
        new_mean=(sp.trace(Hg*Vg)+new_second*(fg.T*Hg*fg)[0])/2
        assert sp.simplify(old_mean-new_mean)==0
        assert sp.simplify(sp.diff(old_mean-new_mean,t,3))==0
    # The rank-one covariance difference stays positive under ANY finite
    # linear response, provided its intrinsic/cross terms are held fixed.
    dd=sp.Matrix([d(H),d(K),d(H+K)])
    R=sp.Matrix([[1,2,-1],[0,1,3]])
    delta=sp.Rational(3,4)*dd*dd.T
    assert R*delta*R.T==sp.Rational(3,4)*(R*dd)*(R*dd).T
    assert (R*delta*R.T).det()==0
    return {
        "ordered_quadratic_covariance_difference":"(3/4)*D_H*D_K",
        "independent_interval_product_negative_control":pair(interval_product),
        "commutator_expectation_identical":True,
        "same_mean_under_common_canonical_evolution":True,
        "same_existing_metric_derivatives_not_a_proof_of_differentiability":True,
        "finite_canonical_cross_check_not_a_substitute_for_continuum_tail":True,
        "linear_covariance_transfer":"(3/4)*(R D)*(R D)^T",
        "transfer_requires_same_response_and_intrinsic_cross_terms":True,
        "retarded_response_alone_does_not_determine_noise":True,
        "no_general_thermal_fluctuation_dissipation_assumption":True,
    }

def common_scale(noise,oldmean,oldprep,oldlinear):
    lam_value=int(noise["certificate"]["lambda_certified"])
    c0=I(F(noise["certificate"]["c0_over_D2_upper"]))
    lam=I(lam_value)
    assert lam_value>=8192
    c1_fraction=F(oldlinear["certificate"]["local_test_all_mode_linear_coefficient_c1_upper"])
    assert c1_fraction==F(noise["certificate"]["c1_over_D2_upper"])
    c1=I(c1_fraction)
    q0=parse(oldmean["physical_models"]["quantum_initial_effective_interval"])+iv.log(lam/8192)/(96*iv.pi**2)
    qcap=absolute(q0)
    d2=1-2*q0/lam**2
    assert F(pair(d2)[0])>0 and F(pair(d2)[1])<1
    ref=oldmean["independent_uniform_reference"]
    R=upper(parse(ref["rho_absolute_upper"])+parse(ref["H1rho_absolute_upper"])*iv.log(lam)/(576*iv.pi**2))
    P=upper(parse(ref["pressure_absolute_upper"])+parse(ref["H1p_absolute_upper"])*iv.log(lam)/(576*iv.pi**2))
    erho=upper((2*qcap+2*R)/lam**2)
    ep=upper((2*qcap+2*P)/lam**2)
    assert F(pair(erho)[1])<F(1,100) and F(pair(ep)[1])<F(1,100)
    raw=upper(c0/lam**4+d2*c1/lam**2)
    relative=upper(raw/(1-erho)**2)
    old_mixture_lower=box(F(pair(3*d2**2/(4*(1+erho)**2))[0]),F(pair(3*d2**2/(4*(1+erho)**2))[0]))
    factor=1+old_mixture_lower/relative
    assert F(pair(relative)[1])<F(1,100)
    T=I(F(3,16));c=iv.cos(2*T);amin=iv.sqrt(3*c)
    K2=upper(3/c**2-1);K=iv.sqrt(K2)
    forcing=upper(iv.sqrt(3)*(R+3*P)+18*qcap/amin**3)
    b=upper(forcing*(cosh(K*T)-1)/K2)
    bp=upper(forcing*sinh(K*T)/K)
    ar=upper(b/(lam**2*amin))
    hr=upper((bp+iv.tan(2*T)*b)/(lam**2*amin))
    # Recompute absolute probabilities rather than transfer old-scale numbers.
    mu=parse(oldprep["readout"]["mean_phi_window_interval"])
    gain=box(F(199,200),F(201,200));phase=box(F(-1,100),F(1,100))
    theta=10*gain*iv.sqrt(d2)*mu
    V=parse(oldprep["reference_variance"]["full_base_smeared_field_variance_upper"])
    visibility_min=iv.exp(-2*(I(5)*I(F(201,200))/lam)**2*V)
    visibility=box(F(pair(visibility_min)[0]),1)
    contrast=box(F(99,100),1);bias=box(F(-1,1000),F(1,1000))
    oldre=iv.cos(theta/2)*iv.cos(iv.sqrt(3)*theta/2)
    oldim=box(-1,1)*iv.sin(theta/2)*iv.cos(iv.sqrt(3)*theta/2)
    newre=iv.cos(theta);newim=box(F(-1,2),F(1,2))*iv.sin(theta)
    oldp=probability((1+contrast*visibility*(iv.cos(phase)*oldre-iv.sin(phase)*oldim))/2+bias)
    newp=probability((1+contrast*visibility*(iv.cos(phase)*newre-iv.sin(phase)*newim))/2+bias)
    failure=box(0,F(1,100))
    oldfull=(1-failure)*oldp;newfull=(1-failure)*newp
    assert F(pair(oldfull)[0])>F(9,20)
    assert F(pair(newfull)[1])<F(1,40)
    n=128;margin=F(17,80);threshold=F(19,80)
    risk=upper(iv.exp(-2*I(n)*I(margin)**2))
    assert 2*n*margin**2==F(289,25)
    assert F(pair(risk)[1])<F(1,100000)
    fieldenergy=upper((5*I(F(201,200)))**2*parse(oldprep["reference_variance"]["spatial_L2_squared_upper"])/(2*lam**3*(3*iv.cos(I(F(1,2))))**I(F(3,2))))
    return {
        "lambda":lam_value,"source_family":"exact correlated source retuned at this lambda",
        "Qeff0":pair(q0),"d_squared":pair(d2),
        "M2":pair(27*lam**4*d2),
        "full_c0_over_D2_upper":pair(c0),"all_mode_c1_over_D2_upper":pair(c1),
        "raw_generator_variance_upper":pair(raw),
        "relative_total_stress_variance_upper":pair(relative),
        "relative_total_stress_standard_deviation_upper":pair(upper(iv.sqrt(relative))),
        "old_mixture_relative_variance_lower":pair(old_mixture_lower),
        "old_to_new_total_variance_ratio_lower":pair(factor),
        "uniform_mean_density_relative_defect_upper":pair(erho),
        "uniform_mean_pressure_relative_defect_upper":pair(ep),
        "independent_first_order_scale_relative_upper":pair(ar),
        "independent_first_order_conformal_H_upper":pair(hr),
        "independent_first_order_log_volume_upper":pair(upper(3*ar)),
        "mean_and_geometry_eta_interval":["0","3/16"],
        "reference_visibility_lower":pair(visibility_min)[0],
        "source_phase_interval":pair(theta),
        "old_all_start_plus_interval":pair(oldfull),
        "new_all_start_plus_interval":pair(newfull),
        "independent_fresh_starts":n,"all_start_threshold":str(threshold),
        "minimum_margin":str(margin),"per_candidate_classification_error_upper":pair(risk)[1],
        "same_calibration_and_heralded_preparation_failure_contract_as_parent":True,
        "field_added_energy_upper":pair(fieldenergy),"field_energy_evaluation_eta":"1/4",
        "physical_gain":"5; maximum 201/40",
        "future_effect_probability_derivative_at_epsilon0_upper":pair(upper(iv.sqrt(raw))),
        "derivative_perturbation":"delta g_ab=2*epsilon*F/(D*lambda^2)*u_lambda_a*u_lambda_b",
        "finite_epsilon_probability_bound_proved":False,
        "physical_lengths_and_proper_times_relative_to_8192":str(F(lam_value,8192)),
        "full_device_cost_advantage_certified":False,
        "full_nonlinear_SCE_solution_or_distance_certified":False,
        "all_mode_bound_does_not_certify_arbitrary_test_resolution":True,
    }

def calculate():
    if not __debug__:raise RuntimeError("Do not disable scientific assertions")
    paths={
        "noise":HERE/"noise/result.json",
        "noise_code":HERE/"noise/check.py",
        "old_mean":REPO/(TL+"compatibility/review.json"),
        "old_preparation":REPO/(TL+"response/preparation/result.json"),
        "old_linear_noise":REPO/(TL+"response/noise/result.json"),
        "self":HERE/"review.py",
    }
    for key in ["old_mean","old_preparation","old_linear_noise"]:
        p=paths[key];assert p.read_bytes()==subprocess.check_output(["git","show",BASE+":"+str(p.relative_to(REPO))],cwd=REPO)
    frozen={p:sha(p) for p in paths.values()}
    result={
        "schema":"ueot-stress-kernel-independent-integration/1",
        "status":"PASS",
        "reviewed_base":BASE,
        "canonical_algebra":canonical_algebra(),
        "same_scale":common_scale(*[json.loads(paths[k].read_text()) for k in ["noise","old_mean","old_preparation","old_linear_noise"]]),
        "new_mode_integrations":0,"matched_hardware_data":False,
        "full_nonlinear_SCE":"OPEN","infinite_RSET_derivative_norm":"OPEN",
        "source_sha256":{str(p.relative_to(REPO)):h for p,h in sorted(frozen.items())},
    }
    for p,h in frozen.items():assert sha(p)==h,"Input changed during calculation"
    return result

if __name__=="__main__":
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--write",action="store_true")
    ap.add_argument("--check",action="store_true")
    args=ap.parse_args();result=calculate()
    rendered=json.dumps(result,indent=2,sort_keys=True,ensure_ascii=False)+"\n"
    target=HERE/"review.json"
    if args.write:target.write_text(rendered)
    if args.check:assert target.read_text()==rendered,"Independent integration receipt mismatch"
    row=result["same_scale"]
    for key in ["relative_total_stress_variance_upper","independent_first_order_scale_relative_upper","old_all_start_plus_interval","new_all_start_plus_interval"]:
        print(key, [float(F(x)) for x in row[key]])
    print("PASS: independent canonical algebra and common-scale source/noise/geometry/records.")
