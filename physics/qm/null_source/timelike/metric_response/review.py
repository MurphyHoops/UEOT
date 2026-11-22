"""Independent integration of finite metric response, local TT readout and clocks.

Recomputes conditional fixed-horizon error bounds and independent exact algebra.
No predecessor checker and no mode ODE is executed.
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
BASE="719babd3386b9d9274d5c91dd0b8ad5e71688049"
mp.dps=90
iv.dps=78

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def I(x):return iv.mpf(x.numerator)/x.denominator if isinstance(x,F) else iv.mpf(x)
def endpoint(x,j):return mp.make_mpf(x._mpi_[j])
def rational(x):
    s,m,p,_=x._mpf_
    return F((-1 if s else 1)*m)*F(2)**p
def pair(x):return [str(rational(endpoint(x,j))) for j in (0,1)]
def box(a,b):return iv.mpf([endpoint(I(a),0),endpoint(I(b),1)])
def parse(x):
    assert isinstance(x,list) and len(x)==2,"Expected interval pair"
    return box(F(x[0]),F(x[1]))
def upper(x):return I(endpoint(x,1))

def exact_algebra():
    # A different compact-TT construction from the component's Cotton tensor.
    # Its constant-coefficient polynomial symbol maps a compact scalar bump
    # to a compact symmetric transverse trace-free tensor.
    k=sp.Matrix(sp.symbols("k1:4",real=True))
    k2=(k.T*k)[0]
    P=k2*sp.eye(3)-k*k.T
    S=sp.diag(1,-1,0)
    T=sp.simplify(P*S*P-P*sp.trace(P*S)/2)
    assert T==T.T
    assert sp.simplify(sp.trace(T))==0
    assert sp.simplify(k.T*T)==sp.zeros(1,3)
    axis=T.subs(dict(zip(k,[0,0,1])))
    assert axis==S
    # Explicit covariant conformal-divergence cancellation in dimension 3:
    # gamma'=Omega^2 gamma, tau'=Omega^-1 tau.
    u=sp.symbols("u1:4",real=True)
    t11,t12,t13,t22,t23=sp.symbols("t11 t12 t13 t22 t23",real=True)
    tau=sp.Matrix([[t11,t12,t13],[t12,t22,t23],[t13,t23,-t11-t22]])
    def delta(i,j):return int(i==j)
    def Gamma(l,i,j):return delta(l,i)*u[j]+delta(l,j)*u[i]-delta(i,j)*u[l]
    transformed=[]
    for j in range(3):
        value=sum(-u[i]*tau[i,j]-sum(
            Gamma(l,i,i)*tau[l,j]+Gamma(l,i,j)*tau[i,l]
            for l in range(3)) for i in range(3))
        transformed.append(sp.simplify(value))
    assert transformed==[0,0,0]
    # Exact Weyl-kernel insensitivity of a spatial trace-free stress smearing:
    # T_tau[f+phi]=tau^{ij} partial_i(phi) partial_j(phi) if partial_i f=0.
    v=sp.Matrix(sp.symbols("v1:4",real=True))
    c=sp.symbols("c",real=True)
    contracted=sp.expand((v.T*tau*v)[0]+c*sp.trace(tau))
    assert sp.diff(contracted,c)==0
    # The finite-lapse KG energy identity, after its one spatial IBP,
    # retains the gradient(n) term. Each mixed term is controlled by 2xy.
    n,h=sp.symbols("n h",real=True)
    p0,q0,g0,b0=sp.symbols("p0 q0 g0 b0",real=True)
    rate=2*h*(g0*g0+q0*q0-p0*p0)+2*b0*p0*g0+2*n*p0*q0
    assert sp.diff(rate,b0)==2*p0*g0
    assert sp.expand((p0-g0)**2-(p0*p0+g0*g0-2*p0*g0))==0
    assert sp.expand((p0-q0)**2-(p0*p0+q0*q0-2*p0*q0))==0
    # Zero-margin omission of gradient(n) would change the full PDE identity.
    assert sp.simplify(rate-rate.subs(b0,0))==2*b0*p0*g0
    # Proper-clock monotonicity and one-point mass reconstruction.
    eta,r,t=sp.symbols("eta r t",positive=True)
    cc=sp.cos(2*eta)
    y=sp.Rational(3,2)*sp.log(cc)
    dydeta=sp.diff(y,eta)
    assert sp.simplify(dydeta+3*sp.tan(2*eta))==0
    integral=sp.symbols("I_eta",positive=True)
    deta_dr=-integral/(r*sp.sqrt(cc))
    assert sp.simplify(dydeta*deta_dr-
        3*sp.tan(2*eta)*integral/(r*sp.sqrt(cc)))==0
    # Independent chain rule for the exact classical Jensen negative control.
    mass_symbol=sp.symbols("M",positive=True)
    fclock=sp.sqrt(cc)
    assert sp.simplify(sp.diff(fclock,eta,2)+fclock*(1+1/cc**2))==0
    B=integral*sp.tan(2*eta)/fclock
    Bprime=sp.diff(B,eta)+sp.diff(B,integral)*fclock
    expected_Bprime=sp.tan(2*eta)+(integral/fclock)*(
        2/sp.cos(2*eta)**2+sp.tan(2*eta)**2)
    assert sp.simplify(Bprime-expected_Bprime)==0
    dydM=3*B/(4*mass_symbol)
    d2ydM2=sp.diff(dydM,mass_symbol)+(sp.diff(dydM,eta)+
        sp.diff(dydM,integral)*fclock)*(-integral/(4*mass_symbol*fclock))
    target=-3*(B+integral*Bprime/(4*fclock))/(4*mass_symbol**2)
    assert sp.simplify(d2ydM2-target)==0
    # An internal scalar clock is a genuine physical blind control.
    # All branches have |phi-phi0|=(sqrt(3)/2)*atanh(sin(2 eta)).
    scalar_clock=sp.sqrt(3)*sp.atanh(sp.sin(2*eta))/2
    assert sp.simplify(sp.diff(scalar_clock,eta)-sp.sqrt(3)/sp.cos(2*eta))==0
    uclock=sp.symbols("uclock",positive=True)
    assert sp.simplify(1-sp.tanh(2*uclock/sp.sqrt(3))**2-
        sp.sech(2*uclock/sp.sqrt(3))**2)==0
    # cos(2 eta)>0 selects the positive square root; the entire ratio
    # curve R(u)=sech(2u/sqrt(3))^(3/2) is independent of M.
    # This is positive on 0<eta<pi/4; finite positive gates preserve it.
    # It is NOT an inference about the existence of a semiclassical metric.
    tau_clock=sp.symbols("tau_clock",positive=True)
    mass=3*(tau_clock/integral)**4
    assert sp.simplify((mass/3)**sp.Rational(1,4)*integral-tau_clock)==0
    return {
        "finite_KG_energy_identity":"(N^2)'=2h(||A grad q||^2+||A q||^2-||p/A||^2)+2 integral p grad(n).grad(q)+2 integral n p q",
        "spatial_lapse_gradient_retained":True,
        "finite_KG_energy_growth":"abs(N') <= (|h|+(||n||inf+||grad n||inf)/2) N plus source",
        "independent_compact_TT_symbol":"P S P - P tr(P S)/2; P=|k|^2 I-k k^T; S=diag(1,-1,0)",
        "TT_symbol_symmetric_tracefree_transverse":True,
        "TT_symbol_at_k_001":"diag(1,-1,0)",
        "conformal_covariant_TT_weight":"-1 in dimension three",
        "conformal_divergence_cancellation_checked":True,
        "homogeneous_shift_absent_from_spatial_tracefree_stress":True,
        "clock_monotonicity":"d y_r/d r=3 tan(2 eta) I(eta)/(r sqrt(cos(2 eta)))>0",
        "strict_classical_mass_concavity":"y_MM=-3*(B+I*Bprime/(4*f))/(4*M^2)<0 at fixed positive proper time",
        "branchwise_average_geometry_equals_mean_source_geometry":False,
        "internal_scalar_clock":"u=abs(phi-phi0)=(sqrt(3)/2)*atanh(sin(2 eta))",
        "internal_scalar_clock_volume_curve":"R(u)=sech(2u/sqrt(3))^(3/2), independent of M",
        "internal_scalar_clock_alone_identifies_absolute_scale":False,
        "point_clock_reconstruction":"M=3*(tau/I(0.5*acos(R^(2/3))))^4",
        "point_formula_applies_to_finite_gate_without_modification":False,
        "independent_algebra_not_a_replacement_for_all_mode_or_PDE_proofs":True,
    }

def conditional_records(old_interval,new_interval):
    lo=F(old_interval[0]);hi=F(new_interval[1])
    lower=F(9,20);upper_gate=F(1,40);q=F(1,6);n=64
    assert lo>lower>q>upper_gate>hi
    # If every conditional Bernoulli mean is bounded, iterated conditional
    # MGFs give the same Chernoff bounds as iid Bernoulli(l/u). Independence
    # is sufficient but is not needed when this stronger conditional
    # preparation/calibration/finite-metric contract is directly imposed.
    def divergence(a,b):
        a=I(a);b=I(b)
        return a*iv.log(a/b)+(1-a)*iv.log((1-a)/(1-b))
    Dold=divergence(q,lower);Dnew=divergence(q,upper_gate)
    oldrisk=upper(iv.exp(-n*Dold));newrisk=upper(iv.exp(-n*Dnew))
    assert F(pair(oldrisk)[1])<F(1,100000)
    assert F(pair(newrisk)[1])<F(1,100000)
    assert F(10,n)<q<F(11,n)
    # Perfectly correlated records can satisfy the actual one-trial marginals.
    assert lo<F(19,40)<F(old_interval[1])
    assert F(new_interval[0])<F(1,100)<hi
    # Optimizing MGF tilts have the required signs.
    told=iv.log(I(q*(1-lower)/(lower*(1-q))))
    tnew=iv.log(I(q*(1-upper_gate)/(upper_gate*(1-q))))
    assert F(pair(told)[1])<0<F(pair(tnew)[0])
    for p,tilt,D in [(lower,told,Dold),(upper_gate,tnew,Dnew)]:
        residual=iv.log(1-I(p)+I(p)*iv.exp(tilt))-I(q)*tilt+D
        assert F(pair(residual)[0])<=0<=F(pair(residual)[1])
    return {
        "fixed_number_of_all_starts":n,
        "score":"1 for plus; 0 for minus or heralded preparation failure",
        "classifier":"old iff plus count >= 11; new iff plus count <= 10",
        "fractional_threshold":str(q),
        "old_conditional_plus_probability_lower_gate":str(lower),
        "new_conditional_plus_probability_upper_gate":str(upper_gate),
        "actual_old_finite_metric_plus_interval":old_interval,
        "actual_new_finite_metric_plus_interval":new_interval,
        "old_Bernoulli_KL_interval":pair(Dold),
        "new_Bernoulli_KL_interval":pair(Dnew),
        "old_error_upper":pair(oldrisk)[1],
        "new_error_upper":pair(newrisk)[1],
        "each_error_less_than":"1/100000",
        "proof":"iterated conditional moment generating functions, fixed horizon",
        "history_dependent_lapse_and_calibration_allowed":True,
        "requires_complete_contract_given_every_previous_record":True,
        "independent_fresh_preparations_are_sufficient":True,
        "unconditional_one_trial_marginals_are_sufficient":False,
        "arbitrary_optional_stopping_certified":False,
        "marginal_only_negative_control":{
            "construction":"X_i=Z for every i; Z Bernoulli(p)",
            "new_example_probability":"1/100",
            "64_start_new_error":"1/100",
            "old_example_probability":"19/40",
            "64_start_old_error":"21/40",
            "failure_reason":"conditional probability becomes 0 or 1 after first record"
        },
        "improvement_over_128":"tighter probability inequality; not new physics or full device cost",
        "minimum_sample_size_proved":False,
    }

def finite_fraction_review(finite,parent,oldprep):
    family=finite["finite_family"];a=finite["analytic_constants"];r=finite["record_stability"]
    assert finite["status"]=="FINITE_EPSILON_RECORD_BAND_CERTIFIED"
    assert family["lambda"]==32768 and family["epsilon_interval"]==["-1","1"]
    assert family["same_exact_lapse_family_as_parent"] is True
    assert finite["scope"]["finite_metric_perturbation_bound"] is True
    assert finite["scope"]["fixed_proper_clock_window_without_recalibration"] is False
    assert finite["scope"]["self_consistent_or_nonlinear_SCE_solution"] is False
    def U(obj,key):return F(obj[key][1])
    lam=32768;t=F(201,20)
    N=U(a,"backward_difference_energy_norm_per_epsilon_upper")
    sd=U(a,"sqrt_base_delta_variance_per_epsilon_upper")
    V0=U(a,"base_probe_variance_upper")
    assert V0==F(oldprep["reference_variance"]["full_base_smeared_field_variance_upper"][1])
    mu=U(a,"homogeneous_phase_mean_difference_per_epsilon_upper")
    assert sd**2>=F(9,8)*N**2
    qlin=U(r,"quantum_probability_linear_coefficient")
    qquad=U(r,"quantum_probability_quadratic_coefficient")
    nc=U(r,"new_coherent_probability_coefficient")
    oc=U(r,"old_coherent_probability_coefficient")
    ycap=U(r,"old_amplitude_absolute_bound")
    assert qlin**2 >= (t*t/F(2*lam*lam))**2*V0*sd**2
    assert qquad >= t*t/F(4*lam*lam)*sd**2
    assert nc>=t*mu/2 and oc>=ycap*nc
    nd=U(r,"new_all_start_probability_change_upper")
    od=U(r,"old_all_start_probability_change_upper")
    assert nd>=nc+qlin+qquad and od>=oc+qlin+qquad
    assert U(r,"common_complete_three_label_total_variation_upper")>=od>=nd
    for label,delta in [("old",od),("new",nd)]:
        key=label+"_all_start_plus_interval"
        prev=parent["same_scale"][key];current=r[key]
        assert F(current[0])<=max(F(0),F(prev[0])-delta)
        assert F(current[1])>=min(F(1),F(prev[1])+delta)
    assert U(family,"metric_00_relative_change_upper")<F("0.000004624143")
    return {
        "lambda":lam,"epsilon_interval":family["epsilon_interval"],
        "finite_abs_epsilon_le_one_probability_bound":True,
        "new_probability_change_upper":r["new_all_start_probability_change_upper"],
        "old_probability_change_upper":r["old_all_start_probability_change_upper"],
        "complete_three_label_TV_upper":r["common_complete_three_label_total_variation_upper"],
        "metric_relative_00_change_upper":family["metric_00_relative_change_upper"],
        "old_all_start_plus_interval":r["old_all_start_plus_interval"],
        "new_all_start_plus_interval":r["new_all_start_plus_interval"],
        "independent_exact_fraction_Weyl_bound_factors_checked":True,
        "future_test_is_fixed_coordinate_smearing":True,
        "uncompensated_proper_clock_probe_included":False,
        "probability_comparison_uses_same_calibration_and_failure_rule":True,
        "uniform_over_declared_calibration_ranges":True,
        "full_mean_defect_or_density_noise_transferred_to_perturbed_metrics":False,
    }

def tensor_fraction_review(tensor):
    a=tensor["all_mode_noise"];r=tensor["readout"];scope=tensor["scope"]
    assert tensor["status"]=="LOCAL_TT_STRAIN_READOUT_AND_COMPLETE_REFERENCE_NOISE_BOUND"
    def U(obj,key):return F(obj[key][1])
    K=a["K"];lam=a["lambda"]
    assert K==256 and lam==32768
    H=U(a,"H");L=U(a,"L0");E=U(a,"E5");Lg=U(a,"L_grad")
    S4=F(K*(K+1)*(2*K+1)*(3*K*K+3*K-1),30)
    low=U(a,"complete_low_row_Hilbert_Schmidt_upper")
    main=U(a,"high_positive_Hilbert_Schmidt_upper")
    error=U(a,"high_preparation_remainder_Hilbert_Schmidt_upper")
    CT=U(a,"C_T_upper");variance=U(a,"raw_readout_variance_upper");rms=U(a,"raw_readout_RMS_upper")
    assert low**2>=H**2*L**2*S4
    assert main**2>=Lg**2/(4*K)
    assert error**2>=16*L**2*E**2/(5*K**5)
    assert CT>=32*(2*low**2+(main+error)**2)
    assert variance*lam**4>=CT and rms**2>=variance
    assert a["homogeneous_displacement_linear_coefficient"]==0
    assert a["homogeneous_displacement_classical_amplitude_coefficient"]==0
    assert a["old_new_TT_noise_difference"]==0
    assert a["mean_TT_readout_in_isotropic_reference"]==0
    assert a["stress_distribution_Gaussian_assumed"] is False
    assert r["all_homogeneous_TT_initial_data_cancel"] is True
    assert r["initial_source_correlations_need_be_zero"] is False
    assert r["normalized_unit_strain_noise_claimed"] is False
    assert r["calibration_gain_numerically_certified"] is False
    assert scope["full_quantum_RSET_metric_response_included"] is False
    assert scope["full_quantum_background_SCE_on_shell_claimed"] is False
    assert tensor["compact_TT_test"]["normalizer_M_integer"]==7640
    assert F(tensor["compact_TT_test"]["tau_frobenius_sup_upper"][1])<=1
    assert F(tensor["compact_TT_test"]["tau_frobenius_norm_at_origin"][0])>0
    return {
        "lambda":lam,"normalizer_M":7640,
        "C_T_upper":a["C_T_upper"],
        "raw_readout_variance_upper":a["raw_readout_variance_upper"],
        "raw_readout_RMS_upper":a["raw_readout_RMS_upper"],
        "pointwise_strain_error_gain_upper":r["pointwise_strain_error_gain_upper"],
        "independent_exact_fraction_low_high_and_factor32_checks":True,
        "old_new_TT_stress_subalgebra_identical":True,
        "classical_forced_TT_PDE_with_compact_local_gauge_invariant_test":True,
        "valid_on_finite_inhomogeneous_lapse_path":False,
        "complete_quantum_metric_response_included":False,
        "calibrated_unit_strain_sensitivity_certified":False,
    }

def clock_independent_review(clock):
    a=clock["numerical"];scope=clock["scope"]
    assert clock["status"]=="EXACT_CLASSICAL_PROPER_CLOCK_RECORDS_CERTIFIED"
    assert scope["old_and_new_initial_absolute_scale_distributions_differ"] is True
    assert scope["same_initial_geometry_quantum_preparation_comparison"] is False
    assert scope["full_nonlinear_SCE_constructed"] is False
    assert scope["full_quantum_reference_or_stress_noise_included"] is False
    tlo=F(199,200)*F(95,1024)-F(1,10000)
    thi=F(201,200)*F(97,1024)+F(1,10000)
    assert list(map(F,a["actual_gate_t"]))==[tlo,thi]
    # Different integral certification from the component:
    # concavity gives trapezoidal <= integral <= midpoint, with no fitted
    # or inherited remainder estimate and no inverse-iteration reuse.
    def primitive_bracket(z,n=512):
        z=F(z);assert 0<=z<=F(3,16)
        step=z/n
        def f(x):return iv.sqrt(iv.cos(2*I(x)))
        trapezoid=(f(F(0))+f(z))/2
        midpoint=I(0)
        for j in range(n):
            if j:trapezoid+=f(step*j)
            midpoint+=f(step*F(2*j+1,2))
        return [F(pair(I(step)*trapezoid)[0]),F(pair(I(step)*midpoint)[1])]
    audit={}
    acceptlo=F(-1,20);accepthi=F(-23,1000)
    for name,b in a["branches"].items():
        r=parse(b["r"])
        target=box(tlo,thi)/r
        etalo,etahi=map(F,b["eta_over_entire_gate"])
        pl=primitive_bracket(etalo);ph=primitive_bracket(etahi)
        assert pl[1]<=F(pair(target)[0]),"Lower inverse endpoint failed independent quadrature"
        assert ph[0]>=F(pair(target)[1]),"Upper inverse endpoint failed independent quadrature"
        audit[name]={
            "primitive_at_eta_lower":list(map(str,pl)),
            "primitive_at_eta_upper":list(map(str,ph)),
            "target_interval":pair(target),
            "inverse_bracket_independently_verified":True,
        }
        yy=I(F(3,2))*iv.log(iv.cos(2*box(etalo,etahi)))
        claimed=b["log_volume_over_entire_gate"]
        assert F(claimed[0])<=F(pair(yy)[0])
        assert F(claimed[1])>=F(pair(yy)[1])
        mlo,mhi=map(F,b["measured_finite_gate_log_volume"])
        assert mlo<=F(claimed[0])-F(1,1000)
        assert mhi>=F(claimed[1])+F(1,1000)
        if name=="old_low":assert mhi<acceptlo
        elif name=="old_high":assert mlo>accepthi
        elif name=="new":assert acceptlo<mlo<mhi<accepthi
        else:raise AssertionError("Unknown branch")
    assert F(a["minimum_strict_classification_margin"])>F(1,1000)
    return {
        "model":"additional exact classical Einstein-scalar branch family; M=P^2",
        "old_and_new_initial_absolute_scale_distributions_differ":True,
        "same_background_quantum_preparation_experiment":False,
        "measured_intervals":{name:b["measured_finite_gate_log_volume"] for name,b in a["branches"].items()},
        "new_acceptance_interval":a["new_acceptance_interval"],
        "minimum_strict_margin":a["minimum_strict_classification_margin"],
        "independent_inverse_brackets":audit,
        "independent_quadrature":"512-cell trapezoidal lower / midpoint upper from strict concavity",
        "independent_absolute_clock_and_known_turnaround_required":True,
        "internal_scalar_clock_unsigned_volume_curve_blind_to_M":True,
        "signed_scalar_motion_extra_record_included_in_blindness":False,
        "finite_positive_gate_not_instantaneous_quantum_shot":True,
        "fixed_background_Weyl_probabilities_transferred":False,
    }

def calculate():
    assert __debug__,"Scientific assertions must remain enabled"
    paths={
        "parent":REPO/(TL+"stress_kernel/review.json"),
        "parent_receipt":REPO/(TL+"stress_kernel/verification.json"),
        "finite":HERE/"finite/result.json","finite_code":HERE/"finite/check.py",
        "tensor":HERE/"tensor/result.json","tensor_code":HERE/"tensor/check.py",
        "clock":HERE/"clock/result.json","clock_code":HERE/"clock/check.py",
        "finite_proof":HERE/"finite/README.md","tensor_proof":HERE/"tensor/README.md",
        "clock_proof":HERE/"clock/README.md",
        "old_preparation":REPO/(TL+"response/preparation/result.json"),
        "self":HERE/"review.py",
    }
    for key in ["parent","parent_receipt","old_preparation"]:
        p=paths[key]
        assert p.read_bytes()==subprocess.check_output(
            ["git","show",BASE+":"+str(p.relative_to(REPO))],cwd=REPO)
    frozen={p:sha(p) for p in paths.values()}
    parent=json.loads(paths["parent"].read_text())
    finite=json.loads(paths["finite"].read_text())
    tensor=json.loads(paths["tensor"].read_text())
    clock=json.loads(paths["clock"].read_text())
    for component in [finite,tensor,clock]:
        assert component["new_mode_integrations"]==0
    frow=finite_fraction_review(finite,parent,json.loads(paths["old_preparation"].read_text()))
    trow=tensor_fraction_review(tensor)
    crow=clock_independent_review(clock)
    records=conditional_records(frow["old_all_start_plus_interval"],frow["new_all_start_plus_interval"])
    result={
        "schema":"ueot-metric-response-independent-review/1","status":"PASS",
        "reviewed_base":BASE,
        "exact_algebra":exact_algebra(),
        "finite_metric":frow,"local_tensor":trow,"proper_clock":crow,
        "conditional_records":records,
        "unchanged_parent_base_metric":{
            "lambda":parent["same_scale"]["lambda"],
            "complete_density_relative_variance_upper":parent["same_scale"]["relative_total_stress_variance_upper"],
            "old_to_new_complete_density_variance_ratio_lower":parent["same_scale"]["old_to_new_total_variance_ratio_lower"],
            "not_recomputed_or_transferred_to_finite_corrected_geometry":True,
        },
        "scope":{
            "three_results_share_a_single_self_consistent_metric":False,
            "full_nonlinear_SCE_solution":False,
            "full_quantum_metric_response":False,
            "finite_path_full_RSET_or_stress_noise_operator_norm":False,
            "uncalibrated_proper_clock_probe_covered_by_finite_Weyl_bound":False,
            "matched_hardware_data":False,"new_Lean_proofs":False,
            "full_device_cost_advantage":False,"Core_independent_physical_selection":False,
        },
        "new_mode_integrations":0,"new_geometry_ODE_integrations":0,
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
    if args.check:assert target.read_text()==rendered,"Independent review receipt mismatch"
    print("PASS: independent TT/clock algebra and finite-metric conditional 64-start records.")
    for k in ["old_error_upper","new_error_upper"]:
        print(k,float(F(result["conditional_records"][k])))
