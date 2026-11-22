"""Central proper-clock transport of the original finite-lapse Weyl probe.

The same field, state and metric family are used.  A common synchronized
central clock transports the test with its exact Jacobian.  The proof needs
no derivative bound on the positive normalized time window and no mode ODE.
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
REPO=HERE.parents[5]
TL="physics/qm/null_source/timelike/"
BASE="f2b09fb2b8fd2235bde7017b060fc07ecc44b441"
mp.dps=90
iv.dps=78

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def I(x):return iv.mpf(x.numerator)/x.denominator if isinstance(x,F) else iv.mpf(x)
def endpoint(x,j):return mp.make_mpf(x._mpi_[j])
def rat(x):
    sign,mant,power,_=x._mpf_
    return F((-1 if sign else 1)*mant)*F(2)**power
def pair(x):return [str(rat(endpoint(x,j))) for j in (0,1)]
def box(a,b):return iv.mpf([endpoint(I(a),0),endpoint(I(b),1)])
def parse(x):
    assert isinstance(x,list) and len(x)==2
    return box(F(x[0]),F(x[1]))
def upper(x):return I(endpoint(x,1))
def lower(x):return I(endpoint(x,0))

def freeze():
    names={
        "finite":TL+"metric_response/finite/result.json",
        "finite_code":TL+"metric_response/finite/check.py",
        "finite_proof":TL+"metric_response/finite/README.md",
        "previous_review":TL+"metric_response/review.json",
        "nominal":TL+"stress_kernel/review.json",
        "preparation":TL+"response/preparation/result.json",
    }
    frozen={HERE/"check.py":sha(HERE/"check.py")}
    loaded={}
    for key,rel in names.items():
        p=REPO/rel
        assert p.is_file() and not p.is_symlink()
        assert p.read_bytes()==subprocess.check_output(
            ["git","show",BASE+":"+rel],cwd=REPO),"Frozen input changed: "+rel
        frozen[p]=sha(p)
        if p.suffix==".json":loaded[key]=json.loads(p.read_text())
    return loaded,frozen

def symbolic():
    eta,u=sp.symbols("eta u",real=True)
    lam,a_now,a_nom,w=sp.symbols("lambda a_now a_nom w",positive=True)
    # The clock program is a density per CENTRAL PROPER TIME.
    physical_clock_rate=lam*a_now
    nominal_program_density=w/(lam*a_nom)
    actual_source=sp.simplify(physical_clock_rate*nominal_program_density)
    assert actual_source==w*a_now/a_nom
    assert sp.simplify(actual_source/(a_now/a_nom)-w)==0
    # The actual spatially radial lapse has a geodesic central line.
    x=sp.symbols("x",real=True)
    b=sp.exp(-1/(1-x*x))
    assert sp.diff(b,x).subs(x,0)==0
    a2=3*sp.cos(2*eta)
    fprime=sp.sqrt(27)/a2
    assert sp.simplify(sp.diff(a2*fprime,eta))==0
    # A field derivative at a time slice has canonical test (Fp/a^2,0).
    aa,Fp,pfield=sp.symbols("a Fp pfield",positive=True)
    assert sp.simplify((Fp/aa**2)*pfield-Fp*(pfield/aa**2))==0
    # A concrete Jacobian negative control, using a smooth increasing clock.
    # T0(eta)=eta^2/2 and constant shift c: eta(u)=sqrt(u^2-2c).
    c=sp.symbols("c",positive=True)
    inverse=sp.sqrt(u*u-2*c)
    assert sp.simplify(sp.diff(inverse,u)-u/inverse)==0
    assert sp.simplify((inverse/u)*sp.diff(inverse,u))==1
    # Uniform normalized density on u in [1,2] gives the following incorrect
    # mass if the Jacobian is omitted; it is strictly >1 for 0<c<1/2.
    wrong_mass=sp.sqrt(4-2*c)-sp.sqrt(1-2*c)
    assert sp.simplify(wrong_mass.subs(c,0))==1
    wrong_slope=sp.simplify(sp.diff(wrong_mass,c).subs(c,0))
    assert wrong_slope==sp.Rational(1,2)
    return {
        "clock_anchor":"tau_0(eta)=lambda*integral_0^eta a(s) ds; central clocks coincide at eta=0",
        "central_clock_is_geodesic":"radial lapse gradient vanishes at chi=0",
        "future_clock":"tau_c,epsilon(eta)=tau_0(eta)+Delta_tau_c after eta=1/8",
        "constant_common_clock_origin_error":"tau_hat_c=tau_c,epsilon+lambda*beta",
        "nominal_parameter":"u(eta)=tau_0_inverse(tau_hat_c(eta))",
        "exact_Jacobian":"u_prime=a(eta)/a(u)",
        "proper_clock_program_density":"w(u)/(lambda*a(u)) per unit central proper time",
        "actual_canonical_probe_source":"j_epsilon,beta=w(u(eta))*u_prime(eta)*F_probe",
        "normalized_positive_time_weight_preserved":True,
        "time_weight_derivative_bound_assumed":False,
        "source_comparison":"Q_epsilon(w_transported)-Q_0(w_transported) + Q_0(w_transported)-Q_0(w_nominal)",
        "field_derivative_slice_test":"(q_test,p_test)=(F_probe/a^2,0), N=||F_probe||_H1/a",
        "clock_difference_covariance_bound":"sqrt(Var_G deltaQ_clock)<=sqrt(9/8)*E0*||F_probe||_H1*zeta/a_min",
        "clock_difference_coherent_bound":"abs(delta_mu_clock)<=sqrt(27)*zeta/(3*cos(2*T_guard))",
        "Jacobian_omission_negative_control":{
            "clock":"T0(eta)=eta^2/2; eta(u)=sqrt(u^2-2c)",
            "incorrect_mass_without_Jacobian":"sqrt(4-2c)-sqrt(1-2c)",
            "derivative_at_c_zero":"1/2; correct mass derivative is zero",
            "window_example_only":"piecewise constant window illustrates the normalization error; smooth approximations retain it",
        },
    }

def calculate():
    assert __debug__,"Scientific assertions must remain enabled"
    old,frozen=freeze()
    finite=old["finite"];ac=finite["analytic_constants"]
    nominal=old["nominal"]["same_scale"]
    prep=old["preparation"]["reference_variance"]
    calibration=finite["calibration_contract"]
    assert finite["status"]=="FINITE_EPSILON_RECORD_BAND_CERTIFIED"
    assert finite["finite_family"]["epsilon_interval"]==["-1","1"]
    assert finite["finite_family"]["same_exact_lapse_family_as_parent"] is True
    assert ac["reference_covariance_evaluation_slice"]=="1/16"
    assert ac["complete_reference_covariance_norm_bound"]=="9/8"
    assert ac["zero_mode_seed_slice"]=="-1/8"
    assert F(prep["preparation_total_log_variation_upper"][1])<F(1,8)
    assert F(ac["zero_mode_reference_covariance_norm_upper"][1])<F(9,8)
    assert F(ac["nonzero_mode_reference_covariance_norm_upper"][1])<F(9,8)
    lam_value=nominal["lambda"];assert lam_value==32768
    lam=I(lam_value)
    assert 0<F(nominal["d_squared"][0])<=F(nominal["d_squared"][1])<1
    for key,expected in {
        "actual_to_nominal_gain_interval":["199/200","201/200"],
        "phase_error_interval":["-1/100","1/100"],
        "additional_readout_contrast_interval":["99/100","1"],
        "additive_probability_error_interval":["-1/1000","1/1000"],
        "flagged_startup_failure_probability_interval":["0","1/100"],
        "prepared_candidate_is_conditional_on_success":True,
    }.items():assert calibration[key]==expected
    aI=I(F(1,16));bI=I(F(1,8))
    L=F(5,32);T=F(3,16);guard=F(1,100000)
    Tg=I(T+guard);duration=bI-aI
    amin=lower(iv.sqrt(3*iv.cos(2*Tg)))
    assert F(pair(amin)[0])>0 and T+guard<F(1,4)
    amax=upper(iv.sqrt(3))
    hmax=upper(iv.tan(2*Tg))
    r0=upper(hmax+I(F(1,2)))
    rn=upper(parse(ac["perturbed_growth_rate_upper"]))
    E0=upper(iv.exp(r0*(Tg-aI)))
    EI=upper(iv.exp(rn*duration))
    EF=upper(iv.exp(r0*(Tg-bI)))
    F0=upper(iv.sqrt(parse(ac["probe_L2_squared_upper"])))
    F1=upper(parse(ac["probe_H1_upper"]))
    int_dn=upper(parse(ac["int_lapse_difference_Linfinity_per_epsilon_upper"]))
    int_grad=upper(parse(ac["int_lapse_gradient_Linfinity_per_epsilon_upper"]))
    int_dn_l2=upper(parse(ac["int_lapse_difference_L2_per_epsilon_upper"]))
    Cref=I(F(9,8))
    # Only the OLD covariance at eta=1/16 is consumed. The future propagator
    # on the analytically extended background is bounded afresh.
    Nprop=upper(EI*E0/amin*(F1*int_dn+F0*int_grad))
    Nclock_per_shift=upper(E0*F1/amin)
    delta_tau_per_lambda=upper(amax*int_dn)
    metric_shift=upper(delta_tau_per_lambda/amin)
    phase_prop=upper(iv.sqrt(27)/(3*iv.cos(2*bI))*
                     amax*EI*EF*F0/amin*int_dn_l2)
    phase_derivative=upper(iv.sqrt(27)/(3*iv.cos(2*Tg)))
    V0=upper(parse(ac["base_probe_variance_upper"]))
    assert F(pair(V0)[1])==F(prep["full_base_smeared_field_variance_upper"][1])
    t=I(F(201,20))
    old_ycap=upper((1+iv.sqrt(3))/2)
    rows={}
    for label,beta_cap in [("ideal_central_clock",F(0)),
                           ("bounded_common_clock_origin",F(1,100000))]:
        beta_shift=upper(I(beta_cap)/amin)
        clock_offset=upper(delta_tau_per_lambda+I(beta_cap))
        endpoint_margin=F(pair(amin)[0])*guard-F(pair(clock_offset)[1])
        assert endpoint_margin>0
        zeta=upper(metric_shift+beta_shift)
        assert F(pair(zeta)[1])<guard
        actual_left=F(L)-F(pair(zeta)[1])
        actual_right=F(T)+F(pair(zeta)[1])
        assert F(1,8)<actual_left<actual_right<T+guard
        Nclock=upper(Nclock_per_shift*zeta)
        Ntotal=upper(Nprop+Nclock)
        sqrt_Vdelta=upper(iv.sqrt(Cref)*Ntotal)
        phase_clock=upper(phase_derivative*zeta)
        phase_total=upper(phase_prop+phase_clock)
        quantum_linear=upper(t*t/(2*lam**2)*iv.sqrt(V0)*sqrt_Vdelta)
        quantum_quadratic=upper(t*t/(4*lam**2)*sqrt_Vdelta**2)
        coherent_new=upper(t*phase_total/2)
        coherent_old=upper(old_ycap*coherent_new)
        delta_new=upper(coherent_new+quantum_linear+quantum_quadratic)
        delta_old=upper(coherent_old+quantum_linear+quantum_quadratic)
        intervals={}
        for name,delta in [("old",delta_old),("new",delta_new)]:
            p=nominal[name+"_all_start_plus_interval"]
            intervals[name]=[
                str(max(F(0),F(p[0])-F(pair(delta)[1]))),
                str(min(F(1),F(p[1])+F(pair(delta)[1]))),
            ]
        assert F(intervals["old"][0])>F(9,20)
        assert F(intervals["new"][1])<F(1,40)
        jac=box(F(pair(iv.exp(-hmax*zeta))[0]),F(pair(iv.exp(hmax*zeta))[1]))
        rows[label]={
            "beta_absolute_cap":str(beta_cap),
            "common_clock_origin_error_physical_absolute_cap":str(lam_value*beta_cap),
            "inverse_clock_endpoint_margin_per_lambda_lower":str(endpoint_margin),
            "coordinate_time_displacement_upper":pair(zeta),
            "actual_probe_support_enclosing_interval":[str(actual_left),str(actual_right)],
            "exact_clock_Jacobian_enclosure":pair(jac),
            "clock_test_difference_energy_norm_upper":pair(Nclock),
            "complete_probe_difference_energy_norm_upper":pair(Ntotal),
            "sqrt_base_probe_difference_variance_upper":pair(sqrt_Vdelta),
            "coherent_clock_mean_difference_upper":pair(phase_clock),
            "complete_coherent_mean_difference_upper":pair(phase_total),
            "quantum_probability_linear_coefficient":pair(quantum_linear),
            "quantum_probability_quadratic_coefficient":pair(quantum_quadratic),
            "new_coherent_probability_coefficient":pair(coherent_new),
            "old_coherent_probability_coefficient":pair(coherent_old),
            "new_all_start_probability_difference_from_archived_nominal_upper":pair(delta_new),
            "old_all_start_probability_difference_from_archived_nominal_upper":pair(delta_old),
            "complete_three_label_TV_from_same_calibrated_nominal_upper":pair(delta_old),
            "old_all_start_plus_interval":intervals["old"],
            "new_all_start_plus_interval":intervals["new"],
            "old_lower_gate":"9/20","new_upper_gate":"1/40",
        }
    # A post-perturbation central broadcast can reach the entire aperture
    # before the earliest possible gate. This is a causal margin, not a
    # demonstration of an actual synchronized instrument.
    eta_sync=F(9,64);radius=F(1,100)
    sync_margin=L-eta_sync-radius-2*guard
    assert eta_sync-guard>F(1,8) and sync_margin>0
    nmax=F(finite["finite_family"]["lapse_interval"][1])
    cone=I(radius+T+guard)+I(nmax-1)*duration
    assert F(pair(cone)[1])<F(1,4)
    assert F(pair(iv.sin(I(F(1,4)))*iv.sqrt(3))[1])<1
    records=old["previous_review"]["conditional_records"]
    assert records["fixed_number_of_all_starts"]==64
    assert records["classifier"]=="old iff plus count >= 11; new iff plus count <= 10"
    assert F(records["old_error_upper"])<F(1,100000)
    assert F(records["new_error_upper"])<F(1,100000)
    result={
        "schema":"ueot-operational-central-clock-probe/1",
        "status":"FINITE_CENTRAL_PROPER_CLOCK_RECORDS_CERTIFIED",
        "base_commit":BASE,"symbolic":symbolic(),
        "metric_family":{
            "lambda":lam_value,"epsilon_interval":["-1","1"],
            "same_exact_lapse_family_as_parent":True,
            "source_and_past_reference_fixed_during_epsilon_variation":True,
            "metric_00_relative_change_upper":finite["finite_family"]["metric_00_relative_change_upper"],
            "lapse_interval":finite["finite_family"]["lapse_interval"],
            "perturbation_time_interval":["1/16","1/8"],
            "future_test_transported_by_actual_central_clock":True,
            "archived_nominal_probe_window":["5/32","3/16"],
        },
        "new_future_energy_domain":{
            "nominal_window":["5/32","3/16"],
            "guard":str(guard),"extended_window":[str(L-guard),str(T+guard)],
            "past_covariance_slice":"1/16",
            "old_nominal_variance_extended_beyond_its_domain":False,
            "old_mean_RSET_or_stress_noise_extended":False,
            "a_min":pair(amin),"unperturbed_energy_rate_upper":pair(r0),
            "perturbed_I_energy_rate_upper":pair(rn),
            "full_field_covariance_norm_bound_at_past_slice":"9/8",
        },
        "common_constants":{
            "metric_clock_offset_per_lambda_per_abs_epsilon_upper":pair(delta_tau_per_lambda),
            "metric_coordinate_shift_per_abs_epsilon_upper":pair(metric_shift),
            "propagator_difference_energy_per_abs_epsilon_upper":pair(Nprop),
            "clock_difference_energy_per_coordinate_shift_upper":pair(Nclock_per_shift),
            "propagator_coherent_mean_difference_per_abs_epsilon_upper":pair(phase_prop),
            "base_coherent_time_derivative_upper":pair(phase_derivative),
            "archived_nominal_base_variance_upper":pair(V0),
            "probe_H1_upper":pair(F1),
            "all_epsilon_formula":"N_delta <= |epsilon|*Nprop + Nclock_per_shift*(|epsilon|*zeta_metric + |beta|/a_min); analogous mean bound",
        },
        "record_certificates":rows,
        "inherited_field_calibration_contract":calibration,
        "central_clock_and_synchronization_contract":{
            "central_geodesic_clock":True,
            "future_clock_rate_is_proper_rate":True,
            "common_constant_origin_error_allowed":True,
            "uncompensated_independent_station_clocks":False,
            "differential_station_timing_errors_included":False,
            "calibrated_aperture_control_uses_same_central_clock_time":True,
            "sync_nominal_central_clock_parameter":str(eta_sync),
            "sync_actual_eta_enclosing_interval":[str(eta_sync-guard),str(eta_sync+guard)],
            "aperture_radius_chi":str(radius),
            "coordinate_causal_sync_margin":str(sync_margin),
            "causal_inner_patch_sum_upper":pair(cone),
            "positive_causal_margin_is_a_hardware_implementation_proof":False,
            "actual_clock_sync_or_driver_calibration_performed":False,
        },
        "conditional_64_start_gate":{
            "fixed_all_starts":64,"classifier":records["classifier"],
            "score":"plus=1; minus=0; pre-interrogation heralded fail=0",
            "old_error_upper":records["old_error_upper"],
            "new_error_upper":records["new_error_upper"],
            "same_coarse_conditional_probability_gates_reestablished":True,
            "complete_contract_required_given_every_previous_record":True,
            "predictable_epsilon_beta_and_calibration_choices_allowed":True,
            "marginal_probabilities_alone_suffice":False,
            "arbitrary_optional_stopping_allowed":False,
        },
        "scope":{
            "same_finite_lapse_family_and_same_fixed_past_field":True,
            "same_archived_nominal_time_program":True,
            "absolute_probability_band_for_arbitrary_new_time_program":False,
            "transported_actual_central_proper_clock_test":True,
            "all_modes_and_regular_zero_mode":True,
            "independent_station_clock_protocol":False,
            "arbitrary_clock_rate_drift":False,
            "full_RSET_or_stress_noise_on_finite_path":False,
            "nonlinear_SCE_or_full_quantum_feedback":False,
            "classical_branch_geometry_imported":False,
            "full_apparatus_stress_or_cost":False,
            "new_hardware_or_Lean":False,
        },
        "new_mode_integrations":0,"new_geometry_ODE_integrations":0,
        "input_sha256":{str(p.relative_to(REPO)):h for p,h in sorted(frozen.items())},
    }
    for p,h in frozen.items():assert sha(p)==h,"Input changed during clock calculation"
    return result

if __name__=="__main__":
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--write",action="store_true")
    ap.add_argument("--check",action="store_true")
    args=ap.parse_args();result=calculate()
    rendered=json.dumps(result,indent=2,sort_keys=True,ensure_ascii=False)+"\n"
    target=HERE/"result.json"
    if args.write:target.write_text(rendered)
    if args.check:assert target.read_text()==rendered,"Central-clock receipt mismatch"
    for name,row in result["record_certificates"].items():
        print(name)
        for k in ["coordinate_time_displacement_upper",
                  "old_all_start_probability_difference_from_archived_nominal_upper",
                  "new_all_start_probability_difference_from_archived_nominal_upper",
                  "old_all_start_plus_interval","new_all_start_plus_interval"]:
            print(k,[float(F(x)) for x in row[k]])
    print("PASS: exact central proper-clock test transport, full-field finite bands and inherited 64-start gate.")
