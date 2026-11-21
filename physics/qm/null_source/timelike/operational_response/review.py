"""Independent operational records, tensor calibration and counterterm review.

This check recomputes the statistical gates, normalization inequalities and
local Weyl-square tensor algebra. It neither runs a predecessor checker nor
integrates mode or geometry ODEs.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
import hashlib
from itertools import product
import json
from pathlib import Path
import subprocess
from mpmath import iv, mp
import sympy as sp

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[4]
TL="physics/qm/null_source/timelike/"
BASE="f2b09fb2b8fd2235bde7017b060fc07ecc44b441"
mp.dps=100
iv.dps=85

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def I(x):return iv.mpf(x.numerator)/x.denominator if isinstance(x,F) else iv.mpf(x)
def endpoint(x,j):return mp.make_mpf(x._mpi_[j])
def rational(x):
    sign,m,p,_=x._mpf_
    return F((-1 if sign else 1)*m)*F(2)**p
def pair(x):return [str(rational(endpoint(x,j))) for j in (0,1)]
def lower(x):return F(pair(x)[0])
def upper(x):return F(pair(x)[1])
def U(obj,key):return F(obj[key][1])
def L(obj,key):return F(obj[key][0])
def divergence(p,q):
    p=I(p);q=I(q)
    return p*iv.log(p/q)+(1-p)*iv.log((1-p)/(1-q))
def decimal(x):return mp.nstr(mp.mpf(x.numerator)/x.denominator,22)

def local_algebra():
 t,x,y,z=sp.symbols('t x y z',real=True);coords=[t,x,y,z];f=sp.Function('f')(t,z)
 metric=sp.diag(-1,1,1,1);sign=[-1,1,1,1]
 h=sp.diag(0,f,-f,0)
 R={}
 for a,b,c,d in product(range(4),repeat=4):
  R[a,b,c,d]=sp.simplify((sp.diff(h[a,d],coords[b],coords[c])+sp.diff(h[b,c],coords[a],coords[d])-sp.diff(h[b,d],coords[a],coords[c])-sp.diff(h[a,c],coords[b],coords[d]))/2)
 Ric=sp.Matrix(4,4,lambda b,d:sp.simplify(sum(sign[a]*R[a,b,a,d] for a in range(4))))
 scalar=sp.simplify(sum(sign[a]*Ric[a,a] for a in range(4)))
 assert scalar==0
 C={}
 for a,b,c,d in product(range(4),repeat=4):
  C[a,b,c,d]=sp.simplify(R[a,b,c,d]-(metric[a,c]*Ric[d,b]-metric[a,d]*Ric[c,b]-metric[b,c]*Ric[d,a]+metric[b,d]*Ric[c,a])/2+scalar*(metric[a,c]*metric[d,b]-metric[a,d]*metric[c,b])/6)
 assert all(sp.simplify(sum(sign[a]*C[a,b,a,d] for a in range(4)))==0 for b,d in product(range(4),repeat=2))
 HC=sp.Matrix(4,4,lambda a,b:sp.simplify(4*sum(sign[c]*sign[d]*sp.diff(C[a,c,b,d],coords[c],coords[d]) for c,d in product(range(4),repeat=2))))
 wave2=sp.diff(f,t,4)-2*sp.diff(f,t,2,z,2)+sp.diff(f,z,4)
 assert sp.simplify(HC-sp.diag(0,-wave2,wave2,0))==sp.zeros(4)
 F=sp.Function('F')(t)
 square=sp.simplify(sum(sign[a]*sign[b]*sign[c]*sign[d]*C[a,b,c,d]**2 for a,b,c,d in product(range(4),repeat=4)))
 assert sp.simplify(square.subs(f,F).doit()-sp.diff(F,t,2)**2)==0
 p=sp.symbols('a b c d e',real=True);a,b,c,d,e=p
 T=sp.Matrix([[a,b,c],[b,d,e],[c,e,-a-d]]);v=sp.Matrix([0,0,1]);Tv=T*v
 H=[sp.Matrix(3,3,lambda i,j:3*v[k]*T[i,j]+v[i]*T[k,j]+v[j]*T[i,k]-int(k==i)*Tv[j]-int(k==j)*Tv[i]) for k in range(3)]
 J=sp.Matrix([[0,-1,0],[1,0,0],[0,0,0]])
 norm=lambda m:sum(q*q for q in m)
 assert sp.expand(sum(norm(q) for q in H)-15*norm(T)+norm(J*T-T*J))==0
 eps=sp.symbols("eps",real=True)
 quadratic=eps**2*sp.diff(F,t,2)**2
 assert sp.diff(quadratic,eps).subs(eps,0)==0
 assert sp.diff(quadratic,eps,2)==2*sp.diff(F,t,2)**2
 assert HC.subs(f,t**4/24).doit().subs(t,0)==sp.diag(0,-1,1,0)
 X,Y=sp.symbols("X Y",commutative=False)
 c,d,m,m2=sp.symbols("c d m m2",real=True)
 assert sp.expand((X+c)*(Y+d)-(Y+d)*(X+c)-X*Y+Y*X)==0
 assert sp.expand(m2+2*c*m+c*c-(m+c)**2-(m2-m*m))==0
 scale,U0,G0,C0,lam=sp.symbols("scale U G C lambda",positive=True)
 score_variance=U0**4*C0/(lam**4*G0**2)
 scaled=(scale*U0)**4*C0/(lam**4*(scale**2*G0)**2)
 assert sp.simplify(scaled-score_variance)==0
 return {
  "convention":"H_C_ab=4 nabla^c nabla^d C_acbd+2 R^cd C_acbd",
  "flat_TT_perturbation":"h11=f(t,z), h22=-f(t,z), other components zero",
  "flat_TT_components":str(HC),
  "Weyl_tensor_trace_checks":True,
  "time_only_linearized_Weyl_tensor_squared":str(sp.diff(F,t,2)**2),
  "first_variation_of_Weyl_square_on_conformally_flat_background":0,
  "time_only_second_variation_density":"2*(F''(t))^2",
  "compact_fourth_jet_witness":"F=F'=F''=F'''=0, F''''=1 at an interior point",
  "curved_nonzero_by_principal_symbol_argument":True,
  "curved_principal_jet":"delta H_C,ij=-a_lambda^-2 F'''' tau_ij",
  "full_curved_Bach_operator_computed":False,
  "exists_nonzero_overlapping_TT_pairing":True,
  "every_overlapping_pairing_nonzero_claimed":False,
  "c_number_covariance_and_commutator_cancellation_checked":True,
  "spin2_connection_cap_15_verified":True,
  "spin2_identity":"sum_k ||H_k||_F^2=15 ||T||_F^2-||J_3 T-T J_3||_F^2 for unit radial direction",
  "calibrated_shape_rescaling_cancellation_checked":True,
  "independent_algebra_replaces_no_all_mode_or_PDE_proof":True,
 }

def fixed_64_records(old_interval,new_interval):
    lo=F(old_interval[0]);hi=F(new_interval[1])
    pold=F(9,20);pnew=F(1,40);q=F(1,6);n=64
    assert lo>pold>q>pnew>hi
    assert F(10,n)<q<F(11,n)
    oldrisk=upper(iv.exp(-n*divergence(q,pold)))
    newrisk=upper(iv.exp(-n*divergence(q,pnew)))
    assert oldrisk<F(1,100000) and newrisk<F(1,100000)
    assert lo<F(19,40)<F(old_interval[1])
    assert F(new_interval[0])<F(1,100)<hi
    return {
        "fixed_all_start_count":n,
        "classifier":"old iff plus count >= 11; minus and pre-interrogation failure score zero",
        "old_error_upper":str(oldrisk),"new_error_upper":str(newrisk),
        "old_error_upper_decimal":decimal(oldrisk),"new_error_upper_decimal":decimal(newrisk),
        "conditional_plus_probability_gates":[str(pold),str(pnew)],
        "requires_contract_given_complete_past":True,
        "independent_fresh_preparations_sufficient":True,
        "unconditional_marginals_sufficient":False,
        "marginal_only_negative_control":{
            "all_records_equal_one_Bernoulli_variable":True,
            "old_marginal":"19/40","old_error":"21/40",
            "new_marginal":"1/100","new_error":"1/100",
        },
        "arbitrary_optional_stopping_certified":False,
    }

def fixed_256_records(variance,claimed):
    n=256;kmin=240;fail=F(1,100);bad=17
    bias=F(1,1000);threshold=F(1,200);signal=F(1,100)
    margin=min(threshold-bias,signal-threshold-bias)
    assert margin==F(1,250) and n-kmin+1==bad
    noise=F(n)*variance/(F(kmin)*margin)**2
    D=divergence(F(bad,n),fail)
    failure=upper(iv.exp(-n*D))
    risk=noise+failure
    assert risk<F(1,100000)
    assert claimed["fixed_number_of_all_starts"]==n
    assert claimed["minimum_success_records"]==kmin
    assert U(claimed,"failure_tail_upper")>=failure
    assert U(claimed,"martingale_noise_risk_upper")>=noise
    assert U(claimed,"per_hypothesis_total_error_upper")>=risk
    # Exact marginal-only counterexample; a fully shared variable has no
    # sample averaging improvement, while each one-trial variance is valid.
    a=F(1,200);prob=variance/(variance+a*a);negative=-variance/a
    assert prob*a+(1-prob)*negative==0
    assert prob*a*a+(1-prob)*negative*negative==variance
    assert a+bias>threshold and prob>F(1,100000)
    return {
        "fixed_all_start_count":n,"minimum_success_records":kmin,
        "comparison":"known TT profile coefficients theta=0 versus theta=1/100",
        "threshold":str(threshold),"total_normalized_bias_gate":str(bias),
        "margin":str(margin),"conditional_success_noise_variance_upper":str(variance),
        "failure_tail_upper":str(failure),
        "martingale_noise_risk_upper":str(noise),
        "per_candidate_error_upper":str(risk),
        "per_candidate_error_upper_decimal":decimal(risk),
        "independent_exact_fraction_and_interval_recomputation":True,
        "failure_count_is_at_least_17":True,
        "all_failures_count_in_256_starts_and_error_budget":True,
        "fallback_on_fewer_than_240_successes_predeclared":True,
        "noise_mean_and_variance_required_given_past_and_current_success":True,
        "full_256_term_unconditional_martingale_second_moment_used":True,
        "variance_conditioned_on_success_count_reused_without_proof":False,
        "iid_or_Gaussian_noise_required":False,
        "bound_is_per_candidate_not_two_dataset_joint_error":True,
        "marginal_only_negative_controls":{
            "shared_noise_positive_value":str(a),
            "shared_noise_negative_value":str(negative),
            "shared_noise_error_probability":str(prob),
            "shared_noise_first_two_marginal_moments_exact":True,
            "shared_failure_probability":"1/100",
            "shared_failure_17_or_more_probability":"1/100",
            "these_examples_violate_complete_past_condition":True,
        },
    }

def clock_review(clock,nominal,finite,prep):
    assert clock["status"]=="FINITE_CENTRAL_PROPER_CLOCK_RECORDS_CERTIFIED"
    family=clock["metric_family"];domain=clock["new_future_energy_domain"]
    assert family["lambda"]==32768 and family["epsilon_interval"]==["-1","1"]
    assert family["same_exact_lapse_family_as_parent"] is True
    assert family["source_and_past_reference_fixed_during_epsilon_variation"] is True
    assert domain["past_covariance_slice"]=="1/16"
    assert domain["full_field_covariance_norm_bound_at_past_slice"]=="9/8"
    assert domain["old_nominal_variance_extended_beyond_its_domain"] is False
    c=clock["common_constants"];a=finite["analytic_constants"]
    guard=F(1,100000);Tg=F(3,16)+guard;lam=32768;t=F(201,20)
    amin=L(domain,"a_min");r0=U(domain,"unperturbed_energy_rate_upper")
    assert 0<amin<=lower(iv.sqrt(3*iv.cos(2*I(Tg))))
    assert r0>=upper(iv.tan(2*I(Tg))+I(F(1,2)))
    rn=U(a,"perturbed_growth_rate_upper")
    E0=iv.exp(I(r0)*I(Tg-F(1,16)))
    EI=iv.exp(I(rn)/16);EF=iv.exp(I(r0)*I(Tg-F(1,8)))
    F1=U(a,"probe_H1_upper")
    F0=iv.sqrt(I(U(a,"probe_L2_squared_upper")))
    offset=U(c,"metric_clock_offset_per_lambda_per_abs_epsilon_upper")
    assert offset>=upper(iv.sqrt(3)*I(U(a,"int_lapse_difference_Linfinity_per_epsilon_upper")))
    shift=U(c,"metric_coordinate_shift_per_abs_epsilon_upper")
    assert shift>=offset/amin
    Nprop=U(c,"propagator_difference_energy_per_abs_epsilon_upper")
    Nclock_per=U(c,"clock_difference_energy_per_coordinate_shift_upper")
    fresh_N=EI*E0/I(amin)*(I(F1)*I(U(a,"int_lapse_difference_Linfinity_per_epsilon_upper"))+
             F0*I(U(a,"int_lapse_gradient_Linfinity_per_epsilon_upper")))
    assert Nprop>=upper(fresh_N) and Nclock_per>=upper(E0*I(F1)/I(amin))
    mprop=U(c,"propagator_coherent_mean_difference_per_abs_epsilon_upper")
    mdot=U(c,"base_coherent_time_derivative_upper")
    fresh_mu=iv.sqrt(27)/(3*iv.cos(I(F(1,4))))*iv.sqrt(3)*EI*EF*F0/I(amin)*I(U(a,"int_lapse_difference_L2_per_epsilon_upper"))
    assert mprop>=upper(fresh_mu)
    assert mdot>=upper(iv.sqrt(27)/(3*iv.cos(2*I(Tg))))
    V0=U(c,"archived_nominal_base_variance_upper")
    assert V0==F(prep["reference_variance"]["full_base_smeared_field_variance_upper"][1])
    audited={}
    for name,row in clock["record_certificates"].items():
        beta=F(row["beta_absolute_cap"]);zeta=U(row,"coordinate_time_displacement_upper")
        assert beta in {F(0),guard}
        assert zeta>=shift+beta/amin and zeta<guard
        margin=amin*guard-offset-beta
        assert margin>0 and F(row["inverse_clock_endpoint_margin_per_lambda_lower"])<=margin
        assert F(row["common_clock_origin_error_physical_absolute_cap"])==lam*beta
        assert list(map(F,row["actual_probe_support_enclosing_interval"]))==[F(5,32)-zeta,F(3,16)+zeta]
        nc=U(row,"clock_test_difference_energy_norm_upper")
        nt=U(row,"complete_probe_difference_energy_norm_upper")
        sd=U(row,"sqrt_base_probe_difference_variance_upper")
        mc=U(row,"coherent_clock_mean_difference_upper")
        mu=U(row,"complete_coherent_mean_difference_upper")
        assert nc>=Nclock_per*zeta and nt>=Nprop+nc
        assert sd**2>=F(9,8)*nt**2
        assert mc>=mdot*zeta and mu>=mprop+mc
        qlin=U(row,"quantum_probability_linear_coefficient")
        qquad=U(row,"quantum_probability_quadratic_coefficient")
        cnew=U(row,"new_coherent_probability_coefficient")
        cold=U(row,"old_coherent_probability_coefficient")
        assert qlin**2 >= (t*t/F(2*lam*lam))**2*V0*sd**2
        assert qquad>=t*t/F(4*lam*lam)*sd**2
        assert cnew>=t*mu/2
        assert cold>=upper(I(cnew)*(1+iv.sqrt(3))/2)
        changes={}
        for label,coherent in [("old",cold),("new",cnew)]:
            delta=U(row,label+"_all_start_probability_difference_from_archived_nominal_upper")
            assert delta>=coherent+qlin+qquad
            previous=nominal["same_scale"][label+"_all_start_plus_interval"]
            current=row[label+"_all_start_plus_interval"]
            assert F(current[0])<=max(F(0),F(previous[0])-delta)
            assert F(current[1])>=min(F(1),F(previous[1])+delta)
            changes[label]=str(delta)
        assert U(row,"complete_three_label_TV_from_same_calibrated_nominal_upper")>=F(changes["old"])>=F(changes["new"])
        records=fixed_64_records(row["old_all_start_plus_interval"],row["new_all_start_plus_interval"])
        audited[name]={
            "beta_absolute_cap":str(beta),"coordinate_shift_upper":str(zeta),
            "old_probability_change_upper":changes["old"],"new_probability_change_upper":changes["new"],
            "old_all_start_plus_interval":row["old_all_start_plus_interval"],
            "new_all_start_plus_interval":row["new_all_start_plus_interval"],
            "independent_fraction_energy_and_probability_factors_checked":True,
            "comparison_is_archived_nominal_not_parent_finite_interval":True,
            "records":records,
        }
    sync=clock["central_clock_and_synchronization_contract"]
    assert F(sync["coordinate_causal_sync_margin"])==F(5,32)-F(9,64)-F(1,100)-2*guard>0
    assert sync["central_geodesic_clock"] is True
    assert sync["differential_station_timing_errors_included"] is False
    main=audited["bounded_common_clock_origin"]
    assert F(main["old_probability_change_upper"])<F("0.0003013810")
    assert F(main["new_probability_change_upper"])<F("0.0002603350")
    return {
        "finite_proper_clock_probability_bound":True,
        "lambda":lam,"epsilon_interval":["-1","1"],
        "fixed_all_start_count":64,
        "old_error_upper":main["records"]["old_error_upper"],
        "new_error_upper":main["records"]["new_error_upper"],
        "clock_rows":audited,
        "original_nominal_probability_band_counted_once":True,
        "positive_causal_sync_margin":sync["coordinate_causal_sync_margin"],
        "proper_clock_offset_and_Jacobian_retained":True,
        "uncompensated_independent_station_clocks_included":False,
        "full_stress_noise_transferred_to_finite_metric":False,
    }

def kernel_review(kernel,parent_tensor):
    assert kernel["status"]=="FULL_SEPARATED_WINDOW_RETARDED_RSET_AND_CERTIFIED_TEST_SPACE_NORM"
    lam=kernel["lambda"];K=kernel["reuse"]["K"]
    assert lam==32768 and K==256
    assert kernel["reuse"]["preparation_remainder_valid_eta"]==["0","3/16"]
    E=U(kernel["reuse"],"preparation_remainder_E5_upper")
    S4=F(K*(K+1)*(2*K+1)*(3*K*K+3*K-1),30)
    caps={}
    for name,w in kernel["windows"].items():
        end=F(w["time_support_closure"][1])
        assert end==({"past":F(1,8),"future":F(3,16)}[name])
        growth=w["preparation_growth"]
        H=U(growth,"all_nonzero_mode_field_factor_upper")
        # A_L is an auxiliary analytic lower bound on the smooth splice,
        # not its actual static left endpoint A_0.
        A0=iv.sqrt(3);AL=iv.sqrt(3*iv.cos(I(F(1,4))))
        AR=iv.sqrt(3*iv.cos(I(F(1,8))))
        Aend=iv.sqrt(3*iv.cos(2*I(end)))
        R=(A0+AR-2*AL)/AL+iv.log(A0/AR)+iv.log(A0/Aend)
        assert H>=upper(iv.exp(2*R)/2)
        assert growth["past_H_reused_outside_its_domain"] is False
        Ls=[F(p[1]) for p in w["time_derivative_L1_upper"]]
        phase=w["positive_frequency_phase"]
        gs=[F(p[1]) for p in phase["gradient_time_derivative_coefficients_abs_upper"]]
        assert phase["IBP_order"]==3 and phase["pair_frequencies_independent"] is True
        assert phase["fresh_time_jets_not_transplanted_from_past"] is True
        Lg=U(w,"gradient_IBP_L1_upper")
        assert Lg>=sum(a*b for a,b in zip(gs,Ls))
        low=U(w,"complete_low_row_Hilbert_Schmidt_upper")
        main=U(w,"high_positive_Hilbert_Schmidt_upper")
        err=U(w,"high_preparation_remainder_Hilbert_Schmidt_upper")
        C=U(w,"C_T_upper");variance=U(w,"raw_readout_variance_upper_at_lambda")
        assert low**2>=H**2*Ls[0]**2*S4
        assert main**2>=Lg**2/F(4*K)
        assert err**2>=16*Ls[0]**2*E**2/F(5*K**5)
        assert C>=32*(2*low**2+(main+err)**2)
        assert variance*lam**4>=C
        assert U(w,"raw_readout_RMS_upper_at_lambda")**2>=variance
        caps[name]=C
    P=kernel["windows"]["past"];Q=kernel["windows"]["future"]
    for j,(p,q) in enumerate(zip(P["time_derivative_L1_upper"],Q["time_derivative_L1_upper"])):
        assert F(q[1])==F(2)**(j-1)*F(p[1])
    assert U(Q["preparation_growth"],"all_nonzero_mode_field_factor_upper")>U(P["preparation_growth"],"all_nonzero_mode_field_factor_upper")
    previous=U(parent_tensor["all_mode_noise"],"C_T_upper")
    assert abs(caps["past"]/previous-1)<F(1,10**12)
    r=kernel["response"];norm=kernel["separated_test_space_bound"]
    response=U(r,"susceptibility_absolute_upper")
    assert response**2>=caps["past"]*caps["future"]/F(16*lam**4)
    assert response<F("0.249425721")
    assert U(norm,"operator_norm_upper")==F(1,4*lam**2)==F(1,2**32)
    assert U(norm,"coarser_sum_W31_time_norm_bilinear_upper")>=U(P,"noise_norm_over_sum_W31_upper")*U(Q,"noise_norm_over_sum_W31_upper")/F(4*lam**2)
    assert F(r["time_gap"])==F(5,32)-F(1,8)==F(1,32)
    for key in ["contact_distribution_pairing","all_input_metric_jets_on_output_neighborhood",
                "explicit_output_metric_frame_volume_variation","pressure_times_h_term_on_output",
                "homogeneous_displacement_first_order_response_difference"]:
        assert r[key]==0
    assert r["full_smeared_RSET_derivative_for_these_windows"] is True
    assert r["response_nonzero_certified"] is False
    assert kernel["scope"]["feedback_small_gain_certified"] is False
    assert kernel["scope"]["full_feedback_operator_including_overlap_contacts"] is False
    return {
        "lambda":lam,"past_C_upper":str(caps["past"]),"future_C_upper":str(caps["future"]),
        "susceptibility_absolute_upper":str(response),
        "susceptibility_absolute_upper_decimal":decimal(response),
        "projective_test_space_norm_upper":str(F(1,4*lam**2)),
        "independent_fraction_low_high_mixed_and_response_factors_checked":True,
        "future_low_mode_growth_and_time_jets_recomputed":True,
        "full_smeared_RSET_derivative_on_strictly_separated_windows":True,
        "input_generator":"-lambda^2 O_P/8",
        "local_contacts_vanish_by_support_for_this_pair":True,
        "old_new_homogeneous_preparation_TT_response_identical":True,
        "actual_response_nonzero_certified":False,
        "overlapping_response_or_feedback_small_gain_certified":False,
        "central_clock_error_contract_automatically_transferred":False,
    }

def calibration_review(data,parent_tensor):
    assert data["status"]=="CALIBRATED_TT_PROFILE_AND_COMPLETE_RECORD_GATE_CERTIFIED"
    c=data["calibration"];rad=data["radial_certificate"];scope=data["scope"]
    lam=c["lambda"];assert lam==32768
    u=F(c["fixed_rational_U"]);assert u==F(269939,100000000)
    assert u*u>=F(rad["tau_sup_squared_upper"])
    assert rad["Bernstein_dyadic_depth"]==11 and rad["regular_cells"]==2016
    assert rad["denominator_powers"]==[12,16,20] and rad["tail_v_min"]==64
    assert data["symbolic"]["angular_reproducing_kernel_dimension"]==28
    A=rad["weighted_flat_first_derivative_squared"];B=rad["tau_L2_squared"]
    r0=iv.tan(I(F(1,16)));correction=15*r0*r0*I(F(B[1]))
    assert F(A[0])>upper(correction)>0
    elo=(iv.sqrt(I(F(A[0])))-iv.sqrt(correction))**2+2*I(F(B[0]))
    ehi=(iv.sqrt(I(F(A[1])))+iv.sqrt(correction))**2+2*I(F(B[1]))
    energy=rad["spatial_calibration_energy_interval"]
    assert 0<F(energy[0])<=lower(elo)
    assert F(energy[1])>=upper(ehi)
    timeweight=c["time_weight_integral_A2_psi"]
    gain=c["raw_tau_profile_gain_interval"]
    assert 0<F(gain[0])<=F(timeweight[0])*F(energy[0])
    assert F(gain[1])>=F(timeweight[1])*F(energy[1])
    normalized=c["normalized_profile_gain_interval"]
    assert F(normalized[0])<=F(gain[0])/u and F(normalized[1])>=F(gain[1])/u
    gainlo=L(c,"normalized_gain_lower")
    assert gainlo==F(normalized[0])>0
    CT=U(parent_tensor["all_mode_noise"],"C_T_upper")
    variance=U(c,"raw_readout_variance_upper")
    score_variance=U(c,"calibrated_score_variance_upper")
    rms=U(c,"calibrated_score_RMS_upper")
    assert variance>=u*u*CT/lam**4
    assert U(c,"raw_readout_RMS_upper")**2>=variance
    assert score_variance>=variance/gainlo**2
    assert rms*rms>=score_variance and rms<F("0.0001678368")
    EQ=U(c,"improved_pointwise_strain_error_gain_upper")
    assert EQ<F("0.023592734")<U(parent_tensor["readout"],"pointwise_strain_error_gain_upper")
    assert U(c,"rough_Laplacian_L2_upper")**2>=3*U(c,"covariant_second_derivative_L2_upper")**2
    assert U(c,"normalized_bias_gain_upper")>=EQ/gainlo
    bias=U(c,"total_normalized_bias_upper")
    assert bias>=EQ*F(c["pointwise_reconstruction_error_budget"])/gainlo+F(c["other_normalized_bias_budget"])
    assert bias<F(1,1000)
    assert L(c,"allowed_pointwise_error_if_other_bias_le_1_over_2000")<=F(1,2000)*gainlo/EQ
    assert c["profile_has_exact_unit_sup_norm"] is False
    assert scope["distinguishes_old_new_homogeneous_source_preparations"] is False
    assert scope["finite_theta_perturbed_state_noise_transferred"] is False
    assert scope["actual_quantum_geometry_measurement_instrument_constructed"] is False
    assert scope["full_quantum_RSET_feedback_included"] is False
    records=fixed_256_records(score_variance,data["complete_record_gate"])
    records.update({
        "lambda":lam,"profile_sup_upper":str(u),
        "raw_profile_gain_interval":gain,"normalized_gain_interval":normalized,
        "normalized_gain_lower":str(gainlo),
        "calibrated_score_RMS_upper":str(rms),
        "calibrated_score_RMS_upper_decimal":decimal(rms),
        "pointwise_strain_error_gain_upper":str(EQ),
        "total_normalized_bias_upper":str(bias),
        "independent_fraction_gain_variance_and_bias_checks":True,
        "reference_model":"forced linear TT geometry and archived unperturbed induced covariance",
        "actual_quantum_geometry_instrument_constructed":False,
        "finite_theta_quantum_noise_transferred":False,
        "distinguishes_old_new_homogeneous_preparations":False,
    })
    return records

def calculate():
    assert __debug__,"Scientific assertions must remain enabled"
    parent_paths={
        "nominal":REPO/(TL+"stress_kernel/review.json"),
        "finite":REPO/(TL+"metric_response/finite/result.json"),
        "tensor":REPO/(TL+"metric_response/tensor/result.json"),
        "preparation":REPO/(TL+"response/preparation/result.json"),
    }
    frozen={}
    parents={}
    for key,path in parent_paths.items():
        relative=str(path.relative_to(REPO))
        assert path.read_bytes()==subprocess.check_output(["git","show",BASE+":"+relative],cwd=REPO)
        frozen[path]=sha(path);parents[key]=json.loads(path.read_text())
    components={}
    for name in ["clock","kernel","calibration"]:
        path=HERE/name/"result.json"
        component=json.loads(path.read_text())
        assert component.get("base_commit",component.get("reviewed_base"))==BASE
        assert component.get("new_mode_integrations",component["scope"].get("new_mode_integrations"))==0
        for relative,expected in component["input_sha256"].items():
            p=REPO/relative
            assert sha(p)==expected,("Component input hash mismatch",relative)
            frozen[p]=expected
        for file in ["check.py","README.md","result.json"]:
            p=HERE/name/file;frozen[p]=sha(p)
        components[name]=component
    for file in ["review.py","README.md","CONTRACT.md"]:
        path=HERE/file;frozen[path]=sha(path)
    clock=clock_review(components["clock"],parents["nominal"],parents["finite"],parents["preparation"])
    quantum=kernel_review(components["kernel"],parents["tensor"])
    calibration=calibration_review(components["calibration"],parents["tensor"])
    algebra=local_algebra()
    counterterm={
        "background":"conformally flat FLRW family",
        "local_addition":"T_c=T_0+c*H_C*identity",
        "all_FLRW_mean_values_unchanged":True,
        "fixed_background_connected_noise_and_commutators_unchanged":True,
        "strictly_separated_response_unchanged":True,
        "exists_nonzero_overlapping_TT_pairing":True,
        "overlap_witness_at_eta0":"4 A^2 integral tau:delta H_C = -4*F''''*||tau||_2^2/lambda^2",
        "requires_declared_net_renormalized_Weyl_squared_coupling":True,
        "different_net_couplings_with_other_side_fixed_are_different_models":True,
        "pure_scheme_change_with_compensating_gravity_term_changes_physics":False,
        "previous_fixed_scheme_mean_functional_equivalence_invalidated":False,
        "uniform_overlap_bound_independent_of_unconstrained_net_coupling_follows":False,
        "specific_coupling_instability_proved":False,
        "full_curved_Bach_operator_computed":False,
        "written_principal_symbol_argument_in":"README.md section 4.1",
        "flat_tensor_algebra_computed_this_check":True,
    }
    result={
        "schema":"ueot-operational-response-independent-review/1",
        "status":"PASS","reviewed_base":BASE,
        "proper_clock":clock,"quantum_response":quantum,
        "calibrated_TT":calibration,"counterterm_contract":counterterm,
        "exact_algebra":algebra,
        "legacy_base_metric_quantities":{
            "complete_density_relative_variance_upper":parents["nominal"]["same_scale"]["relative_total_stress_variance_upper"],
            "old_to_new_complete_density_variance_ratio_lower":parents["nominal"]["same_scale"]["old_to_new_total_variance_ratio_lower"],
            "recomputed_or_transferred_to_finite_corrected_geometry":False,
        },
        "scope":{
            "three_components_are_one_realized_self_consistent_experiment":False,
            "complete_retarded_RSET_for_declared_separated_windows":True,
            "full_quantum_feedback_resolvent":False,
            "full_nonlinear_SCE_solution":False,
            "finite_path_complete_RSET_noise_norm":False,
            "net_Weyl_squared_coupling_selected_by_FLRW_data":False,
            "new_Lean_proofs":False,"matched_hardware_data":False,
            "full_apparatus_stress_or_cost_advantage":False,
            "Core_unique_physical_selection":False,
        },
        "new_mode_integrations":0,"new_geometry_ODE_integrations":0,
        "input_sha256":{str(p.relative_to(REPO)):v for p,v in sorted(frozen.items())},
    }
    for p,expected in frozen.items():assert sha(p)==expected,("Input changed during independent review",str(p))
    return result

if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write",action="store_true")
    parser.add_argument("--check",action="store_true")
    args=parser.parse_args();result=calculate()
    rendered=json.dumps(result,indent=2,sort_keys=True,ensure_ascii=False)+"\n"
    target=HERE/"review.json"
    if args.write:target.write_text(rendered)
    if args.check:assert target.read_text()==rendered,"Operational independent review receipt mismatch"
    print("Proper-clock errors:",*[decimal(F(result["proper_clock"][k])) for k in ["old_error_upper","new_error_upper"]])
    print("Separated full RSET upper:",result["quantum_response"]["susceptibility_absolute_upper_decimal"])
    print("Calibrated TT RMS upper:",result["calibrated_TT"]["calibrated_score_RMS_upper_decimal"])
    print("256-start per-candidate error upper:",result["calibrated_TT"]["per_candidate_error_upper_decimal"])
    print("PASS: independent clock, response, calibration, conditional records and local-counterterm algebra.")
