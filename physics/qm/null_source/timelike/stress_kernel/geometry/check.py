"""Smooth geometry readouts, boundary cancellation, local flux, and ADM scope.

This independently proves the adjoint-domain interface of the archived linear
Einstein-scalar operator. It does not construct a full stochastic SCE solution.
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
BASE="29d49e3eee6299e2085492b0e061288b8166b5fa"
PREFIX="physics/qm/null_source/timelike/response/"
INPUTS=[
    PREFIX+"geometry/result.json",PREFIX+"noise/result.json",
    PREFIX+"CONTRACT.md",PREFIX+"verification.json",
]
mp.dps=90
iv.dps=78

def sha_bytes(data):return hashlib.sha256(data).hexdigest()
def sha(path):return sha_bytes(path.read_bytes())
def I(x):
    return iv.mpf(x.numerator)/x.denominator if isinstance(x,F) else iv.mpf(x)
def end(x,j):return mp.make_mpf(x._mpi_[j])
def rat(x):
    sign,mant,power,_=x._mpf_
    return F((-1 if sign else 1)*mant)*F(2)**power
def pair(x):return [str(rat(end(x,j))) for j in (0,1)]
def box(a,b):return iv.mpf([end(I(a),0),end(I(b),1)])
def upper(x):return I(end(x,1))
def lower(x):return I(end(x,0))
def simplify(x):return sp.trigsimp(sp.simplify(x))

def symbolic():
    t,s=sp.symbols("eta s",real=True)
    c=sp.cos(2*t)
    A=sp.sqrt(3*c)
    V=1-3/c**2
    v=c**sp.Rational(-1,2)
    u=sp.sin(2*t)/(2*sp.sqrt(c))
    L=lambda y:sp.diff(y,t,2)+V*y
    assert simplify(L(v))==0 and simplify(L(u))==0
    assert simplify(v*sp.diff(u,t)-sp.diff(v,t)*u)==1
    G=u*v.subs(t,s)-v*u.subs(t,s)
    assert simplify(G.subs(t,s))==0
    assert simplify(sp.diff(G,t).subs(t,s))==1
    psi=sp.Function("psi")(t)
    boundary=G*sp.diff(psi,t)-sp.diff(G,t)*psi
    assert simplify(sp.diff(boundary,t)-G*L(psi))==0
    for y in [v,u]:
        assert simplify(sp.diff(y*sp.diff(psi,t)-sp.diff(y,t)*psi,t)-y*L(psi))==0
    x=sp.symbols("x",real=True)
    bump=sp.exp(-1/(1-x*x))
    assert sp.simplify(sp.diff(bump,x,2)/bump-(6*x**4-2)/(1-x*x)**4)==0
    # The displaced stiff scalar has rho_f=p_f=27/(2*A^6).
    rho_f=sp.Rational(27,2)/A**6
    assert simplify(A**3*(rho_f-3*rho_f)/3+9/A**3)==0
    # Absolute scale and own-initial normalized volume are different readouts.
    assert simplify(L(A)+36/A**3)==0
    amplitude_kappa=sp.symbols("amplitude_kappa",real=True)
    beta_amp=amplitude_kappa*A
    assert simplify(3*beta_amp/A-3*beta_amp.subs(t,0)/A.subs(t,0))==0
    stiff_M=sp.symbols("stiff_M",positive=True)
    aM=(stiff_M/3)**sp.Rational(1,4)*sp.sqrt(c)
    volume_ratio=simplify((aM/aM.subs(t,0))**3)
    assert simplify(volume_ratio-c**sp.Rational(3,2))==0
    assert sp.diff(volume_ratio,stiff_M)==0
    clock_a,clock_h,clock_tau=sp.symbols("clock_a clock_h clock_tau",positive=True)
    delta_eta=-amplitude_kappa*clock_tau/clock_a
    assert sp.expand(3*clock_h*delta_eta
                     +3*amplitude_kappa*clock_h*clock_tau/clock_a)==0
    # Density-form ADM constraint: half of G_nn-2*T_cl,nn.
    lam=sp.symbols("lambda",positive=True)
    eps,b,bp,m=sp.symbols("eps b bp m",real=True)
    Ap=sp.diff(A,t)
    a=lam*(A+eps*b)
    ap=lam*(Ap+eps*bp)
    M2=lam**4*(27+eps*m)
    C=3*(a*a+ap*ap)/(2*a**4)-M2/(2*a**6)
    assert simplify(C.subs(eps,0))==0
    friedmann_first=2*Ap*bp+2*A*b+18*b/A**3-m/(3*A**2)
    assert simplify(sp.diff(C,eps).subs(eps,0)
                    -3*friedmann_first/(2*lam**2*A**4))==0
    chi=sp.symbols("chi",positive=True)
    Y=sp.cos(chi)
    assert simplify(sp.diff(Y,chi,2)+2*sp.cot(chi)*sp.diff(Y,chi)+3*Y)==0
    flux_primitive=sp.cos(chi)*sp.sin(chi)**3
    assert simplify(sp.diff(flux_primitive,chi)
                    -sp.sin(chi)**2*(3-4*sp.sin(chi)**2))==0
    k1,k2,z1,z2=sp.symbols("k1 k2 z1 z2",real=True)
    Delta=sp.Rational(3,4)*sp.Matrix([[k1*k1,k1*k2],[k1*k2,k2*k2]])
    assert sp.det(Delta)==0
    assert sp.expand((sp.Matrix([[z1,z2]])*Delta*sp.Matrix([z1,z2]))[0]
                     -sp.Rational(3,4)*(z1*k1+z2*k2)**2)==0
    variance_Z=sp.Rational(3,4);variance_E=sp.Integer(1)
    induced_old_minus_new=(variance_E+variance_Z)-variance_E
    total_old_minus_new=variance_E-(variance_E+variance_Z)
    assert induced_old_minus_new==sp.Rational(3,4)
    assert total_old_minus_new==-sp.Rational(3,4)
    return {
        "initial_correlation_negative_control":{
            "independent_Z_E_variances":["3/4","1"],
            "same_initial_H":"-Z","old_source":"E+Z","new_source":"E",
            "induced_old_minus_new":"3/4","total_old_minus_new":"-3/4",
            "statistical_counterexample_not_constructed_EL_state":True},
        "operator":"L=d_eta^2+1-3*sec(2*eta)^2 on [0,3/16]",
        "retarded_G":"u(eta)*v(s)-v(eta)*u(s)",
        "Wronskian":"1","Green_diagonal":"0","Green_derivative_jump":"1",
        "Lagrange_boundary_identity":"d_t[G*psi_prime-G_t*psi]=G*Lpsi",
        "compact_adjoint_domain_iff":"integral q*v=0 and integral q*u=0",
        "explicit_readout":"psi=b(32*(eta-3/32)); q=Lpsi; G_adjoint*q=psi",
        "positive_nonzero_q_fails_compact_past_test":True,
        "all_homogeneous_initial_terms_removed":True,
        "initial_source_independence_needed_for_this_filter":False,
        "generic_readout_intrinsic_source_cross_terms_may_exist":True,
        "absolute_scale_and_relative_volume":{
            "L_A":"-36/A^3","integral_q_A":"-4*Dpsi",
            "amplitude_particular_solution":"beta=(d_lambda^2/4)*A*(Y^2-1)",
            "own_initial_relative_log_volume_at_common_eta":"3*beta/A-3*beta(0)/A(0)=0",
            "pure_classical_stiff_family":"a_M^2=sqrt(M/3)*cos(2*eta), M>0",
            "own_initial_volume_ratio_at_common_eta":"cos(2*eta)^(3/2), independent of M",
            "fixed_proper_clock_time_shift":"delta_eta=-kappa*tau/a",
            "fixed_proper_clock_relative_log_volume_change":"-3*kappa*h*tau/a; generally nonzero",
            "q_reconstruction_needs_absolute_initial_scale":"int q*beta=(1/3)*int q*A*y-4*Dpsi*beta(0)/A(0)",
            "relative_volume_blindness_asserted_for_proper_clock_instrument":False},
        "classical_amplitude_forcing":"-9/A^3",
        "beta_normalization":"beta=delta_a/lambda; L beta=lambda^2*A^3*(xi_rho-3xi_p)/3",
        "signed_transfer_for_biased_source":"kappa=-d_lambda^2*Dpsi; Dpsi=9*integral psi/A^3",
        "old_minus_new_filtered_covariance":"(3/4)*kappa_i*kappa_j for the same declared linear response",
        "covariance_difference_PSD_rank_at_most_one":True,
        "legal_local_trace_test":{
            "spatial_window":"w=b(8*chi)/integral b(8*chi) dOmega_3",
            "tensor":"H^ab=-psi*w*g_lambda^ab/(3*lambda^2*A)",
            "compact_four_dimensional_test":True,
            "classical_D_of_H":"-Dpsi",
            "new_full_noise":"N_G(H,K)+d_lambda^2*Re<W_G[L_f(H)L_f(K)]>",
            "old_minus_new_noise":"(3/4)*d_lambda^4*D(H)*D(K)",
            "all_mode_trace_noise_numeric_bound_supplied":False,
            "legal_stress_test_by_itself_constructs_local_geometry_response":False},
        "ADM_density_residual":"C=(R3+K^2-Kij*Kij)/4-rho_classical",
        "ADM_homogeneous_background":"C[A,27]=0",
        "ADM_first_variation":"3*C1_no_quantum/(2*lambda^2*A^4)",
        "local_weighted_energy_balance":"rho_w_prime+3*h*(rho_w+p_w)=integral D_i(w)*J^i dOmega",
        "conformal_time_flux":"J^i=-A^-2*gamma^ij*T_eta_j; scalar J^i=-A^-2*phi_prime*D^i(phi)",
        "physical_KG_flux_negative_control":"phi=u(eta)*cos(chi), omega^2=3, u=u_prime=1 at eta=3/32",
        "local_weighted_source_is_automatically_FLRW_conserved":False,
    }

def bump_point(x):
    if abs(x)>=1:return I(0)
    return iv.exp(-1/(1-I(x)**2))
def bump_range(x0,x1):
    a=min(abs(x0),abs(x1)) if x0*x1>0 else F(0)
    b=max(abs(x0),abs(x1))
    return iv.mpf([end(bump_point(b),0),end(bump_point(a),1)])

def numerical():
    N=2048
    center=F(3,32);width=F(1,32);R=F(1,8)
    Ih=I(0);Ia=I(0);radial_flux=I(0)
    for j in range(N):
        x0=F(2*j,N)-1;x1=F(2*(j+1),N)-1
        bb=bump_range(x0,x1)
        t=box(center+width*x0,center+width*x1)
        aa=iv.sqrt(3*iv.cos(2*t))
        Ih+=I(width*(x1-x0))*bb
        Ia+=I(width*(x1-x0))*bb/aa**3
        r0=F(j,N);r1=F(j+1,N)
        chi=box(R*r0,R*r1)
        spatial=bump_range(r0,r1)
        ss=iv.sin(chi)**2
        radial_flux+=I(R*(r1-r0))*spatial*ss*(3-4*ss)
    Dpsi=9*Ia
    xstar=iv.sqrt(iv.sqrt(I(F(1,3))))
    peak=2*xstar/(1-xstar*xstar)**2*iv.exp(-1/(1-xstar*xstar))
    kappa2=3/iv.cos(2*I(F(1,8)))**2-1
    Q1=upper(4*peak/I(width)+kappa2*Ih)
    calibration=upper(Q1/lower(Dpsi))
    assert F(pair(calibration)[1])<5000
    c0=iv.cos(2*I(center))
    qcenter=iv.exp(-1)*(-2/I(width)**2+1-3/c0**2)
    xpos=I(F(4,5));tpos=I(center)+I(width)*xpos
    qpositive=iv.exp(-1/(1-xpos*xpos))*(
        (6*xpos**4-2)/(I(width)**2*(1-xpos*xpos)**4)
        +1-3/iv.cos(2*tpos)**2)
    assert F(pair(qcenter)[1])<0 and F(pair(qpositive)[0])>0
    flux_abs=4*iv.pi*radial_flux/(3*c0)
    assert F(pair(flux_abs)[0])>0
    # Retarded test of q=psi (a positive geometry window) has a nonzero past endpoint.
    past_endpoint=I(0)
    for j in range(N):
        x0=F(2*j,N)-1;x1=F(2*(j+1),N)-1
        t=box(center+width*x0,center+width*x1)
        past_endpoint+=I(width*(x1-x0))*bump_range(x0,x1)*iv.sin(2*t)/(2*iv.sqrt(iv.cos(2*t)))
    assert F(pair(past_endpoint)[0])>0
    assert F(pair(iv.sin(I(F(1,4)))*iv.sqrt(3))[1])<1
    return {
        "cells_per_integral":N,
        "method":"outward interval Riemann bounds with exact bump extrema",
        "psi_support":["1/16","1/8"],"geometry_interval":["0","3/16"],
        "psi_integral":pair(Ih),"positive_amplitude_transfer_Dpsi":pair(Dpsi),
        "q_L1_upper":pair(Q1),"normalized_readout_L1_upper":pair(calibration),
        "uniform_beta_calibration_error_gain_certified_below":5000,
        "q_at_center_negative":pair(qcenter),"q_at_eta_19_over_160_positive":pair(qpositive),
        "positive_window_retarded_test_at_eta0":pair(past_endpoint),
        "KG_local_flux_negative_control_abs":pair(flux_abs),
        "KG_local_flux_is_strictly_negative_at_center":True,
        "local_density_test_causal_support":"chi+eta<=1/4<arcsin(1/sqrt(3))",
    }

def calculate():
    if not __debug__:raise RuntimeError("Proof assertions cannot be optimized away")
    before={HERE/"check.py":sha(HERE/"check.py")}
    for rel in INPUTS:
        p=REPO/rel
        expected=subprocess.check_output(["git","show",BASE+":"+rel],cwd=REPO)
        assert p.read_bytes()==expected,"Archived input changed: "+rel
        before[p]=sha(p)
    old=json.loads((REPO/(PREFIX+"verification.json")).read_text())
    assert old["status"]=="PASS"
    for rel in INPUTS[:-1]:
        assert old["current_source_manifest"][rel]==before[REPO/rel]
    noise=json.loads((REPO/(PREFIX+"noise/result.json")).read_text())
    assert noise["local_test_integrals"]["time_support"]==["1/16","1/8"]
    assert noise["local_test_integrals"]["spatial_radial_support"]==["0","1/8"]
    n=numerical()
    result={
        "schema":"ueot-smooth-geometry-noise-readouts/1",
        "status":"ADJOINT_DOMAIN_AND_LOCAL_CONSTRAINT_INTERFACE_CERTIFIED",
        "reviewed_base":BASE,"symbolic":symbolic(),"numerical":n,
        "same_local_ADM_density_test":noise["local_test_integrals"]["test_F"],
        "ADM_noise_interface":{
            "units":"4*pi*G=1, hence Einstein G_ab=2*T_ab",
            "classical_background_on_shell":True,
            "classical_scalar_is_positive_amplitude_base_not_mixture_mean":True,
            "classical_forced_model":"delta(G_ab-2*T_classical_ab)=2*xi_ab",
            "observable":"O_F=int F_lambda*delta_C dvol_lambda; delta_C=xi_nn",
            "covariance":"Cov(O_F,O_H)=N(F_lambda*u_lambda*u_lambda,H_lambda*u_lambda*u_lambda)",
            "new_sign_source_variance":"lambda^-8*C0+d_lambda^2*lambda^-6*C1",
            "normalization":"centered variance may be divided by (lambda^-2*D)^2, not by the zero mean of O_F",
            "gauge_invariance_condition":"covariant coupled metric-scalar operator on its classical on-shell background; normal-variation terms multiply E_background=0",
            "full_quantum_response":"full EL requires delta_C-delta<RSET_nn>=xi_nn, including local renormalization terms",
            "unsubtracted_curvature_noise_bound_from_C0_alone":False,
            "same_F_full_C0_numerics_delegated_to_sibling_noise_certificate":True,
        },
        "scope":{
            "ODE_filter_applies_to_declared_archived_L":True,
            "ODE_time_readout_fixed_conformal_identification":True,
            "ODE_trace_noise_certified_by_density_C0_alone":False,
            "ODE_filter_automatically_applies_to_changed_nonlocal_quantum_response":False,
            "localized_spatial_window_justifies_homogeneous_stochastic_metric":False,
            "generic_intrinsic_geometry_noise_set_to_zero":False,
            "initial_noise_cross_correlations_assumed_zero":False,
            "linear_map_covariance_identity_establishes_smallness_of_old_order_one_noise":False,
            "full_Einstein_Langevin_solution_constructed":False,
            "nonlinear_SCE_solution_constructed":False,
            "noise_constants_transported_to_finitely_corrected_geometry":False,
            "actual_geometry_instrument_or_hardware_data":False,
            "Core_unique_physical_selection":False,
        },
        "new_mode_integrations":0,
        "input_sha256":{str(p.relative_to(REPO)):h for p,h in sorted(before.items())},
    }
    for p,h in before.items():assert sha(p)==h,"Input changed during execution"
    return result

if __name__=="__main__":
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--write",action="store_true")
    ap.add_argument("--check",action="store_true")
    args=ap.parse_args()
    result=calculate()
    rendered=json.dumps(result,ensure_ascii=False,indent=2,sort_keys=True)+"\n"
    target=HERE/"result.json"
    if args.write:target.write_text(rendered)
    if args.check:assert target.read_text()==rendered,"Geometry readout receipt mismatch"
    n=result["numerical"]
    print("Dpsi interval:",[float(F(x)) for x in n["positive_amplitude_transfer_Dpsi"]])
    print("Normalized readout calibration gain <=",float(F(n["normalized_readout_L1_upper"][1])))
    print("Local KG flux magnitude interval:",[float(F(x)) for x in n["KG_local_flux_negative_control_abs"]])
    print("PASS: smooth adjoint domain, initial-mode cancellation, local flux and conditional ADM interface.")
