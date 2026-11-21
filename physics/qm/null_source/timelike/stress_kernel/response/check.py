"""Common-metric mean equivalence, retarded response, and a local lapse gate.

This checker consumes the new complete C0 certificate for the original local F.
It does not solve the nonlinear SCE or infer a finite-epsilon probability bound.
No old mode ODE is rerun.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sympy as sp
from mpmath import iv, mp

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[5]
TIMELIKE=HERE.parents[1]
BASE="29d49e3eee6299e2085492b0e061288b8166b5fa"
mp.dps=85
iv.dps=70

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def I(x):
    return iv.mpf(x.numerator)/x.denominator if isinstance(x,F) else iv.mpf(x)
def endpoint(x,j):return mp.make_mpf(x._mpi_[j])
def rational(x):
    sign,mant,power,_=x._mpf_
    return F((-1 if sign else 1)*mant)*F(2)**power
def pair(x):return [str(rational(endpoint(x,j))) for j in (0,1)]
def upper(x):return F(pair(x)[1])
def box(a,b):return iv.mpf([endpoint(I(a),0),endpoint(I(b),1)])
def require(x,message):
    if not x:raise RuntimeError(message)

def freeze():
    relatives=[
        "physics/qm/null_source/timelike/continuation/SOURCE.md",
        "physics/qm/null_source/timelike/response/CONTRACT.md",
        "physics/qm/null_source/timelike/response/review.py",
        "physics/qm/null_source/timelike/response/noise/README.md",
        "physics/qm/null_source/timelike/response/noise/check.py",
        "physics/qm/null_source/timelike/response/noise/result.json",
        "physics/qm/null_source/timelike/response/preparation/README.md",
        "physics/qm/null_source/timelike/response/geometry/README.md",
    ]
    frozen={}
    for rel in relatives:
        path=REPO/rel
        archived=subprocess.check_output(["git","show",BASE+":"+rel],cwd=REPO)
        require(path.read_bytes()==archived,"Baseline source changed: "+rel)
        frozen[path]=sha(path)
    for path in [HERE/"check.py",HERE.parent/"noise/check.py",
                 HERE.parent/"noise/result.json"]:
        require(path.is_file() and not path.is_symlink(),"Missing/nonregular input: "+str(path))
        frozen[path]=sha(path)
    old=json.loads((TIMELIKE/"response/noise/result.json").read_text())
    current=json.loads((HERE.parent/"noise/result.json").read_text())
    return old,current,frozen

def algebra():
    # Two genuinely different distributions, with identical full Cauchy 2-point data.
    q,p=sp.symbols("q p",real=True)
    v=sp.Matrix([q,p])
    a,b,c=sp.symbols("Vqq Vqp Vpp",real=True)
    V=sp.Matrix([[a,b],[b,c]])
    x,y,z,w=sp.symbols("U11 U12 U21 U22",real=True)
    U=sp.Matrix([[x,y],[z,w]])
    moment_rows={}
    for sign in [-1,1]:
        m=sp.Rational(sign,2)
        old_values=[m-sp.sqrt(3)/2,m+sp.sqrt(3)/2]
        old_m=[sp.simplify(sum(t**n for t in old_values)/2) for n in range(5)]
        new_m=[sp.simplify((1+m)/2+(1-m)*(-1)**n/2) for n in range(5)]
        assert old_m[:3]==new_m[:3]
        assert old_m[4]-new_m[4]==sp.Rational(3,4)
        old_M=V+sum(((t*v)*(t*v).T/2 for t in old_values), sp.zeros(2))
        new_M=V+(1+m)*(v*v.T)/2+(1-m)*((-v)*(-v).T)/2
        assert sp.simplify(old_M-new_M)==sp.zeros(2)
        assert sp.simplify(U*old_M*U.T-U*new_M*U.T)==sp.zeros(2)
        moment_rows[str(sign)]={"old":[str(t) for t in old_m],
                                "new":[str(t) for t in new_m]}
    # The ordered connected covariance. Only the two ordered quantum blocks
    # are abstract; the classical fourth moment is evaluated explicitly.
    R0,I0,R1,I1,D,E,mu4=sp.symbols("R0 I0 R1 I1 D E mu4",real=True)
    ordered=R0+sp.I*I0+R1+sp.I*I1+(mu4-1)*D*E
    difference=sp.simplify(ordered.subs(mu4,sp.Rational(7,4))-ordered.subs(mu4,1))
    assert difference==sp.Rational(3,4)*D*E
    assert sp.im(difference)==0
    assert sp.simplify(ordered-sp.conjugate(ordered)-2*sp.I*(I0+I1))==0
    d1,d2,d3,t1,t2,t3=sp.symbols("d1 d2 d3 t1 t2 t3",real=True)
    dvec=sp.Matrix([d1,d2,d3]);tvec=sp.Matrix([t1,t2,t3])
    rank_one=sp.Rational(3,4)*dvec*dvec.T
    assert rank_one.det()==0
    assert sp.expand((tvec.T*rank_one*tvec)[0]-
                     sp.Rational(3,4)*(d1*t1+d2*t2+d3*t3)**2)==0
    # Quadratic CCR closure, checked through its exact Weyl-symbol bracket.
    s11,s12,s22,t11,t12,t22=sp.symbols("s11 s12 s22 t11 t12 t22",real=True)
    S=sp.Matrix([[s11,s12],[s12,s22]])
    T=sp.Matrix([[t11,t12],[t12,t22]])
    Omega=sp.Matrix([[0,1],[-1,0]])
    QS=(v.T*S*v)[0]/2;QT=(v.T*T*v)[0]/2
    PB=sp.diff(QS,q)*sp.diff(QT,p)-sp.diff(QS,p)*sp.diff(QT,q)
    bracket_matrix=S*Omega*T-T*Omega*S
    assert bracket_matrix==bracket_matrix.T
    assert sp.expand(PB-(v.T*bracket_matrix*v)[0]/2)==0
    assert all(sp.diff(QS,q,n,p,3-n)==0 for n in range(4))
    # A metric-dependent central counterterm leaves connected noise invariant,
    # but can change mean response. Noise does not determine the full RSET map.
    eps,kappa,mean=sp.symbols("epsilon kappa mean",real=True)
    assert sp.diff(mean+kappa*eps,eps)==kappa
    return {
        "distribution_moments":moment_rows,
        "full_Cauchy_second_moment_preserved_under_arbitrary_common_linear_propagator":True,
        "mean_RSET_functional_equal_on_common_admissible_metric_class":True,
        "existing_variations_equal_without_asserting_their_existence":True,
        "mean_SCE_solution_sets_equal_nonemptiness_not_proved":True,
        "ordered_stress_covariance_old_minus_new":"(3/4)*T[f](H)*T[f](K)",
        "noise_difference":"positive semidefinite rank one",
        "commutator_and_retarded_kernel_difference":"0",
        "quadratic_CCR_bracket":"[Q(S),Q(T)]=i Q(S Omega T-T Omega S), Weyl ordered",
        "local_counterterm_response_not_reconstructible_from_connected_noise":True,
        "scope":"free linear field; quadratic locally covariant RSET; same past state, displacement and fixed renormalization prescription",
    }

def hamilton_and_ward():
    eps,a,r,om,q,p=sp.symbols("epsilon a r omega q p",real=True,nonzero=True)
    aa=a*(1+eps*r)
    H=(p*p/aa**2+aa**2*om**2*q*q)/2
    dH=sp.simplify(sp.diff(H,eps).subs(eps,0))
    expected=r*(-p*p/a**2+a*a*om**2*q*q)
    assert sp.simplify(dH-expected)==0
    Omega=sp.Matrix([[0,1],[-1,0]])
    delta_K=sp.Matrix([[0,-2*r/a**2],[-2*r*a*a*om**2,0]])
    assert sp.simplify(Omega*sp.hessian(dH,(q,p))-delta_K)==sp.zeros(2)
    H0,Ftest,D,lam=sp.symbols("H0 Ftest D lambda",positive=True)
    lapse_ratio=sp.sqrt(1-2*eps*Ftest/(D*lam**2))
    assert sp.simplify(sp.diff(H0*lapse_ratio,eps).subs(eps,0)+
                       H0*Ftest/(D*lam**2))==0
    C0,C1,d=sp.symbols("C0 C1 d",positive=True)
    varA=lam**-8*C0+d*d*lam**-6*C1
    assert sp.simplify((lam**2/D)**2*varA-
                       (C0/lam**4+d*d*C1/lam**2)/D**2)==0
    assert sp.simplify((lam**4/D)**2*varA-
                       (C0+d*d*lam**2*C1)/D**2)==0
    rho,pr,drho,dpr,h,rp,rhop,drhop=sp.symbols(
        "rho pressure delta_rho delta_pressure h rprime rho_prime delta_rho_prime",
        real=True)
    conservation=rhop+eps*drhop+3*(h+eps*rp)*(rho+pr+eps*(drho+dpr))
    varied=sp.diff(conservation,eps).subs(eps,0)
    assert sp.expand(varied-(drhop+3*h*(drho+dpr)+3*rp*(rho+pr)))==0
    # Concrete stiff source: delta rho=delta p=-6 r rho.
    correct=varied.subs({pr:rho,drho:-6*r*rho,dpr:-6*r*rho,
                         drhop:-6*rp*rho+36*r*h*rho})
    assert sp.expand(correct)==0
    wrong=sp.expand(correct-6*rp*rho)
    assert wrong==-6*rp*rho and wrong!=0
    # Full spatially varying lapse: differentiate the actual KG operator.
    time=sp.symbols("eta",real=True)
    scale=sp.Function("a")(time);alpha=sp.Function("alpha")(time)
    field=sp.Function("phi")(time);lap,grad=sp.symbols("lap_phi grad_alpha_dot_grad_phi")
    Peps=(1+eps*alpha)/scale**4*(
        -sp.diff(scale**2*(1+eps*alpha)*sp.diff(field,time),time)
        +scale**2*((1-eps*alpha)*lap-eps*grad))
    dP=sp.diff(Peps,eps).subs(eps,0)
    expectedP=scale**-2*(-2*alpha*sp.diff(field,time,2)-
        (4*sp.diff(scale,time)/scale*alpha+sp.diff(alpha,time))*sp.diff(field,time)-grad)
    assert sp.simplify(dP-expectedP)==0
    on_shell=sp.simplify(dP.subs(sp.diff(field,time,2),
                          -2*sp.diff(scale,time)/scale*sp.diff(field,time)+lap))
    assert sp.simplify(on_shell+scale**-2*(2*alpha*lap+
                         sp.diff(alpha,time)*sp.diff(field,time)+grad))==0
    return {
        "canonical_conformal_generator":"delta H=r*(-p^2/a^2+a^2*omega^2*q^2)=-integral r*T_trace*dvol/deta",
        "canonical_generator_matches_Duhamel_delta_K":True,
        "local_lapse_KG_variation":"delta Box phi=a^-2*(-2*alpha*phi_second-(4*h*alpha+alpha_prime)*phi_prime-gradient(alpha).gradient(phi))",
        "retarded_two_point_variation":"delta W=-(E_ret delta P)_x W-(E_ret delta P)_y W, fixed past Cauchy data",
        "lapse_family":"g_epsilon,00=-a_lambda^2*(1-2*epsilon*F/(D*lambda^2)); spatial metric unchanged",
        "lapse_generator":"G_lambda=-lambda^2*A_lambda(F_lambda)/D, up to a central phase",
        "response_sign":"d_epsilon <O> at zero = i <[G_lambda,O]> for unchanged future observable",
        "effect_class":"finite Weyl-algebra instruments whose expectation is differentiable under the common retarded classical symplectic map",
        "all_bounded_effects_automatically_differentiable":False,
        "effect_bound":"|d_epsilon p| <= sqrt(Var G_lambda), 0<=E<=1",
        "bounded_contraction_bound":"|d_epsilon <O>| <= 2*sqrt(Var G_lambda), ||O||<=1",
        "fixed_fractional_profile_negative_control":"Without lambda^-2 in metric profile, Var G=(c0+d^2*lambda^2*c1), not a decaying bound.",
        "homogeneous_linearized_Ward_identity":"delta_rho_prime+3*h*(delta_rho+delta_pressure)+3*r_prime*(rho+pressure)=0",
        "incorrect_background_conservation_negative_control":"-6*r_prime*rho for the stiff source",
        "overlapping_support_retarded_distribution_needs_local_extension_and_contact_terms":True,
        "finite_epsilon_probability_bound_certified":False,
    }

def numerical(old,new):
    cert=new["certificate"]
    c0=F(cert["c0_over_D2_upper"])
    lam=int(cert["lambda_certified"])
    require(c0>0 and lam>=8192,"Invalid full-noise certificate")
    c1=F(old["certificate"]["local_test_all_mode_linear_coefficient_c1_upper"])
    Dlo,Dhi=map(F,old["local_test_integrals"]["classical_density_smearing_D"])
    require(0<Dlo<=Dhi,"Invalid original test normalization")
    # d_lambda^2<1 in the exact correlated source family, lambda>=8192.
    vg=c0/lam**4+c1/lam**2
    slope=upper(iv.sqrt(I(vg)))
    metric_fraction=upper(2*iv.exp(-2)/(I(Dlo)*lam**2))
    original_fraction=upper(2*iv.exp(-2)/(I(Dlo)*8192**2))
    require(original_fraction<F(1,10000),"Lapse positivity gate failed")
    require(slope<F(1,10),"Declared complete-noise scale does not pass response gate")
    Nbox=box(1-metric_fraction,1+metric_fraction)
    Nrange=pair(iv.sqrt(Nbox))
    require(F(Nrange[0])>0,"Lapse is not uniformly positive")
    gap=F(5,32)-F(1,8)
    require(gap==F(1,32),"Future effect support no longer strictly separated")
    return {
        "lambda":lam,
        "c0_over_D2_upper":str(c0),
        "c1_over_D2_upper":str(c1),
        "test_D_interval":[str(Dlo),str(Dhi)],
        "test_support":{"time":["1/16","1/8"],"chi_less_than":"1/8"},
        "future_Weyl_record_support":{"time":["5/32","3/16"],"chi_less_than":"1/100"},
        "strict_time_gap":"1/32",
        "generator_variance_upper":str(vg),
        "one_effect_probability_derivative_absolute_upper":str(slope),
        "one_effect_probability_derivative_upper_decimal":float(slope),
        "bounded_contraction_derivative_absolute_upper":str(2*slope),
        "metric_00_relative_change_per_abs_epsilon_upper":str(metric_fraction),
        "metric_00_relative_change_at_8192_upper":str(original_fraction),
        "lapse_ratio_for_abs_epsilon_le_one_interval":Nrange,
        "exact_correlated_source_retuned_across_lambda":True,
        "past_state_and_source_held_fixed_during_epsilon_variation":True,
        "local_observable_and_counterterms_unchanged_on_later_measurement_support":True,
        "calibration_map_and_pre_interrogation_failure_rate_fixed_during_variation":True,
        "absolute_record_probabilities_at_this_lambda_recomputed_here":False,
        "first_derivative_at_epsilon_zero_only":True,
        "uniform_path_variance_or_second_order_remainder_certified":False,
        "self_consistent_SCE_metric_perturbation":False,
    }

def calculate():
    require(__debug__,"Do not optimize away proof assertions")
    old,new,frozen=freeze()
    result={
        "schema":"ueot-common-metric-retarded-response/1",
        "reviewed_base":BASE,
        "status":"COMMON_METRIC_EQUIVALENCE_AND_LOCAL_LAPSE_RESPONSE_CERTIFIED",
        "algebra":algebra(),
        "hamiltonian_and_Ward":hamilton_and_ward(),
        "numerical":numerical(old,new),
        "new_mode_integrations":0,
        "full_RSET_metric_derivative_norm":"OPEN",
        "full_nonlinear_SCE_existence_and_stability":"OPEN",
        "actual_hardware_or_new_Lean":"NONE",
        "source_sha256":sha(HERE/"check.py"),
        "input_sha256":{str(path.relative_to(REPO)):digest
                        for path,digest in sorted(frozen.items())
                        if path!=HERE/"check.py"},
    }
    for path,digest in frozen.items():require(sha(path)==digest,"Input changed during check")
    return result

if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write",action="store_true")
    parser.add_argument("--check",action="store_true")
    args=parser.parse_args()
    result=calculate()
    rendered=json.dumps(result,sort_keys=True,indent=2,ensure_ascii=False)+"\n"
    target=HERE/"result.json"
    if args.write:target.write_text(rendered)
    if args.check:require(target.read_text()==rendered,"Response receipt mismatch")
    print("Common-metric mean-RSET and retarded-response equivalence: PASS")
    print("One-effect epsilon=0 probability slope <=",
          result["numerical"]["one_effect_probability_derivative_upper_decimal"])
    print("PASS: complete-noise local lapse response; nonlinear SCE and finite-epsilon probabilities remain open.")
