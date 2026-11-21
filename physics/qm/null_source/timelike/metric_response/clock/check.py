"""Exact nonlinear stiff-scalar geometries read with a common proper clock.

This is a separately declared classical branch-dependent geometry benchmark.
It does not transport fixed-background quantum/Weyl certificates to that model.
No field mode or geometry ODE is numerically integrated.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sympy as sp
from mpmath import iv,mp

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[5]
BASE="719babd3386b9d9274d5c91dd0b8ad5e71688049"
PREFIX="physics/qm/null_source/timelike/"
INPUTS=[PREFIX+"stress_kernel/geometry/README.md",
        PREFIX+"stress_kernel/geometry/result.json",
        PREFIX+"stress_kernel/CONTRACT.md",
        PREFIX+"stress_kernel/verification.json",
        PREFIX+"response/preparation/result.json"]
mp.dps=90
iv.dps=75

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def I(x):return iv.mpf(x.numerator)/x.denominator if isinstance(x,F) else iv.mpf(x)
def endpoint(x,j):return mp.make_mpf(x._mpi_[j])
def rat(x):
    sign,mant,power,_=x._mpf_
    return F((-1 if sign else 1)*mant)*F(2)**power
def pair(x):return [str(rat(endpoint(x,j))) for j in (0,1)]
def lo(x):return F(pair(x)[0])
def hi(x):return F(pair(x)[1])
def box(a,b):return iv.mpf([endpoint(I(a),0),endpoint(I(b),1)])
def absupper(x):return max(abs(lo(x)),abs(hi(x)))
def simp(x):return sp.trigsimp(sp.simplify(x))

def symbolic():
    eta=sp.symbols("eta",real=True)
    M=sp.symbols("M",positive=True)
    ell=(M/3)**sp.Rational(1,4)
    c=sp.cos(2*eta)
    a=ell*sp.sqrt(c)
    ap=sp.diff(a,eta)
    app=sp.diff(a,eta,2)
    P=sp.sqrt(M)
    phip=P/a**2
    assert simp(ap**2+a**2-M/(3*a**2))==0
    assert simp(app+a+M/(3*a**3))==0
    assert simp(sp.diff(a**2*phip,eta))==0
    adot=ap/a
    addot=sp.diff(adot,eta)/a
    assert simp(addot+2*M/(3*a**5))==0
    Ruu=-3*addot/a
    assert simp(Ruu-2*(phip/a)**2)==0
    y=sp.Rational(3,2)*sp.log(c)
    ydot=sp.diff(y,eta)/a
    yddot=sp.diff(ydot,eta)/a
    assert simp(-yddot-Ruu-ydot**2/3)==0
    assert simp(sp.diff(phip,M))==0
    assert simp((a/a.subs(eta,0))**3-c**sp.Rational(3,2))==0
    f=sp.sqrt(c)
    assert simp(sp.diff(f,eta,2)+f*(1+1/c**2))==0
    prim=sp.Function("I")(eta)
    aa=prim*sp.tan(2*eta)/f
    aa_prime=simp(sp.diff(aa,eta).subs(sp.diff(prim,eta),f))
    aa_expected=sp.tan(2*eta)+(prim/f)*(2/sp.cos(2*eta)**2+sp.tan(2*eta)**2)
    assert simp(aa_prime-aa_expected)==0
    z=sp.symbols("z",positive=True)
    assert sp.diff(z**sp.Rational(1,4),z,2)==-3/(16*z**sp.Rational(7,4))
    moments={}
    for sign in [-1,1]:
        old=[sp.Rational(sign,2)-sp.sqrt(3)/2,sp.Rational(sign,2)+sp.sqrt(3)/2]
        oldmom=[simp(sum(q**n for q in old)/2) for n in [1,2,4]]
        newmom=[simp((2+sign)/sp.Integer(4)+(2-sign)*(-1)**n/sp.Integer(4))
                for n in [1,2,4]]
        assert oldmom[:2]==newmom[:2]
        assert oldmom[1]==newmom[1]==1
        assert oldmom[2]-newmom[2]==sp.Rational(3,4)
        assert set([simp(q*q) for q in old])=={1-sp.sqrt(3)/2,1+sp.sqrt(3)/2}
        moments[str(sign)]={"old":[str(x) for x in oldmom],"new":[str(x) for x in newmom]}
    rr,gg,bb,xx,cc=sp.symbols("r gamma beta x c",positive=True)
    observed=(gg*xx+bb)/rr
    assert simp(observed.subs({rr:cc*rr,gg:cc*gg,bb:cc*bb},simultaneous=True)-observed)==0
    assert simp(observed.subs({gg:rr,bb:0})-xx)==0
    kappa,tau,scale,h=sp.symbols("kappa tau a h",real=True)
    delta_eta=-kappa*tau/scale
    assert simp(3*h*delta_eta+3*kappa*h*tau/scale)==0
    return {
      "exact_classical_Friedmann_constraint":"a_prime^2+a^2=M/(3*a^2)",
      "exact_classical_acceleration":"a_second+a+M/(3*a^3)=0",
      "exact_classical_KG_charge":"a^2*phi_prime=P, P^2=M",
      "solution":"a_M=(M/3)^(1/4)*sqrt(cos(2*eta)), 0<=eta<pi/4",
      "Ricci_and_Raychaudhuri":"R_uu=2*M/a^6; -y_proper_second=R_uu+y_proper_prime^2/3",
      "Jacobi_volume":"V(eta)/V(0)=cos(2*eta)^(3/2); initial expansion=0, no focus before pi/4",
      "conformal_field_trajectory":"phi-phi_0=sgn(P)*sqrt(3)/2*atanh(sin(2*eta)); independent of abs(P)",
      "full_candidate_moments":moments,
      "amplitude_to_geometry":"M_Y=Mbar*Y^2; ell=(Mbar/3)^(1/4); r=sqrt(abs(Y)); a_Y=ell*r*sqrt(cos(2*eta))",
      "proper_clock":"I(eta)=integral_0^eta sqrt(cos(2*s)) ds; t=tau/ell=r*I(eta)",
      "point_readout":"y_r(t)=3/2*log(cos(2*I_inverse(t/r)))",
      "strict_monotonicity":"d y / d log(r)=3*I(eta)*tan(2*eta)/sqrt(cos(2*eta))>0",
      "point_inverse":"M=3*(tau/I(arccos(exp(2*y/3))/2))^4, y<0",
      "proper_clock_log_volume_strictly_concave_in_M":"y_MM=-(3/(4*M^2))*(Afun+I*Afun_prime/(4*f))<0; Afun=I*tan(2*eta)/f, Afun_prime>0",
      "finite_positive_window_monotone_in_M":True,
      "clock_nuisance_negative_control":"observed curve depends only on gamma/r and beta/r; common scaling (r,gamma,beta) leaves it fixed",
      "branch_rescaled_clock_negative_control":"gamma_r=r,beta=0 makes every branch have the same curve",
      "one_unknown_common_gain_proves_mixture_law_indistinguishability":False,
      "existing_linear_proper_clock_limit":"delta_y at fixed tau=-3*kappa*h*tau/a",
      "fixed_Mbar_same_mean_charge_does_not_commute_with_solving_geometry":"E[M_Y]=Mbar, but E[a_Y]/a_Mbar=E[(Y^2)^(1/4)]<1 for the old nonconstant law",
      "integral_midpoint_second_derivative":"f_second=-f*(1+sec(2*eta)^2); bound 1+sec(3/8)^2",
    }

T=F(3,16)
N=256
FMIN=iv.sqrt(iv.cos(2*I(T)))
SECOND=1+1/iv.cos(2*I(T))**2
integral_calls=0

def primitive(z):
    """Outward midpoint quadrature with an analytic second-derivative remainder."""
    global integral_calls
    assert F(0)<=z<=T
    integral_calls+=1
    if z==0:return I(0)
    step=z/N
    total=I(0)
    for j in range(N):
        x=I(step*F(2*j+1,2))
        total+=iv.sqrt(iv.cos(2*x))
    total*=I(step)
    error=hi(I(z**3)*SECOND/(24*N*N))
    return total+box(-error,error)

def inverse(target):
    """Bracket the inverse with directed quadrature and a positive slope floor."""
    assert 0<lo(target)<=hi(target)<lo(primitive(T))
    left=F(0);right=T
    for _ in range(80):
        midpoint=(left+right)/2
        value=primitive(midpoint)
        if hi(value)<lo(target):left=midpoint
        elif lo(value)>hi(target):right=midpoint
        else:
            # value and target overlap; I' >= FMIN bounds the remaining location error.
            dleft=hi(I(hi(value)-lo(target))/FMIN)
            dright=hi(I(hi(target)-lo(value))/FMIN)
            left=max(left,midpoint-dleft)
            right=min(right,midpoint+dright)
            assert 0<left<=right<T
            return box(left,right)
    raise RuntimeError("Inverse certificate failed to terminate")

def numerical():
    global integral_calls
    integral_calls=0
    nominal_lo=F(95,1024);nominal_hi=F(97,1024)
    gain_lo=F(199,200);gain_hi=F(201,200);origin=F(1,10000)
    tlo=gain_lo*nominal_lo-origin
    thi=gain_hi*nominal_hi+origin
    times=box(tlo,thi)
    mags={"old_low":(iv.sqrt(3)-1)/2,"new":I(1),"old_high":(iv.sqrt(3)+1)/2}
    ratios={name:iv.sqrt(v) for name,v in mags.items()}
    assert hi(times/ratios["old_low"])<lo(primitive(T))
    read_error=F(1,1000)
    volume_relative_error=F(1,4000)
    residual_read_error=F(1,2500)
    log_error=iv.log((1+I(volume_relative_error))/(1-I(volume_relative_error)))+I(residual_read_error)
    assert hi(log_error)<read_error
    branches={}
    for name,r in ratios.items():
        eta=inverse(times/r)
        yy=I(F(3,2))*iv.log(iv.cos(2*eta))
        measured=yy+box(-read_error,read_error)
        linear_r=1+(mags[name]**2-1)/4
        branches[name]={"abs_Y":pair(mags[name]),"r":pair(r),"eta_over_entire_gate":pair(eta),
             "log_volume_over_entire_gate":pair(yy),"measured_finite_gate_log_volume":pair(measured),
             "linearized_scale_ratio":pair(linear_r),"exact_minus_linear_scale_ratio":pair(r-linear_r)}
    accept_lo=F(-1,20);accept_hi=F(-23,1000)
    low=branches["old_low"];new=branches["new"];high=branches["old_high"]
    assert F(low["measured_finite_gate_log_volume"][1])<accept_lo
    assert accept_lo<F(new["measured_finite_gate_log_volume"][0])
    assert F(new["measured_finite_gate_log_volume"][1])<accept_hi
    assert accept_hi<F(high["measured_finite_gate_log_volume"][0])
    margins=[accept_lo-F(low["measured_finite_gate_log_volume"][1]),
             F(new["measured_finite_gate_log_volume"][0])-accept_lo,
             accept_hi-F(new["measured_finite_gate_log_volume"][1]),
             F(high["measured_finite_gate_log_volume"][0])-accept_hi]
    assert min(margins)>F(1,1000)
    eta_min=F(high["eta_over_entire_gate"][0])
    eta_max=F(low["eta_over_entire_gate"][1])
    min_derivative=lo(3*primitive(eta_min)*iv.tan(2*I(eta_min))/iv.sqrt(iv.cos(2*I(eta_min))))
    assert min_derivative>0
    inverse_log_M_condition_upper=hi(4/I(min_derivative))
    old_mean_scale=(ratios["old_low"]+ratios["old_high"])/2
    old_mean_gate=(box(*map(F,low["log_volume_over_entire_gate"]))+
                   box(*map(F,high["log_volume_over_entire_gate"])))/2
    new_gate=box(*map(F,new["log_volume_over_entire_gate"]))
    mean_difference=old_mean_gate-new_gate
    assert hi(old_mean_scale)<F(9,10)
    assert hi(mean_difference)<0
    assert F(low["exact_minus_linear_scale_ratio"][1])<F(-17,100)
    # Uniform causal patch margin for a local bundle inside chi<=1/8.
    patch_sum=I(F(1,8))+I(eta_max)
    assert hi(iv.sin(patch_sum)*iv.sqrt(3))<1
    # Explicit classical reference example, not a transported quantum background.
    lam=32768
    proper_times=I(lam)*iv.sqrt(3)*times
    return {
      "nominal_gate_t":[str(nominal_lo),str(nominal_hi)],
      "clock_gain":[str(gain_lo),str(gain_hi)],
      "clock_origin_error":str(origin),
      "actual_gate_t":[str(tlo),str(thi)],
      "clock_t_definition":"tau/ell; same independently calibrated ell and same proper-clock program for all candidates",
      "gate_weight":"any nonnegative normalized weight inside the nominal gate; timing map is monotone",
      "aggregate_log_volume_error":str(read_error),
      "two_volume_relative_error_each":str(volume_relative_error),
      "additional_bundle_sampling_transfer_log_error":str(residual_read_error),
      "combined_log_error_upper":str(hi(log_error)),
      "branches":branches,
      "new_acceptance_interval":[str(accept_lo),str(accept_hi)],
      "decision":"new if measured gate log-volume is in [-1/20,-23/1000]; old otherwise",
      "minimum_strict_classification_margin":str(min(margins)),
      "one_readout_classification_under_uniform_classical_contract":True,
      "real_hardware_trials":0,
      "geometry_blind_to_internal_source_sign":True,
      "all_branches_eta_below":"3/16",
      "all_branches_no_focal_point":True,
      "spatial_bundle_chi_upper":"1/8",
      "causal_inner_patch_condition":"chi+eta<arcsin(1/sqrt(3))",
      "causal_patch_sum_upper":str(hi(patch_sum)),
      "minimum_log_r_readout_derivative_lower":str(min_derivative),
      "inverse_log_M_condition_number_upper":str(inverse_log_M_condition_upper),
      "inverse_conditioning_requires_fixed_known_clock_and_window":True,
      "old_mean_scale_ratio_at_common_eta":pair(old_mean_scale),
      "old_mean_gate_log_volume":pair(old_mean_gate),
      "new_gate_log_volume":pair(new_gate),
      "old_minus_new_mean_gate_log_volume":pair(mean_difference),
      "old_linearized_mean_scale_ratio":"1",
      "classical_example":{"lambda":lam,"Mbar":"27*lambda^4","ell":"sqrt(3)*lambda",
                           "proper_clock_gate":pair(proper_times),
                           "identical_to_retuned_quantum_SCE_background":False},
      "quadrature":{"midpoint_cells":N,"analytic_remainder":"z^3*(1+sec(3/8)^2)/(24*N^2)",
                    "inverse_uses_positive_slope_floor":pair(FMIN),"primitive_calls":integral_calls},
    }

def calculate():
    assert __debug__,"Scientific assertions must remain enabled"
    frozen={HERE/"check.py":sha(HERE/"check.py")}
    for rel in INPUTS:
        path=REPO/rel
        expected=subprocess.check_output(["git","show",BASE+":"+rel],cwd=REPO)
        assert path.read_bytes()==expected,"Baseline source changed: "+rel
        frozen[path]=sha(path)
    parent=json.loads((REPO/(PREFIX+"stress_kernel/verification.json")).read_text())
    assert parent["status"]=="PASS"
    oldprep=json.loads((REPO/(PREFIX+"response/preparation/result.json")).read_text())
    assert oldprep["readout"]["calibration_contract"]["actual_calibration_performed"] is False
    result={"schema":"ueot-exact-classical-proper-clock/1",
        "reviewed_base":BASE,"status":"EXACT_CLASSICAL_PROPER_CLOCK_RECORDS_CERTIFIED",
        "symbolic":symbolic(),"numerical":numerical(),
        "scope":{"pure_classical_Einstein_scalar_branch_model":True,
                 "branch_geometry_rule_is_additional_physical_assumption":True,
                 "old_and_new_initial_absolute_scale_distributions_differ":True,
                 "same_initial_geometry_quantum_preparation_comparison":False,
                 "full_quantum_reference_or_stress_noise_included":False,
                 "fixed_background_Weyl_probabilities_transferred":False,
                 "mean_SCE_equality_theorem_contradicted":False,
                 "full_nonlinear_SCE_constructed":False,
                 "actual_clock_or_volume_device_calibrated":False,
                 "Core_unique_physical_selection":False},
        "new_mode_integrations":0,"new_geometry_ODE_integrations":0,
        "input_sha256":{str(p.relative_to(REPO)):h for p,h in sorted(frozen.items())}}
    for p,h in frozen.items():assert sha(p)==h,"Input changed during calculation"
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
    if args.check:assert target.read_text()==rendered,"Proper-clock receipt mismatch"
    n=result["numerical"]
    for name,b in n["branches"].items():
        print(name,"measured log-volume:",[float(F(x)) for x in b["measured_finite_gate_log_volume"]])
    print("Minimum decision margin:",float(F(n["minimum_strict_classification_margin"])))
    print("Old mean scale:",[float(F(x)) for x in n["old_mean_scale_ratio_at_common_eta"]])
    print("PASS: exact nonlinear classical geometry, common proper-clock gate and calibrated candidate separation.")
