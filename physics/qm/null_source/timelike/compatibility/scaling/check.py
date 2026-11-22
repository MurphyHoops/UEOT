#!/usr/bin/env python3
"""Massless minimal-field homothetic scaling and inherited dynamic bounds.

The earlier validated modes and UV certificate are immutable inputs. This
program performs no mode integration and does not call an external model.
"""
from fractions import Fraction as Q
from pathlib import Path
import argparse
import hashlib
import json
import sys
from mpmath import iv, mp
import sympy as sp

mp.dps=80
iv.dps=70
HERE=Path(__file__).resolve().parent
TIMELIKE=HERE.parents[1]
EVO=TIMELIKE/"evolution"
BASE="1a90c68b6178968e6b8239fc97a8b26200f8d59d"
INHERITED_RESULT_SHA="e68cf02018507c096aaa896c24e11fa32f52204fa08895f3aac615e114e2c218"
ETA_MAX=Q(3,16)
LAMBDAS=(1,15,100,1000,4097,8192,16384)

def I(x):
    if isinstance(x,Q):
        return iv.mpf(x.numerator)/iv.mpf(x.denominator)
    return iv.mpf(x)

def lo(x):return mp.make_mpf(x._mpi_[0])
def hi(x):return mp.make_mpf(x._mpi_[1])
def point(x):return I(x)
def box(a,b):return iv.mpf([lo(I(a)),hi(I(b))])
def top(x):return I(hi(x))
def abs_top(x):return I(max(abs(lo(x)),abs(hi(x))))
def sinh(x):return (iv.exp(x)-iv.exp(-x))/2
def cosh(x):return (iv.exp(x)+iv.exp(-x))/2

def rational(x):
    sign,man,exponent,_=x._mpf_
    return Q((-1 if sign else 1)*man)*Q(2)**exponent

def pair(x):return [str(rational(lo(x))),str(rational(hi(x)))]
def parse(x):return box(Q(x[0]),Q(x[1]))
def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()

LOADED_SOURCE_SHA=digest(HERE/"check.py")

def analytic(c):
    L=iv.log(3*c/4)+2*iv.euler
    den=8640*iv.pi**2*c**6
    return (((168+180*L)*c*c-110-135*L)/den,
            ((160+300*L)*c*c-240-405*L)/den)

def symbolic_checks():
    c,ell,lam,mu,alpha=sp.symbols("c ell lambda mu alpha",positive=True)
    L=sp.symbols("L",real=True)
    Hρ=6*(4*c*c-3)/c**6
    Hp=(40*c*c-54)/c**6
    R=((168+180*L)*c*c-110-135*L)/(8640*sp.pi**2*c**6)
    P=((160+300*L)*c*c-240-405*L)/(8640*sp.pi**2*c**6)
    C=1/(576*sp.pi**2)
    assert sp.simplify(R.subs(L,L+2*ell)-R-C*Hρ*ell)==0
    assert sp.simplify(P.subs(L,L+2*ell)-P-C*Hp*ell)==0
    assert Hρ.subs(c,1)==6 and Hp.subs(c,1)==-14
    # Changing subtraction scale while keeping the total tensor fixed requires
    # alpha(mu*exp(s))=alpha(mu)-C*s, with alpha on the source side.
    s=sp.symbols("s",real=True)
    for T,H in [(R,Hρ),(P,Hp)]:
        assert sp.simplify(T.subs(L,L+2*s)+(alpha-C*s)*H-T-alpha*H)==0
    a=sp.symbols("a",positive=True)
    assert sp.simplify((3*lam**2/2)/(4*sp.pi**2*(lam*a)**6)
                       -lam**-4*3/(8*sp.pi**2*a**6))==0
    assert sp.simplify((sp.Rational(1,6)/lam**2)*(3*lam**2/2)-sp.Rational(1,4))==0
    assert sp.simplify(sp.diff(Hρ,c)-12*(9-8*c*c)/c**7)==0
    assert sp.simplify(sp.diff(Hp,c)-(324-160*c*c)/c**7)==0
    # The two stable vacuum identities use k^2 degeneracy.
    k,w,h,E3,P1,P3=sp.symbols("k w h E3 P1 P3",positive=True)
    rs=k*k*w-k**3+k/2+1/(8*k)
    stable=-(w+3*k)/(8*k*(k+w)**3)
    numerator=sp.together(rs-stable).as_numer_denom()[0]
    assert sp.rem(sp.Poly(numerator,w),sp.Poly(w*w-k*k+1,w)).is_zero
    E1=(h*h-1)/2
    assert sp.expand(k*k*(w-k-E1/k-E3/k**3)
                     -(rs-h*h*k/2-(E3+sp.Rational(1,8))/k))==0
    assert sp.expand(k*k*(w/3-k/3-P1/k-P3/k**3)
                     -(rs/3-(P1+sp.Rational(1,6))*k-(P3+sp.Rational(1,24))/k))==0
    # On a_lambda, homogeneous classical density is M2/(54 lambda^6 c^3).
    powers={"fixed_M2":0,"whole_state_transport":2,"classical_homothetic":4}
    for name,power in powers.items():
        ratio=sp.simplify((27*lam**power/(54*lam**6*c**3))
                          /(sp.Rational(1,2)/(lam**2*c**3)))
        assert ratio==lam**(power-4),(name,ratio)
    return {"AE_log_coefficient":"H1/(576*pi^2)",
            "H1_initial_energy":"6","H1_initial_pressure":"-14",
            "finite_alpha_convention":"source_side_plus_alpha_H1",
            "alpha_running":"alpha(mu*exp(s))=alpha(mu)-s/(576*pi^2)",
            "classical_M2_powers":powers,
            "symbolic_checks":"PASS"}

def inherited_inputs():
    if not __debug__:raise RuntimeError("Proof assertions required; do not use -O.")
    assert digest(HERE/"check.py")==LOADED_SOURCE_SHA,"source changed after import"
    stress_path=EVO/"stress/result.json"
    assert digest(stress_path)==INHERITED_RESULT_SHA,"inherited absolute-stress receipt changed"
    stress=json.loads(stress_path.read_text())
    paths=[stress_path,HERE/"check.py",
           TIMELIKE/"continuation/SOURCE.md",TIMELIKE.parent/"FINITE_WINDOW.md"]
    for rel,sha in stress["input_sha256"].items():
        path=EVO/rel
        assert digest(path)==sha,("inherited proof input changed",rel)
        paths.append(path)
    frozen={str(path.resolve()):digest(path) for path in paths}
    prop=json.loads((EVO/"propagation/result.json").read_text())
    extra=json.loads((EVO/"propagation/extra_eta0_256.json").read_text())
    uv=json.loads((EVO/"stress/tail_K256_M1024.json").read_text())
    modes=prop["targets"]["0"]["modes"]+extra["targets"]["0"]["modes"]
    assert [x["k"] for x in modes]==list(range(2,257))
    lower=next(x for x in stress["initial_energy_certificates"]
               if x["finite_K"]==256)["selected"]["rho_full_lower_bound"][0]
    upper=stress["extra_eta0_finite"]["rho_full_interval_direct_UV"][1]
    density=box(Q(lower),Q(upper))
    pressure=parse(stress["extra_eta0_finite"]["pressure_full_interval_direct_UV"])
    assert lo(density)>mp.mpf(3)/2 and hi(density)<112
    assert uv["K"]==256
    assert uv["uniform_physical_UV_tail"]["eta_interval"]==["0","3/16"]
    return density,pressure,modes,uv,frozen

def uniform_base_bound(modes,uv):
    """Finite modes from exact Hamilton squeeze growth, plus the certified UV.

    At fixed k, A=(sqrt(omega)*a*u+i*p/(sqrt(omega)*a))/sqrt(2)
    and B=(sqrt(omega)*a*u-i*p/(sqrt(omega)*a))/sqrt(2).
    A'=-i*omega*A+h*B, B'=h*A+i*omega*B. Thus
    asinh|B(t)|<=asinh|B(0)|+integral|h|, and e=omega*(1+2|B|^2).
    """
    angle=box(0,2*ETA_MAX)
    c=iv.cos(angle)
    cend=iv.cos(2*I(ETA_MAX))
    assert lo(c)>0 and lo(c*c)>mp.mpf(3)/4
    h=-iv.tan(angle)
    q=1/(c*c)
    E1=(h*h-1)/2
    E3=3*q*(1-3*h*h)/8
    P1=q/3+h*h/2+I(Q(1,6))
    P3=-q*(7+27*h*h)/8
    rmax=top(-iv.log(cend)/2)
    sh,ch=top(sinh(rmax)),top(cosh(rmax))
    rs=I(0)
    sum_k=I(0)
    harmonic=I(0)
    beta2_sum=I(0)
    alphabeta_sum=I(0)
    beta0_max=I(0)
    for mode in modes:
        k=mode["k"]
        omega=iv.sqrt(k*k-1)
        e0=parse(mode["e"])
        b0sq=max(mp.mpf(0),hi((e0/omega-1)/2))
        b0=top(iv.sqrt(I(b0sq)))
        beta=top(b0*ch+iv.sqrt(1+b0*b0)*sh)
        ab=top(beta*iv.sqrt(1+beta*beta))
        beta2_sum+=k*k*omega*beta*beta
        alphabeta_sum+=k*k*omega*ab
        if hi(b0)>hi(beta0_max):beta0_max=top(b0)
        # Algebraically exact, avoiding subtraction of k^3 vacuum terms.
        rs+=-(omega+3*k)/(8*k*(k+omega)**3)
        sum_k+=k
        harmonic+=I(Q(1,k))
    rho_vac=rs-h*h*sum_k/2-(E3+I(Q(1,8)))*harmonic
    p_vac=rs/3-(P1+I(Q(1,6)))*sum_k-(P3+I(Q(1,24)))*harmonic
    zero_e=1/(2*c)
    rho_zero_res=zero_e-1-E1-E3
    p_zero_res=zero_e-I(Q(1,3))-P1-P3
    pref=1/(36*iv.pi**2*c*c)
    anrho,anp=analytic(c)
    finite_rho=top(abs_top(pref*(rho_vac+rho_zero_res))
                   +top(pref)*2*beta2_sum+abs_top(anrho))
    finite_p=top(abs_top(pref*(p_vac+p_zero_res))
                 +top(pref)*(2*beta2_sum/3+4*alphabeta_sum/3)+abs_top(anp))
    tail=uv["uniform_physical_UV_tail"]
    rho_tail=parse(tail["rho_UV_tail_absolute_bound"])
    p_tail=parse(tail["pressure_UV_tail_absolute_bound"])
    rho=top(finite_rho+rho_tail)
    pressure=top(finite_p+p_tail)
    # H1rho and H1p increase with c on the certified domain.
    Hρ=I(6)
    Hp=top(abs_top((40*cend*cend-54)/cend**6))
    return {"eta_interval":["0","3/16"],"c_interval":pair(c),
            "c_endpoint_interval":pair(cend),"hamilton_squeeze_growth_max":pair(rmax),
            "finite_modes":256,"max_initial_hamilton_beta_bound":pair(beta0_max),
            "finite_rho_absolute_upper":pair(finite_rho),
            "finite_pressure_absolute_upper":pair(finite_p),
            "UV_rho_absolute_upper":pair(rho_tail),
            "UV_pressure_absolute_upper":pair(p_tail),
            "full_rho_absolute_upper":pair(rho),
            "full_pressure_absolute_upper":pair(pressure),
            "H1_rho_absolute_upper":pair(Hρ),
            "H1_pressure_absolute_upper":pair(Hp),
            "M2_contract_used_for_quantum_bound":"none; centered reference only"}

def scaling_table(density,pressure,uniform):
    C=1/(576*iv.pi**2)
    Qcap=parse(uniform["full_rho_absolute_upper"])
    Pcap=parse(uniform["full_pressure_absolute_upper"])
    Hρ=parse(uniform["H1_rho_absolute_upper"])
    Hp=parse(uniform["H1_pressure_absolute_upper"])
    Q0cap=I(hi(density))
    cmin=I(lo(parse(uniform["c_interval"])))
    rows=[]
    for lam in LAMBDAS:
        l=I(lam)
        ell=iv.log(l)
        qeff=density+6*C*ell
        peff=pressure-14*C*ell
        rho=qeff/l**4
        p=peff/l**4
        Rcap=top(Qcap+Hρ*C*ell)
        Scap=top(Pcap+Hp*C*ell)
        initial_ratio=2*qeff/l**2
        initial_p_ratio=top(2*(abs_top(pressure)+14*C*ell)/l**2)
        uniform_rho_ratio=top(2*Rcap/l**2)
        uniform_p_ratio=top(2*Scap/l**2)
        q0_upper=top(Q0cap+6*C*ell)
        # Retune M2 with the same exact unknown Q0. This makes the initial
        # Hamiltonian density defect zero, but leaves the pressure/evolution.
        M2_interval=27*l**4-54*l**2*qeff
        rho_defect_abs=top((Rcap+q0_upper/cmin**3)/l**4)
        p_defect_abs=top((Scap+q0_upper/cmin**3)/l**4)
        rho_defect_ratio=top(2*(Rcap+q0_upper)/l**2)
        p_defect_ratio=top(2*(Scap+q0_upper)/l**2)
        rows.append({"lambda":lam,
          "initial_quantum_rho_interval":pair(rho),
          "initial_quantum_pressure_interval":pair(p),
          "initial_required_density":pair(1/(2*l*l)),
          "initial_quantum_density_relative_interval":pair(initial_ratio),
          "initial_quantum_pressure_relative_abs_upper":pair(initial_p_ratio),
          "uniform_quantum_rho_relative_abs_upper":pair(uniform_rho_ratio),
          "uniform_quantum_pressure_relative_abs_upper":pair(uniform_p_ratio),
          "retuned_M2_interval":pair(M2_interval),
          "retuned_M2_is_positive":lo(M2_interval)>0,
          "retuned_uniform_rho_defect_absolute_upper":pair(rho_defect_abs),
          "retuned_uniform_pressure_defect_absolute_upper":pair(p_defect_abs),
          "retuned_uniform_rho_defect_relative_upper":pair(rho_defect_ratio),
          "retuned_uniform_pressure_defect_relative_upper":pair(p_defect_ratio)})
    chosen=next(x for x in rows if x["lambda"]==8192)
    assert chosen["retuned_M2_is_positive"]
    for key in ["uniform_quantum_rho_relative_abs_upper",
                "uniform_quantum_pressure_relative_abs_upper",
                "retuned_uniform_rho_defect_relative_upper",
                "retuned_uniform_pressure_defect_relative_upper"]:
        assert Q(chosen[key][1])<Q(1,100),(key,chosen[key])
    # (B+D log lambda)/lambda^2 decreases for lambda>=1 if 2B>D.
    for B,D in [(Qcap,Hρ*C),(Pcap,Hp*C),
                (Qcap+Q0cap,(Hρ+6)*C),(Pcap+Q0cap,(Hp+6)*C)]:
        assert lo(2*B-D)>0
    return rows,{"lambda_at_least":8192,"eta_interval":["0","3/16"],
                 "relative_stress_component_threshold":"1/100",
                 "finite_alpha":"0",
                 "applies_to":["centered_quantum_vs_classical_homothetic_stress",
                               "retuned_total_RHS_vs_homothetic_Einstein_tensor"],
                 "monotonicity":"(B+D*log(lambda))/lambda^2 strictly decreases for lambda>=1",
                 "metric_solution_error_certified":False,
                 "exact_semiclassical_evolution_certified":False}

def failure_controls():
    C=1/(576*iv.pi**2)
    ell=iv.log(2)
    missing_rho=6*C*ell/16
    missing_p=-14*C*ell/16
    assert lo(missing_rho)>0 and hi(missing_p)<0
    return {
      "pure_lambda_minus_four_at_fixed_physical_mu":{
        "correct_minus_wrong_rho_at_lambda2":pair(missing_rho),
        "correct_minus_wrong_pressure_at_lambda2":pair(missing_p),
        "verdict":"FAILS; fixed-mu anomaly cannot be dropped"},
      "change_mu_without_running_alpha":{
        "verdict":"changes the specified physical total curvature coefficient",
        "consistent_rule":"mu->mu/lambda, alpha->alpha+log(lambda)/(576*pi^2)"},
      "hold_zero_covariance_fixed":{
        "verdict":"different legitimate zero-mode state; kinetic energy scales lambda^-6"},
      "scale_zero_q_but_hold_zero_p_variance":{
        "covariance_determinant":"1/(4*lambda^2)",
        "verdict":"violates the uncertainty lower bound for lambda>1"},
      "fixed_M2_as_classical_homothety":{
        "classical_to_required_initial_density_at_lambda2":"1/16",
        "verdict":"FAILS; fixed M2 is a different preparation contract"},
      "whole_state_transport_as_classical_homothety":{
        "classical_to_required_initial_density_at_lambda2":"1/4",
        "verdict":"FAILS; canonical state transport has M2 proportional to lambda^2"},
      "classical_homothety_plus_quantum_exact_solution":{
        "verdict":"FAILS for every finite lambda>=1 at alpha=0; initial quantum density is strictly positive"},
      "small_stress_defect_as_metric_error":{
        "verdict":"NOT_CERTIFIED; stability, jets, constraints and full evolution remain separate"}}

def calculate():
    if not __debug__:raise RuntimeError("Proof assertions required; do not use -O.")
    symbolic=symbolic_checks()
    density,pressure,modes,uv,frozen=inherited_inputs()
    uniform=uniform_base_bound(modes,uv)
    rows,family=scaling_table(density,pressure,uniform)
    result={"status":"EXACT_HOMOTHETIC_RSET_SCALING_AND_UNIFORM_STRESS_DEFECT_CERTIFICATE",
      "base":BASE,"precision_decimal":iv.dps,
      "interval_encoding":"exact_binary_endpoints_as_rational_strings",
      "scheme":"fixed physical mu=1, alpha=0 on source side, same centered Hadamard reference",
      "symbolic":symbolic,
      "initial_base_density_interval":pair(density),
      "initial_base_pressure_interval":pair(pressure),
      "uniform_base_reference":uniform,
      "scales":rows,"certified_scale_family":family,
      "failure_controls":failure_controls(),
      "source_sha256":{"check.py":LOADED_SOURCE_SHA},
      "inherited_input_sha256":{str(Path(path).relative_to(TIMELIKE.parent)):sha
                                for path,sha in frozen.items() if Path(path)!=(HERE/"check.py")},
      "fresh_mode_integrations":0,
      "claims_not_made":["unique_physical_scale","mu_change_as_physical_repair",
                        "exact_semiclassical_evolution","metric_error_estimate",
                        "arbitrary_finite_curvature_coupling_bound"]}
    assert digest(HERE/"check.py")==LOADED_SOURCE_SHA,"source changed during calculation"
    for path,sha in frozen.items():
        assert digest(Path(path))==sha,("inherited input changed during calculation",path)
    return result

if __name__=="__main__":
    if not __debug__:raise SystemExit("Proof assertions required; do not use -O.")
    parser=argparse.ArgumentParser(description=__doc__)
    action=parser.add_mutually_exclusive_group()
    action.add_argument("--write",action="store_true")
    action.add_argument("--check",action="store_true")
    args=parser.parse_args()
    result=calculate()
    rendered=json.dumps(result,indent=2,sort_keys=True,ensure_ascii=False)+"\n"
    path=HERE/"result.json"
    if args.write:path.write_text(rendered)
    if args.check:assert path.read_text()==rendered,"scaling receipt mismatch"
    u=result["uniform_base_reference"]
    print("Uniform base |rho| <=",float(Q(u["full_rho_absolute_upper"][1])))
    print("Uniform base |p| <=",float(Q(u["full_pressure_absolute_upper"][1])))
    for row in result["scales"]:
        if row["lambda"] in [15,8192]:
            print("lambda",row["lambda"],
                  "initial rho relative upper",float(Q(row["initial_quantum_density_relative_interval"][1])),
                  "retuned rho defect relative upper",float(Q(row["retuned_uniform_rho_defect_relative_upper"][1])),
                  "retuned p defect relative upper",float(Q(row["retuned_uniform_pressure_defect_relative_upper"][1])))
    print("PASS: exact scaling, inherited directed bounds, uniform lambda>=8192 stress defects below 1%.")
