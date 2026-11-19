"""Certified forced linear Einstein--homogeneous-scalar response.

The quantum stress is the already certified full-field stress on the fixed
background. No modes are reintegrated and no finite change of geometry is made
while pretending to keep the old complete Cauchy kernel. This certificate is
for the explicitly stated linear system, not a nonlinear semiclassical error
bound or a constructed quantum state on the corrected geometry.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys
from mpmath import iv, mp
import sympy as sp

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[5]
COMP = HERE.parent.parent / "compatibility"
BASE = "d6ec9eda409ba78d1d7993d7648ba26b5a34374d"
LAMBDA = 8192
END = F(3,16)
mp.dps = 100
iv.dps = 82

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def I(x):
    if isinstance(x,F):
        return iv.mpf(x.numerator)/x.denominator
    return iv.mpf(x)

def endpoint(x,j):
    return mp.make_mpf(x._mpi_[j])

def rational(x):
    sign,man,power,_ = x._mpf_
    return F((-1 if sign else 1)*man)*F(2)**power

def pair(x):
    return [str(rational(endpoint(x,j))) for j in (0,1)]

def parse(p):
    a,b=F(p[0]),F(p[1])
    return iv.mpf([endpoint(I(a),0),endpoint(I(b),1)])

def upper(x):
    return I(endpoint(x,1))

def absolute(x):
    return I(max(abs(endpoint(x,0)),abs(endpoint(x,1))))

def top(x):
    return pair(upper(x))[1]

def symbolic():
    t=sp.symbols("eta",real=True)
    c=sp.cos(2*t)
    A=sp.sqrt(3*c)
    u=sp.sin(2*t)/(2*sp.sqrt(c))
    v=1/sp.sqrt(c)
    L=lambda f:sp.trigsimp(sp.diff(f,t,2)+(1-3/c**2)*f)
    assert sp.trigsimp(sp.diff(A,t,2)+A+9/A**3)==0
    assert L(u)==0 and L(v)==0
    assert sp.trigsimp(v*sp.diff(u,t)-sp.diff(v,t)*u)==1
    assert u.subs(t,0)==0 and sp.diff(u,t).subs(t,0)==1
    assert v.subs(t,0)==1 and sp.diff(v,t).subs(t,0)==0
    s=sp.symbols("s",real=True)
    G=u*v.subs(t,s)-v*u.subs(t,s)
    expected=(sp.sin(2*t)-sp.sin(2*s))/(2*sp.sqrt(c)*sp.sqrt(sp.cos(2*s)))
    assert sp.simplify(G-expected)==0
    assert sp.simplify(G.subs(t,s))==0
    assert sp.trigsimp(sp.diff(G,t).subs(t,s))==1
    a,z,b,w,R,P,m,e=sp.symbols("a z b w R P m epsilon",real=True)
    a0=sp.symbols("a0",positive=True)
    acceleration=(a+e*b)+(27+e*m)/(3*(a+e*b)**3)-e*(a+e*b)**3*(R-3*P)/3
    linear=sp.diff(acceleration,e).subs(e,0)
    assert sp.simplify(linear-((1-27/a**4)*b+m/(3*a**3)-a**3*(R-3*P)/3))==0
    friedmann=(z+e*w)**2+(a+e*b)**2-(27+e*m)/(3*(a+e*b)**2)-sp.Rational(2,3)*e*(a+e*b)**4*R
    C=2*z*w+2*a*b+18*b/a**3-m/(3*a**2)-sp.Rational(2,3)*a**4*R
    assert sp.simplify(sp.diff(friedmann,e).subs(e,0)-C)==0
    vector=[z,-a-9/a**3,w,-(1-27/a**4)*b+a**3*(R-3*P)/3-m/(3*a**3),-3*z*(R+P)/a]
    derivative=sum(sp.diff(C,x)*dx for x,dx in zip([a,z,b,w,R],vector))
    assert sp.simplify(derivative)==0
    bad_vector=vector[:-1]+[-3*z*(R-P)/a]
    wrong=sum(sp.diff(C,x)*dx for x,dx in zip([a,z,b,w,R],bad_vector))
    assert sp.simplify(wrong)!=0
    q0,qhat,dq=sp.symbols("q0 qhat dq",real=True)
    C0=sp.simplify(C.subs({a:sp.sqrt(3),z:0,b:0,w:0,R:q0,m:-54*qhat}))
    assert C0==6*(qhat-q0)
    b0=sp.sqrt(3)*(q0-qhat)/2
    assert sp.simplify(C.subs({a:sp.sqrt(3),z:0,b:b0,w:0,R:q0,m:-54*qhat}))==0
    assert sp.trigsimp(L(A*dq/2)+18*dq/A**3)==0
    # The two positive Green kernel moments are evaluated analytically.
    I1=sp.sin(2*t)**2/2-sp.sin(2*t)**2/4
    I2=sp.sin(2*t)*sp.tan(2*t)/2-(1/c-1)/2
    assert sp.simplify(I1-sp.sin(2*t)**2/4)==0
    assert sp.trigsimp(I2-(1-c)/2)==0
    x,Q,K,ell=sp.symbols("c Q K lambda",positive=True)
    B=(K*(1-x*x)+4*Q*(1-x))/(8*ell**2*x)
    assert sp.simplify(sp.diff(B,x)+(K*(1+x**-2)+4*Q*x**-2)/(8*ell**2))==0
    # Scalar shift charge is constant; the first variation is not frozen.
    scalar=sp.sqrt(27+e*m)/(a+e*b)**2
    scalar_rel=sp.simplify(sp.diff(scalar,e).subs(e,0)/(sp.sqrt(27)/a**2))
    assert sp.simplify(scalar_rel-(m/54-2*b/a))==0
    h,r,rp=sp.symbols("h r rp",real=True)
    scaled_H=(h+e*rp)/(1+e*r)
    assert sp.diff(scaled_H,e).subs(e,0)==rp-h*r
    N=sp.symbols("N",positive=True)
    rapidly_varying=sp.sin(N*t)/N**3
    assert sp.simplify(sp.diff(rapidly_varying,t,4)-N*sp.sin(N*t))==0
    assert sp.simplify(-qhat-2*(sp.Symbol("r")+ (q0-qhat)/2)+q0+2*sp.Symbol("r"))==0
    return {
        "higher_derivative_negative_control":"b_N=sin(N*eta)/N^3: C2 amplitude <=1/N, fourth derivative reaches N for N>=9 on I",
        "background_classical_equation":"A''+A+9/A^3=0",
        "linear_scale_equation":"b''+(1-3/c^2)b=A^3*(rho_eff-3*p_eff)/3+18*qstar/A^3",
        "fundamental_v":"1/sqrt(c)",
        "fundamental_u":"sin(2*eta)/(2*sqrt(c))",
        "Wronskian_v_u":"1",
        "retarded_G":"(sin(2*eta)-sin(2*s))/(2*sqrt(c_eta*c_s)), 0<=s<=eta",
        "Green_diagonal":"0","Green_derivative_jump":"1",
        "linear_Friedmann_C1":"2*A_prime*b_prime+2*A*b+18*b/A^3-m/(3*A^2)-(2/3)*A^4*rho_eff",
        "linear_constraint_derivative":"0 using rho_eff'=-3*A'/A*(rho_eff+p_eff)",
        "wrong_conservation_sign_negative_control":str(sp.simplify(wrong)),
        "zero_initial_correction_constraint":"6*(qstar-Qeff0)",
        "rational_source_linear_constraint_repair_b0":"sqrt(3)*(Qeff0-Qhat)/2; b_prime(0)=0",
        "repaired_rational_minus_exact_relative_coefficient":"(Qeff0-Qhat)/2, constant in eta",
        "positive_kernel_moments":["sin(2*eta)^2/4","(1-cos(2*eta))/2"],
        "scalar_conformal_derivative_relative_coefficient":"m/54-2*b/A",
        "proper_H_scaled_first_variation":"r_prime-h*r",
        "all_symbolic_identities":"PASS",
    }

def load_inputs():
    names=["scaling/result.json","constraints/result.json","review.json","verification.json"]
    frozen={}
    data={}
    for name in names:
        path=COMP/name
        rel=str(path.relative_to(REPO))
        old=subprocess.check_output(["git","show",BASE+":"+rel],cwd=REPO)
        assert path.read_bytes()==old,("Frozen predecessor changed",rel)
        frozen[path]=sha(path)
        data[name]=json.loads(path.read_text())
    receipt=data["verification.json"]
    assert receipt["status"]=="PASS" and len(receipt["executed_now"])==4
    assert all(row["returncode"]==0 for row in receipt["executed_now"])
    for name in names[:-1]:
        path=COMP/name
        assert receipt["current_source_manifest"][str(path.relative_to(REPO))]==sha(path)
    frozen[HERE/"check.py"]=sha(HERE/"check.py")
    return data,frozen

def geometry_bounds(R,P,qcap,lam):
    t=I(END);c=iv.cos(2*t);s=iv.sin(2*t);tan=iv.tan(2*t)
    R=upper(R);P=upper(P);qcap=upper(qcap)
    K=upper(R+3*P)
    r=upper((K*(1-c*c)+4*qcap*(1-c))/(8*lam**2*c))
    h=upper(2*tan*r+(K*s/2+qcap*tan)/lam**2)
    proper_H=upper(h+tan*r)
    volume=upper(3*r)
    scalar=upper(qcap/lam**2+2*r)
    assert F(top(r))<F(1,4000)
    assert F(top(h))<F(3,1000)
    assert F(top(proper_H))<F(3,1000)
    assert F(top(volume))<F(3,4000)
    assert F(top(scalar))<F(1,2000)
    return {
        "uniform_scale_first_variation_relative_abs_upper":top(r),
        "uniform_conformal_H_first_variation_abs_upper":top(h),
        "uniform_lambda_A_times_proper_H_first_variation_abs_upper":top(proper_H),
        "uniform_log_volume_first_variation_abs_upper":top(volume),
        "normalized_nonnegative_volume_window_first_variation_abs_upper":top(volume),
        "proper_clock_first_variation_relative_abs_upper":top(r),
        "scalar_conformal_derivative_first_variation_relative_abs_upper":top(scalar),
        "first_order_scale_factor_positive":True,
        "scale_factor_lower_relative_to_background":pair(1-r)[0],
    }

def calculate():
    assert __debug__ and sys.flags.optimize==0,"Do not use -O"
    symbolic_result=symbolic()
    data,frozen=load_inputs()
    scaling=data["scaling/result.json"]
    constraints=data["constraints/result.json"]
    reviewed=data["review.json"]
    t=I(END);c=iv.cos(2*t);lam=I(LAMBDA)
    assert endpoint(c,0)>0
    qbase=parse(scaling["initial_base_density_interval"])
    log=iv.log(lam);coeff=log/(576*iv.pi**2)
    qeff=qbase+6*coeff
    qcap=absolute(qeff)
    source=next(r for r in constraints["tuned_sources"] if str(r["lambda"])==str(LAMBDA))
    Mhat=F(source["explicit_rational_approximation"]["M2"])
    qhat=F(LAMBDA**2,2)-Mhat/F(54*LAMBDA**2)
    assert qhat==F(source["explicit_rational_approximation"]["Q_effective_midpoint"])
    assert qhat>0 and Mhat>0
    difference=qeff-I(qhat);diffcap=absolute(difference)
    routes={
        "per_mode_predecessor":(
            parse(scaling["uniform_base_reference"]["full_rho_absolute_upper"]),
            parse(scaling["uniform_base_reference"]["full_pressure_absolute_upper"]),
            parse(scaling["uniform_base_reference"]["H1_rho_absolute_upper"]),
            parse(scaling["uniform_base_reference"]["H1_pressure_absolute_upper"])),
        "aggregate_predecessor":(
            parse(reviewed["independent_uniform_reference"]["rho_absolute_upper"]),
            parse(reviewed["independent_uniform_reference"]["pressure_absolute_upper"]),
            parse(reviewed["independent_uniform_reference"]["H1rho_absolute_upper"]),
            parse(reviewed["independent_uniform_reference"]["H1p_absolute_upper"])),
    }
    certificates={}
    for name,(rho,p,Hrho,Hp) in routes.items():
        R=upper(rho+coeff*Hrho);P=upper(p+coeff*Hp)
        exact=geometry_bounds(R,P,qcap,lam)
        rational=geometry_bounds(R,P,I(qhat),lam)
        initial_rel=upper(2*diffcap/lam**2)
        offset=upper(diffcap/(2*lam**2))
        repaired_r=upper(I(F(exact["uniform_scale_first_variation_relative_abs_upper"]))+offset)
        assert F(top(repaired_r))<F(1,4000)
        certificates[name]={
            "full_field_rho_effective_absolute_upper":top(R),
            "full_field_pressure_effective_absolute_upper":top(P),
            "exact_correlated_source_zero_initial_correction":{
                **exact,"C1":"0","linearized_constraint_satisfied":True,
                "b_initial":"0","b_prime_initial":"0"},
            "explicit_rational_source_zero_initial_correction":{
                **rational,"C1_interval":pair(-6*difference),
                "linearized_constraint_satisfied":False,
                "uniform_constraint_relative_to_background_Gnn_abs_upper":top(initial_rel),
                "constraint_not_generated_by_evolution":"C1 constant; its nonzero initial value is retained"},
            "explicit_rational_source_correlated_linear_initial_geometry":{
                "b_initial_interval":pair(iv.sqrt(3)*difference/2),
                "b_prime_initial":"0","C1":"0",
                "linearized_constraint_satisfied":True,
                "relative_scale_difference_from_exact_source_path_interval":pair(difference/(2*lam**2)),
                "relative_scale_difference_abs_upper":top(offset),
                "uniform_scale_first_variation_relative_abs_upper":top(repaired_r),
                "conformal_H_first_variation_equal_to_exact_source_path":True,
                "normalized_log_volume_first_variation_equal_to_exact_source_path":True,
                "scalar_conformal_derivative_first_variation_equal_to_exact_source_path":True,
                "initial_geometry_depends_on_same_exact_Qeff0":True,
                "is_exact_nonlinear_initial_constraint_solution":False,
            }
        }
    for path,value in frozen.items():
        assert sha(path)==value,("Input changed during geometry certificate",str(path))
    return {
        "schema":"ueot-linear-Einstein-scalar-response/1",
        "reviewed_base":BASE,"status":"CERTIFIED_FORCED_LINEAR_RESPONSE_AND_CONSTRAINT_PROPAGATION",
        "eta_interval":["0",str(END)],"lambda":LAMBDA,"units":"4*pi*G=hbar=1",
        "physical_mu":"1","finite_alpha":"0",
        "linear_system_is_exactly_solved":True,
        "quantum_source":"full infinite-field reference RSET evaluated on fixed g_lambda",
        "expansion":"a=lambda*(A+epsilon*b), M2=lambda^4*(27+epsilon*m), epsilon=lambda^-2",
        "relative_coefficient_r":"b/A",
        "quantum_effective_initial_interval":pair(qeff),
        "explicit_rational_M2":str(Mhat),"explicit_rational_Qhat":str(qhat),
        "symbolic":symbolic_result,"certificates":certificates,
        "scope":{
            "classical_scalar_momentum_responds_through_geometry":True,
            "all_mean_source_sign_branches_share_the_linear_response":True,
            "volume_window":"nonnegative normalized conformal-time weight; first variation of log(a^3/a0^3)",
            "proper_clock":"proper time from eta=0 to any fixed eta>0; first variation",
            "proper_H_normalization":"lambda*A*delta H^(1), not division by H0 which vanishes initially",
            "new_quantum_state_on_finitely_corrected_geometry_constructed":False,
            "nonlinear_semiclassical_solution_constructed":False,
            "nonlinear_solution_distance_bound":False,
            "quantum_RSET_response_operator_norm_certified":False,
            "higher_order_semiclassical_remainder_certified":False,
            "full_metric_noise_variance_certified":False,
            "global_exterior_and_apparatus_constructed":False,
        },
        "new_mode_integrations":0,
        "input_sha256":{str(p.relative_to(REPO)):h for p,h in sorted(frozen.items())},
    }

if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write",action="store_true")
    parser.add_argument("--check",action="store_true")
    args=parser.parse_args()
    result=calculate()
    rendered=json.dumps(result,indent=2,sort_keys=True,ensure_ascii=False)+"\n"
    target=HERE/"result.json"
    if args.write:target.write_text(rendered)
    if args.check:assert target.read_text()==rendered,"Linear geometry receipt mismatch"
    for name,row in result["certificates"].items():
        exact=row["exact_correlated_source_zero_initial_correction"]
        print(name,"scale <=",float(F(exact["uniform_scale_first_variation_relative_abs_upper"])),
              "conformal_H <=",float(F(exact["uniform_conformal_H_first_variation_abs_upper"])),
              "log_volume <=",float(F(exact["uniform_log_volume_first_variation_abs_upper"])))
    print("PASS: positive Green response, propagated linear constraints, rational-source distinction; zero new mode integrations.")
