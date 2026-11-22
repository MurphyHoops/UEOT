"""Full stress-noise scaling and a certified local all-mode linear-noise bound.

No old mode ODE is rerun. The quadratic reference noise constant is proved
finite for the stated four-dimensional smooth test, but is NOT assigned a
numerical upper bound here. Exact rational interval endpoints are archived.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
from mpmath import iv, mp
import sympy as sp

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[5]
BASE = "d6ec9eda409ba78d1d7993d7648ba26b5a34374d"
TIMELIKE = HERE.parents[1]
N_CELLS = 2048
LAMBDA = 8192
mp.dps = 85
iv.dps = 65

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def I(x):
    if isinstance(x, F):
        return iv.mpf(x.numerator)/x.denominator
    return iv.mpf(x)

def endpoint(x,j):
    return mp.make_mpf(x._mpi_[j])

def rational(x):
    sign, man, power, _ = x._mpf_
    return F((-1 if sign else 1)*man)*F(2)**power

def pair(x):
    return [str(rational(endpoint(x,j))) for j in (0,1)]

def upper_fraction(x):
    return F(pair(x)[1])

def lower_fraction(x):
    return F(pair(x)[0])

def enclosing(*values):
    return iv.mpf([min(endpoint(x,0) for x in values),
                   max(endpoint(x,1) for x in values)])

def box(a,b):
    return enclosing(I(a),I(b))

def parse(values):
    return box(F(values[0]),F(values[1]))

def bump_at(x):
    x=abs(F(x))
    assert x<=1
    if x==1:
        return I(0)
    return iv.exp(-1/(1-I(x)**2))

def bump_box(left,right):
    assert -1<=left<=right<=1
    far=max(abs(left),abs(right))
    near=F(0) if left<=0<=right else min(abs(left),abs(right))
    return enclosing(bump_at(far),bump_at(near))

def derivative_square_at(x):
    x=F(x)
    assert 0<=x<=1
    if x in (0,1):
        return I(0)
    z=1/(1-I(x)**2)
    return 4*I(x)**2*z**4*iv.exp(-2*z)

def derivative_square_box(left,right):
    values=[derivative_square_at(left),derivative_square_at(right)]
    if left**4<=F(1,3)<=right**4:
        zstar=(3+iv.sqrt(3))/2
        values.append(4*(zstar**4-zstar**3)*iv.exp(-2*zstar))
    return enclosing(*values)

def symbolic_checks():
    z=sp.symbols('z',positive=True)
    g=4*(z**4-z**3)*sp.exp(-2*z)
    assert sp.simplify(sp.diff(g,z)+4*z*z*(2*z*z-6*z+3)*sp.exp(-2*z))==0
    lam,d,D,C0,C1,m2,m4=sp.symbols('lambda d D C0 C1 m2 m4',positive=True)
    U,V,Y=sp.symbols('U V Y',real=True)
    centered=lam**-4*U+d*lam**-3*Y*V+d*d*lam**-2*D*(Y*Y-m2)
    moments_uv={(0,0):1,(1,0):0,(0,1):0,(2,0):C0,(0,2):C1,(1,1):0}
    ymoments={0:1,1:sp.symbols('m1'),2:m2,3:sp.symbols('m3'),4:m4}
    value=0
    for powers,coefficient in sp.Poly(sp.expand(centered**2),U,V,Y).terms():
        a,b,c=powers
        value+=coefficient*moments_uv[(a,b)]*ymoments[c]
    expected=lam**-8*C0+d*d*lam**-6*m2*C1+d**4*lam**-4*D*D*(m4-m2*m2)
    assert sp.simplify(value-expected)==0
    assert sp.simplify(expected.subs({m2:1,m4:1})-
                       (lam**-8*C0+d*d*lam**-6*C1))==0
    assert sp.simplify(expected.subs({m2:1,m4:sp.Rational(7,4)})-
                       expected.subs({m2:1,m4:1})-
                       sp.Rational(3,4)*d**4*lam**-4*D*D)==0
    vp,vol=sp.symbols('Vp V3',positive=True)
    linear_zero=sp.simplify((27*vp/vol)/(sp.Rational(27,2)**2))
    quadratic_zero=sp.simplify((vp*vp/(2*vol*vol))/(sp.Rational(27,2)**2))
    assert sp.simplify(linear_zero.subs({vp:sp.Rational(3,2),vol:2*sp.pi**2})-
                       1/(9*sp.pi**2))==0
    assert sp.simplify(quadratic_zero.subs({vp:sp.Rational(3,2),vol:2*sp.pi**2})-
                       1/(648*sp.pi**4))==0
    c0,c1,tau,eps=sp.symbols('c0 c1 tau eps',positive=True)
    x=(c1+sp.sqrt(c1*c1+4*tau*(1-eps)**2*c0))/(2*tau*(1-eps)**2)
    assert sp.simplify(tau*(1-eps)**2*x*x-c1*x-c0)==0
    return {
        "variance_polynomial_under_stated_Gaussian_moments":"PASS",
        "noncommuting_covariance_input":"<U V+V U>=0 by odd Gaussian moments",
        "homothetic_variance":"lambda^-8*C0+d^2*lambda^-6*C1+Var(Y^2)*d^4*lambda^-4*D^2",
        "old_bounded_source_extra_variance":"(3/4)*d^4*lambda^-4*D^2",
        "new_sign_source_extra_variance":"0",
        "bump_derivative_square_extremum":"x^4=1/3; z=(3+sqrt(3))/2; value 4*(z^4-z^3)*exp(-2*z)",
        "noise_threshold_positive_root":"PASS",
        "finite_counterterms_and_scale_anomaly":"c-number contributions cancel from connected variance",
    }

def freeze_inputs():
    reference_path=TIMELIKE/'compatibility/review.json'
    reference=json.loads(reference_path.read_text())
    relatives={
        "physics/qm/null_source/timelike/continuation/SOURCE.md",
        "physics/qm/null_source/timelike/instrument/instrument.py",
        "physics/qm/null_source/timelike/identification/reference.py",
        "physics/qm/null_source/timelike/compatibility/CONTRACT.md",
        "physics/qm/null_source/timelike/compatibility/review.json",
    } | set(reference["input_sha256"])
    frozen={}
    for relative in sorted(relatives):
        path=REPO/relative
        previous=subprocess.check_output(["git","show",BASE+":"+relative],cwd=REPO)
        assert path.read_bytes()==previous,("inherited source changed",relative)
        frozen[path]=sha(path)
    assert reference["physical_models"]["lambda"]==LAMBDA
    frozen[HERE/'check.py']=sha(HERE/'check.py')
    return reference,frozen

def preparation_growth():
    a0=iv.sqrt(3)
    aleft=iv.sqrt(3*iv.cos(I(F(1,4))))
    aright=iv.sqrt(3*iv.cos(I(F(1,8))))
    prep=(a0+aright-2*aleft)/aleft
    radius=prep+iv.log(a0/aright)+iv.log(a0/aleft)
    kinetic=iv.exp(2*radius)/2
    assert upper_fraction(radius)<F(1,16)
    return {
        "preparation_eta":["-1/8","-1/16"],
        "test_eta":["1/16","1/8"],
        "log_scale_total_variation_upper":pair(radius),
        "mode_derivative_bound_factor":pair(kinetic),
        "bound":"|u_k_prime(eta)|^2 <= kinetic_factor*sqrt(k^2-1)/a(eta)^2, every k>=2",
        "derivation":"static beta=0; |beta|<=sinh(integral|a_prime/a|); |alpha|<=cosh",
        "preparation_variation_bound":"(a0+a(-1/16)-2*a(-1/8))/a(-1/8)",
    }

def local_bump_integrals():
    # F(eta,chi)=b(32*(eta-3/32))*b(8*chi), b(x)=exp[-1/(1-x^2)].
    # Riemann sums enclose the function on each complete cell, including
    # the exact zero limits at the flat bump boundary. No quadrature estimator.
    n=N_CELLS
    radius=I(F(1,8))
    W=I(0);S0=I(0);S1=I(0)
    for j in range(n):
        left,right=F(j,n),F(j+1,n)
        b=bump_box(left,right)
        sine=iv.sin(radius*box(left,right))**2
        W+=b*sine/n
        S0+=b*b*sine/n
        S1+=derivative_square_box(left,right)*sine/n
    W*=4*iv.pi*radius
    S0*=4*iv.pi*radius
    S1*=4*iv.pi/radius
    It=I(0);Ic=I(0)
    for j in range(n):
        left,right=F(-1)+F(2*j,n),F(-1)+F(2*(j+1),n)
        b=bump_box(left,right)
        c=iv.cos(I(F(3,16))+box(left,right)/16)
        It+=b/iv.sqrt(3*c)*I(F(1,16*n))
        Ic+=b/c*I(F(1,16*n))
    D=I(F(9,2))*Ic*W
    assert lower_fraction(D)>0
    assert upper_fraction(iv.sqrt(3)*iv.sin(I(F(1,4))))<1
    return {
        "cells_per_integral":n,
        "method":"outward interval Riemann enclosure with exact bump extrema",
        "test_F":"b(32*(eta-3/32))*b(8*chi), b(x)=exp(-1/(1-x^2)) for |x|<1, otherwise 0",
        "time_support":["1/16","1/8"],"spatial_radial_support":["0","1/8"],
        "causal_support_check":"chi+eta<=1/4<arcsin(1/sqrt(3))",
        "spatial_integral":pair(W),"spatial_L2_squared":pair(S0),
        "spatial_gradient_L2_squared":pair(S1),
        "time_integral_h_over_a":pair(It),"time_integral_h_over_c":pair(Ic),
        "classical_density_smearing_D":pair(D),
        "normalization":"F is unnormalized; all reported c0,c1 are divided by D^2",
    }

def certify(reference,growth,integrals):
    D=parse(integrals["classical_density_smearing_D"])
    H=parse(growth["mode_derivative_bound_factor"])
    It=parse(integrals["time_integral_h_over_a"])
    S0=parse(integrals["spatial_L2_squared"])
    S1=parse(integrals["spatial_gradient_L2_squared"])
    c1_zero=1/(9*iv.pi**2)
    c0_zero=1/(648*iv.pi**4)
    c1_nonzero=27*H*It**2*iv.sqrt(S0*S1)/D**2
    c1_bound=upper_fraction(c1_zero+c1_nonzero)
    assert c1_bound>0
    lam=LAMBDA
    rows={}
    models=reference["physical_models"]
    for name in ["exact_correlated_source","explicit_rational_source"]:
        model=models[name]
        eps=F(model["uniform_density_relative_defect_upper"])
        if name=="exact_correlated_source":
            m2=parse(model["M2_interval"])
        else:
            m2=I(F(model["M2"]))
        d_squared=m2/(27*I(lam)**4)
        assert 0<lower_fraction(d_squared)<=upper_fraction(d_squared)<1
        linear_relative=upper_fraction(d_squared)*c1_bound/(lam**2*(1-eps)**2)
        c0_budget=(F(1,100)*(1-eps)**2*lam**4-
                   upper_fraction(d_squared)*c1_bound*lam**2)
        assert c0_budget>0
        rows[name]={
            "d_squared_interval":pair(d_squared),
            "uniform_density_relative_defect_upper":str(eps),
            "linear_quantum_noise_relative_to_total_mean_squared_upper":str(linear_relative),
            "linear_quantum_noise_upper_decimal":float(linear_relative),
            "quadratic_reference_c0_upper_sufficient_for_total_one_percent":str(c0_budget),
            "quadratic_reference_c0_upper_computed":False,
            "total_one_percent_noise_at_this_scale":"NOT_CERTIFIED_C0_UPPER_MISSING",
        }
    return {
        "lambda":lam,
        "local_test_all_mode_linear_coefficient_c1_upper":str(c1_bound),
        "local_test_all_mode_linear_coefficient_c1_upper_decimal":float(c1_bound),
        "linear_nonzero_spectrum_bound":"sum omega_k |w_kl|^2 <= ||w||_2*||gradient w||_2, includes all degeneracies",
        "zero_mode_linear_coefficient_exact":"1/(9*pi^2)",
        "zero_mode_linear_coefficient_interval":pair(c1_zero),
        "zero_zero_quadratic_coefficient_exact":"1/(648*pi^4)",
        "zero_zero_quadratic_coefficient_interval":pair(c0_zero),
        "zero_mode_scope":"orthogonal contributions/lower bounds, never full-noise upper bounds",
        "branches":rows,
        "full_noise_statement":{
            "constants":"c0=Var_ref(A_F)/D^2; c1=Var_ref(B_F)/D^2, fixed unscaled four-dimensional F",
            "operator_B":"B_F=int F*(u f)*(u Phi) dvol = Phi(j_F)",
            "j_F":"-nabla_a[F*(u f)*u^a]=-sqrt(27)*a^-4*partial_eta F; u=a^-1 partial_eta; phi(j)=int j*phi dvol",
            "full_relative_variance_upper":"(c0/lambda^4+d_squared*c1/lambda^2)/(1-epsilon_rho)^2",
            "finite_for_each_fixed_smooth_compact_spacetime_test":True,
            "fixed_physical_aperture_or_instantaneous_test_covered":False,
            "sufficient_scale":"lambda>=8192 and lambda^2 >= [c1+sqrt(c1^2+4*tau*(1-eps_star)^2*c0)]/[2*tau*(1-eps_star)^2], eps_star=1/100, tau>0",
            "finite_test_family":"For pre-fixed finite F_i, take c0=max_i c0_i and c1=max_i c1_i in the same sufficient scale; no uniform statement over all tests at fixed lambda",
            "resolution_negative_control":"In four-dimensional massless Minkowski vacuum, F_epsilon=epsilon^-4 F(x/epsilon) gives quadratic stress variance epsilon^-8*C0 exactly; constants cannot be held fixed when resolution changes",
            "asymptotic_source_family":"M2(lambda)=27*lambda^4-54*lambda^2*Qeff0(lambda), retuned at each lambda; not a fixed 8192 rational M2",
            "asymptotic_relative_noise":"lambda^2*Var(A_lambda)/E(A_lambda)^2 tends to c1>=1/(9*pi^2) for each fixed test in the exact correlated family",
            "numerical_upper_for_complete_C0":"OPEN",
            "geometric_noise_inferred":False,
        },
    }

def calculate():
    assert __debug__,"Do not use -O: proof assertions are required"
    reference,frozen=freeze_inputs()
    algebra=symbolic_checks()
    growth=preparation_growth()
    integrals=local_bump_integrals()
    result=certify(reference,growth,integrals)
    for path,expected in frozen.items():
        assert sha(path)==expected,("input changed during check",str(path))
    return {
        "schema":"ueot-full-stress-noise-and-linear-bound/1",
        "reviewed_base":BASE,
        "status":"FULL_NOISE_SCALING_THEOREM_AND_LOCAL_ALL_MODE_LINEAR_BOUND",
        "symbolic_checks":algebra,
        "all_mode_preparation_growth":growth,
        "local_test_integrals":integrals,
        "certificate":result,
        "new_mode_integrations":0,
        "source_sha256":sha(HERE/'check.py'),
        "inherited_input_sha256":{str(path.relative_to(REPO)):value
                                  for path,value in sorted(frozen.items())
                                  if path!=HERE/'check.py'},
    }

if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write",action="store_true")
    parser.add_argument("--check",action="store_true")
    args=parser.parse_args()
    result=calculate()
    text=json.dumps(result,indent=2,sort_keys=True,ensure_ascii=False)+"\n"
    target=HERE/"result.json"
    if args.write:
        target.write_text(text)
    if args.check:
        assert target.read_text()==text,"noise certificate mismatch"
    cert=result["certificate"]
    print("c1 full-spectrum upper:",cert["local_test_all_mode_linear_coefficient_c1_upper_decimal"])
    for name,row in cert["branches"].items():
        print(name,"linear-noise relative upper:",row["linear_quantum_noise_upper_decimal"])
    print("PASS: full variance scaling and all-mode local linear bound; complete C0 numerical bound remains OPEN.")
