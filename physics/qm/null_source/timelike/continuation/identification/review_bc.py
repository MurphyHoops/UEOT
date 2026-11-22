"""A's independent cross-review of the B/C formulas, using alternative summation/integration."""
from fractions import Fraction as F
from pathlib import Path
import argparse
import hashlib
import json
import math
from mpmath import mp
import sympy as sp

HERE=Path(__file__).resolve().parent
CONT=HERE.parent
mp.dps=90


def q(x):
    x=F(x)
    return mp.mpf(x.numerator)/x.denominator


def encloses(box,x):
    return q(box[0])<=x<=q(box[1])


def quantum():
    data=json.loads((CONT/"quantum/result.json").read_text())
    # Independent interchange of two absolutely convergent positive series.
    # Original B sums r_k through k=1024; this sums binomial orders through j=80.
    c=mp.mpf(1)/16
    correction=mp.mpf(0)
    J=80
    for j in range(3,J+1):
        correction+=c*(mp.zeta(2*j-3)-1)
        c*=mp.mpf(2*j-1)/(2*j+2)
    tail=(mp.mpf(4)/3)*c*(mp.zeta(2*J-1)-1)
    S=mp.mpf(1)/8-correction
    box=data["static_absolute_seed"]["finite_residual_sum_plus_certified_tail"]
    assert q(box[0]) < S-tail < S < q(box[1])
    a4=mp.mpf(9)
    rho=S/(4*mp.pi**2*a4)+(-mp.mpf(3)/160
        -(mp.log(mp.mpf(3)/4)+2*mp.euler)/64)/(mp.pi**2*a4)
    assert encloses(data["static_absolute_seed"]["rho"],rho)
    # Static k=1's stiff trace plus the analytic geometric trace.
    trace=1/(4*mp.pi**2*a4)+1/(32*mp.pi**2*a4)
    assert encloses(data["static_absolute_seed"]["trace_minus_plus_plus_plus"],trace)
    # Source stress from a geometrically normalized finite shell.
    x=sp.symbols("x",real=True)
    a2=3*sp.cos(2*x)
    f=sp.sqrt(3)*sp.sin(2*x)/2
    rho_s=(sp.diff(f,x)**2+8*f*f)/(2*a2)
    p_s=(sp.diff(f,x)**2-8*f*f/3)/(2*a2)
    assert sp.trigsimp(rho_s-(1/sp.cos(2*x)-sp.cos(2*x)/2))==0
    assert sp.trigsimp(p_s-(sp.Rational(5,6)*sp.cos(2*x)-1/(3*sp.cos(2*x))))==0
    zero_var_p=sp.Rational(3,2)
    zero_rho=zero_var_p/(4*sp.pi**2*a2**3)
    assert sp.simplify(zero_rho-3/(8*sp.pi**2*a2**3))==0
    return dict(independent_binomial_orders=J,residual_S=str(S),
        series_tail_upper=str(tail),rho_inside_B_interval=True,
        zero_mode_and_analytic_trace_inside_B_interval=True,
        shell_stress_symbolically_agrees=True,
        response_scope="same-radius formal first-order derivative, no finite remainder")


def apparatus():
    data=json.loads((CONT/"apparatus/result.json").read_text())
    I0=sum(F(2*(-1)**j*math.comb(12,j),2*j+1) for j in range(13))
    I2=sum(F(2*(-1)**j*math.comb(12,j),2*j+3) for j in range(13))
    c,e,h=F(33,50),F(1,100),F(1,10)
    mass=h*e*(c*c*I0+e*e*I2)
    assert I0==F(data["apparatus_profile"]["I0"])
    assert I2==F(data["apparatus_profile"]["I2"])
    assert mass==F(data["delta_GM"])
    bound=F(3,4)+2*mass/(c-e)
    assert bound==F(data["initial_global_2mu_over_R_upper"])<1
    r=c+e; f0=1-r*r/3
    ratio=f0/(f0-2*mass/r)
    assert encloses(data["initial_radial_metric_ratio_at_outer_edge"],q(ratio))
    chi=mp.asin(q(c-e)/mp.sqrt(3))
    assert encloses(data["inner_initial_chi_interval"],chi)
    margin=chi-mp.mpf(3)/8
    assert encloses(data["conformal_margin"],margin)
    proper=mp.quad(lambda x:mp.sqrt(3*mp.cos(2*x)),[mp.mpf(3)/8,chi])
    assert encloses(data["center_proper_margin"],proper)
    # Alternative high-precision polynomial antiderivative and proper-length integral.
    def integral(j,z):
        return sum((-1)**k*math.comb(12,k)
            *(z**(2*k+j+1)-mp.mpf(-1)**(2*k+j+1))/(2*k+j+1) for k in range(13))
    def length_delta(z):
        r=q(c)+q(e)*z
        dm=q(h)*q(e)*(q(c*c)*integral(0,z)+2*q(c*e)*integral(1,z)
            +q(e*e)*integral(2,z))
        f=1-r*r/3
        return q(e)*(1/mp.sqrt(f-2*dm/r)-1/mp.sqrt(f))
    length=mp.quad(length_delta,[-1,0,1])
    assert encloses(data["proper_shell_thickness_increment"],length)
    assert F(data["local_transfer"]["stiff_minus_dust_phi3"])==3*h
    assert F(data["local_transfer"]["difference_cubic_coefficient"])==h/2
    return dict(exact_mass=str(mass),exact_compactness_upper=str(bound),
        chi=str(chi),proper_margin=str(proper),proper_thickness_increment=str(length),
        all_independent_values_inside_C_bounds=True,
        pressure_counterexample_order="third derivative only; finite-time errors remain open")


def main():
    paths=[CONT/"quantum/README.md",CONT/"quantum/minimal_response.py",
           CONT/"quantum/result.json",CONT/"apparatus/README.md",
           CONT/"apparatus/shell.py",CONT/"apparatus/result.json"]
    return dict(review="A_independent_B_C",inputs_sha256={str(p.relative_to(CONT)):
        hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        B=quantum(),C=apparatus())


if __name__=="__main__":
    if not __debug__:raise RuntimeError("enable assertions")
    p=argparse.ArgumentParser();p.add_argument("--check",action="store_true")
    args=p.parse_args();result=main()
    if args.check:
        old=json.loads((HERE/"review_bc.json").read_text())
        assert result==old,"review inputs or independent exact/high-precision result changed"
        print("A review B/C PASS: alternative binomial-series seed and exact/independent shell integration")
    else:print(json.dumps(result,indent=2),end="\n")
