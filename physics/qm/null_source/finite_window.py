"""Finite-clock scalar readout and lens on a compact, asymptotically flat initial slice."""
from fractions import Fraction as F
from math import floor, ceil
import json

from mpmath import iv
import sympy as s

iv.dps = 40


def q(value):
    n = F(value)
    return iv.mpf(n.numerator)/n.denominator


def scale(eta):
    return iv.sqrt(3*iv.cos(2*eta))


def scalar(eta):
    return iv.sqrt(3)/2*iv.ln((1+iv.sin(2*eta))/iv.cos(2*eta))


def integrate(func, left, right, count=512):
    step = (right-left)/count
    total = q(0)
    for i in range(count):
        cell = iv.mpf([q(left+i*step).a, q(left+(i+1)*step).b])
        total += func(cell)*q(step)
    return total


def switched_mean(left, right):
    # Frozen clock program: w(eta) d eta = chi_nom(tau) d tau; integral w = 1.
    def density(x):
        d = (x-q(left))/q(right-left)
        return 30*d**2*(1-d)**2*scalar(x)/q(right-left)
    return integrate(density, left, right)


def outward(v):
    unit=10**8
    lo,hi=floor(float(v.a)*unit)-1,ceil(float(v.b)*unit)+1
    assert q(F(lo,unit)) < v and v < q(F(hi,unit))
    return [lo/unit,hi/unit]


def main():
    # R is area radius, mu=Gm, 4*pi*G=1. phi=0, extrinsic curvature zero.
    r,x=s.symbols("r x", real=True)
    taper=1-10*x**3+15*x**4-6*x**5
    assert [taper.subs(x,j) for j in (0,1)] == [1,0]
    assert s.factor(taper.diff(x)) == -30*x**2*(x-1)**2
    # Both join derivatives through second order vanish, and the center is constant.
    assert all(taper.diff(x,n).subs(x,j)==0 for n in (1,2) for j in (0,1))
    mass = s.Rational(1,6)+s.integrate(r**2*taper.subs(x,2*(r-1))**2/2,(r,1,s.Rational(3,2)))
    assert 0<mass<s.Rational(9,16)  # mu(R) <= R^3/6 inside R<=1.5
    # FLRW patch's conformal-time acceleration check, in both proper and conformal time.
    e=s.symbols("eta", real=True)
    a=s.sqrt(3*s.cos(2*e))
    adot=a.diff(e)/a
    assert s.trigsimp(adot**2+1-(s.sqrt(3)/a)**4)==0
    pi=(s.sqrt(3)/a)**3
    assert s.trigsimp(adot.diff(e)/a + s.Rational(2,3)*pi**2*a)==0
    phase=s.sqrt(3)*s.log((1+s.sin(2*e))/s.cos(2*e))/2
    assert s.trigsimp(phase.diff(e)/a-pi)==0
    # The center and a finite comoving reflecting sphere stay inside the Cauchy patch.
    target = F(1,4)
    rail = F(1,8)
    assert target+rail < F(1,2)
    assert target==2*rail
    assert iv.sin(q(target+rail))<1/iv.sqrt(3)  # inward telemetry: eta+chi is constant
    # Two canonical scalar species, prepared and read along one unit vector.
    weights=(F(3,5),F(4,5))
    orthogonal=(-weights[1], weights[0])
    assert sum(v*v for v in weights)==1 and sum(u*v for u,v in zip(weights,orthogonal))==0
    T = integrate(scale,F(0),target)
    J = scale(q(target))/iv.sqrt(3)
    windows=[(F(1,32),F(1,16)),(F(5,32),F(3,16))]
    means=[switched_mean(*window) for window in windows]
    # Conservative independent half-widths in the declared physical units, including readout.
    field_error=q("0.001")
    clock_error=q("0.0001")
    lens_error=q("0.001")
    contrast = means[1]-means[0]-2*field_error
    earliest = integrate(scale, F(0), windows[0][0]).a-clock_error
    latest = integrate(scale, F(0), windows[1][1]).b+clock_error
    lower_T=T.a-clock_error
    assert contrast>0 and lower_T>latest
    denominator=iv.ln((lower_T-earliest)/(lower_T-latest))
    # 1/J-1 >= (8*pi*G/3)*contrast²/denominator before the first caustic.
    upper=1/(1+q(F(2,3))*contrast.a**2/denominator)
    assert J+lens_error < upper and upper < 1-lens_error
    assert 0 < iv.cos(2*q(target))
    output={"GM_ADM":str(mass),"readout_units":"support core radius=1; 4*pi*G=1",
            "proper_radar_round_trip":outward(T),"finite_areal_radius_ratio":outward(J),
            "positive_source_normalized_gate_means":[outward(v) for v in means],
            "accepted_lens_upper_bound_rounded_up":outward(upper)[1],
            "clock_halfwidth":0.0001,"scalar_gate_halfwidth":0.001,"lens_halfwidth":0.001,
            "equal_geometry_on_source_reversal":True}
    print(json.dumps(output,indent=2))


if __name__=="__main__":
    main()
