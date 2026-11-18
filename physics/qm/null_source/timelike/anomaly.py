"""A conformal quantum stress fed back into the original closed FLRW core."""
from fractions import Fraction as Fr
import json
import math

from mpmath import iv
import sympy as s

iv.dps=42


def q(x):
    v=Fr(x)
    return iv.mpf(v.numerator)/v.denominator


def interval(x):
    # Twelve decimal places, rounded out. Verify the display encloses the interval.
    size=10**12
    lo,hi=math.floor(float(x.a)*size)-1,math.ceil(float(x.b)*size)+1
    assert q(Fr(lo,size)) < x and q(Fr(hi,size)) > x
    return [lo/size,hi/size]


def identities():
    t=s.symbols("t")
    a=s.Function("a")(t)
    H=a.diff(t)/a
    F=H**2+1/a**2
    accel=a.diff(t,2)/a
    R=6*(F+accel)
    E4=24*F*accel
    boxR=-R.diff(t,2)-3*H*R.diff(t)
    Y=H*R.diff(t)+R*F-R**2/12
    assert s.simplify((a**4*6*F**2).diff(t)-a**4*H*E4)==0
    assert s.simplify((a**4*Y).diff(t)+a**4*H*boxR)==0
    # Four epochs of the original scalar solution; remove all trace shifts 1,R,Box R.
    xs=[s.Integer(1),s.Rational(25,24),s.Rational(13,12),s.Rational(9,8)]
    design=s.Matrix([[1,-2*x**3,24*x**6-16*x**4] for x in xs])
    w=design.T.nullspace()[0]
    w=w/sum(abs(v) for v in w)
    signal=sum(v*s.Rational(8,3)*x**6 for v,x in zip(w,xs))
    assert signal!=0 and design.T*w==s.zeros(3,1)
    return dict(weights=[str(v) for v in w],signed_invariant=str(signal),
                trace_gap=float(signal/(2880*s.pi**2)))


K=q(Fr(2,3))
P=3*iv.sqrt(3)
SCALAR=1/(360*16*iv.pi**2)
RATIOS=[Fr('0.99'),Fr('0.97'),Fr('0.94')]


def epoch(ratio, count, dust=0):
    a=iv.sqrt(3)*q(ratio)
    pi=P/a**3
    source=K*(pi**2/2+q(dust)/a**3)
    c=6*K*SCALAR*count
    F=2*source/(1+iv.sqrt(1-4*c*source))
    H=-iv.sqrt(F-1/a**2)
    assert 0 in F-c*F**2-source
    return a,H,pi


def line(row):
    err=iv.mpf([-1,1])*q('1e-8')
    a,H,pi=(v+err for v in row)
    F=H**2+1/a**2
    return a**4*F**2,a**4*(F/K-pi**2/2)


def infer(dust):
    (x1,d1),(x2,d2),(x3,d3)=[line(epoch(r,1,dust)) for r in RATIOS]
    assert x2>x1
    slope=(d2-d1)/(x2-x1)
    C=d1-slope*x1
    held=d3-(d1+slope*(x3-x1))
    if dust:
        assert 0 not in held
    else:
        assert 0 in C and 0 in held and 1 in slope/(6*SCALAR) and 0 not in slope
    return dict(scalar_equivalent_count=interval(slope/(6*SCALAR)),radiation=interval(C),
                held_residual=interval(held))


def elapsed(count):
    c=6*K*SCALAR*count
    at2=(c+iv.sqrt(c*c+36))/2  # at H=0, at^4 - c at² = k P²/2=9
    aend=iv.sqrt(3)*q(RATIOS[-1])
    end=iv.sqrt(1-aend**2/at2)
    tau=eta=q(0)
    for j in range(512):
        u=end*iv.mpf([j,j+1])/512
        a2=at2*(1-u**2)
        src=9/a2**3
        F=2*src/(1+iv.sqrt(1-4*c*src))
        h=iv.sqrt(at2*(at2+a2-c)/(a2**3*(1-c*(F+1/a2))))
        dt=end/(512*(1-u**2)*h)
        tau+=dt
        eta+=dt/iv.sqrt(a2)
    assert eta+q(Fr(1,8))<q(Fr(3,5))
    assert iv.sqrt(at2)*iv.sin(q(Fr(3,5)))<1  # interior radius at start
    return dict(initial_curvature_radius=interval(iv.sqrt(at2)),target_proper_time=interval(tau),
                target_conformal_time=interval(eta))


def main():
    qrate=epoch(RATIOS[-1],1)[1]
    classical=epoch(RATIOS[-1],0)[1]
    assert qrate<classical
    return dict(trace_contrast=identities(),same_momentum="3 sqrt(3)",counts_one_conformal_scalar=infer(0),
                unmodeled_dust=infer('0.01'),zero_field=elapsed(0),one_field=elapsed(1),
                final_H_classical=interval(classical),final_H_with_field=interval(qrate),
                final_H_change=interval(qrate-classical))


if __name__=="__main__":
    print(json.dumps(main(),indent=2))
