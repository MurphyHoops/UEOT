"""Rational elementary enclosures used by the synthetic calibration analyzer.

All comparisons used for certification are Fraction/integer calculations.
Floating conversion is presentation only.
"""
from fractions import Fraction as F
from functools import lru_cache
from math import isqrt, factorial


def sqrt_interval(x, digits=30):
    x=F(x)
    if x<0:raise ValueError("negative square root")
    den=10**digits
    k=isqrt(x.numerator*den*den//x.denominator)
    lo=F(k,den);hi=lo if lo*lo==x else F(k+1,den)
    assert lo*lo<=x<=hi*hi
    return lo,hi


def atan_interval(x, terms=40):
    x=F(x)
    assert 0<x<1
    values=[(-1)**j*x**(2*j+1)/F(2*j+1) for j in range(terms+1)]
    s=sum(values[:-1],F(0)); t=s+values[-1]
    return min(s,t),max(s,t)


@lru_cache(maxsize=1)
def pi_interval():
    # Machin's identity follows from tangent addition with all angles in
    # (0,pi/2); alternating arctangent remainders give rational brackets.
    a,b=atan_interval(F(1,5));c,d=atan_interval(F(1,239))
    lo,hi=16*a-4*d,16*b-4*c
    assert F(3)<lo<hi<F(22,7)
    return lo,hi


@lru_cache(maxsize=1024)
def normal_half_axis_probability(x):
    """Enclose Phi(2*x), for |x|<=1/4, by an alternating Gaussian integral."""
    x=F(x)
    if x<0:
        lo,hi=normal_half_axis_probability(-x)
        return 1-hi,1-lo
    if x==0:return F(1,2),F(1,2)
    if x>F(1,4):raise ValueError("certified implementation domain |x|<=1/4")
    # Integral_0^x exp(-2t^2)dt; the term ratios are <1 in this domain.
    terms=[(-2)**j*x**(2*j+1)/F(factorial(j)*(2*j+1)) for j in range(25)]
    a=sum(terms[:24],F(0));b=a+terms[24]
    ilo,ihi=min(a,b),max(a,b)
    plo,phi=pi_interval()
    clo=sqrt_interval(2/phi)[0];chi=sqrt_interval(2/plo)[1]
    return F(1,2)+clo*ilo,F(1,2)+chi*ihi


def inverse_probability_interval(p, width=F(1,10**10)):
    """Outer bracket for the unique x with Phi(2x)=p.

    This computational range is not silently made into a physical prior.
    If it cannot cover p, the analyzer returns no certificate.
    """
    p=F(p)
    lo,hi=F(-1,4),F(1,4)
    if normal_half_axis_probability(lo)[1]>p or normal_half_axis_probability(hi)[0]<p:
        raise ValueError("inverse outside certified computational bracket")
    while hi-lo>width:
        m=(lo+hi)/2;ml,mh=normal_half_axis_probability(m)
        if mh<p:lo=m
        elif ml>p:hi=m
        else:
            # The probability enclosure is far narrower than the requested
            # inverse precision; bracket adjacent points rigorously instead.
            half=width/2
            if m-half>=lo and m+half<=hi and normal_half_axis_probability(m-half)[1]<=p and normal_half_axis_probability(m+half)[0]>=p:
                return m-half,m+half
            raise ArithmeticError("insufficient probability precision")
    return lo,hi


def exp_negative_upper(x, terms=60):
    """e^-x <= inverse of a positive partial exponential sum."""
    x=F(x)
    assert x>=0
    return 1/sum((x**j/F(factorial(j)) for j in range(terms)),F(0))


def galerkin_interval(n,l,exposure):
    """Paper finite-Duhamel bound min(1,2*c_(l+1)); exact radicand."""
    x=abs(F(exposure));j=l+1
    p=1
    for k in range(1,j+1):p*=n+2*k-1
    squared=4*x**(2*j)*p/F(factorial(j)**2)
    lo,hi=sqrt_interval(squared)
    return min(F(1),lo),min(F(1),hi)
