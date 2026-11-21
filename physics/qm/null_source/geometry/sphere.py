"""Regular finite scalar initial slice, 4*pi*G=1. All checks use exact rationals."""
from fractions import Fraction as Q
from math import comb, isqrt
import json

import sympy as sp


def flux(r, amplitude):
    """-r² psi' for 0 <= r <= 1."""
    return amplitude**2*r**3*sum(Q((-1)**i*comb(8,i),2*i+3)*r**(2*i) for i in range(9))/4


def slice_at(r, amplitude):
    r,amplitude=Q(r),Q(amplitude)
    if r<0:
        raise ValueError("radius must be nonnegative")
    s=min(r,Q(1))
    z=flux(s,amplitude)
    outer=1+amplitude**2*(1-s*s)**9/72
    psi=outer+(z/r if r else 0)
    R=r*psi**2
    U=1-2*z/(r*psi) if r else Q(1)
    P=amplitude*(1-s*s)**4
    mass=R*(1-U**2)/2
    assert mass==2*z*outer
    return psi,R,U,P**2/psi**5,mass


def exact_check():
    r=sp.symbols("r",positive=True)
    a=sp.symbols("a",real=True)
    P=a*(1-r*r)**4
    z=flux(r,a)
    psi=sp.expand(1+z/r+a*a*(1-r*r)**9/72)
    assert sp.expand(sp.diff(r*r*sp.diff(psi,r),r)+r*r*P**2/4)==0
    assert sp.diff(psi,r).subs(r,0)==0
    q_inf=z.subs(r,1)
    assert sp.simplify(psi.subs(r,1)-1-q_inf)==0
    assert sp.simplify(sp.diff(psi,r).subs(r,1)+q_inf)==0
    # Matter integral from Pi, area and its radial change; evaluate without using m(R).
    integrand=sp.Poly(r*r*P**2*(psi+2*r*sp.diff(psi,r))/2,r)
    integral=integrand.integrate()
    def mass_between(lo,hi):
        return Q(integral.eval(hi).subs(a,1)-integral.eval(lo).subs(a,1))
    return mass_between


DR, DPI, DU = Q(1,10**7), Q(4,10**6), Q(1,10**5)
LIPSCHITZ = 4
BINS = 256


def readout(v):
    return Q(round(v*10**8),10**8)


def signed_readout(pi2,amplitude):
    scaled=pi2*10**16
    return (1 if amplitude>=0 else -1)*Q(isqrt(scaled.numerator//scaled.denominator),10**8)


def geometry_mass(R,U):
    # R is the measured area radius, U its independently measured proper-distance slope.
    assert R>DR and U>DU
    corners=[r*(1-u*u)/2 for r in (R-DR,R+DR) for u in (U-DU,U+DU)]
    return min(corners),max(corners)


def shell_witness(samples, endpoint_slopes):
    """Samples contain (area radius, signed normal derivative); slopes are withheld."""
    if len(samples)<2 or len(endpoint_slopes)!=2:
        raise ValueError("need at least two radii and both endpoint slopes")
    matter_lo=matter_hi=Q(0)
    for (r,s),(t,v) in zip(samples,samples[1:]):
        width=t-r+2*DR
        assert r>DR and t-r>2*DR
        uncertainty=(abs(s)+abs(v))*DPI+DPI**2+LIPSCHITZ*width/2
        avg=(s**2+v**2)/2
        lo=max(0,avg-uncertainty)
        hi=avg+uncertainty
        matter_lo+=lo*((t-DR)**3-(r+DR)**3)/6
        matter_hi+=hi*((t+DR)**3-(r-DR)**3)/6
    inner=geometry_mass(samples[0][0],endpoint_slopes[0])
    outer=geometry_mass(samples[-1][0],endpoint_slopes[1])
    return (matter_lo,matter_hi),(outer[0]-inner[1],outer[1]-inner[0])


def display(interval):
    # Outward decimal values encoded as exact fractions.
    a,b=(v*10**9 for v in interval)
    return [str(Q(a//1,10**9)),str(Q(-(-b//1),10**9))]


def calculate():
    mass_between=exact_check()
    lo,hi=Q(1,2),Q(3,4)
    expected=mass_between(lo,hi)
    states=[slice_at(lo+(hi-lo)*i/BINS,Q(1)) for i in range(BINS+1)]
    source=[(readout(R),signed_readout(pi2,1)) for _,R,_,pi2,_ in states]
    # Maximum of |d (1-r²)^8 / dr| is at 1/sqrt(15).
    assert Q(256,15)*Q(14,15)**14 < Q(11,4)**2 and (Q(11,4)+Q(5,12))*Q(6,5)<LIPSCHITZ
    slopes=[readout(states[i][2]) for i in (0,-1)]
    matter,geometry=shell_witness(source,slopes)
    negative=[(readout(R),signed_readout(pi2,-1)) for _,R,_,pi2,_ in states]
    assert negative==[(R,-p) for R,p in source] and source[0][1]>DPI
    assert shell_witness(negative,slopes)==(matter,geometry)
    assert matter[0]>0 and geometry[0]>0
    assert all(left<=expected<=right for left,right in (matter,geometry))
    assert expected==states[-1][-1]-states[0][-1]
    assert states[0][-1]==mass_between(0,lo)
    assert slice_at(Q(2),Q(1))[-1]==mass_between(hi,1)+states[-1][-1]==Q(16384,2078505)
    vacuum=[(R,Q(0)) for R,_ in source]  # same physical area radii
    vm,vg=shell_witness(vacuum,[Q(1),Q(1)])
    assert all(l<=0<=h for l,h in (vm,vg)) and vg[1]<matter[0] and vm[1]<geometry[0]
    for r in (Q(0),lo,hi,Q(1),Q(2)):
        assert slice_at(r,Q(-1))==slice_at(r,Q(1))
        assert slice_at(r,Q(0))==(1,r,1,0,0)
    return {"units":"support radius L=1, 4*pi*G=1; masses reported as Gm",
            "profile":"P=a(1-r²)^4 for r<1, zero outside; a=+1,-1,0",
            "psi_center":str(slice_at(Q(0),Q(1))[0]),
            "GM_ADM":str(mass_between(0,1)),
            "Gm_half":str(states[0][-1]),"Gm_three_quarters":str(states[-1][-1]),
            "held_exact_delta_Gm":str(expected),"radial_bins":BINS,
            "signed_Pi_inner_readouts":[str(source[0][1]),str(negative[0][1])],
            "held_matter":display(matter),"held_geometry":display(geometry),
            "vacuum_matter":display(vm),"vacuum_geometry":display(vg),
            "sign_reversal":"normal derivative flips; energy and geometry identical"}


if __name__=="__main__":
    print(json.dumps(calculate(),indent=2,ensure_ascii=False))
