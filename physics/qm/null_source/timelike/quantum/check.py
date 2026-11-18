"""Outward integral bounds on the baseline core and a finite pp-wave diamond; no network."""
from fractions import Fraction
import hashlib
import json
from pathlib import Path

import sympy as s
from mpmath import iv

iv.dps=39
HERE=Path(__file__).resolve().parent
BASE="7437bd1dec7e84d229c015009b07d698d9739af8"
N=2048


def I(v):
    x=Fraction(v)
    return iv.mpf(x.numerator)/x.denominator


def cell(a,b):
    return iv.mpf([a.a,b.b])


def endpoints(x):
    def dyad(t):
        sign, man, exp, _=t
        return (-1)**sign*man*Fraction(2)**exp
    scale=10**10
    lo,hi=map(dyad,x._mpi_)
    return [f"{v//scale}.{v%scale:010d}" if v>=0 else f"-{(-v)//scale}.{(-v)%scale:010d}"
            for v in ((lo*scale).__floor__(),(hi*scale).__ceil__())]


def algebra():
    # Half-frequency QSEI integral; two-sided Parseval for a real test accounts for pi.
    k,L=s.symbols("k L",positive=True)
    assert s.integrate(k**3,(k,0,L))/(4*s.pi**3)==L**4/(16*s.pi**3)
    t=s.symbols("t",real=True)
    gauss=s.exp(-t**2/2)
    gaussian_Q=s.integrate(s.diff(gauss,t,2)**2,(t,-s.oo,s.oo))/(16*s.pi**2)
    spectral_Q=s.integrate(2*s.pi*k**4*s.exp(-k**2),(k,0,s.oo))/(16*s.pi**3)
    assert gaussian_Q==spectral_Q==3/(64*s.pi**s.Rational(3,2))
    # Dirichlet Jacobi propagator B(s/2,-s/2)/s through s^4 by Volterra iteration.
    x,y=s.symbols("x y")
    moment=lambda h:s.integrate(x*(1-x)*h,(x,0,1))
    nested=s.integrate((1-x)*s.integrate((x-y)*y,(y,0,x)),(x,0,1))
    assert (moment(1), moment((x-s.Rational(1,2))**2)/2,nested)==(
        s.Rational(1,6),s.Rational(1,240),s.Rational(1,120))
    K,Kpp,d=s.symbols("K Kpp d")
    b=1-K*d**2/6+(K**2/120-Kpp/240)*d**4
    coef=s.series(1/b,d,0,6).removeO().expand().coeff(d,4)
    assert s.simplify(2*coef-Kpp/24-(7*K**2/180-Kpp/30))==0
    # n=2 homogeneous isotropic shell: time profile sin(2 eta) solves minimal KG.
    t=s.symbols("t")
    a=s.sqrt(3*s.cos(2*t))
    mode=s.sin(2*t)
    assert s.trigsimp(s.diff(mode,t,2)+2*s.diff(a,t)/a*s.diff(mode,t)+8*mode)==0
    assert s.trigsimp((s.diff(mode,t)*s.sqrt(3)/(2*a))**2-s.cos(2*t))==0


def plane_curvature():
    # Independent Brinkmann calculation. All components are checked for arbitrary K(u).
    u,v,x,y=coords=s.symbols("u v x y",real=True)
    K=s.Function("K")(u)
    metric=s.Matrix([[-K*(x*x+y*y),-1,0,0],[-1,0,0,0],[0,0,1,0],[0,0,0,1]])
    inv=metric.inv()
    idx=range(4)
    def christ(a,b,c):
        return sum(inv[a,d]*(s.diff(metric[c,d],coords[b])+s.diff(metric[b,d],coords[c])
                           -s.diff(metric[b,c],coords[d])) for d in idx)/2
    G={(a,b,c):christ(a,b,c) for a in idx for b in idx for c in idx}
    assert all(G[0,a,b]==G[a,b,1]==0 for a in idx for b in idx)
    ric=s.Matrix(4,4,lambda b,c:sum(
        s.diff(G[a,b,c],coords[a])-s.diff(G[a,b,a],coords[c])
        +sum(G[a,a,d]*G[d,b,c]-G[a,c,d]*G[d,b,a] for d in idx) for a in idx))
    ell=s.Matrix([1,0,0,0])
    assert ric==2*K*ell*ell.T and inv*ell==s.Matrix([0,-1,0,0])
    h=s.Function("h")(u)
    dh=s.Matrix([s.diff(h,z) for z in coords])
    assert (dh.T*inv*dh)[0]==0 and dh*dh.T==s.diff(h,u)**2*ell*ell.T
    assert sum(s.diff(inv[i,j]*dh[j],coords[i]) for i in idx for j in idx)==0


def bump(x):
    z=1/(1-x*x)
    return iv.exp(1-z)


def derivatives(x):
    z=1/(1-x*x)
    b=iv.exp(1-z)
    l1=-2*x*z**2
    l2=-2*z**2-8*x*x*z**3
    l3=-24*x*z**3-48*x**3*z**4
    l4=-24*z**3-288*x*x*z**4-384*x**4*z**5
    return (b*l1,b*(l1**2+l2),b*(l1**3+3*l1*l2+l3),
            b*(l1**4+6*l1**2*l2+3*l2**2+4*l1*l3+l4))


def pp_density(t):
    f1,f2,f3,_=derivatives(t)
    K=f1**2/16
    Kpp=(f2**2+f1*f3)/8
    return (7*K**2/180-Kpp/30)/(4*iv.pi**2)


def pp_bound():
    # g(t)=bump(2t). Evenness and x=2t give integrals on the positive unit interval.
    cutoff=I("63/64")
    step=cutoff/N
    flat=curv=I(0)
    for j in range(N):
        x=cell(j*step,(j+1)*step)
        _,f2,f3,f4=derivatives(x)
        mid=(2*j+1)*step/2
        # Integral midpoint error has a positive Peano kernel with mass step^3/24.
        flat+=(step*derivatives(mid)[1]**2+step**3*(f3**2+f2*f4)/12)/iv.pi**2
        curv+=step*bump(x)**2*pp_density(x/2)
    # z>=32 in the endpoint cell; z^4 exp(1-z) decreases there.
    positive=iv.mpf([0,1])
    flat+=(1-cutoff)*positive*(14*32**4*iv.exp(-31))**2/iv.pi**2
    curv+=(1-cutoff)*positive*iv.exp(-62)*pp_density(cell(cutoff,I(1))/2)
    assert flat>0 and curv<0 and flat+curv>0 and (flat+curv).b < flat.a
    return dict(flat_Q=endpoints(flat),curved_Q_minus_flat_Q=endpoints(curv),curved_Q=endpoints(flat+curv))


def core():
    # g(tau(eta))=bump(8 eta-1), 0<eta<1/4. Endpoint enclosures use monotonicity.
    b=varzero=shell=I(0)
    step=I(1)/(4*N)
    for j in range(N):
        lo,hi=j*step,(j+1)*step
        u=abs(8*cell(lo,hi)-1)
        low=I(0) if j in (0,N-1) else bump(u.b)
        high=bump(u.a)
        measure=step*cell(low,high)**2*iv.sqrt(3)
        c=iv.cos(2*cell(lo,hi))
        b+=measure*iv.sqrt(c)
        varzero+=measure/(c**2*iv.sqrt(c))
        shell+=measure*c*iv.sqrt(c)
    inputs=HERE.parents[1]/"finite_window_result.json"
    raw=inputs.read_bytes()
    assert hashlib.sha256(raw).hexdigest()=="ca04d07513090c8bdc7397e7895c71d2b39fe48735176fd6d86c6bc313cc00e5"
    data=json.loads(raw,parse_float=Fraction)
    first,second=data["positive_source_normalized_gate_means"]
    gap=I(second[0]-first[1]-2*data["scalar_gate_halfwidth"])
    # Gate supports after proper-time uncertainty are inside 0.030 <= eta <= 0.190.
    clock=I(data["clock_halfwidth"])
    assert clock < (I("1/32")-I(".030"))*iv.sqrt(3*iv.cos(I(".38")))
    assert clock < (I(".190")-I("3/16"))*iv.sqrt(3*iv.cos(I(".38")))
    gm=bump(I(".76"))
    upper=iv.sqrt(3)*I(".160")/gm**2
    assert gap>0
    lower=gap**2/upper
    # v0=2, v1=1/4 in initial normal derivative units. Same measured mean of shifted pair.
    relative=(1+I("1/4")-2)*varzero
    assert relative<0 and varzero>lower and lower>I(".01") and shell>0
    return dict(clock_padded_mean_square_lower=endpoints(lower)[0],
                integral_g2_dt=endpoints(b),unit_zero_mode_integral=endpoints(varzero),
                centered_v1_minus_v0=endpoints(-I("7/4")*varzero),
                unit_mean_v1_minus_centered_reference_v0=endpoints(relative),
                n2_unit_velocity_variance_shell=endpoints(shell),
                baseline_window_sha256=hashlib.sha256(raw).hexdigest())


if __name__=="__main__":
    if not __debug__:
        raise RuntimeError("assertions required")
    algebra()
    plane_curvature()
    print(json.dumps(dict(baseline=BASE,mesh=N,core=core(),pp_wave=pp_bound()),indent=2))
