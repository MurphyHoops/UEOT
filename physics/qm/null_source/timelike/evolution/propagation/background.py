"""Directed Taylor jets of the archived C-infinity preparation background.

Coefficients are derivatives divided by factorial. q_box returns actual
q derivatives. Endpoint caps are bounded analytically, not sampled.
"""
from fractions import Fraction as Q
from math import factorial
from mpmath import iv, mp

START, STOP = Q(-1,8), Q(-1,16)
CAP = Q(1,1024)
BREAKS = (START, START+CAP, STOP-CAP, STOP)
iv.dps = 65
mp.dps = 65


def I(x):
    if hasattr(x, '_mpi_'):
        return x
    if isinstance(x, mp.mpf):
        return iv.mpf(x)
    x = Q(str(x)) if isinstance(x,float) else Q(x)
    return iv.mpf(x.numerator)/x.denominator


def box(lo, hi):
    return iv.mpf([I(lo).a,I(hi).b])


def absmax(x):
    return max(abs(mp.make_mpf(x._mpi_[0])), abs(mp.make_mpf(x._mpi_[1])))


def upper(x):
    return mp.make_mpf(x._mpi_[1])


def lower(x):
    return mp.make_mpf(x._mpi_[0])


class Jet:
    def __init__(self,c):
        self.c=[I(x) for x in c]
        self.n=len(c)-1
    @classmethod
    def const(cls,x,n):
        return cls([x]+[0]*n)
    def coerce(self,x):
        return x if isinstance(x,Jet) else Jet.const(x,self.n)
    def __add__(self,x):
        x=self.coerce(x); assert x.n==self.n
        return Jet([a+b for a,b in zip(self.c,x.c)])
    __radd__=__add__
    def __neg__(self):
        return Jet([-x for x in self.c])
    def __sub__(self,x): return self+-self.coerce(x)
    def __rsub__(self,x): return self.coerce(x)+-self
    def __mul__(self,x):
        x=self.coerce(x); assert x.n==self.n
        return Jet([sum((self.c[j]*x.c[k-j] for j in range(k+1)),I(0)) for k in range(self.n+1)])
    __rmul__=__mul__
    def inverse(self):
        assert not (self.c[0].a<=0<=self.c[0].b)
        out=[1/self.c[0]]
        for k in range(1,self.n+1):
            out.append(-sum((self.c[j]*out[k-j] for j in range(1,k+1)),I(0))/self.c[0])
        return Jet(out)
    def __truediv__(self,x): return self*self.coerce(x).inverse()
    def __rtruediv__(self,x): return self.coerce(x)*self.inverse()
    def exp(self):
        out=[iv.exp(self.c[0])]
        for k in range(1,self.n+1):
            out.append(sum((j*self.c[j]*out[k-j] for j in range(1,k+1)),I(0))/k)
        return Jet(out)
    def sqrt(self):
        assert self.c[0]>0
        out=[iv.sqrt(self.c[0])]
        for k in range(1,self.n+1):
            out.append((self.c[k]-sum((out[j]*out[k-j] for j in range(1,k)),I(0)))/(2*out[0]))
        return Jet(out)
    def sincos(self):
        sn,cs=[iv.sin(self.c[0])],[iv.cos(self.c[0])]
        for k in range(1,self.n+1):
            sn.append(sum((j*self.c[j]*cs[k-j] for j in range(1,k+1)),I(0))/k)
            cs.append(-sum((j*self.c[j]*sn[k-j] for j in range(1,k+1)),I(0))/k)
        return Jet(sn),Jet(cs)
    def scaled(self,h):
        return Jet([v*I(h)**j for j,v in enumerate(self.c)])


def cap_step_bound(eps,order,right=False):
    """Bounds S derivatives in x on [0,eps], or [1-eps,1].

z=exp(-1/x+1/(1-x)). Each Bell monomial is bounded at eps:
its largest x pole is x^(-2n), and x^(-m)exp(-1/x) increases
on 0<x<=eps if 2n*eps<=1. Positive (1-x)^(-j) factors also
increase. Reciprocation uses 1+z>=1 and a derivative recurrence.
"""
    eps=Q(eps)
    assert 0<eps<=Q(1,64) and 2*order*eps<=1
    e=I(eps)
    z0=iv.exp(-1/e+1/(1-e))
    L=[I(0)]+[e**(-j-1)+(1-e)**(-j-1) for j in range(1,order+1)]
    bell=[I(1)]
    for n in range(1,order+1):
        bell.append(sum((j*L[j]*bell[n-j] for j in range(1,n+1)),I(0))/n)
    z=[z0*b for b in bell]
    inv=[I(1)]
    for n in range(1,order+1):
        inv.append(sum((z[j]*inv[n-j] for j in range(1,n+1)),I(0)))
    sb=[sum((z[j]*inv[n-j] for j in range(n+1)),I(0)) for n in range(order+1)]
    out=[box(lower(1-z0),1) if right else box(0,upper(z0))]
    out.extend(box(-upper(v),upper(v)) for v in sb[1:])
    return Jet(out).scaled(16)


def physical_jet(lo,hi,order):
    t=Jet([box(lo,hi),1]+[0]*(order-1)) if order else Jet([box(lo,hi)])
    return (3*(2*t).sincos()[1]).sqrt()


def derivative_box(lo,hi,order=6):
    """a^(j)/j! on a single phase cell; use BREAKS when building a mesh."""
    lo,hi=Q(lo),Q(hi)
    assert lo<=hi and order>=0
    if hi<=START:
        return Jet.const(iv.sqrt(3),order)
    if lo>=STOP:
        return physical_jet(lo,hi,order)
    assert START<=lo<=hi<=STOP
    target=physical_jet(lo,hi,order)
    a0=iv.sqrt(3)
    # A point in the open transition has nonsingular exact jets.
    if lo==hi and START<lo<STOP:
        t=Jet([I(lo),1]+[0]*(order-1)) if order else Jet([I(lo)])
        x=16*(t-START)
        if lo<=(START+STOP)/2:
            z=(-1/x+1/(1-x)).exp()
            step=z/(1+z)
        else:
            z=(1/x-1/(1-x)).exp()
            step=1/(1+z)
    elif hi<=START+CAP:
        step=cap_step_bound(16*(hi-START),order)
    elif lo>=STOP-CAP:
        step=cap_step_bound(16*(STOP-lo),order,right=True)
    else:
        assert lo>=START+CAP and hi<=STOP-CAP, 'split at flat-cap boundaries'
        t=Jet([box(lo,hi),1]+[0]*(order-1)) if order else Jet([box(lo,hi)])
        x=16*(t-START)
        # Choose a stable logistic branch; neither denominator can approach zero.
        if hi<=(START+STOP)/2:
            z=(-1/x+1/(1-x)).exp()
            step=z/(1+z)
        else:
            z=(1/x-1/(1-x)).exp()
            step=1/(1+z)
    return (target-a0)*step+a0


def q_box(lo,hi,order=4):
    """Actual q^(j), j=0..order, q=-1-a''/a, with directed intervals."""
    lo,hi=Q(lo),Q(hi)
    if hi<=START:
        return [I(-1)]+[I(0)]*order
    if lo>=STOP:
        t=Jet([box(lo,hi),1]+[0]*(order-1)) if order else Jet([box(lo,hi)])
        cosine=(2*t).sincos()[1]
        q=cosine.inverse()*cosine.inverse()
        return [v*factorial(j) for j,v in enumerate(q.c)]
    a=derivative_box(lo,hi,order+2)
    aa=Jet(a.c[:order+1])
    second=Jet([(j+1)*(j+2)*a.c[j+2] for j in range(order+1)])
    q=-1-second/aa
    return [v*factorial(j) for j,v in enumerate(q.c)]


def coefficients(lo,hi,order,step):
    a=derivative_box(lo,hi,order).scaled(step)
    c=a*a
    return a,c,c.inverse()
