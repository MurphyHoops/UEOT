"""Independent interval evaluation of Bell-input terminal event probabilities.

This implements the Gaussian history-pair formula with exact rational timing,
algebraic control matrices and mpmath interval arithmetic. It does not call the
floating Weyl or Galerkin implementations. It is not an all-input Choi proof.
"""
from __future__ import annotations
import itertools
from fractions import Fraction
from functools import lru_cache
from mpmath import iv
from common_c import outward_fraction

iv.dps = 50

def q(x):
    x=Fraction(str(x)) if not isinstance(x,Fraction) else x
    return iv.mpf(x.numerator)/x.denominator

def mm(a,b):
    return [[sum(a[i][k]*b[k][j] for k in range(len(b))) for j in range(len(b[0]))] for i in range(len(a))]

def conj(x):
    return x.real-I*x.imag

def inner(x,y):
    return sum(conj(a)*b for a,b in zip(x,y))

def real(x):
    return x.real

def imag(x):
    return x.imag

I=iv.mpc(0,1)
IDENT=[[q(1),q(0)],[q(0),q(1)]]
Z=[[q(1),q(0)],[q(0),q(-1)]]
X=[[q(0),q(1)],[q(1),q(0)]]
Y=[[q(0),-I],[I,q(0)]]
PAULI={"X":X,"Y":Y,"Z":Z,"I":IDENT}
PROJECT=[[[q(1),q(0)],[q(0),q(0)]],[[q(0),q(0)],[q(0),q(1)]]]
FAIL=[[iv.sqrt(q("1/8")),q(0)],[q(0),q("1/2")]]
PASS=[[iv.sqrt(q("7/8")),q(0)],[q(0),iv.sqrt(q("3/4"))]]
ROTATIONS=[[[iv.sqrt(q("1/2")),-iv.sqrt(q("1/2"))],[iv.sqrt(q("1/2")),iv.sqrt(q("1/2"))]],
           [[iv.sqrt(q("3/4")),-I/2],[-I/2,iv.sqrt(q("3/4"))]],IDENT]

def kron(a,b):
    return [[a[i//2][j//2]*b[i%2][j%2] for j in range(4)] for i in range(4)]

def mv(a,v):
    return [sum(x*y for x,y in zip(row,v)) for row in a]

def bath_path(times,indices):
    beta=[iv.mpc(0),iv.mpc(0)]; phase=q(0)
    for t,index in zip(times,indices):
        sign=1-2*index
        for mode,(omega,c) in enumerate((("1","1"),("3/2","3/5"))):
            omega=q(omega); c=q(c); tt=q(t)
            rot=iv.exp(-I*omega*tt)
            displaced=sign*c/omega*(rot-1)
            rotated=rot*beta[mode]
            phase+=(c/omega)**2*(omega*tt-iv.sin(omega*tt))+imag(conj(rotated)*displaced)
            beta[mode]=rotated+displaced
    return beta,phase

@lru_cache(maxsize=4)
def prepare(times):
    """All coefficients below are independent of lambda and detector eta."""
    result={}
    observables=[kron(PAULI[a],PAULI[b]) for a,b in ("XX","XY","YZ","ZZ")]
    for stop in range(4):
        count=min(stop+1,3)
        record="p"*stop+"f" if stop<3 else "ppp"
        ks=[mm(ROTATIONS[j],PASS) for j in range(stop)] + ([FAIL] if stop<3 else [])
        hs=[]
        for indices in itertools.product((0,1),repeat=count):
            a=IDENT
            for k,index in zip(ks,indices):
                a=mm(mm(k,PROJECT[index]),a)
            vec=[a[i][j] for i in range(2) for j in range(2)]
            beta,phase=bath_path(times[:count],indices)
            hs.append((vec,beta,phase))
        diag=[q(0) for _ in range(5)]
        pairs=[]
        for j,(v,b,p) in enumerate(hs):
            diag[0]+=real(inner(v,v))/2
            for k,obs in enumerate(observables):
                diag[k+1]+=real(inner(v,mv(obs,v)))/2
            for vp,bp,pp in hs[j+1:]:
                exponent=I*(p-pp)-(real(inner(b,b))+real(inner(bp,bp)))/2+inner(bp,b)
                coeff=[inner(vp,v)/2]+[inner(vp,mv(obs,v))/2 for obs in observables]
                pairs.append((exponent,coeff))
        result[record]=(diag,pairs)
    return result

def moments(lam,times):
    result={}
    lam2=q(lam)**2
    for record,(diag,pairs) in prepare(tuple(str(t) for t in times)).items():
        values=list(diag)
        for exponent,coeffs in pairs:
            influence=iv.exp(lam2*exponent)
            for j,c in enumerate(coeffs):
                values[j]+=2*real(influence*c)
        result[record]=values
    return result

def probabilities(lam,eta,times):
    moment=moments(lam,times); eta=q(eta)
    result={name:[] for name in ("XX","XY","YZ","ZZ")}
    for record in ("f","pf","ppf","ppp"):
        values=moment[record]
        for j,name in enumerate(result):
            for sign in (-1,1):
                result[name].append((values[0]+sign*eta*values[j+1])/2)
    return result

def probability_bounds(lam,eta,times,digits=12):
    return {name:[[outward_fraction(p,False,digits),outward_fraction(p,True,digits)] for p in values]
            for name,values in probabilities(lam,eta,times).items()}
