"""Exact non-Gaussian cumulants: all 16^4 ordered shell words, no Fock truncation."""
from itertools import product
from fractions import Fraction as F
from math import factorial
import sympy as sp
from common import finish
d=4
# Unnormalized monomial kets have norm product(n!).
# |A_sign> = sum sign_r |2_r> / 4; the vector is exactly normalized.
vac=(0,)*8
seeds=[]
for j in range(8):
    occ=[0]*8;occ[j]=2;seeds.append(tuple(occ))
norms={vac:1,**{x:2 for x in seeds}}
assert sum(F(2,16) for _ in seeds)==1
ops=list(product((0,1),range(8)))  # 0 annihilation, 1 creation

def act(word,occ):
    occ=list(occ);coef=1
    for create,j in reversed(word):
        if create:
            occ[j]+=1
        else:
            coef*=occ[j]
            if not coef:return 0,None
            occ[j]-=1
    return coef,tuple(occ)

def moments(word):
    coef,out=act(word,vac)
    v=coef if out==vac else 0
    plus=0;minus=0
    for j,occ in enumerate(seeds):
        coef,out=act(word,occ)
        if coef and out in norms and out!=vac:
            k=out.index(2)
            plus+=coef*2
            sj=1 if j<4 else -1
            sk=1 if k<4 else -1
            minus+=coef*2*sj*sk
    return F(v),F(plus,16),F(minus,16)

def twopoint(a,b,p):
    if a[1]!=b[1] or a[0]==b[0]:return F(0)
    return p/d+(1 if a[0]==0 else 0)

pvals=[F(0),F(1,7),F(2,5)]
count=0
for word in product(ops,repeat=4):
    v,ep,em=moments(word)
    creates=[o[1] for o in word if o[0]]
    annih=[o[1] for o in word if not o[0]]
    for sign,pure in ((1,ep),(-1,em)):
        for p in pvals:
            raw=(1-p)*v+p*pure
            a,b,c,e=word
            wick=(twopoint(a,b,p)*twopoint(c,e,p)
                 +twopoint(a,c,p)*twopoint(b,e,p)
                 +twopoint(a,e,p)*twopoint(b,c,p))
            expected=F(0)
            if len(creates)==len(annih)==2:
                r,s=creates;t,u=annih
                sr=1 if r<4 else sign
                st=1 if t<4 else sign
                expected=(p/d*sr*st*(r==s)*(t==u)
                    -(p/d)**2*((r==t)*(s==u)+(r==u)*(s==t)))
            assert raw-wick==expected,(word,sign,p,raw-wick,expected)
    count+=1
assert count==16**4
# Radial and cross-state energy covariance, with no independence substitution.
p,ep,sig,mu2,Ez,A=sp.symbols("p epsilon sigma mu2 Ez A",positive=True)
varN=4*p*(1-p)
varHz=sig**2*mu2+ep**2*varN
cov=-ep*varN
correct=sp.expand(varHz+ep**2*varN+2*ep*cov)
wrong=sp.expand(varHz+ep**2*varN)
assert sp.simplify(correct-sig**2*mu2)==0
assert sp.simplify(wrong-correct-8*p*(1-p)*ep**2)==0
e2=Ez-2*(1-p)*ep
mixed=sp.expand(A**3*(p/d)*(e2-Ez))
assert sp.simplify(mixed+2*A**3*ep*p*(1-p)/d)==0
# The normal-order pair moments independently reconstruct the collective noise.
for sign in (1,-1):
    p0=F(1,7);Ada=F(0);AAda=F(0)
    for i,j in product(range(8),repeat=2):
        w=((1,i),(1,i),(0,j),(0,j))
        m0,mp,mm=moments(w);pure=mp if sign==1 else mm
        Ada+=(1-p0)*m0+p0*pure
        w=((0,i),(0,i),(1,j),(1,j))
        m0,mp,mm=moments(w);pure=mp if sign==1 else mm
        AAda+=(1-p0)*m0+p0*pure
    assert Ada==(16*p0 if sign==1 else 0)
    assert AAda-Ada==16+8*p0
    assert AAda+Ada==16+(24+16*sign)*p0
assert (16+(24+16)*F(1,7))-(16+(24-16)*F(1,7))==32*F(1,7)
# Check exact KG conservation of complex pair coefficients without solving an ODE.
a,h,v,r,om,V0=sp.symbols("a h v r omega V0",nonzero=True)
Br=(r*r+om*om*v*v)/(2*V0*a**4)
Bp=(r*r-om*om*v*v/3)/(2*V0*a**4)
def deriv(f):
    return sp.diff(f,a)*h*a+sp.diff(f,v)*(r+h*v)+sp.diff(f,r)*(-h*r-om*om*v)
assert sp.simplify(deriv(Br)+3*h*(Br+Bp))==0
assert sp.simplify(Br-Bp-2*om**2*v**2/(3*V0*a**4))==0
finish("tensor_noise.py",{
    "ordered_shell_words_exactly_checked":count,
    "independent_NOON_signs_checked":2,
    "probability_polynomial_interpolation_points":[str(x) for x in pvals],
    "arbitrary_occupation_word_action_no_Fock_cutoff":True,
    "zero_radial_fourth_and_zero_shell_cumulants_retained":True,
    "wrong_independence_variance_excess":"8*p*(1-p)*epsilon^2",
    "Gaussian_low_mode_replacement_detectably_wrong":True,
    "collective_pair_noise_coefficients":["16+40p","16+8p"],
    "full_tensor_difference_coefficient":"32p",
    "same_direction_Hadamard_products_not_absolute_square":True,
    "full_absolute_source_tensor_noise_explicit_bidistr":True,
    "pointwise_or_sharp_time_noise_value_claimed":False,
    "mode_Ward_checked_without_ODE":True,
    "general_tensor_cutoff_numeric_constants_all_computed":False,
    "finite_scalar_harmonic_tail_domain":"K>=2L+4",
    "full_retarded_contact_extension_constructed":False
},["finite_stress/BOUNDARY_STATE.md","finite_stress/DYNAMIC_CHARGE.md",
    "nonlinear_history/KERNELS.md"])
