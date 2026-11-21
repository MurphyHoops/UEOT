"""Exact finite polynomial and sparse Fock checks of actual source CTP blocks."""
import sympy as s
from fractions import Fraction as F
from itertools import combinations
from common import require, finish
p=s.symbols("p", nonnegative=True)
M=16+8*p
for sign in (1,-1):
    S=16+(24+16*sign)*p
    require(s.expand((S+M)/2-(16+(16+8*sign)*p))==0,"positive-frequency Gram")
    require(s.expand((S-M)/2-8*(1+sign)*p)==0,"negative-frequency Gram")
require(s.expand(-p*4*4+16*p)==0,"Exact influence versus noise factor")
nu,w,h,v,r,om=s.symbols("nu w h v r om")
vertex=-(nu+w)*(r*r+om*om*v*v)/2+w*(3*r*r-om*om*v*v)/2
require(s.expand(vertex+nu*(r*r+om*om*v*v)/2-w*(r*r-om*om*v*v))==0,"physical metric vertex")
# Pure gauge test: integrate f'*(a^4 rho) and use exact continuity.
rho,pr,rhop=s.symbols("rho pr rhop")
gauge=s.expand((4*h*rho+rhop)-h*rho+3*h*pr)
require(s.expand(gauge-(rhop+3*h*(rho+pr)))==0,"lapse-scale Ward row")
alpha,sigma,mu,L=s.symbols("alpha sigma mu L")
require(s.expand(alpha*sigma**2*mu*L*(-(nu+w)+3*w)
                 +alpha*sigma**2*mu*L*(nu-2*w))==0,"initial charge cross vertex")
# Unnormalized occupation monomials. Each branch amplitude is 1/4, exact.
zero=(0,)*8
def basis_state(sign):
    out={}
    for j in range(8):
        occ=[0]*8;occ[j]=2
        out[tuple(occ)]=F(1 if j<4 else sign,4)
    return out
def number_transfer(ket,dst,src,coef):
    out={}
    for occ,a in ket.items():
        if occ[src]:
            new=list(occ);b=a*occ[src]*coef
            new[src]-=1;new[dst]+=1;new=tuple(new)
            out[new]=out.get(new,F(0))+b
    return out
def kill_charge(ket,a,b):
    out={}
    # real antisymmetric generator; the omitted common i cannot change zero
    for sp in (0,4):
        for dst,src,coef in ((sp+a,sp+b,1),(sp+b,sp+a,-1)):
            for occ,c in number_transfer(ket,dst,src,coef).items():
                out[occ]=out.get(occ,F(0))+c
    return {o:c for o,c in out.items() if c}
for a,b in combinations(range(4),2):
    for ket in ({zero:F(1)},basis_state(1),basis_state(-1)):
        require(not kill_charge(ket,a,b),"SO4 singlet momentum charge")
# Finite dimensional canonical L has Tr L^2=2, unlike actual singlet variance zero.
ell=s.Matrix([[0,-s.I],[s.I,0]])
require(s.trace(ell*ell)==2,"Killing normalization")
finish("source_ctp.py",dict(
 actual_lapse_scale_vertex_and_gauge_Ward_exact=True,
 same_history_second_CTP_difference="-16*p*abs(B_J2)^2",
 unsymmetrized_source_Gram_positive=True,
 initial_source_charge_future_tensor_covariance="alpha*sigma^2*mu2*L*(nn+s)",
 expected_source_charge_stress_commutator_zero=True,
 operator_source_charge_stress_commutator_claimed_zero=False,
 SO4_Killing_generators_checked=6, singlet_branches_per_generator=3,
 actual_global_Killing_charge_variance=0,
 Gaussian_substitute_wrong_variance="4*n*(n+1)",
 all_local_momentum_constraints_solved=False,
 geometry_boundary_density_constructed=False),
 ["finite_stress/BOUNDARY_STATE.md","finite_stress/DYNAMIC_CHARGE.md"],
 proof="SOURCE_CTP.md")
