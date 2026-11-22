"""Exact connection, finite-Fock algebra and inverse excitation gaps."""
from __future__ import annotations
from collections import defaultdict
import sympy as sp
from common import finish, require, iv, interval, outward, above, below
k,x=sp.symbols("k x",positive=True,real=True)
Om=sp.sqrt(k*k-1-x*x)
c=-1/(4*Om)-sp.I*x/(4*Om**2)
d=-1/(2*Om)
cc=1/(16*Om**2)+x*x/(16*Om**4)
require(sp.simplify(cc-(k*k-1)/(16*(k*k-1-x*x)**2))==0,"Connection modulus")
require(sp.simplify(4*k*k*cc-k*k*(k*k-1)/(4*(k*k-1-x*x)**2))==0,"2k^2 degeneracy")
u,G=sp.symbols("u G",real=True)
al=1/(2*(G+u/4))
require(sp.simplify(sp.diff(al,u)+al**2/2)==0,"Exact clock derivative")
# Gaussian derivative after removal of scalar Berry mean:
# -i d_kappa chi/chi + 1/(4 Omega) = c sqrt(2)|2>/|0>.
q=sp.symbols("q",real=True)
ratio=-sp.I*(sp.diff(Om,x)/(4*Om)-sp.diff(Om,x)*q*q/2-sp.I*q*q/2)+1/(4*Om)
require(sp.simplify(ratio-c*(2*Om*q*q-1))==0,"Gaussian connection on vacuum")

N=3
cs=[sp.Rational(1,3)+sp.I/7, -sp.Rational(1,5)+sp.I/11, sp.Rational(2,9)-sp.I/13]
ds=[sp.Rational(-1,2),sp.Rational(-1,3),sp.Rational(-1,7)]
oms=[sp.Rational(5,2),sp.Rational(9,2),sp.Rational(13,2)]
kap=sp.Rational(7,5)
vac={(0,)*N:sp.S.One}
def create_pair(v,coeff):
    out=defaultdict(lambda:sp.S.Zero)
    for ns,a in v.items():
        for j,cj in enumerate(coeff):
            nn=list(ns); nn[j]+=2
            out[tuple(nn)]+=a*cj*sp.sqrt((ns[j]+1)*(ns[j]+2))
    return {n:sp.simplify(a) for n,a in out.items()}
def gamma(v):
    out=defaultdict(lambda:sp.S.Zero)
    for ns,a in v.items():
        for j in range(N):
            nn=list(ns); nn[j]+=2
            out[tuple(nn)]+=a*cs[j]*sp.sqrt((ns[j]+1)*(ns[j]+2))
            if ns[j]>=2:
                nn=list(ns); nn[j]-=2
                out[tuple(nn)]+=a*sp.conjugate(cs[j])*sp.sqrt(ns[j]*(ns[j]-1))
            out[ns]+=a*ds[j]*ns[j]
    return {n:sp.simplify(a) for n,a in out.items() if a!=0}
g2=gamma(gamma(vac))
require(sp.simplify(g2[(0,)*N]-2*sum(abs(z)**2 for z in cs))==0,"Vacuum metric")
for j in range(N):
    ns=[0]*N; ns[j]=2
    require(sp.simplify(g2[tuple(ns)]-2*ds[j]*cs[j]*sp.sqrt(2))==0,"Number-pair sector")
four=create_pair(create_pair(vac,cs),cs)
require(all(sp.simplify(g2[n]-a)==0 for n,a in four.items()),"All four-particle coefficients")
actual=sp.S.Zero
for ns,a in four.items():
    gap=sum(ns[j]*oms[j] for j in range(N))/kap
    actual+=sp.simplify(abs(a/kap/gap)**2)
expected=sp.Rational(3,2)*sum(abs(cs[j])**4/oms[j]**2 for j in range(N))
expected+=4*sum(abs(cs[j]*cs[l])**2/(oms[j]+oms[l])**2 for j in range(N) for l in range(j+1,N))
require(sp.simplify(actual-expected)==0,"Exact four-particle inverse-gap norm")
# A genuine shell bound with outward arithmetic; no huge field matrix.
M=100
ss=sum((interval(1,1)/(i+j)**2 for i in range(3,M+1) for j in range(3,M+1)),iv.mpf(0))
bound=1+iv.log(2*M)
require(below(ss,bound.a),"Logarithmic shell bound")
finish("adiabatic_connection.py",{
"connection":"c=-1/(4Omega)-i kappa/(4Omega^2), d=-1/(2Omega)",
"mode_multiplicity":"2k^2 real modes per shell","exact_fock_modes_checked":N,
"four_particle_configurations":len(four),
"inverse_gap_norm_coefficients":["3/2 diagonal","4 unordered cross"],
"shell_sum_example":{"K":M,"outward_sum":outward(ss),"outward_upper":outward(bound)},
"complete_generator_terms_retained":True,"high_particle_projection_of_evolution":False,
"uniform_inverse_gap_profile_budget":"H^4; two kappa derivatives; O(sqrt(log K))",
"exact_orbit_assumed_compact":False
},inputs=[
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_feedback/JOINT_CUTOFF.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_feedback/CORRELATED_GAUSSIAN.md"])
