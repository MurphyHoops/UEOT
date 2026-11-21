"""Actual finite-K coefficients and a source-bound common positive-form patch."""
import sympy as s
from common import *
prefix="physics/qm/null_source/timelike/"
inp=prefix+"joint_history/history.json"
history=load(inp)
A=box(history["cases"]["unfiltered"]["A"]);U0=box(history["fixed_U0"])
require(above(U0,"1.49e-10") and below(U0,"1.50e-10"),"Nonzero frozen U0 retained")
K0=65536;J=interval("-0.01","0.01")
def harmonic(k):
    n=iv.mpf(k)
    return iv.ln(n)+iv.euler+1/(2*n)-1/(12*n*n)+1/(120*n**4)+interval(-1,0)/(252*n**6)
def gbox(k):
    return iv.mpf(19)/120+iv.ln(A*A/4)/8+iv.euler/4-harmonic(k)/4+J/4
g=gbox(K0);d3=iv.mpf(59)/720-g/2
require(above(g,".0377337689") and below(g,".0427338873"),"Actual common positive window")
require(above(d3,".0605775008") and below(d3,".0630775600"),"Actual confining scalar coefficient")
V0=2*iv.pi**2;a=A*iv.exp(J)
d1=3*V0*a*a/2-g+iv.mpf(K0*(K0+1))/4+iv.mpf(29)/120
require(above(d1),"Full linear scalar coefficient")
neg={}
for k in [32768,131072]:
    z=gbox(k);d=iv.mpf(59)/720-z/2
    neg[str(k)]={"g":outward(z),"d3":outward(d)}
require(above(gbox(32768)) and below(iv.mpf(59)/720-gbox(32768)/2,0),"Inverted potential negative control")
require(below(gbox(131072),0),"Negative principal negative control")
kk,H,C,u,kap,chi,an=s.symbols("K H C u kap chi an",real=True)
BK=-(kk*(kk+1)+H)/4
Cr=kk*(kk+1)*(kk*(kk+1)-1)/4-H/8
gg=C/120-H/4
Lan=C*chi**2/240+(C-29)*kap**2/120+(3*C-59)*kap**4/720+u/8+an
L=BK*(chi+kap**2)-H*(chi+kap**2)**2/8+Lan+Cr
remainder=s.expand(L-gg*chi**2/2-(BK-H*kap**2/4)*chi)
target=u/8+an+Cr+(gg-kk*(kk+1)/4-s.Rational(29,120))*kap**2+(gg/2-s.Rational(59,720))*kap**4
require(s.simplify(remainder-target)==0,"All scalar coefficients retained")
require(s.simplify((-((kk+1)*(kk+2)+(H+1/(kk+1)))/4)-BK+((kk+1)/2+1/(4*(kk+1))))==0,"BK recurrence")
def uniform(k):
    z=gbox(k);return above(z) and below(z,iv.mpf(59)/360)
lo,hi=2,K0
while lo<hi:
    m=(lo+hi)//2
    if below(gbox(m),iv.mpf(59)/360):hi=m
    else:lo=m+1
Klo=lo
lo,hi=K0,131072
while lo<hi:
    m=(lo+hi+1)//2
    if above(gbox(m)):lo=m
    else:hi=m-1
Khi=lo
require(uniform(Klo) and uniform(Khi),"Certified common-K band endpoints")
require(not uniform(Klo-1) and not uniform(Khi+1),"Uniform band adjacent boundaries")
finish("coefficient_window.py",dict(
 selected_K=K0,clock_patch_u=["-1/100","1/100"],
 frozen_A=outward(A),frozen_U0=outward(U0),g_on_patch=outward(g),d1_on_patch=outward(d1),d3_on_patch=outward(d3),
 certified_uniform_positive_band_K=[Klo,Khi],
 negative_controls=neg,source_real_mode_count=K0*(K0+1)*(2*K0+1)//3,
 all_scalar_counterterms_retained=True,
 full_field_limit_inferred_from_positive_band=False,
 model_K_derived_from_Core=False,
 finite_matrix_materialized=False),
 [inp,prefix+"finite_stress/lapse_boundary/ACTION_LIFT.md",
 prefix+"finite_stress/lapse_boundary/RELATIONAL_DOMAIN.md",
 prefix+"finite_stress/lapse_boundary/quiet_window.json"],
 proof="COEFFICIENT_WINDOW.md")
