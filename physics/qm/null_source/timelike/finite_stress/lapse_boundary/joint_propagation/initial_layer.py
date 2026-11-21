"""Algebraic and outward coefficient checks for the full initial-layer proof."""
from __future__ import annotations
import sympy as sp
from common import finish, require, iv, interval, outward, above, below
alpha,d,L,A0,Q0,E,Et,AE=sp.symbols("alpha d L A0 Q0 E Et AE")
# i v0'=alpha d, H v0=L+alpha(A0+d+Q0), F eta=-alpha Q0.
res=sp.expand(alpha*d+sp.I*Et-(L+alpha*(A0+d+Q0)-alpha*Q0+E+alpha*AE))
expected=sp.I*Et-L-E-alpha*A0-alpha*AE
require(sp.expand(res-expected)==0,"Complete residual cancellation")
N,s=sp.symbols("N s",positive=True)
require(sp.simplify((s*sp.log(N**2)/N**2)/(sp.log(N)/N)-2*s/N)==0,"Two-cutoff same-time ratio")
ell,K=sp.symbols("ell K",positive=True)
require(sp.simplify((ell/K)*(K/ell**sp.Rational(3,2))-1/sp.sqrt(ell))==0,"Integrated residual scale")
require(sp.simplify((1/ell)*sp.sqrt(ell)-1/sp.sqrt(ell))==0,"Endpoint corrector scale")
# Outward finite coefficient illustration, independent of the predecessor executable.
# Euler--Maclaurin bounds on H_K, with the exact affine g_K(u).
rows=[]
a=iv.mpf(11)/10; b=iv.mpf(19)/10; J=3
beta=1+b*b; q=1-beta/J**2
metric_rem=interval(-(J-1)/4,0)+(2*beta-1)/(4*q*q*(J-1))*interval(0,1)
# The broad remainder interval safely contains -(J-1)/4 + positive summable tail.
for kk in [10**6,10**12,10**24]:
    logk=iv.log(kk)
    hk=logk+iv.euler+iv.mpf(1)/(2*kk)+interval(-1,0)/(12*kk**2)
    gi=iv.mpf(19)/120-hk/4
    require(below(gi,0),"Cofinal negative g patch")
    tau=4*logk/kk
    intalpha=2*iv.log(1+tau/(4*gi))
    numerator=(iv.mpf(kk)/4+metric_rem)*intalpha+2
    err=numerator/interval(a.a,b.b)
    rows.append({"K":str(kk),"phase_error_at_s4_outward":outward(err)})
require(max(abs(v) for v in rows[-1]["phase_error_at_s4_outward"])<0.01,"Asymptotic coefficient illustration")
finish("initial_layer.py",{
"complete_residual_identity":"i eta'-L(v0+eta)-alpha A_eta phi-alpha A_ad eta",
"prepared_error":"C_S[(log K)^(-1/2)+log K/K]",
"epsilon_K":"log K/K","full_strong_limit":"exp(i s/(2 kappa))",
"uniform_strong_adjoint_and_two_time_limit":True,
"same_time_cutoff_pair":"K=N^2,L=N; rescaled L-time=2s/N",
"coefficient_examples":rows,
"coefficient_example_scope":{"illustrative_only":True,"G_at_initial_slice":"19/120","support":["11/10","19/10"],"J":3,"s":4,"frozen_actual_history_parameters":False},
"ordinary_time_uniform_initial_window":"REJECTED",
"ordinary_fixed_positive_time_limit":"OPEN",
"full_corrector_domain_argument":"analytic proof P2-P4; not certified by finite algebra alone",
"exact_orbit_confined_to_support":False
},inputs=[
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/relational_coupled/ALL_SIGN_EVOLUTION.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_feedback/CORRELATED_GAUSSIAN.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_feedback/NEXT_PROPAGATOR_TEST.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_propagation/ADIABATIC_CONNECTION.md"])
