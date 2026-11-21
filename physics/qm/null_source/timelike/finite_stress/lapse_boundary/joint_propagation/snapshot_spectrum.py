"""Frozen resolvent identities and actual rare-tail scaling checks."""
from __future__ import annotations
import sympy as sp
from common import finish, require, iv, interval, outward, above
a,s,b=sp.symbols("a s b",real=True,positive=True)
require(sp.simplify(sp.I/(1+sp.I*a)-1/(a-sp.I))==0,"Laplace resolvent sign")
poly=sum(sp.binomial(5,j)*sp.factorial(j) for j in range(6))
require(poly==326,"Polynomial Laplace constant")
ell,K,I1=sp.symbols("ell K I1",positive=True)
require(sp.simplify((ell/K)**2*(I1**2*K**2/(2*ell))/ell-I1**2/2)==0,"Scaled actual variance lower coefficient")
# An exact scalar example of non-UI, kept distinct from the actual spectral theorem.
p=1/(2*ell); low=-I1/2; high=(1-p)*I1/(2*p)
mean=sp.simplify((1-p)*low+p*high)
var=sp.simplify((1-p)*low**2+p*high**2)
require(mean==0,"Rare-tail illustrative mean")
require(sp.simplify(var-I1**2*(2*ell-1)/4)==0,"Rare-tail illustrative variance")
rows=[]
for ee in [10,100,1000]:
    pp=iv.mpf(1)/(2*ee); lo=-iv.mpf(1)/2; hi=(1-pp)/(2*pp)
    rows.append({"log_cutoff_parameter":ee,"rare_probability":outward(pp),
                 "tail_energy":outward(hi),"mean":0,
                 "variance":outward((1-pp)*lo**2+pp*hi**2)})
finish("snapshot_spectrum.py",{
"snapshot":"same selected original H_bulk,K(u_i)",
"strong_resolvent_limit":"(log K/K) H_bulk,K(u_i) -> -1/(2 kappa)",
"prepared_resolvent_rate":"326 C/sqrt(log K), plus C5 tail for fixed limiting vector",
"autonomous_all_s_profile_degree":5,"Laplace_integral":int(poly),
"actual_C9_spectral_law":"weak probability pushforward under -1/(2 kappa)",
"original_pure_C5_second_moment_limit":"3 I2/4",
"original_pure_C5_second_tail_limit":"I2/2 beyond every R>1/(2a)",
"original_pure_C5_first_moments_uniformly_integrable":True,
"original_pure_C5_QFI_excess":"2 I2",
"actual_C9_scaled_mean_limit":0,"limiting_normal_state_mean":"-I1/2",
"positive_tail_first_moment_liminf":"at least I1/2 beyond every fixed R>1/(2a)",
"actual_scaled_variance_over_logK_liminf":"at least I1^2/2",
"QFI_lower_bound_claimed":False,
"illustrative_scalar_rare_tail_only":rows
},inputs=[
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/relational_coupled/ALL_SIGN_EVOLUTION.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_feedback/CORRELATED_GAUSSIAN.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_propagation/INITIAL_LAYER.md"])
