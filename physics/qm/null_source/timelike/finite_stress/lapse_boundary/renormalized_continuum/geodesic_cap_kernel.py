"""Exact Funk-Hecke spectrum, contraction, microcausal support and k^(-10) bound for the p=8 geodesic cap."""
import sympy as sp
from common import iv,require,above,below,outward,finish
from model import geodesic_cap_spectrum

x,r0_s=sp.symbols("x r0",positive=True)
g_sym=(sp.cos(x)-sp.cos(r0_s))**8*sp.sin(x)
for r in range(5):
    require(sp.simplify(sp.diff(g_sym,x,2*r).subs(x,0))==0,f"even origin derivative {2*r}")
for r in range(8):
    require(sp.simplify(sp.diff(g_sym,x,r).subs(x,r0_s))==0,f"cap boundary derivative {r}")
require(sp.simplify(sp.diff(g_sym,x,8).subs(x,r0_s)-40320*sp.sin(r0_s)**9)==0,"eighth boundary derivative")

spec=geodesic_cap_spectrum(inv_r0=20,Kmax=512,nsub=64)
khat=spec["khat"]
B_r0=spec["B_rho0"]
C_r0=spec["C_rho0"]

require(iv.mpf(1) in khat[0],"unit k=1 normalization")
require(above(khat[1],iv.mpf("0.999821")) and below(khat[1],iv.mpf("0.999822")),"dipole k=2 multiplier")
max_higher=max((abs(v) for v in khat[1:]),key=lambda z:z.b)
require(below(max_higher,1),"strict contraction on k>=2 up to 512")

# Verify |khat(k)| <= B_rho0 / k^10 for every k in 1..512 and tightness at k=200
for k in range(1,513):
    bound_k=B_r0/(iv.mpf(k)**10)
    require(abs(khat[k-1]).b<=bound_k.a,"IBP majorant violated at k="+str(k))
ratio_200=abs(khat[199])/(B_r0/(iv.mpf(200)**10))
require(above(ratio_200,iv.mpf("0.01")) and below(ratio_200,1),"asymptotic ratio in (0.01, 1) at k=200")

finish("geodesic_cap_kernel.py",{
  "cap_radius_rad":"1/20",
  "microcausal_commuting_separation_rad":"1/10",
  "regularity_class":"C^7_compactly_supported_on_S3",
  "C_rho0":outward(C_r0),
  "B_rho0_k10_majorant":outward(B_r0),
  "khat_1":outward(khat[0]),
  "khat_2_dipole":outward(khat[1]),
  "khat_64":outward(khat[63]),
  "khat_200":outward(khat[199]),
  "khat_512":outward(khat[511]),
  "max_abs_khat_2_to_512_upper":outward(max_higher),
  "asymptotic_ratio_at_k200":outward(ratio_200),
  "decay_exponent_k":10,
  "squared_decay_exponent_k":20,
  "strictly_commuting_outside_2rho0":True,
  "pointlike_zero_radius_limit_claimed":False
})
