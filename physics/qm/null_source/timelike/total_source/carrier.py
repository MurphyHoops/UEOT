"""Internal commutant and correlated-output invariant reduction."""
import sympy as s
from common import *
sx=s.Matrix([[0,1],[1,0]]);sz=s.diag(1,-1)
xs=s.symbols("x0:16");Z=s.Matrix(4,4,xs)
eqs=list(Z*s.kronecker_product(sx,s.eye(2))-s.kronecker_product(sx,s.eye(2))*Z)
eqs+=list(Z*s.kronecker_product(sz,s.eye(2))-s.kronecker_product(sz,s.eye(2))*Z)
sol=s.linsolve(eqs,xs)
v=next(iter(sol));restricted=s.Matrix(4,4,v)
B=restricted[:2,:2]
assert restricted==s.kronecker_product(s.eye(2),B)
rho=s.Matrix(4,4,s.symbols("r0:16"))
sig=s.Matrix(2,2,s.symbols("m0:4"))
bs=s.Matrix(2,2,s.symbols("b0:4"))
cm=s.Matrix(2,2,s.symbols("c0:4"))
reduced=s.Matrix([[sum(rho[2*i+j,2*k+j] for j in range(2)) for k in range(2)] for i in range(2)])
lhs=s.trace(s.kronecker_product(rho,sig)*s.kronecker_product(bs,s.eye(2),cm))
rhs=s.trace(reduced*bs)*s.trace(sig*cm)
assert s.expand(lhs-rhs)==0
finish("carrier.py",{
 "proof":"CARRIER.md","carrier_action":"two equal-mass m>0 minimal complex scalars with U(2)",
 "complete_fundamental_isotypic_sector_retained":True,
 "one_particle_truncation_during_metric_history":False,
 "actual_correlated_output_restricts_to_product_on_future_invariant_algebra":True,
 "individual_future_influences_factor_for_all_c":True,
 "carrier_stress_noise_and_response_removed":False,
 "nonzero_expanded_future_contrast_for_some_small_epsilon":True,
 "numeric_carrier_epsilon0_or_bare_contrast_bound_inherited":False,
 "local_gate_controller_or_expanded_on_shell_geometry_closed":False
},("CARRIER.md","PREPARATION.md","TOTAL_FUTURE.md","HISTORY_WITNESS.md"))
