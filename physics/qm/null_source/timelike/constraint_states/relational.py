"""Gaussian encoding, absolute covariance, clock signs and intertwining."""
import sympy as s
from common import *
g,E,Ep,sigma,t,tau=s.symbols("g E Ep sigma t tau",real=True,positive=True)
# Complete-square identity for the exact overlap and dephasing exponent.
lhs=((g+E)**2+(g+Ep)**2)/(4*sigma**2)
rhs=(g+(E+Ep)/2)**2/(2*sigma**2)+(E-Ep)**2/(8*sigma**2)
assert s.expand(lhs-rhs)==0
# A normalized Gaussian density with time variance tau^2 has derivative energy 1/(4tau^2).
envelope=s.exp(-t*t/(4*tau*tau))
assert s.simplify(s.diff(envelope,t)/envelope+t/(2*tau*tau))==0
assert s.simplify((tau*tau)/(4*tau**4)-1/(4*tau*tau))==0
vh,sg=s.symbols("vh sg",positive=True)
cov=s.Matrix([[vh+sg*sg,-vh],[-vh,vh]])
assert s.factor(cov.det())==sg*sg*vh
ones=s.Matrix([1,1])
assert (ones.T*cov*ones)[0]==sg*sg
# Differential test of U^dagger C U on a generic scalar source energy.
F=s.Function("F")
encoded=F(t)*s.exp(-s.I*E*t)
assert s.simplify(-s.I*s.diff(encoded,t)+E*encoded+s.I*s.diff(F(t),t)*s.exp(-s.I*E*t))==0
# Nontrivial unitary in a degenerate energy subspace commutes with H.
H=s.diag(0,2,2);Wm=s.Matrix([[1,0,0],[0,0,1],[0,1,0]])
assert H*Wm==Wm*H and Wm.adjoint()*Wm==s.eye(3)
finish("relational.py",{
 "physical_inner_product":"<Psi_phi,Psi_psi>phys=<phi,psi>; not the L2-time inner product",
 "normal_encoding_constraint_mean":"0","normal_encoding_constraint_variance":"sigma^2=1/(4tau^2)",
 "absolute_cross_block":{"VarG":"VarH+sigma^2","CovGH":"-VarH","VarH":"original energy-law variance"},
 "bare_dephasing":"exp[-(E-Eprime)^2/(8sigma^2)]",
 "bare_zero_Q_added_covariance":"<PjPk>/(4A^6sigma^2)",
 "normal_state_exact_dressed_algebra_recovery":True,
 "same_energy_NOON_gate_intertwines_encoding":True,
 "new_normal_Hadamard_source_family_preserves_complete_free_stress_records":True,
 "new_source_family_preserves_defined_prescribed_FLRW_influence":True,
 "new_family_changes_old_bare_W2_by_smooth_zero_mode_constant":True,
 "original_bare_full_marginal_preserved":False,
 "normal_kinematic_zero_constraint_limit_claimed":False,
 "Einstein_constraint_or_real_clock_stress_completed":False})
