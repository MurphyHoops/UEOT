"""Actual C9 complete-outcome Fisher algebra."""
from __future__ import annotations
import sympy as sp
from common import finish, require
sig,I1,z,p,q,qp,ell=sp.symbols("sig I1 z p q qp ell",positive=True,real=True)
M=sp.Matrix([[I1,sig],[sig,z]])
Z=sp.Matrix([1,sp.I])/sp.sqrt(2)
E=Z*Z.conjugate().T
require(sp.simplify(E*E-E)==sp.zeros(2),"Isometry-range effect is a projection")
require(sp.simplify((M*E-E*M)[0,0]-sp.I*sig)==0,"Exact derivative commutator")
require(E[0,0]==sp.Rational(1,2),"Odd conditional probability")
probs=[p*q,p*(1-q),1-p]; derivs=[p*qp,-p*qp,0]
FI=sp.simplify(sum(v*v/w for v,w in zip(derivs,probs)))
require(sp.simplify(FI-p*qp**2/(q*(1-q)))==0,"Complete failure-retaining Fisher information")
scaled=sp.simplify(FI.subs({p:1/(2*ell),q:sp.Rational(1,2),qp:-ell*sig})/ell)
require(sp.simplify(scaled-2*sig*sig)==0,"Actual asymptotic coefficient")
finish("rare_fisher.py",{
"family":"actual fixed-ordering C9, initial/frozen rescaled parameter",
"graph_estimate":"H_K/K -> kappa^-1 on actual odd branch and rare T partner, uniformly label",
"complete_POVM":["E","P_odd-E","I-P_odd"],
"failure_probability_retained":True,
"F_cl_exact":"p (q')^2/[q(1-q)]",
"rescaled_QFI_over_logK_liminf":"at least 2(I2-I1^2)>0",
"original_initial_QFI_scaled_by_logK_over_K2":"same lower coefficient",
"derived_from_mixed_state_variance":False,
"cutoff_dependent_mathematical_measurement":True,
"local_calibrated_probe_constructed":False,
"unrestricted_normal_low_input_without_graph_moments":False
},inputs=[
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_feedback/CORRELATED_GAUSSIAN.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/relational_coupled/ALL_SIGN_EVOLUTION.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_propagation/ADIABATIC_CONNECTION.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_propagation/RARE_PREPARATION.md"])
