"""Uniform ordering-sequence scaling and phase checks."""
from __future__ import annotations
import sympy as sp
from common import finish, require, iv, outward, above, below
x,lam=sp.symbols("x lam",positive=True,real=True)
aa=lam/(2*x)+2*(1-lam)/x**3
der=sp.diff(aa,x)
require(sp.simplify(der+lam/(2*x*x)+6*(1-lam)/x**4)==0,"Exact monotone phase derivative")
# Coefficient comparison with positive ordering eta_K/M=1-lambda.
require(sp.simplify(-2*(lam/(4*x)+(1-lam)/x**3)+aa)==0,"Fast Hamiltonian sign")
# Interval verification uses separate nonnegative weights; endpoint cases included.
rows=[]
for ll in [0,iv.mpf(1)/4,iv.mpf(1)/2,1]:
    xx=iv.mpf([iv.mpf(11)/10,iv.mpf(19)/10])
    av=ll/(2*xx)+2*(1-ll)/xx**3
    dd=-ll/(2*xx**2)-6*(1-ll)/xx**4
    require(above(av) and below(dd,0),"Strict positivity and monotonicity")
    rows.append({"lambda":float(ll),"phase_outward":outward(av),"derivative_outward":outward(dd)})
finish("ordering_sweep.py",{
"ordering_class":"any eta_K>=-1/4, same selected Friedrichs family",
"M_K":"K+max(eta_K,0)","epsilon_K":"log K/M_K",
"subsequence_phase":"lambda/(2 kappa)+2(1-lambda)/kappa^3",
"fixed_original_test_kernel_for_full_sequence":"ZERO",
"uniform_ordering_form_domain_assumed":False,
"complete_generator_retained":True,"other_boundary_realizations_covered":False,
"phase_examples":rows
},inputs=[
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/relational_coupled/ALL_SIGN_EVOLUTION.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_propagation/ADIABATIC_CONNECTION.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_propagation/INITIAL_LAYER.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_propagation/INTERIOR_COLLAPSE.md"])
