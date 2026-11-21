"""Exact ordering, bounded-readout and physical-completion checks."""
from __future__ import annotations
import sympy as sp
import numpy as np
from common import finish, require, iv, outward, below
r,eta=sp.symbols("r eta",real=True)
rr=1+sp.sqrt(1+4*eta)/2
require(sp.simplify(rr**2-2*rr-(eta-sp.Rational(3,4)))==0,"Ground-state ordering coefficient")
x=sp.symbols("x",positive=True)
B=x*x/(1+x*x); bbound=sp.diff(B,x)**2/x
require(sp.simplify(sp.diff(bbound,x)-4*(1-7*x*x)/(1+x*x)**5)==0,"Unique positive readout maximum")
atmax=sp.simplify(bbound.subs(x,1/sp.sqrt(7)))
require(sp.simplify(atmax-7**sp.Rational(7,2)/1024)==0,"Exact readout maximum")
bb=iv.mpf(7)**iv.mpf("3.5")/1024
require(below(bb,1),"Form multiplier bound")
# Pure feature space differs from algebra GNS; check the actual null counterexample.
psi=np.array([1.,0.,0.]); xx=np.array([0.,1.,0.])
rho=np.outer(psi,psi); A=np.outer(psi,xx)
require(abs(xx@rho@xx)<1e-15,"Feature-null input")
require(abs((A@xx)@rho@(A@xx)-1)<1e-15,"Bounded operation not feature-null preserving")
ranks=[]
for rank in [1,2,3]:
    sq=np.diag([1/np.sqrt(rank)]*rank+[0.]*(3-rank))
    cols=[]
    for i in range(3):
        for j in range(3):
            E=np.zeros((3,3));E[i,j]=1
            cols.append((E@sq).ravel())
    alg_rank=int(np.linalg.matrix_rank(np.stack(cols,axis=1)))
    require(alg_rank==3*rank,"Algebra GNS column rank")
    ranks.append({"slice_dimension":3,"density_rank":rank,"vector_feature_dimension":rank,
                  "algebra_GNS_dimension":alg_rank})
finish("local_constraint.py",{
"exact_local_complex":"0 -> Y_C -> Phi_C -> Q -> 0",
"explicit_split":["C G_h=I-J_h T","G_h C=I","T J_h=I","G_h J_h=0"],
"state_independent_completion":"H",
"prepared_vector_feature_completion":"supp(rho) H",
"algebra_GNS_completion":"S_2(supp(rho) H,H)",
"finite_completion_examples":ranks,"readout_form_coefficient_outward":outward(bb),
"critical_eta_closed_form_retained":True,"global_self_adjoint_constraint_claimed":False,
"raw_kernel_flat_trace_class_claimed":False,"full_K_rigging_limit_from_this_theorem":False
},inputs=[
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/RELATIONAL_DOMAIN.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/relational_coupled/ALL_SIGN_EVOLUTION.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/relational_coupled/PHYSICAL_SLICE.md"])
