"""Joint-covariance counterexample and quantum-uncertainty distinction."""
import sympy as s
from common import *
a1,a2,b,k=s.symbols("a1 a2 b k",real=True,nonzero=True)
v=s.Matrix([k*a1/b,k*a2/b])
Gp=s.eye(2).col_join(v.T);Gm=s.eye(2).col_join(-v.T)
Sp=Gp*Gp.T;Sm=Gm*Gm.T
ell=s.Matrix([[-k*a1,-k*a2,b]])
assert s.simplify((ell*Sp*ell.T)[0])==0
assert s.simplify((ell*Sm*ell.T)[0]-4*k*k*(a1*a1+a2*a2))==0
assert Sp[:2,:2]==Sm[:2,:2]==s.eye(2)
assert s.simplify(Sp[2,2]-Sm[2,2])==0
n=s.symbols("n",nonnegative=True)
assert s.expand((n+1)*(n+2)-n*(n-1))==4*n+2
assert above(N**2-WEIGHT,0)
uncertainty=16*(1+2*N)
vminus=16*(2*N**2+2*N+1)-32*WEIGHT
assert above(vminus-uncertainty,0)
finish("initial_correlations.py",{
 "proof":"INITIAL_CORRELATIONS.md",
 "same_source_and_initial_amplitude_marginals_different_test_variances":True,
 "both_joint_covariances_are_positive_Gram_matrices":True,
 "necessary_initial_contribution_condition":"Delta(H CY H* + H K R* + R K* H*)=0",
 "actual_shell_quantum_Robertson_rhs":outward(uncertainty**2),
 "lower_state_quadrature_variance":outward(vminus),
 "Gaussian_auxiliary_cancellation_claimed_actual_joint_quantum_preparation":False,
 "fast_pole_initial_cancellation_claimed_full_stability":False,
 "complete_physical_joint_state_closed":False
},("INITIAL_CORRELATIONS.md","RESPONSE.md","CONSTRAINTS.md","COHERENCE.md"))
