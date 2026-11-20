"""Additive quantum constraint, exact QFI optimum and energy-degenerate code."""
import sympy as s
from common import *
I=s.I
rho=s.diag(s.Rational(3,4),s.Rational(1,4))
psi=s.Matrix([s.sqrt(3)/2,0,0,s.Rational(1,2)])
x=s.Matrix([[0,1],[1,0]]);y=s.Matrix([[0,-I],[I,0]])
examples=[]
for name,H in [("sigma_x",x),("sigma_y",y)]:
    G=-s.sqrt(3)*H.T/2
    C=s.kronecker_product(H,s.eye(2))+s.kronecker_product(s.eye(2),G)
    mean=(psi.adjoint()*C*psi)[0]
    var=s.simplify((psi.adjoint()*C*C*psi)[0]-mean**2)
    fq=2*sum((rho[i,i]-rho[j,j])**2/(rho[i,i]+rho[j,j])*abs(H[i,j])**2 for i in range(2) for j in range(2))
    assert mean==0 and var==s.Rational(1,4) and fq==1
    examples.append({"H":name,"G":str(G),"FQ":str(fq),"minimum_variance":str(var)})
# Exact discrete code: source energy 0,1,1; degenerate coherence is retained.
H=s.diag(0,1,1);G=s.diag(0,-1);C=s.kronecker_product(G,s.eye(3))+s.kronecker_product(s.eye(2),H)
V=s.zeros(6,3);V[0,0]=1;V[4,1]=1;V[5,2]=1
assert V.adjoint()*V==s.eye(3) and C*V==s.zeros(6,3)
rho3=s.Matrix([[s.Rational(1,2),0,0],[0,s.Rational(1,4),s.Rational(1,8)],[0,s.Rational(1,8),s.Rational(1,4)]])
joint=V*rho3*V.adjoint()
reduced=joint[:3,:3]+joint[3:,3:]
assert reduced==rho3 and rho3*H==H*rho3
cross=s.zeros(3);cross[0,1]=1;cross[1,0]=1
lost=V*cross*V.adjoint()
assert lost[:3,:3]+lost[3:,3:]==s.zeros(3)
finish("quantum_floor.py",{
 "known_primary_theorem":"Marvian PRL129 190502 (2022) Theorem3; arXiv:2112.04694",
 "bound":"Var_R(H+G)>=F_Q(rho,H)/4","finite_dimensional_optimum_examples":examples,
 "complex_transpose_orientation_verified":True,
 "strong_additive_normal_constraint_requires_stationary_marginal":True,
 "original_noncompact_zero_mode_has_no_normal_stationary_state":True,
 "degenerate_discrete_code_preserves_NOON_type_coherence":True,
 "cross_energy_bare_coherence_preserved_by_exact_code":False,
 "infinite_dimensional_optimum_attained_claimed":False,
 "designed_G_claimed_physical_geometry":False,
 "physical_Hilbert_constraint_solutions_excluded":False})
