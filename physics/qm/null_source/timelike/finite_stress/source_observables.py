"""Actual inverse-volume derivatives and physical-observable distinctions."""
import sympy as s
from common import *
n,g,de,p=s.symbols("n g de p",positive=True)
a=g*de*s.sqrt(n*(n+1))
comm=s.simplify(a*(1/(de*(n+1))-1/(de*n)))
assert s.simplify(comm+g/s.sqrt(n*(n+1)))==0
assert s.diff(p**2/(2*de*n),p)==p/(de*n)
# Each oriented shift coefficient of the symmetrized expansion has this magnitude.
expansion=s.simplify(a*de/(3*s.sqrt(de*n)*s.sqrt(de*(n+1))))
assert s.simplify(expansion-g*de/3)==0
x,y,q,S0,a0=s.symbols("x y q S0 a0",positive=True)
Hv=s.Matrix([[0,a0],[a0,0]]);V=s.diag(x,y);Mv=V.inv()
dotV=s.I*(Hv*V-V*Hv)
energy=q*V+S0*Mv/2;pressure=-q*s.eye(2)+S0*Mv**2/2
work=s.I*(Hv*energy-energy*Hv)+(pressure*dotV+dotV*pressure)/2
nested=Mv*(Mv*dotV-dotV*Mv)-(Mv*dotV-dotV*Mv)*Mv
assert (work-S0*nested/4).applyfunc(s.simplify)==s.zeros(2)
assert s.simplify(work[0,1]-s.I*S0*a0*(y-x)**3/(4*x**2*y**2))==0
P2=2*VP+K2*L
P4=8*VP**2+8*VP*K2*L+K2**2*(iv.mpf(11)/8+iv.sqrt(3)/2)
ward_c=GAMMA*(2**(-iv.mpf(3)/2)+6**(-iv.mpf(3)/2))/4
c=GAMMA*(1/iv.sqrt(2)+1/iv.sqrt(6))
finish("source_observables.py",{
 "actual_Q_first_derivative":"P_j/v",
 "actual_Q_second_derivative":"i P_j [H,v^(-1)]",
 "old_A_derivative_difference_squared":"E_P[P^2 E((v^(-1)-A^(-3))^2|P)]",
 "inverse_volume_commutator_upper":outward(c),
 "sum_second_derivative_squared_upper":outward(c**2*P2),
 "reduced_expansion_norm_upper":outward(1/(2*V0*ELLC)),
 "Q_requires_compressed_POVM_or_explicit_domain":True,
 "all_original_bare_observables_preserved":False,
 "fixed_background_finite_mode_Hadamard_extension":True,
 "actual_quantum_geometry_Hadamard_RSET_constructed":False,
 "original_normal_derivative_error_computed_small":False,
 "classical_symmetric_work_residual":"P^2/4 [v^(-1),[v^(-1),dot(v)]]",
 "work_residual_second_moment_coarse_upper":outward(ward_c**2*P4),
 "naive_classical_symmetric_work_law_exact":False,
 "old_AE_history_recovered":False})
