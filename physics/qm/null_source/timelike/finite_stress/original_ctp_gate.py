"""Read frozen original constraints; check new projection/boundary identities."""
import json,hashlib
import sympy as s
from common import *
old_path=TIMELIKE/"total_source/constraints.json"
old=json.loads(old_path.read_text())
assert old["status"]=="PASS"
assert old["complete_density_tangent"]=="delta_rho_geom=-3*u/A^2"
assert old["independent_density_source_linear_constraint"]=="xi_rho_total=0"
for rel,digest in old["source_sha256"].items():
    assert hashlib.sha256((REPO/rel).read_bytes()).hexdigest()==digest
n00=box(old["actual_baseline_spatial_average_density_variance"])
assert above(n00)
rms=iv.sqrt(n00)
rho0=3/(2*A**2)
relative_rms=rms/rho0
assert above(relative_rms)
AA,BB,CC,DD=s.symbols("AA BB CC DD",commutative=False)
comm=lambda x,y:x*y-y*x
rhs=AA*comm(BB,CC)*DD+AA*CC*comm(BB,DD)+comm(AA,CC)*DD*BB+CC*comm(AA,DD)*BB
assert s.expand(comm(AA*BB,CC*DD)-rhs)==0
rho,p,a,u,c=s.symbols("rho p a u c",positive=True)
drho=-3*(rho+p)*u+c
assert s.simplify((-3*u/a**2-drho).subs(rho,1/a**2-p)+c)==0
p1,p2=s.symbols("p1 p2",real=True)
vv,aa=s.symbols("vv aa",positive=True)
wave=s.Function("wave")(p1,p2)
dilation=lambda z:s.I*(p1*s.diff(z,p1)+p2*s.diff(z,p2)+z)
density=(p1**2+p2**2)/(2*vv*aa**6)
assert s.simplify(density*dilation(wave)-dilation(density*wave)
    +s.I*(p1**2+p2**2)*wave/(vv*aa**6))==0
nu,u0=s.symbols("nu u0")
counterexample=nu-u0
assert counterexample.subs(nu,u0)==0
assert s.diff(counterexample,nu)==1
n=s.symbols("n",positive=True)
gram=n*s.Matrix([[1,-1],[-1,1]])
row=s.Matrix([[1,1]])
assert gram.det()==0 and (row*gram*row.T)[0]==0
assert gram.trace()==2*n
z,x,epsilon=s.symbols("z x epsilon",nonnegative=True)
assert s.expand(z**2+x**2-2*z*x-(z-x)**2)==0
sigma_z2=s.symbols("sigma_z2",nonnegative=True)
cov=(epsilon**2-sigma_z2-n)/2
assert s.simplify(sigma_z2+n+2*cov-epsilon**2)==0
finish("original_ctp_gate.py",{
 "frozen_absolute_density_variance":outward(n00),
 "finite_window_density_RMS_if_no_new_boundary_column":outward(rms),
 "same_unfiltered_static_mean_density":outward(rho0),
 "same_state_density_relative_RMS":outward(relative_rms),
 "preserved_matter_commuting_boundary_quantum_exact_cancellation":False,
 "source_case":"frozen original product zero/high baseline and either NOON sign",
 "source_variance_units":"physical density squared in original model units",
 "SO4_invariance_of_actual_W2_proved_from_full_shell_occupations":True,
 "free_quadratic_commutator_uses_W2_not_Gaussian_W4":True,
 "pure_inhomogeneous_singlet_response_zero_if_equivariant":True,
 "full_zero_row_requires_projection_domain_and_anchored_diffeomorphism_Ward":True,
 "SO4_alone_suffices_for_full_lapse_row":False,
 "actual_full_inhomogeneous_CTP_Hessian_computed":False,
 "absolute_density_noise_removed_by_NOON_difference":False,
 "arbitrary_geometry_noise_cross_correlations_fix_an_identically_zero_row":False,
 "finite_boundary_conservation_constant":"delta_rho=-3*u/A^2+C_boundary",
 "new_source_sign_convention":"R=L_rho*h-xi_rho-B*Y",
 "necessary_boundary_covariance":"B0*CY*B0*=N00; B0*K0=-N00",
 "budget_RMS_lower":"(sqrt(N00)-sqrt(V))_+ if Var(B0*Y)<=V",
 "classical_PSD_block_is_quantum_preparation":False,
 "deterministic_mean_solution_invalidated":False,
 "nonlinear_or_changed_boundary_contract_excluded":False,
 "two_field_stochastic_approximation_error_control_proved":False,
 "normal_quantum_boundary_state_constructed":False,
 "common_preparation_and_calibrated_gravity_record":"OPEN"},
 extra=["../total_source/constraints.json","../total_source/CONSTRAINTS.md",
 "../total_source/COHERENCE.md","../total_source/INITIAL_CORRELATIONS.md",
 "../joint_history/HISTORY.md"])
