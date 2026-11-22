"""Exact 3x2 algebra test, with the necessary state-dependent counterexample."""
import sympy as s
from common import require,finish
ket=lambda j:s.eye(6)[:,j]
u0=(ket(2)+ket(4))/s.sqrt(2);u2=(ket(1)+ket(3))/s.sqrt(2)
rho=(u0*u0.T+u2*u2.T)/2
C=s.diag(*[p+n-s.Rational(5,2) for p in (1,2,3) for n in (0,1)])
Ps=[s.diag(*[int(bool(sign*c>0)) for c in C.diagonal()]) for sign in (-1,1)]
channel=lambda a:sum((P*a*P for P in Ps),s.zeros(6))
out=channel(rho)
evals=(out-rho).eigenvals()
dist=sum(abs(lam)*multiplicity for lam,multiplicity in evals.items())/2
require(dist==s.Rational(1,2),"Bare trace distance")
count=0
for j in range(3):
 for a in range(2):
  for b in range(2):
   O=ket(2*j+a)*ket(2*j+b).T
   require(s.trace((out-rho)*O)==0,"Decomposable operator restriction")
   count+=1
sigx=s.kronecker_product(s.eye(3),s.Matrix([[0,1],[1,0]]))
require(channel(sigx)!=sigx,"Channel incorrectly called algebra identity")
bad=(ket(2)+ket(3))/s.sqrt(2);bad=bad*bad.T
require(s.trace((channel(bad)-bad)*sigx)!=0,"Same-fiber coherence counterexample")
for power in range(7):
 require(s.trace((out-rho)*C**power)==0,"Source energy law not preserved")
finish("operational_state.py",dict(
 exact_matrix_dimension=6, decomposable_basis_operators_checked=count,
 finite_bare_trace_distance=str(dist),
 operational_quotient_principle_reused_from_RELATIONAL=True,
 new_thin_finite_smooth_record_application=True,
 whole_source_derivative_stress_restriction_preserved_for_declared_state=True,
 channel_identity_on_decomposable_algebra=False,
 same_P_fiber_high_energy_coherence_counterexample=True,
 whole_source_stress_incoming_and_actual_transport_frame_fixed=True,
 relative_influence_equality_only_when_common_implementer_exists=True,
 record_conditioned_mean_history_preserved=False,
 whole_device_stress_preserved=False, source_Q_or_phi_observables_preserved=False),
 ["finite_stress/BOUNDARY_STATE.md","finite_stress/FINITE_SLICE_UV.md",
  "constraint_states/RELATIONAL.md"], proof="OPERATIONAL_STATE.md")
