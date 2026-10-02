import UEOT.V3.Compression.CrossTrack.ParentSemanticStability

/-!
# Track X — X5 robust parent semantic certificate

This is a derived, typed G2 certificate.  It packages exactly the finite-state
data consumed by X4.  It is not Objecthood, teleology, selection-unit identity,
or a counted-core primitive.
-/

namespace UEOT.V3.Compression.CrossTrack

open UEOT.V3
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.InvariantSetGaugeInvariance
open UEOT.V3.Compression.TopologyChangingGoaL1ResidualConorm

universe uP uC uS

noncomputable section

variable {P : Type uP} {C : Type uC}
variable {S : Type uS} [Fintype S] [Nonempty S]
noncomputable local instance robustParentCertificateDecidableEq : DecidableEq S :=
  Classical.decEq S

/-- **X5 — derived robust parent-semantic certificate.**

The certificate fixes one child-evidence fibre, supplies an invariant law for
each parent completion, bounds the pairwise within-fibre row defect, and gives
a uniform positive lower floor on canonical residual isolation. -/
structure RobustParentSemanticCertificate
    (pi : P → C)
    (K : P → Matrix S S ℝ)
    (hK : ∀ p, K p ∈ Matrix.rowStochastic ℝ S) where
  child : C
  invariantLaw : P → stdSimplex ℝ S
  invariant : ∀ p,
    invariantLaw p ∈ invariantLawSet (K p) (hK p)
  epsilon : ℝ
  epsilon_nonneg : 0 ≤ epsilon
  kappaMin : ℝ
  kappaMin_pos : 0 < kappaMin
  fiber_nonempty : ∃ p, pi p = child
  row_defect : ∀ p q, pi p = child → pi q = child → ∀ x,
    crossRowTV (K p) (hK p) (K q) (hK q) x ≤ epsilon
  isolation_floor : ∀ p, pi p = child →
    kappaMin ≤ l1ResidualConorm (K p)

/-- Every two completions certified over the same child evidence lie inside
the certificate's semantic tracking radius. -/
theorem RobustParentSemanticCertificate.pairwise_bound
    (pi : P → C)
    (K : P → Matrix S S ℝ)
    (hK : ∀ p, K p ∈ Matrix.rowStochastic ℝ S)
    (cert : RobustParentSemanticCertificate pi K hK)
    (hcard : 1 < Fintype.card S)
    {p q : P}
    (hp : pi p = cert.child)
    (hq : pi q = cert.child) :
    lawTV (cert.invariantLaw p) (cert.invariantLaw q) ≤
      cert.epsilon / cert.kappaMin := by
  exact x4_fiber_pairwiseSemanticBound
    pi K hK cert.invariantLaw cert.invariant cert.child
    cert.epsilon cert.kappaMin
    cert.epsilon_nonneg cert.kappaMin_pos hcard
    cert.row_defect cert.isolation_floor hp hq

/-- The full certified parent-completion fibre has the same
`epsilon / kappaMin` diameter bound. -/
theorem RobustParentSemanticCertificate.diameter_bound
    (pi : P → C)
    (K : P → Matrix S S ℝ)
    (hK : ∀ p, K p ∈ Matrix.rowStochastic ℝ S)
    (cert : RobustParentSemanticCertificate pi K hK)
    (hcard : 1 < Fintype.card S) :
    fiberSemanticDiameter pi cert.invariantLaw cert.child ≤
      cert.epsilon / cert.kappaMin := by
  exact x4_fiberSemanticDiameter
    pi K hK cert.invariantLaw cert.invariant cert.child
    cert.fiber_nonempty cert.epsilon cert.kappaMin
    cert.epsilon_nonneg cert.kappaMin_pos hcard
    cert.row_defect cert.isolation_floor

end

end UEOT.V3.Compression.CrossTrack
