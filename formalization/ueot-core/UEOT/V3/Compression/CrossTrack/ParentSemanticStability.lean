import UEOT.V3.Compression.CrossTrack.ParentSemanticCore

/-!
# Track X — X3/X4 quantitative parent-semantic stability

The source parent completion supplies the residual-isolation denominator.
Target invariant-law existence is always explicit.
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
noncomputable local instance parentSemanticStabilityDecidableEq : DecidableEq S :=
  Classical.decEq S

/-- **X3 — quantitative parent-semantic stability.**

For any explicitly supplied target completion in the same child fibre, its
explicit invariant law lies within the canonical
`epsilonBind / l1ResidualConorm (K p0)` source radius.  No target existence
claim is inferred from source isolation. -/
theorem x3_parentSemanticTracking
    (pi : P → C)
    (K : P → Matrix S S ℝ)
    (hK : ∀ p, K p ∈ Matrix.rowStochastic ℝ S)
    (mu : P → stdSimplex ℝ S)
    (hmu : ∀ p, mu p ∈ invariantLawSet (K p) (hK p))
    (p0 p : P)
    (_hsame : pi p = pi p0)
    (epsilonBind : ℝ)
    (hcard : 1 < Fintype.card S)
    (hisolation : 0 < l1ResidualConorm (K p0))
    (hrow : ∀ x,
      crossRowTV (K p0) (hK p0) (K p) (hK p) x ≤ epsilonBind) :
    lawTV (mu p0) (mu p) ≤
      epsilonBind / l1ResidualConorm (K p0) := by
  exact suppliedInvariant_tracking
    (K p0) (hK p0) (K p) (hK p)
    (mu p0) (mu p) (hmu p0) (hmu p)
    epsilonBind hcard hisolation hrow

/-- Pairwise X4 form before taking the fibre supremum.  The exact constant
supported by the Track-S interface is `epsilon / kappaMin`, with no factor
two. -/
theorem x4_fiber_pairwiseSemanticBound
    (pi : P → C)
    (K : P → Matrix S S ℝ)
    (hK : ∀ p, K p ∈ Matrix.rowStochastic ℝ S)
    (mu : P → stdSimplex ℝ S)
    (hmu : ∀ p, mu p ∈ invariantLawSet (K p) (hK p))
    (c : C)
    (epsilon kappaMin : ℝ)
    (hepsilon : 0 ≤ epsilon)
    (hkappaMin : 0 < kappaMin)
    (hcard : 1 < Fintype.card S)
    (hrow : ∀ p q, pi p = c → pi q = c → ∀ x,
      crossRowTV (K p) (hK p) (K q) (hK q) x ≤ epsilon)
    (hisolationFloor : ∀ p, pi p = c →
      kappaMin ≤ l1ResidualConorm (K p))
    {p q : P}
    (hp : pi p = c) (hq : pi q = c) :
    lawTV (mu p) (mu q) ≤ epsilon / kappaMin := by
  have hsourceIsolation : 0 < l1ResidualConorm (K p) :=
    lt_of_lt_of_le hkappaMin (hisolationFloor p hp)
  have htrack :
      lawTV (mu p) (mu q) ≤ epsilon / l1ResidualConorm (K p) := by
    apply x3_parentSemanticTracking
      pi K hK mu hmu p q
    · exact hq.trans hp.symm
    · exact hcard
    · exact hsourceIsolation
    · exact hrow p q hp hq
  have hradius :
      epsilon / l1ResidualConorm (K p) ≤ epsilon / kappaMin :=
    div_le_div_of_nonneg_left hepsilon hkappaMin (hisolationFloor p hp)
  exact htrack.trans hradius

/-- **X4 — fibre-wide parent semantic diameter.**

If the fibre is nonempty, every pair of parent completions in it has row-kernel
defect at most `epsilon`, and every source completion has canonical residual
isolation at least `kappaMin > 0`, then the supremal long-run semantic
diameter is at most `epsilon / kappaMin`. -/
theorem x4_fiberSemanticDiameter
    (pi : P → C)
    (K : P → Matrix S S ℝ)
    (hK : ∀ p, K p ∈ Matrix.rowStochastic ℝ S)
    (mu : P → stdSimplex ℝ S)
    (hmu : ∀ p, mu p ∈ invariantLawSet (K p) (hK p))
    (c : C)
    (hfiber : ∃ p, pi p = c)
    (epsilon kappaMin : ℝ)
    (hepsilon : 0 ≤ epsilon)
    (hkappaMin : 0 < kappaMin)
    (hcard : 1 < Fintype.card S)
    (hrow : ∀ p q, pi p = c → pi q = c → ∀ x,
      crossRowTV (K p) (hK p) (K q) (hK q) x ≤ epsilon)
    (hisolationFloor : ∀ p, pi p = c →
      kappaMin ≤ l1ResidualConorm (K p)) :
    fiberSemanticDiameter pi mu c ≤ epsilon / kappaMin := by
  unfold fiberSemanticDiameter
  apply csSup_le
  · rcases hfiber with ⟨p, hp⟩
    exact ⟨lawTV (mu p) (mu p), p, p, hp, hp, rfl⟩
  · intro d hd
    rcases hd with ⟨p, q, hp, hq, rfl⟩
    exact x4_fiber_pairwiseSemanticBound
      pi K hK mu hmu c epsilon kappaMin
      hepsilon hkappaMin hcard hrow hisolationFloor hp hq

end

end UEOT.V3.Compression.CrossTrack
