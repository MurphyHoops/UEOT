import UEOT.V3.Compression.CrossTrack.ParentBindingNoGo
import UEOT.V3.Compression.CrossTrack.ParentSemanticStability

/-!
# Parent Binding Mechanism — PB1/PB2/PB3 static bridge

The missing Track-X premise is not hidden in a new primitive. It is exposed as
regularity of a domain realization map from richer parent-completion data to
finite parent dynamics.

If one child-evidence fibre is small in an assembly-space metric and the
realization map is row-TV Lipschitz, then the Track-X dynamics defect is
generated rather than postulated. Track-S residual isolation then converts
that generated dynamics defect into a long-run semantic bound.
-/

namespace UEOT.V3.Compression.CrossTrack

open UEOT.V3
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.InvariantSetGaugeInvariance
open UEOT.V3.Compression.TopologyChangingGoaL1ResidualConorm

universe uP uC uA uS

noncomputable section

variable {P : Type uP} {C : Type uC} {A : Type uA}
variable [PseudoMetricSpace A]
variable {S : Type uS} [Fintype S] [Nonempty S]
noncomputable local instance parentBindingStaticDecidableEq : DecidableEq S :=
  Classical.decEq S

/-- Domain binding regularity.

`repr p` is the domain-level assembly realization of richer parent completion
`p`. The certificate says only that the induced finite parent kernel varies
Lipschitz-continuously, rowwise in total variation, with this domain
realization. It does not assert that child evidence uniquely determines
`repr`, nor does it contain any long-run semantic conclusion. -/
structure ParentBindingLipschitz
    (repr : P → A)
    (K : P → Matrix S S ℝ)
    (hK : ∀ p, K p ∈ Matrix.rowStochastic ℝ S) where
  L : ℝ
  L_nonneg : 0 ≤ L
  row_lipschitz : ∀ p q x,
    crossRowTV (K p) (hK p) (K q) (hK q) x ≤
      L * dist (repr p) (repr q)

/-- **PB1/PB2 — binding regularity generates the Track-X row defect.**

If all richer parent completions over one child-evidence fibre lie within
assembly distance `delta`, the rowwise dynamics defect is at most
`L * delta`. -/
theorem parentRowDefect_of_binding
    (pi : P → C)
    (repr : P → A)
    (K : P → Matrix S S ℝ)
    (hK : ∀ p, K p ∈ Matrix.rowStochastic ℝ S)
    (bind : ParentBindingLipschitz repr K hK)
    (c : C) (delta : ℝ)
    (_hdelta : 0 ≤ delta)
    (hfiber : ∀ p q, pi p = c → pi q = c →
      dist (repr p) (repr q) ≤ delta)
    {p q : P}
    (hp : pi p = c) (hq : pi q = c)
    (x : S) :
    crossRowTV (K p) (hK p) (K q) (hK q) x ≤
      bind.L * delta := by
  calc
    crossRowTV (K p) (hK p) (K q) (hK q) x
        ≤ bind.L * dist (repr p) (repr q) :=
      bind.row_lipschitz p q x
    _ ≤ bind.L * delta :=
      mul_le_mul_of_nonneg_left (hfiber p q hp hq) bind.L_nonneg

/-- **PB3 — static parent-emergence stability bound.**

A child fibre of assembly diameter at most `delta`, realized into parent
kernels with row-TV Lipschitz constant `L`, and carrying a uniform positive
Track-S residual-isolation floor `kappaMin`, has long-run semantic diameter at
most `L * delta / kappaMin`.

This is exactly the missing bridge identified after Track X:
assembly uncertainty -> dynamics uncertainty -> long-run semantic uncertainty.
-/
theorem parentSemanticDiameter_of_binding
    (pi : P → C)
    (repr : P → A)
    (K : P → Matrix S S ℝ)
    (hK : ∀ p, K p ∈ Matrix.rowStochastic ℝ S)
    (bind : ParentBindingLipschitz repr K hK)
    (mu : P → stdSimplex ℝ S)
    (hmu : ∀ p, mu p ∈ invariantLawSet (K p) (hK p))
    (c : C)
    (hfiberNonempty : ∃ p, pi p = c)
    (delta kappaMin : ℝ)
    (hdelta : 0 ≤ delta)
    (hkappaMin : 0 < kappaMin)
    (hcard : 1 < Fintype.card S)
    (hfiber : ∀ p q, pi p = c → pi q = c →
      dist (repr p) (repr q) ≤ delta)
    (hisolationFloor : ∀ p, pi p = c →
      kappaMin ≤ l1ResidualConorm (K p)) :
    fiberSemanticDiameter pi mu c ≤
      (bind.L * delta) / kappaMin := by
  apply x4_fiberSemanticDiameter
      pi K hK mu hmu c hfiberNonempty
      (bind.L * delta) kappaMin
  · exact mul_nonneg bind.L_nonneg hdelta
  · exact hkappaMin
  · exact hcard
  · intro p q hp hq x
    exact parentRowDefect_of_binding
      pi repr K hK bind c delta hdelta hfiber hp hq x
  · exact hisolationFloor

/-- Exact assembly collapse is an exact semantic-collapse corollary of PB3.
This is not a new quotient theorem: exactness enters only through zero assembly
diameter and the already-established stability bridge. -/
theorem parentSemanticDiameter_zero_of_exact_binding
    (pi : P → C)
    (repr : P → A)
    (K : P → Matrix S S ℝ)
    (hK : ∀ p, K p ∈ Matrix.rowStochastic ℝ S)
    (bind : ParentBindingLipschitz repr K hK)
    (mu : P → stdSimplex ℝ S)
    (hmu : ∀ p, mu p ∈ invariantLawSet (K p) (hK p))
    (c : C)
    (hfiberNonempty : ∃ p, pi p = c)
    (kappaMin : ℝ)
    (hkappaMin : 0 < kappaMin)
    (hcard : 1 < Fintype.card S)
    (hexact : ∀ p q, pi p = c → pi q = c → repr p = repr q)
    (hisolationFloor : ∀ p, pi p = c →
      kappaMin ≤ l1ResidualConorm (K p)) :
    fiberSemanticDiameter pi mu c ≤ 0 := by
  have hbound := parentSemanticDiameter_of_binding
    pi repr K hK bind mu hmu c hfiberNonempty
    0 kappaMin (le_rfl) hkappaMin hcard
    (by
      intro p q hp hq
      simpa [hexact p q hp hq])
    hisolationFloor
  simpa using hbound

end

end UEOT.V3.Compression.CrossTrack
