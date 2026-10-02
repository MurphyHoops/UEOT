import UEOT.V3.Compression.CrossTrack.DualIsolationCanonical
import UEOT.V3.Resolution

/-!
# Dual Isolation — exact P-RES-06 realization branch

P-RES-06 already contains a genuine exact identifiability mechanism: equality
of the lower/upper realization endpoints is equivalent to uniqueness of every
active microscopic fibre.  This module connects that exact resolution result
to Parent Binding.

The result is deliberately specialized.  It does not claim that all P-COMP
parent completions are resolution fibres.
-/

namespace UEOT.V3.Compression.CrossTrack

open UEOT.V3
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.InvariantSetGaugeInvariance
open UEOT.V3.Compression.TopologyChangingGoaL1ResidualConorm

universe uP uC uV uW uS

noncomputable section

variable {P : Type uP} {C : Type uC}
variable {V : Type uV} {W : Type uW}
variable [MetricSpace V]
variable {S : Type uS} [Fintype S] [Nonempty S]
noncomputable local instance dualIsolationResolutionDecidableEq : DecidableEq S :=
  Classical.decEq S

/-- Endpoint collapse in P-RES-06 makes every active resolution fibre exact. -/
theorem resolutionEndpointCollapse_exactActiveRealization
    (coarse : V → W) (D : Set (Set W))
    (hsurj : Function.Surjective coarse)
    (hD : UEOT.V3.Resolution.IsAntichain D)
    (hendpoints :
      UEOT.Resolution.lower coarse (UEOT.V3.Resolution.UpClosure D) =
        UEOT.Resolution.upper coarse (UEOT.V3.Resolution.UpClosure D))
    (w : W) (hw : UEOT.V3.Resolution.Active D w)
    {v₁ v₂ : V}
    (hv₁ : coarse v₁ = w) (hv₂ : coarse v₂ = w) :
    v₁ = v₂ := by
  have hunique : UEOT.V3.Resolution.UniqueFiber coarse w :=
    ((UEOT.V3.Resolution.endpoint_equality_iff_unique_active_fibers
      coarse D hsurj hD).1 hendpoints) w hw
  rcases hunique with ⟨v, hv, honly⟩
  exact (honly v₁ hv₁).trans (honly v₂ hv₂).symm

/-- **Exact-resolution dual-isolation specialization.**

If all richer parent completions in one child fibre realize the same active
coarse atom, then P-RES-06 endpoint collapse forces exact microscopic
realization equality.  Parent Binding then gives zero long-run semantic
diameter under the already explicit semantic-isolation assumptions. -/
theorem resolutionEndpointCollapse_parentSemanticDiameter_zero
    (pi : P → C)
    (repr : P → V)
    (coarse : V → W) (D : Set (Set W))
    (hsurj : Function.Surjective coarse)
    (hD : UEOT.V3.Resolution.IsAntichain D)
    (hendpoints :
      UEOT.Resolution.lower coarse (UEOT.V3.Resolution.UpClosure D) =
        UEOT.Resolution.upper coarse (UEOT.V3.Resolution.UpClosure D))
    (w : W) (hw : UEOT.V3.Resolution.Active D w)
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
    (hrealize : ∀ p, pi p = c → coarse (repr p) = w)
    (hisolationFloor : ∀ p, pi p = c →
      kappaMin ≤ l1ResidualConorm (K p)) :
    fiberSemanticDiameter pi mu c ≤ 0 := by
  apply parentSemanticDiameter_zero_of_exact_binding
    pi repr K hK bind mu hmu c hfiberNonempty
    kappaMin hkappaMin hcard
  · intro p q hp hq
    exact resolutionEndpointCollapse_exactActiveRealization
      coarse D hsurj hD hendpoints w hw (hrealize p hp) (hrealize q hq)
  · exact hisolationFloor

end

end UEOT.V3.Compression.CrossTrack
