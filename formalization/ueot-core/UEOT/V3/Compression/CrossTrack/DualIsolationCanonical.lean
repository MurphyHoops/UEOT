import UEOT.V3.Compression.CrossTrack.DualIsolationConorm

/-!
# Canonical dual-isolation semantic bound

On a finite nontrivial assembly space the binding margin can be chosen
canonically.  The final denominator then contains the product of two distinct
canonical isolation gains:

* `bindingIsolationConorm diagnostic` — assembly identifiability;
* `l1ResidualConorm K` (uniformly bounded below) — long-run semantic isolation.
-/

namespace UEOT.V3.Compression.CrossTrack

open UEOT.V3
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.InvariantSetGaugeInvariance
open UEOT.V3.Compression.TopologyChangingGoaL1ResidualConorm

universe uP uC uA uY uS

noncomputable section

variable {P : Type uP} {C : Type uC}
variable {A : Type uA} {Y : Type uY}
variable [Fintype A] [Nontrivial A] [MetricSpace A] [MetricSpace Y]
variable {S : Type uS} [Fintype S] [Nonempty S]
noncomputable local instance dualIsolationCanonicalDecidableEq : DecidableEq S :=
  Classical.decEq S

/-- **Canonical dual-isolation theorem.**

For a finite assembly space with an injective lower-level diagnostic, the
canonical binding conorm is positive.  Together with parent realization
Lipschitz regularity and a uniform positive Track-S semantic-isolation floor,
one diagnostic error ball controls the whole parent long-run semantic fibre. -/
theorem canonicalDualIsolation_fiberSemanticDiameter
    (pi : P → C)
    (repr : P → A)
    (diagnostic : A → Y)
    (hdiagInjective : Function.Injective diagnostic)
    (eta : ℝ) (heta : 0 ≤ eta)
    (observed : Y)
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
    (hobs : ∀ p, pi p = c →
      dist (diagnostic (repr p)) observed ≤ eta)
    (hisolationFloor : ∀ p, pi p = c →
      kappaMin ≤ l1ResidualConorm (K p)) :
    fiberSemanticDiameter pi mu c ≤
      (2 * bind.L * eta) /
        (bindingIsolationConorm diagnostic * kappaMin) := by
  have hbindIso := canonicalBindingIsolation_of_injective diagnostic hdiagInjective
  exact dualIsolation_fiberSemanticDiameter_normalized
    pi repr diagnostic (bindingIsolationConorm diagnostic) eta
    hbindIso heta observed K hK bind mu hmu c hfiberNonempty
    kappaMin hkappaMin hcard hobs hisolationFloor

/-- Canonical binding isolation and Track-S semantic isolation are logically
distinct: diagnostic injectivity supplies the first denominator, while the
parent-kernel residual conorm supplies the second. -/
theorem canonicalDualIsolation_two_positive_margins
    (diagnostic : A → Y) (hdiagInjective : Function.Injective diagnostic)
    (P0 : Matrix S S ℝ)
    (hsemantic : 0 < l1ResidualConorm P0) :
    0 < bindingIsolationConorm diagnostic ∧
      0 < l1ResidualConorm P0 := by
  exact ⟨(bindingIsolationConorm_pos_iff_injective diagnostic).2 hdiagInjective,
    hsemantic⟩

end

end UEOT.V3.Compression.CrossTrack
