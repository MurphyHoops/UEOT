import UEOT.V3.HilbertMeanCenteredFiber
import Mathlib.Tactic

/-!
# P-STAT-06 — unit-ball clipping of active-coordinate sections

The frozen source gives unit-ball support only almost everywhere under the
active marginal law.  To reuse the exact global-range lemmas without silently
strengthening that assumption, replace values outside the unit ball by the
value at zero.  The clipped section agrees with the original section almost
everywhere, while any unit-ball pairwise oscillation bound becomes a global
pairwise oscillation bound.
-/

namespace UEOT.V3.HilbertMeanUnitClip

open MeasureTheory

universe uH

variable {H : Type uH} [NormedAddCommGroup H]

/-- Replace a section outside the closed unit ball by its value at zero. -/
def unitClip (q : H → ℝ) (a : H) : ℝ :=
  if ‖a‖ ≤ 1 then q a else q 0

@[simp] theorem unitClip_eq_of_norm_le (q : H → ℝ) {a : H} (ha : ‖a‖ ≤ 1) :
    unitClip q a = q a := by
  simp [unitClip, ha]

@[simp] theorem unitClip_zero (q : H → ℝ) : unitClip q 0 = q 0 := by
  simp [unitClip]

/-- Under unit-ball support, clipping does not change the section almost
everywhere. -/
theorem unitClip_ae_eq
    [MeasurableSpace H]
    (ν : Measure H) (q : H → ℝ)
    (hunit : ∀ᵐ a ∂ν, ‖a‖ ≤ 1) :
    unitClip q =ᵐ[ν] q := by
  filter_upwards [hunit] with a ha
  exact unitClip_eq_of_norm_le q ha

/-- A pairwise oscillation bound required only on unit-ball arguments becomes a
fully global oscillation bound after clipping. -/
theorem unitClip_pairwise_abs_sub_le
    (q : H → ℝ) {c : ℝ}
    (hosc : ∀ a b, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → |q a - q b| ≤ c) :
    ∀ a b, |unitClip q a - unitClip q b| ≤ c := by
  intro a b
  by_cases ha : ‖a‖ ≤ 1
  · by_cases hb : ‖b‖ ≤ 1
    · simpa [unitClip, ha, hb] using hosc a b ha hb
    · simpa [unitClip, ha, hb] using hosc a 0 ha (by simp)
  · by_cases hb : ‖b‖ ≤ 1
    · simpa [unitClip, ha, hb] using hosc 0 b (by simp) hb
    · simpa [unitClip, ha, hb] using hosc 0 0 (by simp) (by simp)

/-- Borel measurability is preserved by unit-ball clipping. -/
theorem measurable_unitClip
    [MeasurableSpace H] [BorelSpace H]
    (q : H → ℝ) (hq : Measurable q) :
    Measurable (unitClip q) := by
  have hs : MeasurableSet {a : H | ‖a‖ ≤ 1} :=
    measurableSet_le continuous_norm.measurable measurable_const
  exact hq.ite hs measurable_const

end UEOT.V3.HilbertMeanUnitClip
