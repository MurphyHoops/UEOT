import UEOT.V3.PathEventIProjection
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace UEOT.V3.PathEventIProjection

noncomputable section

open MeasureTheory InformationTheory
open UEOT.V3.InformationBernoulliKL
open UEOT.V3.PathEventKL

universe uX

variable {X : Type uX} [MeasurableSpace X]

theorem eventIProjection_klDiv_toReal
    (P0 : Measure X) [IsProbabilityMeasure P0]
    (A : Set X) (p : ℝ) (hA : MeasurableSet A)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 < P0.real A) (hq1 : P0.real A < 1) :
    (klDiv (eventIProjection P0 A p) P0).toReal =
      p * Real.log (p / P0.real A) +
        (1 - p) * Real.log ((1 - p) / (1 - P0.real A)) := by
  have hqne : P0.real A ≠ 0 := hq0.ne'
  have h1qne : 1 - P0.real A ≠ 0 := sub_ne_zero.mpr hq1.ne'
  have hratioA : 0 ≤ p / P0.real A := div_nonneg hp0 hq0.le
  have hratioB : 0 ≤ (1 - p) / (1 - P0.real A) :=
    div_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hq1.le)
  have hcomp : P0.real Aᶜ = 1 - P0.real A := by
    rw [measureReal_compl hA]
    simp [measureReal_def]
  have hAalg :
      P0.real A * klFun (p / P0.real A) =
        p * Real.log (p / P0.real A) + P0.real A - p := by
    rw [klFun_apply]
    field_simp [hqne]
  have hBalg :
      (1 - P0.real A) * klFun ((1 - p) / (1 - P0.real A)) =
        (1 - p) * Real.log ((1 - p) / (1 - P0.real A)) +
          (1 - P0.real A) - (1 - p) := by
    rw [klFun_apply]
    field_simp [h1qne]
  rw [eventIProjection_klDiv_formula P0 A p hA hp0 hp1 hq0 hq1]
  rw [ENNReal.toReal_add]
  · rw [ENNReal.toReal_mul, ENNReal.toReal_mul]
    rw [ENNReal.toReal_ofReal (klFun_nonneg hratioA),
      ENNReal.toReal_ofReal (klFun_nonneg hratioB)]
    change
      klFun (p / P0.real A) * P0.real A +
        klFun ((1 - p) / (1 - P0.real A)) * P0.real Aᶜ = _
    rw [hcomp]
    rw [mul_comm (klFun (p / P0.real A)) (P0.real A),
      mul_comm (klFun ((1 - p) / (1 - P0.real A))) (1 - P0.real A)]
    rw [hAalg, hBalg]
    ring
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top P0 A)
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top P0 Aᶜ)

theorem eventIProjection_klDiv_eq_dBern
    (P0 : Measure X) [IsProbabilityMeasure P0]
    (A : Set X) (p : ℝ) (hA : MeasurableSet A)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 < P0.real A) (hq1 : P0.real A < 1) :
    klDiv (eventIProjection P0 A p) P0 = dBern p (P0.real A) := by
  have hopt : klDiv (eventIProjection P0 A p) P0 ≠ ⊤ := by
    rw [eventIProjection_klDiv_formula P0 A p hA hp0 hp1 hq0 hq1]
    exact ENNReal.add_ne_top.mpr ⟨
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top P0 A),
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top P0 Aᶜ)⟩
  have hbern : dBern p (P0.real A) ≠ ⊤ := by
    unfold dBern
    exact klDiv_ne_top
      (bernoulliLaw_ac_of_reference_interior hq0 hq1)
      bernoulliLaw_llr_integrable
  apply (ENNReal.toReal_eq_toReal_iff' hopt hbern).mp
  rw [eventIProjection_klDiv_toReal P0 A p hA hp0 hp1 hq0 hq1]
  unfold dBern
  exact (bernoulliLaw_klDiv_toReal hp0 hp1 hq0 hq1).symm

end

end UEOT.V3.PathEventIProjection
