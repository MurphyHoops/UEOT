import UEOT.V3.PathEventKL
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# P-KL-02 — exact event I-projection

The frozen Core 3 source minimizes KL divergence over all path laws absolutely
continuous with respect to a baseline `P0`, subject only to a lower bound on a
measurable event probability.  The optimizer for the active constraint is the
explicit two-region density

`(p / q) 1_A + ((1-p)/(1-q)) 1_{Aᶜ}`,

where `q = P0(A)` and `0 < q < 1`.

This file keeps that density as an actual Lean definition.  The source-facing
theorem will prove its probability, absolute-continuity, event mass and exact-KL
properties before using P-KL-01 to establish global optimality among all
absolutely continuous path laws.
-/

namespace UEOT.V3.PathEventIProjection

noncomputable section

open MeasureTheory InformationTheory
open UEOT.V3.InformationBernoulliKL
open UEOT.V3.PathEventKL

universe uX

variable {X : Type uX} [MeasurableSpace X]

/-- The frozen P-KL-02 Radon--Nikodym density, written directly on the two
regions `A` and `Aᶜ`. -/
noncomputable def eventTiltDensity
    (P0 : Measure X) (A : Set X) (p : ℝ) : X → ENNReal := by
  classical
  exact fun x =>
    if x ∈ A then ENNReal.ofReal (p / P0.real A)
    else ENNReal.ofReal ((1 - p) / (1 - P0.real A))

lemma measurable_eventTiltDensity
    (P0 : Measure X) (A : Set X) (p : ℝ) (hA : MeasurableSet A) :
    Measurable (eventTiltDensity P0 A p) := by
  classical
  unfold eventTiltDensity
  exact Measurable.ite hA measurable_const measurable_const

/-- Explicit P-KL-02 candidate optimizer.  Defining it by `withDensity` makes
its source-prescribed Radon--Nikodym form part of the construction rather than
a post-hoc existence statement. -/
noncomputable def eventIProjection
    (P0 : Measure X) (A : Set X) (p : ℝ) : Measure X :=
  P0.withDensity (eventTiltDensity P0 A p)

/-- The explicit event tilt never creates new support. -/
theorem eventIProjection_ac
    (P0 : Measure X) (A : Set X) (p : ℝ) :
    eventIProjection P0 A p ≪ P0 := by
  unfold eventIProjection
  exact withDensity_absolutelyContinuous P0 (eventTiltDensity P0 A p)

/-- The RN derivative is exactly the frozen two-region density whenever the
event is measurable. -/
theorem eventIProjection_rnDeriv
    (P0 : Measure X) [SigmaFinite P0]
    (A : Set X) (p : ℝ) (hA : MeasurableSet A) :
    (eventIProjection P0 A p).rnDeriv P0 =ᵐ[P0]
      eventTiltDensity P0 A p := by
  unfold eventIProjection
  exact Measure.rnDeriv_withDensity P0
    (measurable_eventTiltDensity P0 A p hA)

/-- On the constrained event, the active event tilt has exactly mass `p`. -/
theorem eventIProjection_apply_event
    (P0 : Measure X) [IsProbabilityMeasure P0]
    (A : Set X) (p : ℝ) (hA : MeasurableSet A)
    (hp0 : 0 ≤ p) (hq0 : 0 < P0.real A) :
    eventIProjection P0 A p A = ENNReal.ofReal p := by
  classical
  unfold eventIProjection
  rw [withDensity_apply _ hA]
  rw [setLIntegral_congr_fun
    (g := fun _ => ENNReal.ofReal (p / P0.real A)) hA
    (fun x hx => by simp [eventTiltDensity, hx])]
  rw [MeasureTheory.lintegral_const]
  rw [Measure.restrict_apply_univ]
  rw [← ofReal_measureReal (μ := P0) (s := A)]
  rw [← ENNReal.ofReal_mul (div_nonneg hp0 hq0.le)]
  rw [div_mul_cancel₀ p hq0.ne']

/-- On the complement, the active event tilt has exactly the remaining mass. -/
theorem eventIProjection_apply_compl
    (P0 : Measure X) [IsProbabilityMeasure P0]
    (A : Set X) (p : ℝ) (hA : MeasurableSet A)
    (hp1 : p ≤ 1) (hq1 : P0.real A < 1) :
    eventIProjection P0 A p Aᶜ = ENNReal.ofReal (1 - p) := by
  classical
  have hden : 0 < 1 - P0.real A := sub_pos.mpr hq1
  have hcomp : P0.real Aᶜ = 1 - P0.real A := by
    rw [measureReal_compl hA]
    simp [measureReal_def]
  unfold eventIProjection
  rw [withDensity_apply _ hA.compl]
  rw [setLIntegral_congr_fun
    (g := fun _ => ENNReal.ofReal ((1 - p) / (1 - P0.real A))) hA.compl
    (fun x hx => by
      have hxA : x ∉ A := by simpa using hx
      simp [eventTiltDensity, hxA])]
  rw [MeasureTheory.lintegral_const]
  rw [Measure.restrict_apply_univ]
  rw [← ofReal_measureReal (μ := P0) (s := Aᶜ)]
  rw [hcomp]
  rw [← ENNReal.ofReal_mul (div_nonneg (sub_nonneg.mpr hp1) hden.le)]
  rw [div_mul_cancel₀ (1 - p) hden.ne']

/-- Under the frozen active-case hypotheses, the explicit optimizer is itself a
probability law. -/
theorem eventIProjection_isProbability
    (P0 : Measure X) [IsProbabilityMeasure P0]
    (A : Set X) (p : ℝ) (hA : MeasurableSet A)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 < P0.real A) (hq1 : P0.real A < 1) :
    IsProbabilityMeasure (eventIProjection P0 A p) := by
  constructor
  rw [← measure_add_measure_compl hA]
  rw [eventIProjection_apply_event P0 A p hA hp0 hq0]
  rw [eventIProjection_apply_compl P0 A p hA hp1 hq1]
  rw [← ENNReal.ofReal_add hp0 (sub_nonneg.mpr hp1)]
  norm_num

/-- The KL divergence of the explicit event tilt is the two-region `klFun`
expression dictated by its RN density.  This is kept in `ENNReal`, so the
endpoint `p = 1` requires no separate logarithmic-integrability hypothesis. -/
theorem eventIProjection_klDiv_formula
    (P0 : Measure X) [IsProbabilityMeasure P0]
    (A : Set X) (p : ℝ) (hA : MeasurableSet A)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 < P0.real A) (hq1 : P0.real A < 1) :
    klDiv (eventIProjection P0 A p) P0 =
      ENNReal.ofReal (klFun (p / P0.real A)) * P0 A +
        ENNReal.ofReal (klFun ((1 - p) / (1 - P0.real A))) * P0 Aᶜ := by
  letI : IsProbabilityMeasure (eventIProjection P0 A p) :=
    eventIProjection_isProbability P0 A p hA hp0 hp1 hq0 hq1
  rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac
    (eventIProjection_ac P0 A p)]
  trans ∫⁻ x,
      ENNReal.ofReal (klFun (eventTiltDensity P0 A p x).toReal) ∂P0
  · apply lintegral_congr_ae
    filter_upwards [eventIProjection_rnDeriv P0 A p hA] with x hx
    rw [hx]
  rw [← lintegral_add_compl _ hA]
  rw [setLIntegral_congr_fun
    (g := fun _ => ENNReal.ofReal (klFun (p / P0.real A))) hA
    (fun x hx => by
      have hratio : 0 ≤ p / P0.real A := div_nonneg hp0 hq0.le
      unfold eventTiltDensity
      rw [if_pos hx, ENNReal.toReal_ofReal hratio])]
  rw [setLIntegral_congr_fun
    (g := fun _ => ENNReal.ofReal (klFun ((1 - p) / (1 - P0.real A)))) hA.compl
    (fun x hx => by
      have hxA : x ∉ A := by simpa using hx
      have hratio : 0 ≤ (1 - p) / (1 - P0.real A) :=
        div_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hq1.le)
      unfold eventTiltDensity
      rw [if_neg hxA, ENNReal.toReal_ofReal hratio])]
  rw [MeasureTheory.lintegral_const, MeasureTheory.lintegral_const]
  rw [Measure.restrict_apply_univ, Measure.restrict_apply_univ]

end

end UEOT.V3.PathEventIProjection
