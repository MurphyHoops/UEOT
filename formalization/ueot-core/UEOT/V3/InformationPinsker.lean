import UEOT.V3.TotalVariation
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# P-INFO-02 foundation — measure-level Pinsker inequality

This module supplies the general probability-measure bridge required by the
frozen P-INFO-02 proof contract:

`D_TV(μ,ν) ≤ sqrt((KL(μ || ν)).toReal / 2)`

under absolute continuity and finite KL.  It deliberately reuses
`UEOT.V3.TotalVariation.tvDist`; it does not introduce a second UEOT notion of
total variation.

The proof is a minimal adaptation of the Apache-2.0 formalization in
Jiyuan Tan, `CausalSmith/Causalean/Stat/Minimax/{Scheffe,Pinsker}.lean`
(Copyright (c) 2026 Jiyuan Tan), whose public implementation uses Lean 4.33.0.
The mathematical route is classical: a one-sided Scheffé bound, a scalar lower
bound for Mathlib's `klFun`, and a weighted Cauchy--Schwarz/Hölder argument.

This is prior-art infrastructure, not claimed as a UEOT-original theorem.
-/

namespace UEOT.V3.InformationPinsker

open MeasureTheory Real
open scoped ENNReal
open InformationTheory
open UEOT.V3.TotalVariation

universe uΩ
variable {Ω : Type uΩ} {mΩ : MeasurableSpace Ω}
variable {μ ν : Measure Ω}

/-- Any integrable real function of mean zero has each measurable-set integral
bounded by half of its `L¹` norm.  This is the analytic core of the one-sided
Scheffé inequality. -/
theorem abs_setIntegral_le_half_integral_abs_of_integral_eq_zero
    {f : Ω → ℝ} (hf : Integrable f ν) (hf0 : ∫ x, f x ∂ν = 0)
    {A : Set Ω} (hA : MeasurableSet A) :
    |∫ x in A, f x ∂ν| ≤ (1 / 2) * ∫ x, |f x| ∂ν := by
  have hfA : IntegrableOn f A ν := hf.integrableOn
  have hfAc : IntegrableOn f Aᶜ ν := hf.integrableOn
  have hsplit : ∫ x in A, f x ∂ν + ∫ x in Aᶜ, f x ∂ν = 0 := by
    rw [MeasureTheory.integral_add_compl hA hf, hf0]
  have hcompl : ∫ x in Aᶜ, f x ∂ν = -(∫ x in A, f x ∂ν) := by
    linarith
  have habs : Integrable (fun x => |f x|) ν := hf.abs
  have hsplitabs :
      ∫ x, |f x| ∂ν = (∫ x in A, |f x| ∂ν) + ∫ x in Aᶜ, |f x| ∂ν :=
    (MeasureTheory.integral_add_compl hA habs).symm
  have hbA : ∫ x in A, f x ∂ν ≤ ∫ x in A, |f x| ∂ν :=
    integral_mono_ae hfA habs.integrableOn
      (Filter.Eventually.of_forall fun x => le_abs_self _)
  have hbAc : ∫ x in Aᶜ, f x ∂ν ≤ ∫ x in Aᶜ, |f x| ∂ν :=
    integral_mono_ae hfAc habs.integrableOn
      (Filter.Eventually.of_forall fun x => le_abs_self _)
  have hbAneg : -(∫ x in A, f x ∂ν) ≤ ∫ x in A, |f x| ∂ν := by
    have h : ∫ x in A, (-f x) ∂ν ≤ ∫ x in A, |f x| ∂ν :=
      integral_mono_ae hfA.neg habs.integrableOn
        (Filter.Eventually.of_forall fun x => neg_le_abs _)
    rwa [integral_neg] at h
  have hbAcneg : -(∫ x in Aᶜ, f x ∂ν) ≤ ∫ x in Aᶜ, |f x| ∂ν := by
    have h : ∫ x in Aᶜ, (-f x) ∂ν ≤ ∫ x in Aᶜ, |f x| ∂ν :=
      integral_mono_ae hfAc.neg habs.integrableOn
        (Filter.Eventually.of_forall fun x => neg_le_abs _)
    rwa [integral_neg] at h
  rw [abs_le, hsplitabs]
  constructor
  · nlinarith [hbAneg, hbAc, hcompl]
  · nlinarith [hbA, hbAcneg, hcompl]

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Signed probability-mass difference as a set integral of the RN density
minus one. -/
theorem measureReal_sub_eq_setIntegral_rnDeriv_sub_one (hac : μ ≪ ν)
    {A : Set Ω} (_hA : MeasurableSet A) :
    μ.real A - ν.real A =
      ∫ x in A, ((μ.rnDeriv ν x).toReal - 1) ∂ν := by
  have hp : ∫ x in A, (μ.rnDeriv ν x).toReal ∂ν = μ.real A :=
    Measure.setIntegral_toReal_rnDeriv hac A
  have hint : IntegrableOn (fun x => (μ.rnDeriv ν x).toReal) A ν :=
    Measure.integrable_toReal_rnDeriv.integrableOn
  have hc : IntegrableOn (fun _ : Ω => (1 : ℝ)) A ν :=
    (integrable_const 1).integrableOn
  have h1 : ∫ _ in A, (1 : ℝ) ∂ν = ν.real A := by
    rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
  rw [integral_sub hint hc, hp, h1]

/-- One-sided Scheffé inequality for UEOT's source total-variation distance. -/
theorem tvDist_le_half_integral_abs_rnDeriv (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hac : μ ≪ ν) :
    tvDist μ ν ≤ (1 / 2) * ∫ x, |(μ.rnDeriv ν x).toReal - 1| ∂ν := by
  let f : Ω → ℝ := fun x => (μ.rnDeriv ν x).toReal - 1
  have hint_p : Integrable (fun x => (μ.rnDeriv ν x).toReal) ν :=
    Measure.integrable_toReal_rnDeriv
  have hf : Integrable f ν := hint_p.sub (integrable_const 1)
  have hf0 : ∫ x, f x ∂ν = 0 := by
    rw [show f = fun x => (μ.rnDeriv ν x).toReal - 1 from rfl]
    rw [integral_sub hint_p (integrable_const 1)]
    rw [Measure.integral_toReal_rnDeriv hac]
    simp only [integral_const, smul_eq_mul, mul_one]
    rw [measureReal_def]
    simp [measure_univ]
  unfold tvDist
  refine csSup_le (tvEventSet_nonempty μ ν) ?_
  intro r hr
  rcases hr with ⟨A, hA, rfl⟩
  have hgap : μ.real A - ν.real A = ∫ x in A, f x ∂ν := by
    simpa [f] using measureReal_sub_eq_setIntegral_rnDeriv_sub_one (μ := μ) (ν := ν) hac hA
  rw [hgap]
  exact abs_setIntegral_le_half_integral_abs_of_integral_eq_zero hf hf0 hA

/-! ## Scalar engine -/

private noncomputable def pinskerPhi (x : ℝ) : ℝ :=
  (x + 2) * klFun x - (3 / 2) * (x - 1) ^ 2

private theorem hasDerivAt_pinskerPhi {x : ℝ} (hx : 0 < x) :
    HasDerivAt pinskerPhi (2 * (x + 1) * Real.log x - 4 * (x - 1)) x := by
  have hk : HasDerivAt klFun (Real.log x) x := hasDerivAt_klFun (ne_of_gt hx)
  have hxlog : HasDerivAt (fun y => (y + 2) * klFun y)
      (klFun x + (x + 2) * Real.log x) x := by
    have h1 : HasDerivAt (fun y : ℝ => y + 2) 1 x := by
      simpa using (hasDerivAt_id x).add_const 2
    have h := h1.fun_mul hk
    simpa using h
  have hsq : HasDerivAt (fun y : ℝ => (3 / 2) * (y - 1) ^ 2)
      (3 * (x - 1)) x := by
    have h2 : HasDerivAt (fun y : ℝ => (y - 1) ^ 2) (2 * (x - 1)) x := by
      have h := ((hasDerivAt_id x).sub_const 1).fun_pow 2
      simpa [mul_comm] using h
    have h := h2.const_mul (3 / 2 : ℝ)
    exact h.congr_deriv (by ring)
  have h := hxlog.fun_sub hsq
  refine h.congr_deriv ?_
  rw [klFun]
  ring

private theorem hasDerivAt_pinskerDeriv {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y => 2 * (y + 1) * Real.log y - 4 * (y - 1))
      (2 * (Real.log x + 1 / x - 1)) x := by
  have hlog : HasDerivAt Real.log (1 / x) x := by
    simpa [one_div] using Real.hasDerivAt_log (ne_of_gt hx)
  have h1 : HasDerivAt (fun y : ℝ => 2 * (y + 1)) 2 x := by
    have h : HasDerivAt (fun y : ℝ => 2 * (y + 1)) (2 * 1) x :=
      ((hasDerivAt_id x).add_const 1).const_mul 2
    simpa using h
  have hprod : HasDerivAt (fun y : ℝ => 2 * (y + 1) * Real.log y)
      (2 * Real.log x + 2 * (x + 1) * (1 / x)) x := by
    have h := h1.fun_mul hlog
    convert h using 1
  have hlin : HasDerivAt (fun y : ℝ => 4 * (y - 1)) 4 x := by
    have h : HasDerivAt (fun y : ℝ => 4 * (y - 1)) (4 * 1) x :=
      ((hasDerivAt_id x).sub_const 1).const_mul 4
    simpa using h
  have h := hprod.fun_sub hlin
  refine h.congr_deriv ?_
  field_simp
  ring

private theorem pinskerSecondDeriv_nonneg {x : ℝ} (hx : 0 < x) :
    0 ≤ 2 * (Real.log x + 1 / x - 1) := by
  have hinv : Real.log (1 / x) ≤ 1 / x - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div one_ne_zero (ne_of_gt hx), Real.log_one] at hinv
  nlinarith [hinv]

private theorem pinskerDeriv_monotone :
    MonotoneOn (fun y => 2 * (y + 1) * Real.log y - 4 * (y - 1)) (Set.Ioi 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) ?_ ?_ ?_
  · intro y hy
    exact ((hasDerivAt_pinskerDeriv (hy : (0 : ℝ) < y)).continuousAt).continuousWithinAt
  · intro y hy
    rw [interior_Ioi] at hy
    exact (hasDerivAt_pinskerDeriv hy).differentiableAt.differentiableWithinAt
  · intro y hy
    rw [interior_Ioi] at hy
    rw [(hasDerivAt_pinskerDeriv hy).deriv]
    exact pinskerSecondDeriv_nonneg hy

private noncomputable def pinskerDeriv (y : ℝ) : ℝ :=
  2 * (y + 1) * Real.log y - 4 * (y - 1)

private theorem pinskerDeriv_one : pinskerDeriv 1 = 0 := by
  simp [pinskerDeriv]

private theorem pinskerPhi_one : pinskerPhi 1 = 0 := by
  simp [pinskerPhi, klFun]

private theorem deriv_pinskerPhi {y : ℝ} (hy : 0 < y) :
    deriv pinskerPhi y = pinskerDeriv y :=
  (hasDerivAt_pinskerPhi hy).deriv

private theorem pinskerDeriv_sign {y : ℝ} (hy : 0 < y) :
    (1 ≤ y → 0 ≤ pinskerDeriv y) ∧ (y ≤ 1 → pinskerDeriv y ≤ 0) := by
  have hmono := pinskerDeriv_monotone
  constructor
  · intro h1
    have h := hmono (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 1))
      (Set.mem_Ioi.mpr hy) h1
    simpa [pinskerDeriv, pinskerDeriv_one] using h
  · intro h1
    have h := hmono (Set.mem_Ioi.mpr hy)
      (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 1)) h1
    simpa [pinskerDeriv, pinskerDeriv_one] using h

private theorem pinskerPhi_monotone_Ici :
    MonotoneOn pinskerPhi (Set.Ici 1) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici 1) ?_ ?_ ?_
  · intro y hy
    have hy0 : (0 : ℝ) < y := lt_of_lt_of_le one_pos hy
    exact ((hasDerivAt_pinskerPhi hy0).continuousAt).continuousWithinAt
  · intro y hy
    rw [interior_Ici] at hy
    have hy0 : (0 : ℝ) < y := lt_trans one_pos hy
    exact (hasDerivAt_pinskerPhi hy0).differentiableAt.differentiableWithinAt
  · intro y hy
    rw [interior_Ici] at hy
    have hy0 : (0 : ℝ) < y := lt_trans one_pos hy
    rw [deriv_pinskerPhi hy0]
    exact (pinskerDeriv_sign hy0).1 (le_of_lt hy)

private theorem pinskerPhi_antitone_Ioc :
    AntitoneOn pinskerPhi (Set.Ioc 0 1) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ioc 0 1) ?_ ?_ ?_
  · intro y hy
    exact ((hasDerivAt_pinskerPhi hy.1).continuousAt).continuousWithinAt
  · intro y hy
    rw [interior_Ioc] at hy
    exact (hasDerivAt_pinskerPhi hy.1).differentiableAt.differentiableWithinAt
  · intro y hy
    rw [interior_Ioc] at hy
    rw [deriv_pinskerPhi hy.1]
    exact (pinskerDeriv_sign hy.1).2 (le_of_lt hy.2)

/-- Scalar Pinsker engine in Mathlib's `klFun` normalization. -/
theorem klFun_lower_bound {x : ℝ} (hx : 0 ≤ x) :
    (3 / 2) * (x - 1) ^ 2 / (x + 2) ≤ klFun x := by
  have haux : 0 ≤ (x + 2) * klFun x - (3 / 2) * (x - 1) ^ 2 := by
    suffices h : 0 ≤ pinskerPhi x by simpa [pinskerPhi] using h
    rcases eq_or_lt_of_le hx with h0 | h0
    · rw [← h0]
      norm_num [pinskerPhi, klFun]
    rcases le_total x 1 with hle | hge
    · have h := pinskerPhi_antitone_Ioc
          (Set.mem_Ioc.mpr ⟨h0, hle⟩)
          (Set.mem_Ioc.mpr ⟨one_pos, le_refl 1⟩) hle
      rw [pinskerPhi_one] at h
      exact h
    · have h := pinskerPhi_monotone_Ici
          (Set.mem_Ici.mpr (le_refl 1))
          (Set.mem_Ici.mpr hge) hge
      rw [pinskerPhi_one] at h
      exact h
  have hpos : (0 : ℝ) < x + 2 := by linarith
  rw [div_le_iff₀ hpos]
  nlinarith [haux]

/-- Packaging of the finite-real-valued Pinsker bound. -/
def PinskerBound (μ ν : Measure Ω) : Prop :=
  tvDist μ ν ≤ Real.sqrt ((InformationTheory.klDiv μ ν).toReal / 2)

private theorem pinsker_weight_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ (x - 1) ^ 2 / (x + 2) := by
  exact div_nonneg (sq_nonneg _) (by linarith)

private theorem pinsker_weight_le_klFun {x : ℝ} (hx : 0 ≤ x) :
    (x - 1) ^ 2 / (x + 2) ≤ (2 / 3) * klFun x := by
  have h := klFun_lower_bound hx
  have ha : (3 / 2) * ((x - 1) ^ 2 / (x + 2)) ≤ klFun x := by
    convert h using 1
    ring
  nlinarith

private theorem pinsker_abs_div_sqrt_sq {x : ℝ} (hx : 0 ≤ x) :
    (|x - 1| / Real.sqrt (x + 2)) ^ 2 = (x - 1) ^ 2 / (x + 2) := by
  have hpos : 0 < x + 2 := by linarith
  have hsqrt : Real.sqrt (x + 2) ^ 2 = x + 2 := Real.sq_sqrt (le_of_lt hpos)
  rw [div_pow, hsqrt, sq_abs]

private theorem pinsker_abs_div_sqrt_mul_sqrt {x : ℝ} (hx : 0 ≤ x) :
    (|x - 1| / Real.sqrt (x + 2)) * Real.sqrt (x + 2) = |x - 1| := by
  have hpos : 0 < x + 2 := by linarith
  exact div_mul_cancel₀ _ (ne_of_gt (Real.sqrt_pos_of_pos hpos))

private theorem pinsker_half_sqrt_two_mul (K : ℝ) (hK : 0 ≤ K) :
    (1 / 2) * Real.sqrt (2 * K) = Real.sqrt (K / 2) := by
  have h2K : 0 ≤ 2 * K := by nlinarith
  have hleft : 0 ≤ (1 / 2) * Real.sqrt (2 * K) := by positivity
  symm
  rw [Real.sqrt_eq_iff_eq_sq (by positivity) hleft]
  rw [mul_pow, Real.sq_sqrt h2K]
  ring

/-- General Pinsker inequality for UEOT's total variation, under the hypotheses
needed to turn the `ENNReal` KL value into a faithful finite real number. -/
theorem pinskerBound_of_ac_of_ne_top (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) (hfin : InformationTheory.klDiv μ ν ≠ ⊤) :
    PinskerBound μ ν := by
  let p : Ω → ℝ := fun x => (μ.rnDeriv ν x).toReal
  let K : ℝ := (InformationTheory.klDiv μ ν).toReal
  let g : Ω → ℝ := fun x => (p x - 1) ^ 2 / (p x + 2)
  let f₁ : Ω → ℝ := fun x => |p x - 1| / Real.sqrt (p x + 2)
  let f₂ : Ω → ℝ := fun x => Real.sqrt (p x + 2)
  have hp_nonneg : ∀ x, 0 ≤ p x := by
    intro x
    simp only [p]
    exact ENNReal.toReal_nonneg
  have hK_nonneg : 0 ≤ K := by
    simp only [K]
    exact ENNReal.toReal_nonneg
  have hp_int : Integrable p ν := by
    simp only [p]
    exact Measure.integrable_toReal_rnDeriv
  have hp_meas : AEStronglyMeasurable p ν := by
    simp only [p]
    exact (Measure.measurable_rnDeriv μ ν).ennreal_toReal.aestronglyMeasurable
  have hp_integral_one : ∫ x, p x ∂ν = 1 := by
    simp only [p]
    rw [Measure.integral_toReal_rnDeriv hac]
    rw [measureReal_def, measure_univ]
    simp
  have hllr_int : Integrable (llr μ ν) μ :=
    (InformationTheory.klDiv_ne_top_iff.mp hfin).2
  have hkl_int : Integrable (fun x => klFun (p x)) ν := by
    simp only [p]
    exact (InformationTheory.integrable_klFun_rnDeriv_iff hac).2 hllr_int
  have hK_eq_integral : K = ∫ x, klFun (p x) ∂ν := by
    simp only [K, p]
    exact InformationTheory.toReal_klDiv_eq_integral_klFun hac
  have hg_nonneg : ∀ x, 0 ≤ g x := by
    intro x
    simp only [g]
    exact pinsker_weight_nonneg (hp_nonneg x)
  have hg_le : ∀ x, g x ≤ (2 / 3) * klFun (p x) := by
    intro x
    simp only [g]
    exact pinsker_weight_le_klFun (hp_nonneg x)
  have hg_meas : AEStronglyMeasurable g ν := by
    simp only [g]
    exact (by fun_prop : AEMeasurable (fun x => (p x - 1) ^ 2 / (p x + 2)) ν).aestronglyMeasurable
  have hf₂_meas : AEStronglyMeasurable f₂ ν := by
    simp only [f₂]
    fun_prop
  have hf₁_meas : AEStronglyMeasurable f₁ ν := by
    simp only [f₁]
    exact (by fun_prop : AEMeasurable (fun x => |p x - 1| / Real.sqrt (p x + 2)) ν).aestronglyMeasurable
  have hg_int : Integrable g ν := by
    refine Integrable.mono' (hkl_int.const_mul (2 / 3)) hg_meas ?_
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hg_nonneg x)]
      exact hg_le x
  have hg_integral_le : ∫ x, g x ∂ν ≤ (2 / 3) * K := by
    have hdom_int : Integrable (fun x => (2 / 3) * klFun (p x)) ν :=
      hkl_int.const_mul (2 / 3)
    have hle_int : ∫ x, g x ∂ν ≤ ∫ x, (2 / 3) * klFun (p x) ∂ν :=
      integral_mono_ae hg_int hdom_int (Filter.Eventually.of_forall hg_le)
    calc
      ∫ x, g x ∂ν ≤ ∫ x, (2 / 3) * klFun (p x) ∂ν := hle_int
      _ = (2 / 3) * K := by rw [integral_const_mul, ← hK_eq_integral]
  have hf₁_sq_int : Integrable (fun x => f₁ x ^ 2) ν := by
    refine hg_int.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [f₁, g]
    exact (pinsker_abs_div_sqrt_sq (hp_nonneg x)).symm
  have hf₂_sq_int : Integrable (fun x => f₂ x ^ 2) ν := by
    refine (hp_int.add (integrable_const 2)).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [f₂]
    exact (Real.sq_sqrt (by linarith [hp_nonneg x] : 0 ≤ p x + 2)).symm
  have hf₁L2 : MemLp f₁ (ENNReal.ofReal 2) ν := by
    simpa using (memLp_two_iff_integrable_sq hf₁_meas).2 hf₁_sq_int
  have hf₂L2 : MemLp f₂ (ENNReal.ofReal 2) ν := by
    simpa using (memLp_two_iff_integrable_sq hf₂_meas).2 hf₂_sq_int
  have hf₁_nonneg : 0 ≤ᵐ[ν] f₁ := Filter.Eventually.of_forall fun x => by
    simp only [f₁]
    exact div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have hf₂_nonneg : 0 ≤ᵐ[ν] f₂ := Filter.Eventually.of_forall fun x => by
    simp only [f₂]
    exact Real.sqrt_nonneg _
  have hholder :
      ∫ x, f₁ x * f₂ x ∂ν
        ≤ (∫ x, f₁ x ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ))
          * (∫ x, f₂ x ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) :=
    integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      hf₁_nonneg hf₂_nonneg hf₁L2 hf₂L2
  have hLHS : ∫ x, f₁ x * f₂ x ∂ν = ∫ x, |p x - 1| ∂ν := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      simp only [f₁, f₂]
      exact pinsker_abs_div_sqrt_mul_sqrt (hp_nonneg x)
  have hf₁_rpow : ∫ x, f₁ x ^ (2 : ℝ) ∂ν = ∫ x, g x ∂ν := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      simp only [f₁, g]
      change (|p x - 1| / √(p x + 2)) ^ (2 : ℝ) = (p x - 1) ^ 2 / (p x + 2)
      rw [Real.rpow_two]
      exact pinsker_abs_div_sqrt_sq (hp_nonneg x)
  have hf₂_rpow : ∫ x, f₂ x ^ (2 : ℝ) ∂ν = 3 := by
    have hsqrt_sq : ∫ x, f₂ x ^ (2 : ℝ) ∂ν = ∫ x, p x + 2 ∂ν := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simp only [f₂]
        change √(p x + 2) ^ (2 : ℝ) = p x + 2
        rw [Real.rpow_two]
        exact Real.sq_sqrt (by linarith [hp_nonneg x] : 0 ≤ p x + 2)
    rw [hsqrt_sq]
    calc
      ∫ x, p x + 2 ∂ν = (∫ x, p x ∂ν) + ∫ _ : Ω, (2 : ℝ) ∂ν :=
        integral_add hp_int (integrable_const 2)
      _ = 3 := by rw [hp_integral_one]; norm_num
  have h_int_abs : ∫ x, |p x - 1| ∂ν ≤ Real.sqrt (2 * K) := by
    rw [hLHS, hf₁_rpow, hf₂_rpow] at hholder
    have hrpow_g : (∫ x, g x ∂ν) ^ (1 / (2 : ℝ)) = Real.sqrt (∫ x, g x ∂ν) :=
      (Real.sqrt_eq_rpow (∫ x, g x ∂ν)).symm
    have hrpow_three : (3 : ℝ) ^ (1 / (2 : ℝ)) = Real.sqrt 3 :=
      (Real.sqrt_eq_rpow 3).symm
    rw [hrpow_g, hrpow_three] at hholder
    have hsqrt_g_le : Real.sqrt (∫ x, g x ∂ν) ≤ Real.sqrt ((2 / 3) * K) :=
      Real.sqrt_le_sqrt hg_integral_le
    have hprod_le :
        Real.sqrt (∫ x, g x ∂ν) * Real.sqrt 3
          ≤ Real.sqrt ((2 / 3) * K) * Real.sqrt 3 :=
      mul_le_mul_of_nonneg_right hsqrt_g_le (Real.sqrt_nonneg 3)
    calc
      ∫ x, |p x - 1| ∂ν
          ≤ Real.sqrt (∫ x, g x ∂ν) * Real.sqrt 3 := hholder
      _ ≤ Real.sqrt ((2 / 3) * K) * Real.sqrt 3 := hprod_le
      _ = Real.sqrt (2 * K) := by
        rw [← Real.sqrt_mul (by positivity : 0 ≤ (2 / 3) * K) (3 : ℝ)]
        congr 1
        ring
  have hscheffe := tvDist_le_half_integral_abs_rnDeriv μ ν hac
  unfold PinskerBound
  calc
    tvDist μ ν ≤ (1 / 2) * ∫ x, |p x - 1| ∂ν := by
      simpa [p] using hscheffe
    _ ≤ (1 / 2) * Real.sqrt (2 * K) := by
      exact mul_le_mul_of_nonneg_left h_int_abs (by norm_num)
    _ = Real.sqrt (K / 2) := pinsker_half_sqrt_two_mul K hK_nonneg
    _ = Real.sqrt ((InformationTheory.klDiv μ ν).toReal / 2) := by rfl

end UEOT.V3.InformationPinsker
