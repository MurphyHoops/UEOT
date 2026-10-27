import UEOT.V3.PathError
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.NoisyFiniteRiskOracle
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic

/-!
# Finite same-event conditional stability

Conditioning two actual finite laws on the SAME positive-mass event amplifies
their total-variation error by at most the reciprocal of the larger event
mass.  The conditional laws below are Mathlib's actual `PMF.filter` laws.
No conditional error radius, conditional-source identity, or equality of the
two survival probabilities is supplied as an assumption.

The reference-only certificate requires its event mass to exceed the
unconditional error budget.  This proves positivity of the actual event and
gives the bound epsilon / referenceMass.  Application after training fixes
the training record and its selected controller first; this is not a claim
about conditioning a joint training/deployment experiment while retaining the
original training marginal.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteConditionalStability

open MeasureTheory
open UEOT.V3.PathError UEOT.V3.TotalVariation
open scoped BigOperators Classical

noncomputable section

universe u v

variable {X : Type u} [Fintype X]
variable [MeasurableSpace X] [MeasurableSingletonClass X]

private theorem positive_event_support
    (p : PMF X) (S : Set X) (hp : 0 < p.toMeasure.real S) :
    ∃ x ∈ S, x ∈ p.support := by
  by_contra hnone
  have hzero : p.toMeasure S = 0 := by
    apply (p.toMeasure_apply_eq_zero_iff (Set.toFinite S).measurableSet).2
    apply Set.disjoint_left.mpr
    intro x hsupp hS
    exact hnone ⟨x, hS, hsupp⟩
  change 0 < (p.toMeasure S).toReal at hp
  rw [hzero, ENNReal.toReal_zero] at hp
  exact (lt_irrefl 0) hp

/-- The original finite PMF filtered on the declared positive-mass event. -/
def conditionedPMF (p : PMF X) (S : Set X)
    (hp : 0 < p.toMeasure.real S) : PMF X :=
  p.filter S (positive_event_support p S hp)

private theorem event_mass_sum (p : PMF X) (S : Set X) :
    p.toMeasure.real S = ∑ x : X, if x ∈ S then (p x).toReal else 0 := by
  have hset : S = (Finset.univ.filter (fun x : X => x ∈ S) : Set X) := by
    ext x
    simp
  rw [hset, pmfMeasureReal_eq_sum_finset, Finset.sum_filter]
  simp

private theorem total_mass_sum (p : PMF X) :
    ∑ x : X, (p x).toReal = 1 := by
  have h := congrArg ENNReal.toReal (PMF.tsum_coe p)
  rw [tsum_fintype, ENNReal.toReal_sum
    (fun x _ => PMF.apply_ne_top p x)] at h
  simpa using h

private theorem complement_mass_sum (p : PMF X) (S : Set X) :
    (∑ x : X, if x ∈ S then 0 else (p x).toReal) =
      1 - p.toMeasure.real S := by
  have hsum :
      (∑ x : X, if x ∈ S then (p x).toReal else 0) +
        (∑ x : X, if x ∈ S then 0 else (p x).toReal) = 1 := by
    rw [← Finset.sum_add_distrib]
    have heq : (∑ x : X,
        ((if x ∈ S then (p x).toReal else 0) +
          (if x ∈ S then 0 else (p x).toReal))) =
        ∑ x : X, (p x).toReal := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ S <;> simp [hx]
    rw [heq, total_mass_sum]
  rw [← event_mass_sum] at hsum
  linarith

/-- Exact atom identity for the actual filtered law, retaining its original
event mass.  This lets finite consumers evaluate conditioning without any
separately stipulated conditional distribution. -/
theorem mass_mul_conditioned_atom
    (p : PMF X) (S : Set X) (hp : 0 < p.toMeasure.real S) (x : X) :
    p.toMeasure.real S * (conditionedPMF p S hp x).toReal =
      if x ∈ S then (p x).toReal else 0 := by
  have hden : (∑' a, S.indicator (fun a => p a) a) = p.toMeasure S := by
    rw [tsum_fintype, PMF.toMeasure_apply_fintype]
  have hne : p.toMeasure S ≠ 0 := by
    intro hz
    change 0 < (p.toMeasure S).toReal at hp
    simp [hz] at hp
  have he : p.toMeasure S * conditionedPMF p S hp x =
      if x ∈ S then p x else 0 := by
    simp only [conditionedPMF, PMF.filter_apply, hden]
    rw [mul_left_comm, ENNReal.mul_inv_cancel hne
      (measure_ne_top p.toMeasure S), mul_one]
    simp only [Set.indicator_apply]
  have hr := congrArg ENNReal.toReal he
  simpa only [ENNReal.toReal_mul, Measure.real, ENNReal.toReal_zero,
    apply_ite] using hr

private theorem finite_tv_symm (p q : PMF X) :
    tvDist p.toMeasure q.toMeasure = tvDist q.toMeasure p.toMeasure := by
  rw [tvDist_eq_one_sub_pmfCommonMass, tvDist_eq_one_sub_pmfCommonMass]
  simp only [pmfCommonMass, min_comm]

private theorem max_mass_mul_conditioned_tv_le_right
    (p q : PMF X) (S : Set X)
    (hp : 0 < p.toMeasure.real S) (hq : 0 < q.toMeasure.real S)
    (hmass : p.toMeasure.real S ≤ q.toMeasure.real S) :
    q.toMeasure.real S *
      tvDist (conditionedPMF p S hp).toMeasure
        (conditionedPMF q S hq).toMeasure ≤
      tvDist p.toMeasure q.toMeasure := by
  let pc := conditionedPMF p S hp
  let qc := conditionedPMF q S hq
  have hpoint (x : X) :
      min (p x).toReal (q x).toReal ≤
        q.toMeasure.real S * min (pc x).toReal (qc x).toReal +
          (if x ∈ S then 0 else (q x).toReal) := by
    by_cases hx : x ∈ S
    · have hpatom := mass_mul_conditioned_atom p S hp x
      have hqatom := mass_mul_conditioned_atom q S hq x
      simp only [hx, if_true] at hpatom hqatom ⊢
      have hple : (p x).toReal ≤ q.toMeasure.real S * (pc x).toReal := by
        calc
          (p x).toReal = p.toMeasure.real S * (pc x).toReal := hpatom.symm
          _ ≤ q.toMeasure.real S * (pc x).toReal :=
            mul_le_mul_of_nonneg_right hmass ENNReal.toReal_nonneg
      have hqeq : (q x).toReal = q.toMeasure.real S * (qc x).toReal :=
        hqatom.symm
      have hmin := min_le_min hple (le_of_eq hqeq)
      have hmul :
          min (q.toMeasure.real S * (pc x).toReal)
            (q.toMeasure.real S * (qc x).toReal) =
          q.toMeasure.real S * min (pc x).toReal (qc x).toReal := by
        rcases le_total (pc x).toReal (qc x).toReal with hc | hc
        · rw [min_eq_left hc,
            min_eq_left (mul_le_mul_of_nonneg_left hc (le_of_lt hq))]
        · rw [min_eq_right hc,
            min_eq_right (mul_le_mul_of_nonneg_left hc (le_of_lt hq))]
      rw [hmul] at hmin
      simpa using hmin
    · have hn : 0 ≤ q.toMeasure.real S * min (pc x).toReal (qc x).toReal :=
        mul_nonneg (le_of_lt hq)
          (le_min ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      simp only [hx, if_false]
      exact (min_le_right _ _).trans (le_add_of_nonneg_left hn)
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset X)) => hpoint x)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [complement_mass_sum q S] at hsum
  change pmfCommonMass p q ≤
    q.toMeasure.real S * pmfCommonMass pc qc + (1 - q.toMeasure.real S) at hsum
  rw [tvDist_eq_one_sub_pmfCommonMass, tvDist_eq_one_sub_pmfCommonMass]
  change q.toMeasure.real S * (1 - pmfCommonMass pc qc) ≤ 1 - pmfCommonMass p q
  nlinarith

/-- Sharp same-event amplification bound.  The event is identical in both
laws and both conditional PMFs are generated by filtering those original laws. -/
theorem conditional_tv_le_max_mass
    (p q : PMF X) (S : Set X)
    (hp : 0 < p.toMeasure.real S) (hq : 0 < q.toMeasure.real S)
    (epsilon : ℝ) (hTV : tvDist p.toMeasure q.toMeasure ≤ epsilon) :
    tvDist (conditionedPMF p S hp).toMeasure
      (conditionedPMF q S hq).toMeasure ≤
      min 1 (epsilon / max (p.toMeasure.real S) (q.toMeasure.real S)) := by
  apply le_min (tvDist_le_one _ _)
  have hmax : 0 < max (p.toMeasure.real S) (q.toMeasure.real S) :=
    lt_of_lt_of_le hp (le_max_left _ _)
  apply (le_div_iff₀ hmax).2
  rcases le_total (p.toMeasure.real S) (q.toMeasure.real S) with hmass | hmass
  · rw [max_eq_right hmass, mul_comm]
    exact (max_mass_mul_conditioned_tv_le_right p q S hp hq hmass).trans hTV
  · rw [max_eq_left hmass, mul_comm]
    have h := max_mass_mul_conditioned_tv_le_right q p S hq hp hmass
    rw [finite_tv_symm q p, finite_tv_symm
      (conditionedPMF q S hq) (conditionedPMF p S hp)] at h
    exact h.trans hTV

/-- A reference event mass strictly exceeding the unconditional TV budget
certifies positivity of the true event.  A zero-probability event is never
silently assigned a conditional law. -/
theorem reference_mass_certifies_positive
    (p q : PMF X) (S : Set X) (epsilon : ℝ)
    (hTV : tvDist p.toMeasure q.toMeasure ≤ epsilon)
    (hgap : epsilon < q.toMeasure.real S) :
    0 < p.toMeasure.real S ∧ 0 < q.toMeasure.real S := by
  have he := (tvEvent_le p.toMeasure q.toMeasure S
    (Set.toFinite S).measurableSet).trans hTV
  have hlo := (abs_le.mp he).1
  have heps : 0 ≤ epsilon := (tvDist_nonneg _ _).trans hTV
  constructor <;> linarith

/-- With both events positive, the larger-mass theorem gives a bound using
only the reference mass.  The reference need not have the larger mass. -/
theorem conditional_tv_le_reference_mass
    (p q : PMF X) (S : Set X)
    (hp : 0 < p.toMeasure.real S) (hq : 0 < q.toMeasure.real S)
    (epsilon : ℝ) (hTV : tvDist p.toMeasure q.toMeasure ≤ epsilon) :
    tvDist (conditionedPMF p S hp).toMeasure
      (conditionedPMF q S hq).toMeasure ≤
      min 1 (epsilon / q.toMeasure.real S) := by
  have heps : 0 ≤ epsilon := (tvDist_nonneg _ _).trans hTV
  have hbound := conditional_tv_le_max_mass p q S hp hq epsilon hTV
  apply hbound.trans
  apply min_le_min_left 1
  exact div_le_div_of_nonneg_left heps hq (le_max_right _ _)

/-- Complete reference-only certificate: positivity is derived before the
conditional laws are constructed, and no true survival mass is an input. -/
theorem reference_mass_conditional_certificate
    (p q : PMF X) (S : Set X) (epsilon : ℝ)
    (hTV : tvDist p.toMeasure q.toMeasure ≤ epsilon)
    (hgap : epsilon < q.toMeasure.real S) :
    ∃ (hp : 0 < p.toMeasure.real S) (hq : 0 < q.toMeasure.real S),
      tvDist (conditionedPMF p S hp).toMeasure
        (conditionedPMF q S hq).toMeasure ≤
        min 1 (epsilon / q.toMeasure.real S) := by
  obtain ⟨hp, hq⟩ := reference_mass_certifies_positive p q S epsilon hTV hgap
  exact ⟨hp, hq, conditional_tv_le_reference_mass p q S hp hq epsilon hTV⟩

/-- Measurable prefix, terminal, or other readouts of the conditioned paths
inherit the same certificate.  The same map is applied to both laws. -/
theorem conditioned_readout_tv_le_reference_mass
    {Y : Type v} [MeasurableSpace Y]
    (p q : PMF X) (S : Set X)
    (hp : 0 < p.toMeasure.real S) (hq : 0 < q.toMeasure.real S)
    (epsilon : ℝ) (hTV : tvDist p.toMeasure q.toMeasure ≤ epsilon)
    (f : X → Y) (hf : Measurable f) :
    tvDist ((conditionedPMF p S hp).map f).toMeasure
      ((conditionedPMF q S hq).map f).toMeasure ≤
      min 1 (epsilon / q.toMeasure.real S) := by
  rw [← PMF.toMeasure_map f (conditionedPMF p S hp) hf,
    ← PMF.toMeasure_map f (conditionedPMF q S hq) hf]
  exact (tvDist_map_le _ _ f hf).trans
    (conditional_tv_le_reference_mass p q S hp hq epsilon hTV)

/-- The existing actual causal path TV bound supplies the conditional budget.
This applies to a fixed controller's two record kernels, with a single initial
law and the same declared survival event. -/
theorem causal_path_conditional_certificate
    {H Z : Type u} [Fintype H] [Fintype Z]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (p0 : PMF H) (K L : ∀ n, CausalHistory H Z n → PMF Z)
    (epsilon : ℕ → ℝ) (heps0 : ∀ n, 0 ≤ epsilon n)
    (heps1 : ∀ n, epsilon n ≤ 1)
    (hrow : ∀ n h, tvDist (K n h).toMeasure (L n h).toMeasure ≤ epsilon n)
    (T : ℕ) (S : Set (CausalHistory H Z T))
    (hgap : 1 - (∏ i ∈ Finset.range T, (1 - epsilon i)) <
      (causalLaw p0 L T).toMeasure.real S) :
    ∃ (hp : 0 < (causalLaw p0 K T).toMeasure.real S)
      (hq : 0 < (causalLaw p0 L T).toMeasure.real S),
      tvDist (conditionedPMF (causalLaw p0 K T) S hp).toMeasure
        (conditionedPMF (causalLaw p0 L T) S hq).toMeasure ≤
        min 1 ((1 - (∏ i ∈ Finset.range T, (1 - epsilon i))) /
          (causalLaw p0 L T).toMeasure.real S) := by
  exact reference_mass_conditional_certificate (causalLaw p0 K T)
    (causalLaw p0 L T) S _ (causalLaw_tv_bound p0 K L epsilon heps0 heps1 hrow T) hgap

/-- Direct R2 consumer at a fixed training record and fixed actual program.
The existing row calibration and empirical fibre defect derive the path error;
the caller does not provide a new conditional or unconditional fit hypothesis.
The event is on the common observed action/state record alphabet.  Interpreting
it as microscopic physical survival additionally requires that very survival
event to be a pullback of this registered observation event. -/
theorem noisy_reference_conditional_certificate
    {X Y A : Type u} [Fintype X] [Fintype Y] [Fintype A]
    [LinearOrder X] [DecidableEq Y] [DecidableEq A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    {N : ℕ} (hN : 0 < N) (p0 : PMF X) (q : X → Y)
    (P : X → A → PMF X) (fallback : X)
    (sample : NoisyFiniteRiskOracle.SampleTable X A N) (u : ℚ) (hu : 0 ≤ u)
    (hgood : NoisyFiniteRiskOracle.CalibrationGood P hN sample u)
    (program : ExecutableSupportSynthesis.Program X Y A)
    (T : ℕ) (S : Set (CausalHistory Y (A × Y) T))
    (hgap :
      1 - (1 - min 1 ((u : ℝ) +
        (NoisyFiniteRiskOracle.empiricalDefect q sample : ℝ))) ^ T <
      (causalLaw (p0.map q)
        (riskMacroControlKernel
          (fun _ => NoisyFiniteRiskOracle.referenceKernel hN q fallback sample)
          program.toController.policy) T).toMeasure.real S) :
    let actual := (causalLaw p0
      (riskMicroControlKernel q (fun _ => P) program.toController.policy) T).map
      (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) T)
    let reference := causalLaw (p0.map q)
      (riskMacroControlKernel
        (fun _ => NoisyFiniteRiskOracle.referenceKernel hN q fallback sample)
        program.toController.policy) T
    let pathError := 1 - (1 - min 1 ((u : ℝ) +
      (NoisyFiniteRiskOracle.empiricalDefect q sample : ℝ))) ^ T
    ∃ (hp : 0 < actual.toMeasure.real S) (hq : 0 < reference.toMeasure.real S),
      tvDist (conditionedPMF actual S hp).toMeasure
        (conditionedPMF reference S hq).toMeasure ≤
        min 1 (pathError / reference.toMeasure.real S) := by
  let e : ℝ := min 1 ((u : ℝ) +
    (NoisyFiniteRiskOracle.empiricalDefect q sample : ℝ))
  have he0 : 0 ≤ e := by
    apply le_min (by norm_num)
    apply add_nonneg
    · exact_mod_cast hu
    · exact_mod_cast NoisyFiniteRiskOracle.empiricalDefect_nonneg q sample
  have he1 : e ≤ 1 := min_le_left _ _
  have hpath := (same_policy_projected_path_error p0 q (fun _ => P)
    (fun _ => NoisyFiniteRiskOracle.referenceKernel hN q fallback sample)
    program.toController.policy (fun _ => e) T
    (fun _ _ => he0) (fun _ _ => he1) (by
      intro _ _ x a
      exact NoisyFiniteRiskOracle.calibrated_reference_row hN P q fallback
        sample u hgood x a)).1
  dsimp only
  apply reference_mass_conditional_certificate
  · simpa only [Finset.prod_const, Finset.card_range, e] using hpath
  · exact hgap

end

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteConditionalStability
