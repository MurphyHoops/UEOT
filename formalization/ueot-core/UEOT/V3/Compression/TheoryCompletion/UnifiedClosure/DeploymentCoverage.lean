import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MicroscopicFailureRisk
import UEOT.V3.TransportDefect
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.EmpiricalReferenceRisk

/-!
# Finite deployment coverage under the actual microscopic path law

This additive theorem integrates row errors under the actual deployment law.
It does not replace the uniform hypotheses of the existing product bound by
mean errors. An unknown deployment coverage probability remains unknown;
defining its PMF does not certify it from restricted training data.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open MeasureTheory UEOT.V3.PathError UEOT.V3.TotalVariation
open scoped BigOperators Classical

noncomputable section

universe u

/-- The real coordinate masses of a finite PMF sum to one. This public
helper is shared with the independent finite deployment witnesses. -/
theorem coverage_sum_toReal {H : Type u} [Fintype H] (p : PMF H) :
    (∑ h, (p h).toReal) = 1 := by
  simpa only [pmfCommonMass, min_self] using pmfCommonMass_self p

/-- Keeping the common initial record makes TV exactly the actual-weighted
average of the conditional next-record TV distances. -/
theorem coverage_tv_extend_same_initial
    {H Z : Type u} [Fintype H] [Fintype Z]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (p : PMF H) (K L : H → PMF Z) :
    tvDist (pmfExtend p K).toMeasure (pmfExtend p L).toMeasure =
      ∑ h, (p h).toReal * tvDist (K h).toMeasure (L h).toMeasure := by
  have hc : pmfCommonMass (pmfExtend p K) (pmfExtend p L) =
      ∑ h, (p h).toReal * pmfCommonMass (K h) (L h) := by
    unfold pmfCommonMass
    rw [← Finset.univ_product_univ, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro h _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    rw [pmfExtend_apply, pmfExtend_apply, ENNReal.toReal_mul, ENNReal.toReal_mul]
    rcases le_total (K h z).toReal (L h z).toReal with hkl | hlk
    · rw [min_eq_left hkl,
        min_eq_left (mul_le_mul_of_nonneg_left hkl ENNReal.toReal_nonneg)]
    · rw [min_eq_right hlk,
        min_eq_right (mul_le_mul_of_nonneg_left hlk ENNReal.toReal_nonneg)]
  rw [tvDist_eq_one_sub_pmfCommonMass, hc]
  simp_rw [tvDist_eq_one_sub_pmfCommonMass, mul_sub, mul_one]
  rw [Finset.sum_sub_distrib, coverage_sum_toReal]

/-- A shared next-record kernel does not amplify TV of its input history law. -/
theorem coverage_tv_extend_same_kernel
    {H Z : Type u} [Fintype H] [Fintype Z]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (p q : PMF H) (L : H → PMF Z) :
    tvDist (pmfExtend p L).toMeasure (pmfExtend q L).toMeasure ≤
      tvDist p.toMeasure q.toMeasure := by
  have hc := pmfCommonMass_extend_lower_bound p q L L 1
    (by intro h; rw [pmfCommonMass_self]) (by norm_num)
  rw [mul_one] at hc
  rw [tvDist_eq_one_sub_pmfCommonMass, tvDist_eq_one_sub_pmfCommonMass]
  exact sub_le_sub_left hc 1

private theorem coverage_tv_map_pmf_le
    {H Z : Type u} [Fintype H]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    [MeasurableSpace Z]
    (p q : PMF H) (f : H → Z) :
    tvDist (p.map f).toMeasure (q.map f).toMeasure ≤ tvDist p.toMeasure q.toMeasure := by
  have hf : Measurable f := measurable_of_countable f
  simpa only [PMF.toMeasure_map f p hf, PMF.toMeasure_map f q hf] using
    tvDist_map_le p.toMeasure q.toMeasure f hf

/-- A reference row depending only on the projection commutes with the
actual initial-law projection. No conditional kernel is assumed. -/
theorem coverage_map_extend_reference
    {H Y Z : Type u} [Fintype H] [Fintype Y] [Fintype Z]
    (p : PMF H) (f : H → Y) (L : Y → PMF Z) :
    (pmfExtend p (fun h => L (f h))).map (fun hz => (f hz.1, hz.2)) =
      pmfExtend (p.map f) L := by
  apply PMF.ext
  rintro ⟨y, z⟩
  rw [risk_map_extend_apply, pmfExtend_apply, PMF.map_apply, tsum_fintype,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h _
  by_cases hf : f h = y
  · simp [hf]
  · simp [hf, Ne.symm hf]

private theorem coverage_map_extend_both
    {H Y Z W : Type u} (p : PMF H) (K : H → PMF Z)
    (f : H → Y) (g : Z → W) :
    (pmfExtend p K).map (fun hz => (f hz.1, g hz.2)) =
      (pmfExtend p (fun h => (K h).map g)).map (fun hz => (f hz.1, hz.2)) := by
  calc
    _ = ((pmfExtend p K).map (fun hz => (hz.1, g hz.2))).map
        (fun hz => (f hz.1, hz.2)) := by
      rw [PMF.map_comp]
      rfl
    _ = _ := by rw [risk_map_extend_right]

/-- One projected extension costs the TV row errors averaged with the actual
microscopic law, before any comparison-law occupancy is substituted. -/
theorem coverage_projected_extension_error
    {H Y Z W : Type u}
    [Fintype H] [Fintype Y] [Fintype Z] [Fintype W]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [MeasurableSpace W] [MeasurableSingletonClass W]
    (p : PMF H) (K : H → PMF Z) (f : H → Y) (g : Z → W)
    (L : Y → PMF W) :
    tvDist ((pmfExtend p K).map (fun hz => (f hz.1, g hz.2))).toMeasure
        (pmfExtend (p.map f) L).toMeasure ≤
      ∑ h, (p h).toReal * tvDist ((K h).map g).toMeasure (L (f h)).toMeasure := by
  have hm := coverage_tv_map_pmf_le
    (pmfExtend p (fun h => (K h).map g))
    (pmfExtend p (fun h => L (f h))) (fun hz => (f hz.1, hz.2))
  rw [coverage_map_extend_reference, ← coverage_map_extend_both] at hm
  exact hm.trans (le_of_eq (coverage_tv_extend_same_initial p
    (fun h => (K h).map g) (fun h => L (f h))))

/-- Actual microscopic history weights, explicit projection, and a genuine
reference causal law give an additive finite-horizon path-TV bound. -/
theorem coverage_projected_causalLaw_error
    {X Y Z W : Type u}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype W]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace W] [MeasurableSingletonClass W]
    (p₀ : PMF X) (K : ∀ n, CausalHistory X Z n → PMF Z)
    (f : X → Y) (g : Z → W)
    (L : ∀ n, CausalHistory Y W n → PMF W) (T : ℕ) :
    tvDist ((causalLaw p₀ K T).map (riskHistoryMap f g T)).toMeasure
        (causalLaw (p₀.map f) L T).toMeasure ≤
      ∑ n ∈ Finset.range T, ∑ h, (causalLaw p₀ K n h).toReal *
        tvDist ((K n h).map g).toMeasure
          (L n (riskHistoryMap f g n h)).toMeasure := by
  induction T with
  | zero =>
    change tvDist (p₀.map f).toMeasure (p₀.map f).toMeasure ≤ 0
    simp only [tvDist_self_eq_zero, le_refl]
  | succ n ih =>
    let p := causalLaw p₀ K n
    let q := causalLaw (p₀.map f) L n
    let proj := riskHistoryMap f g n
    have hstep := coverage_projected_extension_error p (K n) proj g (L n)
    have hcarry := coverage_tv_extend_same_kernel (p.map proj) q (L n)
    have htri := UEOT.V3.TransportDefect.tvDist_triangle
      ((pmfExtend p (K n)).map (fun hz => (proj hz.1, g hz.2))).toMeasure
      (pmfExtend (p.map proj) (L n)).toMeasure
      (pmfExtend q (L n)).toMeasure
    rw [Finset.sum_range_succ]
    change tvDist
      ((pmfExtend p (K n)).map (fun hz => (proj hz.1, g hz.2))).toMeasure
      (pmfExtend q (L n)).toMeasure ≤ _
    exact htri.trans ((add_le_add hstep (hcarry.trans ih)).trans_eq (add_comm _ _))

/-- Finite expectation under a genuine PMF pushforward. -/
theorem coverage_expectation_map
    {H S : Type u} [Fintype H] [Fintype S]
    (p : PMF H) (f : H → S) (e : S → ℝ) :
    (∑ s, ((p.map f) s).toReal * e s) = ∑ h, (p h).toReal * e (f h) := by
  have happ : ∀ s, ((p.map f) s).toReal =
      ∑ h, if f h = s then (p h).toReal else 0 := by
    intro s
    rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum (by
      intro h _
      split_ifs
      · exact PMF.apply_ne_top p h
      · exact ENNReal.zero_ne_top)]
    apply Finset.sum_congr rfl
    intro h _
    by_cases hf : f h = s
    · simp [hf]
    · simp [hf, Ne.symm hf]
  simp_rw [happ, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  rw [Finset.sum_eq_single (f h)]
  · simp
  · intro s _ hs
    simp [Ne.symm hs]
  · simp

/-- The actual state/action law at a transition: first sample the actual
microscopic prefix, then the common coarse-history policy, and record its
last state and chosen action. The reference process supplies no weights. -/
def coverageDeploymentRowLaw
    {X Y A : Type u} (p₀ : PMF X) (q : X → Y)
    (P : ℕ → X → A → PMF X)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A) (n : ℕ) : PMF (X × A) :=
  (pmfExtend (causalLaw p₀ (riskMicroControlKernel q P π) n)
    (fun h => π n (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) n h))).map
    (fun ha => (riskLastState n ha.1, ha.2))

/-- Expand the constructed deployment PMF into the actual prefix/action
weights. In particular, its coverage mass is not an extra asserted law. -/
theorem coverage_rowLaw_expectation
    {X Y A : Type u} [Fintype X] [Fintype A]
    (p₀ : PMF X) (q : X → Y) (P : ℕ → X → A → PMF X)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A) (n : ℕ) (e : X × A → ℝ) :
    (∑ xa, (coverageDeploymentRowLaw p₀ q P π n xa).toReal * e xa) =
      ∑ h, (causalLaw p₀ (riskMicroControlKernel q P π) n h).toReal *
        ∑ a, (π n (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) n h) a).toReal *
          e (riskLastState n h, a) := by
  unfold coverageDeploymentRowLaw
  rw [coverage_expectation_map, ← Finset.univ_product_univ, Finset.sum_product]
  simp_rw [pmfExtend_apply, ENNReal.toReal_mul, mul_assoc, Finset.mul_sum]

/-- An uncovered-row indicator expectation is the actual PMF event mass.
Exposed for exact deployment coverage computations in separate witness modules. -/
theorem coverage_uncovered_indicator_expectation
    {S : Type u} [Fintype S]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (ν : PMF S) (C : S → Prop) :
    (∑ s, (ν s).toReal * (if C s then 0 else 1)) =
      ν.toMeasure.real {s | ¬ C s} := by
  have hset : {s | ¬ C s} = (Finset.univ.filter (fun s => ¬ C s) : Set S) := by
    ext s
    simp
  rw [hset, pmfMeasureReal_eq_sum_finset, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : C s <;> simp [hs]

/-- Certified rows carry their proved error; all other rows carry the full
possible TV error. The uncovered mass is the supplied genuine PMF's event
probability, and is not silently set to its training analogue. -/
theorem coverage_expected_error_le
    {S : Type u} [Fintype S]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (ν : PMF S) (C : S → Prop) (e : S → ℝ) (ε : ℝ)
    (he1 : ∀ s, e s ≤ 1) (hcert : ∀ s, C s → e s ≤ ε) :
    (∑ s, (ν s).toReal * e s) ≤
      ε + (1 - ε) * ν.toMeasure.real {s | ¬ C s} := by
  have he : ∀ s, e s ≤ ε + (1 - ε) * (if C s then 0 else 1) := by
    intro s
    by_cases hs : C s
    · simpa [hs] using hcert s hs
    · simp only [if_neg hs, mul_one]
      linarith [he1 s]
  calc
    (∑ s, (ν s).toReal * e s) ≤
        ∑ s, (ν s).toReal * (ε + (1 - ε) * (if C s then 0 else 1)) := by
      exact Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (he s)
        ENNReal.toReal_nonneg
    _ = ε + (1 - ε) * (∑ s, (ν s).toReal * (if C s then 0 else 1)) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, coverage_sum_toReal, one_mul,
        Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ = _ := by rw [coverage_uncovered_indicator_expectation]

/-- Common-policy row TV equals the conditional action-weighted transition
TV. This identity exposes rather than hides rarely used actions. -/
theorem coverage_same_policy_row_tv
    {X Y A : Type u} [Fintype X] [Fintype Y] [Fintype A]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (q : X → Y) (P : ℕ → X → A → PMF X) (Q : ℕ → Y → A → PMF Y)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (n : ℕ) (h : CausalHistory X (A × X) n) :
    tvDist ((riskMicroControlKernel q P π n h).map
        (fun ax : A × X => (ax.1, q ax.2))).toMeasure
      (riskMacroControlKernel Q π n
        (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) n h)).toMeasure =
      ∑ a, (π n (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) n h) a).toReal *
        tvDist ((P n (riskLastState n h) a).map q).toMeasure
          (Q n (q (riskLastState n h)) a).toMeasure := by
  dsimp only [riskMicroControlKernel, riskMacroControlKernel]
  rw [risk_map_extend_right, risk_last_project]
  exact coverage_tv_extend_same_initial _ _ _

/-- The finite path mismatch is bounded by row TV averaged under actual
microscopic deployment occupancies at each transition. -/
theorem coverage_same_policy_path_error
    {X Y A : Type u} [Fintype X] [Fintype Y] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p₀ : PMF X) (q : X → Y)
    (P : ℕ → X → A → PMF X) (Q : ℕ → Y → A → PMF Y)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A) (T : ℕ) :
    tvDist ((causalLaw p₀ (riskMicroControlKernel q P π) T).map
        (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) T)).toMeasure
      (causalLaw (p₀.map q) (riskMacroControlKernel Q π) T).toMeasure ≤
      ∑ n ∈ Finset.range T, ∑ xa, (coverageDeploymentRowLaw p₀ q P π n xa).toReal *
        tvDist ((P n xa.1 xa.2).map q).toMeasure (Q n (q xa.1) xa.2).toMeasure := by
  have h := coverage_projected_causalLaw_error p₀ (riskMicroControlKernel q P π)
    q (fun ax : A × X => (ax.1, q ax.2)) (riskMacroControlKernel Q π) T
  refine h.trans_eq ?_
  apply Finset.sum_congr rfl
  intro n _
  rw [coverage_rowLaw_expectation]
  apply Finset.sum_congr rfl
  intro h _
  rw [coverage_same_policy_row_tv]

/-- Restricted row certification plus the true uncovered occupancy probability
controls the whole finite path. The existing uniform product theorem remains
separate; this endpoint deliberately has an additive budget. -/
theorem coverage_same_policy_certified_path_error
    {X Y A : Type u} [Fintype X] [Fintype Y] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p₀ : PMF X) (q : X → Y)
    (P : ℕ → X → A → PMF X) (Q : ℕ → Y → A → PMF Y)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (certified : ℕ → X → A → Prop) (ε : ℕ → ℝ) (T : ℕ)
    (hcert : ∀ n, n < T → ∀ x a, certified n x a →
      tvDist ((P n x a).map q).toMeasure (Q n (q x) a).toMeasure ≤ ε n) :
    tvDist ((causalLaw p₀ (riskMicroControlKernel q P π) T).map
        (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) T)).toMeasure
      (causalLaw (p₀.map q) (riskMacroControlKernel Q π) T).toMeasure ≤
      ∑ n ∈ Finset.range T, (ε n + (1 - ε n) *
        (coverageDeploymentRowLaw p₀ q P π n).toMeasure.real
          {xa | ¬ certified n xa.1 xa.2}) := by
  refine (coverage_same_policy_path_error p₀ q P Q π T).trans ?_
  apply Finset.sum_le_sum
  intro n hn
  exact coverage_expected_error_le (coverageDeploymentRowLaw p₀ q P π n)
    (fun xa => certified n xa.1 xa.2)
    (fun xa => tvDist ((P n xa.1 xa.2).map q).toMeasure
      (Q n (q xa.1) xa.2).toMeasure) (ε n)
    (fun _ => tvDist_le_one _ _) (fun xa hx => hcert n (Finset.mem_range.mp hn) xa.1 xa.2 hx)

/-- Actual microscopic failure is controlled only after an explicit
observable envelope, with the same actual occupancy budget as the path law. -/
theorem coverage_same_policy_microscopic_failure_risk
    {X Y A : Type u} [Fintype X] [Fintype Y] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p₀ : PMF X) (q : X → Y)
    (P : ℕ → X → A → PMF X) (Q : ℕ → Y → A → PMF Y)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (certified : ℕ → X → A → Prop) (ε : ℕ → ℝ) (T : ℕ)
    (hcert : ∀ n, n < T → ∀ x a, certified n x a →
      tvDist ((P n x a).map q).toMeasure (Q n (q x) a).toMeasure ≤ ε n)
    (E : Set (CausalHistory X (A × X) T))
    (F : Set (CausalHistory Y (A × Y) T))
    (hEF : E ⊆ (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) T) ⁻¹' F) :
    (causalLaw p₀ (riskMicroControlKernel q P π) T).toMeasure.real E ≤
      min 1 ((causalLaw (p₀.map q) (riskMacroControlKernel Q π) T).toMeasure.real F +
        ∑ n ∈ Finset.range T, (ε n + (1 - ε n) *
          (coverageDeploymentRowLaw p₀ q P π n).toMeasure.real
            {xa | ¬ certified n xa.1 xa.2})) := by
  have hF : MeasurableSet F := Set.to_countable F |>.measurableSet
  exact (risk_microscopic_event_le_envelope _ _ (measurable_of_countable _)
    E F hF hEF).trans (risk_event_transfer _ _ _
      (coverage_same_policy_certified_path_error p₀ q P Q π certified ε T hcert) F hF)




section RestrictedRowCalibration

open ProbabilityTheory
open UEOT.V3.BoundedLossSampling
open UEOT.V3.FiniteAlphabetSampling UEOT.V3.FiniteAlphabetConcentration

universe uΩ uJ

/-- A fixed finite registration set is the only sample index. The existing
bounded-test finite-row theorem supplies the confidence bound; all finite
events turn its calibrated means into genuine source-to-empirical PMF TV.
There are no sample fields, laws or independence premises for omitted rows. -/
theorem coverage_registered_row_calibration
    {Ω : Type uΩ} {X : Type u} {J : Type uJ}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSingletonClass X]
    [Fintype X] [Fintype J]
    {N : ℕ} (hN : 0 < N) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (row : J → PMF X) (sample : J → Fin N → Ω → X) (rho : J → ℝ)
    (hmeas : ∀ j k, Measurable (sample j k))
    (hindep : ∀ j, iIndepFun (sample j) μ)
    (hlaw : ∀ j k, μ.map (sample j k) = (row j).toMeasure)
    (hrho : ∀ j, 0 ≤ rho j) :
    ∃ good : Set Ω, MeasurableSet good ∧
      μ.real goodᶜ ≤ ∑ j, (Fintype.card (Finset X) : ℝ) *
        (2 * Real.exp (-2 * (N : ℝ) * (rho j) ^ 2)) ∧
      ∀ ω ∈ good, ∀ j,
        tvDist (row j).toMeasure
          (empiricalResponsePMF hN (sample j) ω).toMeasure ≤ rho j := by
  let good : Set Ω := {ω | ∀ j s,
    |trueRisk (row j).toMeasure (eventIndicator s) -
      empiricalRisk (eventIndicator s) (sample j) ω| ≤ rho j}
  have hgood : MeasurableSet good := by
    have hset : good = ⋂ j : J, ⋂ s : Finset X,
        {ω | |trueRisk (row j).toMeasure (eventIndicator s) -
          empiricalRisk (eventIndicator s) (sample j) ω| ≤ rho j} := by
      ext ω
      simp only [good, Set.mem_ofPred_eq, Set.mem_iInter]
    rw [hset]
    refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun s => ?_
    have hemp : Measurable (fun ω => empiricalRisk (eventIndicator s) (sample j) ω) := by
      unfold empiricalRisk
      exact (Finset.measurable_sum Finset.univ (fun k _ =>
        (measurable_const.indicator s.measurableSet).comp (hmeas j k))).div_const _
    exact measurableSet_le (measurable_const.sub hemp).abs measurable_const
  have htail := measure_finite_row_calibration_bad_le hN μ
    (fun j => (row j).toMeasure) (fun _ => eventIndicator) sample rho
    (fun _ s => measurable_const.indicator s.measurableSet)
    (by
      intro _ s x
      by_cases hx : x ∈ s <;> simp [eventIndicator, hx])
    hmeas hindep hlaw hrho
  refine ⟨good, hgood, ?_, ?_⟩
  · refine (measureReal_mono ?_).trans htail
    intro ω hω
    change ¬ (∀ j s,
      |trueRisk (row j).toMeasure (eventIndicator s) -
        empiricalRisk (eventIndicator s) (sample j) ω| ≤ rho j) at hω
    push Not at hω
    obtain ⟨j, s, hs⟩ := hω
    exact ⟨j, s, by simpa only [abs_sub_comm] using hs⟩
  · intro ω hω j
    apply tvDist_le_of_finset_event_le
    intro s
    rw [empiricalResponsePMF_event_mean]
    simpa only [pmf_event_test_mean] using hω j s

/-- Only registered transition rows exist in the sample type. The registration
predicate and finite horizon are fixed before observing the training data. -/
abbrev CoverageRegisteredRow {X A : Type u}
    (certified : ℕ → X → A → Prop) (T : ℕ) :=
  {row : Fin T × A × X // certified row.1 row.2.2 row.2.1}

/-- Reuse the generic registered-row experiment on the exact fixed source
rows appearing in the controlled deployment. This specializes the index,
without introducing synthetic samples for unregistered state/actions. -/
theorem coverage_registered_source_calibration
    {Ω : Type uΩ} {X A : Type u}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSingletonClass X]
    [Fintype X] [Fintype A]
    {N : ℕ} (hN : 0 < N) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : ℕ → X → A → PMF X) (certified : ℕ → X → A → Prop) (T : ℕ)
    (sample : CoverageRegisteredRow certified T → Fin N → Ω → X) (rho : ℕ → ℝ)
    (hmeas : ∀ j k, Measurable (sample j k))
    (hindep : ∀ j, iIndepFun (sample j) μ)
    (hlaw : ∀ j k, μ.map (sample j k) = (P j.1.1 j.1.2.2 j.1.2.1).toMeasure)
    (hrho : ∀ n, n < T → 0 ≤ rho n) :
    ∃ good : Set Ω, MeasurableSet good ∧
      μ.real goodᶜ ≤ ∑ j : CoverageRegisteredRow certified T,
        (Fintype.card (Finset X) : ℝ) *
          (2 * Real.exp (-2 * (N : ℝ) * (rho j.1.1) ^ 2)) ∧
      ∀ ω ∈ good, ∀ j : CoverageRegisteredRow certified T,
        tvDist (P j.1.1 j.1.2.2 j.1.2.1).toMeasure
          (empiricalResponsePMF hN (sample j) ω).toMeasure ≤ rho j.1.1 := by
  exact coverage_registered_row_calibration hN μ
    (fun j : CoverageRegisteredRow certified T => P j.1.1 j.1.2.2 j.1.2.1)
    sample (fun j => rho j.1.1) hmeas hindep hlaw
    (fun j => hrho j.1.1 j.1.1.isLt)

/-- On the registered experiment's common good event, an empirical fit to
the selected reference PMFs supplies precisely the certified rows required
by the actual-occupancy theorem. The remaining transition rows have no
samples and retain their true deployment coverage penalty.

The map, reference rows, policy and fit tolerance may be chosen after this
common all-event calibration event; no sampling or coverage estimate for
unregistered rows follows from such a choice. -/
theorem coverage_empirical_registered_microscopic_failure_risk
    {Ω : Type uΩ} {X Y A : Type u}
    [Fintype X] [Fintype Y] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    {N : ℕ} (hN : 0 < N)
    (p₀ : PMF X) (q : X → Y)
    (P : ℕ → X → A → PMF X) (Q : ℕ → Y → A → PMF Y)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (certified : ℕ → X → A → Prop) (T : ℕ)
    (sample : CoverageRegisteredRow certified T → Fin N → Ω → X)
    (rho eta : ℕ → ℝ) (ω : Ω)
    (hcal : ∀ j : CoverageRegisteredRow certified T,
      tvDist (P j.1.1 j.1.2.2 j.1.2.1).toMeasure
        (empiricalResponsePMF hN (sample j) ω).toMeasure ≤ rho j.1.1)
    (hfit : ∀ n (hn : n < T) x a (hc : certified n x a),
      tvDist ((empiricalResponsePMF hN (sample ⟨(⟨n, hn⟩, a, x), hc⟩) ω).map q).toMeasure
        (Q n (q x) a).toMeasure ≤ eta n)
    (E : Set (CausalHistory X (A × X) T))
    (F : Set (CausalHistory Y (A × Y) T))
    (hEF : E ⊆ (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) T) ⁻¹' F) :
    (causalLaw p₀ (riskMicroControlKernel q P π) T).toMeasure.real E ≤
      min 1 ((causalLaw (p₀.map q) (riskMacroControlKernel Q π) T).toMeasure.real F +
        ∑ n ∈ Finset.range T, (min 1 (rho n + eta n) +
          (1 - min 1 (rho n + eta n)) *
          (coverageDeploymentRowLaw p₀ q P π n).toMeasure.real
            {xa | ¬ certified n xa.1 xa.2})) := by
  apply coverage_same_policy_microscopic_failure_risk p₀ q P Q π
    certified (fun n => min 1 (rho n + eta n)) T ?_ E F hEF
  intro n hn x a hc
  exact empirical_coarse_row_tv (P n x a)
    (empiricalResponsePMF hN (sample ⟨(⟨n, hn⟩, a, x), hc⟩) ω)
    q (measurable_of_countable _) (Q n (q x) a) (rho n) (eta n)
    (hcal ⟨(⟨n, hn⟩, a, x), hc⟩) (hfit n hn x a hc)

end RestrictedRowCalibration

end

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
