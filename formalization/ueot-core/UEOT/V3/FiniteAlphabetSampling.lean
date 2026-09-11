import UEOT.V3.FiniteAlphabetConcentration
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic

/-!
# P-STAT-01 sampling layer — empirical laws and Hoeffding

For `N > 0`, the empirical response law is the pushforward of the uniform
probability measure on the sample index type `Fin N`.  Event masses are
therefore empirical Bernoulli averages.  The upper and lower deviations are
handled by Hoeffding's inequality applied respectively to the event indicator
and its negative.
-/

namespace UEOT.V3.FiniteAlphabetSampling

open MeasureTheory ProbabilityTheory Real
open UEOT.V3.FiniteAlphabetConcentration
open scoped BigOperators ENNReal NNReal

universe uΩ uJ uY

variable {Ω : Type uΩ} {J : Type uJ} {Y : Type uY}
variable [MeasurableSpace Ω] [MeasurableSpace Y] [MeasurableSingletonClass Y]

/-- Empirical response law of `N` observed samples. -/
noncomputable def empiricalMeasure {N : ℕ} (hN : 0 < N)
    (sample : Fin N → Ω → Y) (ω : Ω) : Measure Y := by
  letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  letI : MeasurableSpace (Fin N) := ⊤
  exact (PMF.uniformOfFintype (Fin N)).toMeasure.map (fun n => sample n ω)

/-- The empirical law is automatically a probability measure. -/
theorem empiricalMeasure_isProbability {N : ℕ} (hN : 0 < N)
    (sample : Fin N → Ω → Y) (ω : Ω) :
    IsProbabilityMeasure (empiricalMeasure hN sample ω) := by
  letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  letI : MeasurableSpace (Fin N) := ⊤
  have hf : Measurable (fun n : Fin N => sample n ω) := measurable_of_finite _
  unfold empiricalMeasure
  exact (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).2 inferInstance

/-- Indicator of one finite-alphabet event on the response space. -/
noncomputable def eventIndicator (A : Finset Y) : Y → ℝ :=
  (A : Set Y).indicator (1 : Y → ℝ)

/-- Event indicator after one response sample. -/
noncomputable def sampleIndicator (A : Finset Y) (X : Ω → Y) : Ω → ℝ :=
  eventIndicator A ∘ X

private theorem measurable_eventIndicator (A : Finset Y) :
    Measurable (eventIndicator A) := by
  exact measurable_const.indicator A.measurableSet

private theorem measurable_sampleIndicator
    (A : Finset Y) (X : Ω → Y) (hX : Measurable X) :
    Measurable (sampleIndicator A X) := by
  exact (measurable_eventIndicator A).comp hX

private theorem sampleIndicator_mem_Icc
    (A : Finset Y) (X : Ω → Y) :
    ∀ ω, sampleIndicator A X ω ∈ Set.Icc (0 : ℝ) 1 := by
  intro ω
  classical
  by_cases h : X ω ∈ A <;> simp [sampleIndicator, eventIndicator, h]

/-- The expectation of a sampled event indicator is the event probability of
the sample law. -/
theorem integral_sampleIndicator_eq
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : Measure Y)
    (X : Ω → Y) (hX : Measurable X)
    (hlaw : μ.map X = p)
    (A : Finset Y) :
    ∫ ω, sampleIndicator A X ω ∂μ = p.real (A : Set Y) := by
  classical
  have hA : MeasurableSet (A : Set Y) := A.measurableSet
  have hpre : MeasurableSet (X ⁻¹' (A : Set Y)) := hX hA
  have hrepr :
      sampleIndicator A X =
        (X ⁻¹' (A : Set Y)).indicator (1 : Ω → ℝ) := by
    funext ω
    by_cases h : X ω ∈ A <;> simp [sampleIndicator, eventIndicator, h]
  rw [hrepr, integral_indicator_one hpre]
  rw [← hlaw]
  simp only [measureReal_def]
  rw [Measure.map_apply hX hA]

/-- Event mass of the empirical measure equals the arithmetic mean of the
sample event indicators. -/
theorem empiricalMeasure_real_finset {N : ℕ} (hN : 0 < N)
    (sample : Fin N → Ω → Y) (ω : Ω) (A : Finset Y) :
    (empiricalMeasure hN sample ω).real (A : Set Y) =
      (∑ n : Fin N, sampleIndicator A (sample n) ω) / (N : ℝ) := by
  classical
  letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  letI : MeasurableSpace (Fin N) := ⊤
  have hf : Measurable (fun n : Fin N => sample n ω) := measurable_of_finite _
  have hA : MeasurableSet (A : Set Y) := A.measurableSet
  let S : Set (Fin N) := (fun n : Fin N => sample n ω) ⁻¹' (A : Set Y)
  have hS : MeasurableSet S := MeasurableSpace.measurableSet_top
  have hsum :
      (∑ n : Fin N, if sample n ω ∈ A then (1 : ℝ) else 0) =
        ((Finset.univ.filter (fun n : Fin N => sample n ω ∈ A)).card : ℝ) := by
    simpa using
      (Finset.sum_boole (R := ℝ) (fun n : Fin N => sample n ω ∈ A) Finset.univ)
  have hcount :
      ((Finset.univ.filter (fun n : Fin N => sample n ω ∈ A)).card : ℝ) =
        ∑ n : Fin N, sampleIndicator A (sample n) ω := by
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases h : sample n ω ∈ A <;>
      simp [sampleIndicator, eventIndicator, h]
  have hcardNat :
      Fintype.card S =
        (Finset.univ.filter (fun n : Fin N => sample n ω ∈ A)).card := by
    rw [Fintype.card_subtype]
    congr 1
    ext n
    simp [S]
  have hcardReal :
      (Fintype.card S : ℝ) =
        ∑ n : Fin N, sampleIndicator A (sample n) ω := by
    rw [hcardNat]
    exact hcount
  unfold empiricalMeasure
  rw [measureReal_def, Measure.map_apply hf hA]
  change ((PMF.uniformOfFintype (Fin N)).toMeasure S).toReal = _
  rw [PMF.toMeasure_uniformOfFintype_apply hS]
  simp only [Fintype.card_fin, ENNReal.toReal_div, ENNReal.toReal_natCast]
  rw [hcardReal]

/-- One-sided upper Hoeffding bound for a fixed finite-alphabet event. -/
theorem measure_empirical_event_upper_le
    {N : ℕ} (hN : 0 < N)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : Measure Y)
    (sample : Fin N → Ω → Y)
    (hmeas : ∀ n, Measurable (sample n))
    (hindep : iIndepFun sample μ)
    (hlaw : ∀ n, μ.map (sample n) = p)
    (A : Finset Y) {η : ℝ} (hη : 0 ≤ η) :
    μ.real {ω |
      p.real (A : Set Y) + η ≤
        (empiricalMeasure hN sample ω).real (A : Set Y)} ≤
      exp (-2 * (N : ℝ) * η ^ 2) := by
  classical
  let X : Fin N → Ω → ℝ := fun n => sampleIndicator A (sample n)
  let Z : Fin N → Ω → ℝ := fun n ω => X n ω - μ[X n]
  have hXmeas : ∀ n, Measurable (X n) :=
    fun n => measurable_sampleIndicator A _ (hmeas n)
  have hXindep : iIndepFun X μ := by
    simpa [X, sampleIndicator, Function.comp_def] using
      hindep.comp (fun _ => eventIndicator A) (fun _ => measurable_eventIndicator A)
  have hZindep : iIndepFun Z μ := by
    simpa [Z, Function.comp_def] using
      hXindep.comp (fun n x => x - μ[X n])
        (fun _ => measurable_id.sub measurable_const)
  have hmean : ∀ n, ∫ ω, X n ω ∂μ = p.real (A : Set Y) := by
    intro n
    simpa [X] using
      integral_sampleIndicator_eq μ p (sample n) (hmeas n) (hlaw n) A
  have hsub : ∀ n ∈ (Finset.univ : Finset (Fin N)),
      HasSubgaussianMGF (Z n) ((1 / 2 : ℝ≥0) ^ 2) μ := by
    intro n hn
    have hs := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc
      (μ := μ) (X := X n) (a := (0 : ℝ)) (b := (1 : ℝ))
      (hXmeas n).aemeasurable
      (ae_of_all μ (sampleIndicator_mem_Icc A (sample n)))
    simpa [Z] using hs
  have htail := ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    (h_indep := hZindep)
    (s := (Finset.univ : Finset (Fin N)))
    (h_subG := hsub)
    (ε := (N : ℝ) * η)
    (mul_nonneg (Nat.cast_nonneg N) hη)
  have hset :
      {ω | p.real (A : Set Y) + η ≤
        (empiricalMeasure hN sample ω).real (A : Set Y)} ⊆
      {ω | (N : ℝ) * η ≤
        ∑ n ∈ (Finset.univ : Finset (Fin N)), Z n ω} := by
    intro ω hω
    change p.real (A : Set Y) + η ≤
      (empiricalMeasure hN sample ω).real (A : Set Y) at hω
    change (N : ℝ) * η ≤
      ∑ n ∈ (Finset.univ : Finset (Fin N)), Z n ω
    rw [empiricalMeasure_real_finset hN sample ω A] at hω
    simp only [Z, Finset.sum_sub_distrib]
    simp_rw [hmean]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
    field_simp [ne_of_gt hNreal] at hω ⊢
    linarith
  refine (measureReal_mono hset).trans ?_
  calc
    μ.real {ω | (N : ℝ) * η ≤
        ∑ n ∈ (Finset.univ : Finset (Fin N)), Z n ω}
      ≤ exp (-((N : ℝ) * η) ^ 2 /
          (2 * ∑ n ∈ (Finset.univ : Finset (Fin N)), ((1 / 2 : ℝ≥0) ^ 2))) := htail
    _ = exp (-2 * (N : ℝ) * η ^ 2) := by
      have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_num
      field_simp [ne_of_gt hNreal]
      ring

end UEOT.V3.FiniteAlphabetSampling
