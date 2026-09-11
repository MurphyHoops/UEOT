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
variable [MeasurableSpace Ω] [MeasurableSpace Y]

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

/-- Indicator of a finite-alphabet event after one response sample. -/
def sampleIndicator (A : Finset Y) (X : Ω → Y) : Ω → ℝ :=
  fun ω => if X ω ∈ A then 1 else 0

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
  rw [show sampleIndicator A X = (X ⁻¹' (A : Set Y)).indicator (fun _ => (1 : ℝ)) by
    funext ω
    simp [sampleIndicator]]
  rw [integral_indicator_one hpre]
  simp only [measureReal_def]
  rw [← hlaw, Measure.map_apply hX hA]

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
  unfold empiricalMeasure
  rw [measureReal_def, Measure.map_apply hf hA]
  rw [PMF.toMeasure_uniformOfFintype_apply]
  simp only [Fintype.card_fin, ENNReal.toReal_div, ENNReal.toReal_natCast]
  rw [Fintype.card_subtype]
  simp [sampleIndicator, Finset.card_eq_sum_ones, div_eq_mul_inv]

private theorem measurable_sampleIndicator
    (A : Finset Y) (X : Ω → Y) (hX : Measurable X) :
    Measurable (sampleIndicator A X) := by
  classical
  have hA : MeasurableSet (A : Set Y) := A.measurableSet
  rw [show sampleIndicator A X = (X ⁻¹' (A : Set Y)).indicator (fun _ => (1 : ℝ)) by
    funext ω
    simp [sampleIndicator]]
  exact measurable_const.indicator (hX hA)

private theorem sampleIndicator_mem_Icc
    (A : Finset Y) (X : Ω → Y) :
    ∀ ω, sampleIndicator A X ω ∈ Set.Icc (0 : ℝ) 1 := by
  intro ω
  simp [sampleIndicator]

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
  have hXmeas : ∀ n, Measurable (X n) := fun n => measurable_sampleIndicator A _ (hmeas n)
  have hXindep : iIndepFun X μ := by
    simpa [X, Function.comp_def] using
      hindep.comp (fun _ y => if y ∈ A then (1 : ℝ) else 0)
        (fun _ => by
          have hA : MeasurableSet (A : Set Y) := A.measurableSet
          exact measurable_const.indicator hA)
  have hmean : ∀ n, ∫ ω, X n ω ∂μ = p.real (A : Set Y) := by
    intro n
    simpa [X] using integral_sampleIndicator_eq μ p (sample n) (hmeas n) (hlaw n) A
  have hsub : ∀ n ∈ (Finset.univ : Finset (Fin N)),
      HasSubgaussianMGF (fun ω => X n ω - μ[X n]) ((1 / 2 : ℝ≥0) ^ 2) μ := by
    intro n hn
    apply hasSubgaussianMGF_of_mem_Icc (hXmeas n).aemeasurable
    filter_upwards [] with ω
    exact sampleIndicator_mem_Icc A (sample n) ω
  have htail := measure_sum_ge_le_of_iIndepFun
    (h_indep := hXindep.comp (fun _ x => x - μ[X _])
      (fun _ => measurable_id.sub measurable_const))
    (s := (Finset.univ : Finset (Fin N)))
    (h_subG := by
      intro n hn
      simpa [Function.comp_def] using hsub n hn)
    (ε := (N : ℝ) * η)
    (mul_nonneg (Nat.cast_nonneg N) hη)
  have hset :
      {ω | p.real (A : Set Y) + η ≤
        (empiricalMeasure hN sample ω).real (A : Set Y)} ⊆
      {ω | (N : ℝ) * η ≤
        ∑ n ∈ (Finset.univ : Finset (Fin N)),
          (X n ω - μ[X n])} := by
    intro ω hω
    rw [empiricalMeasure_real_finset hN sample ω A] at hω
    simp only [Finset.sum_const_zero, Finset.sum_sub_distrib]
    simp_rw [hmean]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
    field_simp [ne_of_gt hNreal] at hω ⊢
    linarith
  refine (measureReal_mono hset).trans ?_
  calc
    μ.real {ω | (N : ℝ) * η ≤
        ∑ n ∈ (Finset.univ : Finset (Fin N)), (X n ω - μ[X n])}
      ≤ exp (-((N : ℝ) * η) ^ 2 /
          (2 * ∑ n ∈ (Finset.univ : Finset (Fin N)), ((1 / 2 : ℝ≥0) ^ 2))) := htail
    _ = exp (-2 * (N : ℝ) * η ^ 2) := by
      have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_num
      field_simp [ne_of_gt hNreal]
      ring

end UEOT.V3.FiniteAlphabetSampling
