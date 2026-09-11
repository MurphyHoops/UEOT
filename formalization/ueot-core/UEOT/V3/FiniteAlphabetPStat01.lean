import UEOT.V3.FiniteAlphabetSampling
import UEOT.V3.FiniteAlphabetConcentration
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-!
# P-STAT-01 — finite-alphabet simultaneous TV concentration

This module closes the probabilistic wrapper around the already verified
sampling and finite-union layers.  A lower tail is reduced to the upper tail
by complementing the finite response event.  The two one-sided events give the
factor `2`, the finite response alphabet contributes `2^K`, and the response
cells contribute `L`, exactly as in the frozen source proof.
-/

namespace UEOT.V3.FiniteAlphabetPStat01

open MeasureTheory ProbabilityTheory Real
open UEOT.V3.TotalVariation
open UEOT.V3.FiniteAlphabetConcentration
open UEOT.V3.FiniteAlphabetSampling
open scoped BigOperators

universe uΩ uJ uY

variable {Ω : Type uΩ} {J : Type uJ} {Y : Type uY}
variable [MeasurableSpace Ω] [MeasurableSpace Y]
  [MeasurableSingletonClass Y]

/-- Lower empirical deviation for one finite-alphabet event, obtained from the
already verified upper Hoeffding bound by passing to the complementary event. -/
theorem measure_empirical_event_lower_le
    [Fintype Y]
    {N : ℕ} (hN : 0 < N)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : Measure Y) [IsProbabilityMeasure p]
    (sample : Fin N → Ω → Y)
    (hmeas : ∀ n, Measurable (sample n))
    (hindep : iIndepFun sample μ)
    (hlaw : ∀ n, μ.map (sample n) = p)
    (A : Finset Y) {η : ℝ} (hη : 0 ≤ η) :
    μ.real {ω |
      (empiricalMeasure hN sample ω).real (A : Set Y) + η ≤
        p.real (A : Set Y)} ≤
      exp (-2 * (N : ℝ) * η ^ 2) := by
  classical
  let Ac : Finset Y := Finset.univ \ A
  have hAc : (Ac : Set Y) = (A : Set Y)ᶜ := by
    ext y
    simp [Ac]
  have hu := measure_empirical_event_upper_le
    hN μ p sample hmeas hindep hlaw Ac hη
  have hset :
      {ω |
        (empiricalMeasure hN sample ω).real (A : Set Y) + η ≤
          p.real (A : Set Y)} ⊆
      {ω |
        p.real (Ac : Set Y) + η ≤
          (empiricalMeasure hN sample ω).real (Ac : Set Y)} := by
    intro ω hω
    change (empiricalMeasure hN sample ω).real (A : Set Y) + η ≤
      p.real (A : Set Y) at hω
    change p.real (Ac : Set Y) + η ≤
      (empiricalMeasure hN sample ω).real (Ac : Set Y)
    letI : IsProbabilityMeasure (empiricalMeasure hN sample ω) :=
      empiricalMeasure_isProbability hN sample ω
    rw [hAc, measureReal_compl A.measurableSet,
      measureReal_compl A.measurableSet]
    have hp_univ : p.real Set.univ = 1 := by
      simp [measureReal_def]
    have hphat_univ :
        (empiricalMeasure hN sample ω).real Set.univ = 1 := by
      simp [measureReal_def]
    rw [hp_univ, hphat_univ]
    linarith
  exact (measureReal_mono hset).trans hu

/-- Two-sided Hoeffding bound for one response-cell/subset event. -/
theorem measure_subsetBadEvent_empirical_le
    [Fintype Y]
    {N : ℕ} (hN : 0 < N)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : Measure Y) [IsProbabilityMeasure p]
    (sample : Fin N → Ω → Y)
    (hmeas : ∀ n, Measurable (sample n))
    (hindep : iIndepFun sample μ)
    (hlaw : ∀ n, μ.map (sample n) = p)
    (A : Finset Y) {η : ℝ} (hη : 0 ≤ η) :
    μ.real (subsetBadEvent p (empiricalMeasure hN sample) η A) ≤
      2 * exp (-2 * (N : ℝ) * η ^ 2) := by
  let upper : Set Ω :=
    {ω | p.real (A : Set Y) + η ≤
      (empiricalMeasure hN sample ω).real (A : Set Y)}
  let lower : Set Ω :=
    {ω | (empiricalMeasure hN sample ω).real (A : Set Y) + η ≤
      p.real (A : Set Y)}
  have hbad :
      subsetBadEvent p (empiricalMeasure hN sample) η A ⊆ upper ∪ lower := by
    intro ω hω
    change η < |p.real (A : Set Y) -
      (empiricalMeasure hN sample ω).real (A : Set Y)| at hω
    change ω ∈ upper ∪ lower
    by_cases hord : p.real (A : Set Y) ≤
        (empiricalMeasure hN sample ω).real (A : Set Y)
    · left
      change p.real (A : Set Y) + η ≤
        (empiricalMeasure hN sample ω).real (A : Set Y)
      rw [abs_of_nonpos (sub_nonpos.mpr hord)] at hω
      linarith
    · right
      have hord' : (empiricalMeasure hN sample ω).real (A : Set Y) <
          p.real (A : Set Y) := lt_of_not_ge hord
      change (empiricalMeasure hN sample ω).real (A : Set Y) + η ≤
        p.real (A : Set Y)
      rw [abs_of_pos (sub_pos.mpr hord')] at hω
      linarith
  have hupper : μ.real upper ≤ exp (-2 * (N : ℝ) * η ^ 2) := by
    simpa [upper] using
      measure_empirical_event_upper_le
        hN μ p sample hmeas hindep hlaw A hη
  have hlower : μ.real lower ≤ exp (-2 * (N : ℝ) * η ^ 2) := by
    simpa [lower] using
      measure_empirical_event_lower_le
        hN μ p sample hmeas hindep hlaw A hη
  calc
    μ.real (subsetBadEvent p (empiricalMeasure hN sample) η A)
        ≤ μ.real (upper ∪ lower) := measureReal_mono hbad
    _ ≤ μ.real upper + μ.real lower := measureReal_union_le upper lower
    _ ≤ exp (-2 * (N : ℝ) * η ^ 2) +
          exp (-2 * (N : ℝ) * η ^ 2) := add_le_add hupper hlower
    _ = 2 * exp (-2 * (N : ℝ) * η ^ 2) := by ring

/-- **P-STAT-01 tail bound.**  For `L = card J` fixed response cells on a
finite alphabet of size `K = card Y`, with `N` independent identically
lawed samples inside each cell, the probability that any cell has TV error
larger than `η` is bounded by `L * 2^(K+1) * exp(-2*N*η^2)`.

No independence across response cells is assumed. -/
theorem p_stat_01_tail
    [Fintype J] [Fintype Y]
    {N : ℕ} (hN : 0 < N)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : J → Measure Y)
    (hp : ∀ j, IsProbabilityMeasure (p j))
    (sample : J → Fin N → Ω → Y)
    (hmeas : ∀ j n, Measurable (sample j n))
    (hindep : ∀ j, iIndepFun (sample j) μ)
    (hlaw : ∀ j n, μ.map (sample j n) = p j)
    {η : ℝ} (hη : 0 ≤ η) :
    μ.real {ω | ∃ j : J,
      η < tvDist (p j) (empiricalMeasure hN (sample j) ω)} ≤
      (Fintype.card J : ℝ) *
        (2 ^ (Fintype.card Y + 1) : ℝ) *
        exp (-2 * (N : ℝ) * η ^ 2) := by
  have hpHat : ∀ j ω,
      IsProbabilityMeasure (empiricalMeasure hN (sample j) ω) :=
    fun j ω => empiricalMeasure_isProbability hN (sample j) ω
  have hB : ∀ j A,
      μ.real (subsetBadEvent (p j)
        (empiricalMeasure hN (sample j)) η A) ≤
        2 * exp (-2 * (N : ℝ) * η ^ 2) := by
    intro j A
    letI : IsProbabilityMeasure (p j) := hp j
    exact measure_subsetBadEvent_empirical_le
      hN μ (p j) (sample j) (hmeas j) (hindep j) (hlaw j) A hη
  have h := measure_exists_cell_tvBadEvent_le_of_subset_bound
    μ p hp (fun j => empiricalMeasure hN (sample j)) hpHat
    η (2 * exp (-2 * (N : ℝ) * η ^ 2)) hB
  change μ.real {ω | ∃ j : J,
      η < tvDist (p j) (empiricalMeasure hN (sample j) ω)} ≤ _ at h
  calc
    μ.real {ω | ∃ j : J,
        η < tvDist (p j) (empiricalMeasure hN (sample j) ω)}
      ≤ (Fintype.card J : ℝ) *
          (2 ^ Fintype.card Y : ℝ) *
          (2 * exp (-2 * (N : ℝ) * η ^ 2)) := h
    _ = (Fintype.card J : ℝ) *
          (2 ^ (Fintype.card Y + 1) : ℝ) *
          exp (-2 * (N : ℝ) * η ^ 2) := by
      rw [pow_succ]
      ring

end UEOT.V3.FiniteAlphabetPStat01
