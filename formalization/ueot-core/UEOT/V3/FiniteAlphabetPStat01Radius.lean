import UEOT.V3.FiniteAlphabetPStat01
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# P-STAT-01 — clipped confidence radius

This module isolates the final analytic inversion of the already verified
P-STAT-01 simultaneous finite-alphabet TV tail bound.  The un-clipped radius
is chosen so that the exact tail prefactor reduces to `α`; clipping at one is
justified by the deterministic probability-measure bound `D_TV ≤ 1`.
-/

namespace UEOT.V3.FiniteAlphabetPStat01Radius

open MeasureTheory ProbabilityTheory Real
open UEOT.V3.TotalVariation
open UEOT.V3.FiniteAlphabetSampling
open UEOT.V3.FiniteAlphabetPStat01

universe uΩ uJ uY

variable {Ω : Type uΩ} {J : Type uJ} {Y : Type uY}
variable [MeasurableSpace Ω] [MeasurableSpace Y]
  [MeasurableSingletonClass Y]

/-- The literal clipped confidence radius appearing in the frozen P-STAT-01
statement. `K` is the response alphabet size and `L` the number of fixed
response cells. -/
noncomputable def pStat01Radius (N K L : ℕ) (α : ℝ) : ℝ :=
  min 1 (sqrt
    ((((K + 1 : ℕ) : ℝ) * log 2 + log ((L : ℝ) / α)) /
      (2 * (N : ℝ))))

private theorem raw_tail_factor_eq_alpha
    [Fintype J] [Nonempty J] [Fintype Y]
    {N : ℕ} (hN : 0 < N)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    (Fintype.card J : ℝ) *
        (2 ^ (Fintype.card Y + 1) : ℝ) *
        exp (-2 * (N : ℝ) *
          (sqrt
            (((((Fintype.card Y + 1 : ℕ) : ℝ) * log 2 +
                log ((Fintype.card J : ℝ) / α)) /
              (2 * (N : ℝ))))) ^ 2) = α := by
  have hLnat : 0 < Fintype.card J := Fintype.card_pos
  have hL : (0 : ℝ) < (Fintype.card J : ℝ) := by exact_mod_cast hLnat
  have hLoneNat : 1 ≤ Fintype.card J := Nat.succ_le_iff.mpr hLnat
  have hLone : (1 : ℝ) ≤ (Fintype.card J : ℝ) := by exact_mod_cast hLoneNat
  have hratio_pos : 0 < (Fintype.card J : ℝ) / α := div_pos hL hα0
  have hratio_one : 1 ≤ (Fintype.card J : ℝ) / α := by
    rw [le_div_iff₀ hα0]
    simpa using hα1.trans hLone
  have hnum : 0 ≤
      (((Fintype.card Y + 1 : ℕ) : ℝ) * log 2 +
        log ((Fintype.card J : ℝ) / α)) := by
    exact add_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num)))
      (Real.log_nonneg hratio_one)
  have hden : 0 < 2 * (N : ℝ) := by positivity
  have hrad : 0 ≤
      ((((Fintype.card Y + 1 : ℕ) : ℝ) * log 2 +
        log ((Fintype.card J : ℝ) / α)) /
        (2 * (N : ℝ))) := div_nonneg hnum hden.le
  have hexponent :
      -2 * (N : ℝ) *
          (sqrt
            (((((Fintype.card Y + 1 : ℕ) : ℝ) * log 2 +
                log ((Fintype.card J : ℝ) / α)) /
              (2 * (N : ℝ))))) ^ 2 =
        -((((Fintype.card Y + 1 : ℕ) : ℝ) * log 2 +
          log ((Fintype.card J : ℝ) / α))) := by
    rw [Real.sq_sqrt hrad]
    field_simp [ne_of_gt hden]
  have hpowexp :
      exp (((Fintype.card Y + 1 : ℕ) : ℝ) * log 2) =
        (2 : ℝ) ^ (Fintype.card Y + 1) := by
    simpa [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using
      (Real.exp_nat_mul (Real.log 2) (Fintype.card Y + 1))
  have hratioexp :
      exp (log ((Fintype.card J : ℝ) / α)) =
        (Fintype.card J : ℝ) / α := Real.exp_log hratio_pos
  rw [hexponent]
  rw [show
      -((((Fintype.card Y + 1 : ℕ) : ℝ) * log 2 +
          log ((Fintype.card J : ℝ) / α))) =
        -(((Fintype.card Y + 1 : ℕ) : ℝ) * log 2) +
          (-log ((Fintype.card J : ℝ) / α)) by ring]
  rw [Real.exp_add, Real.exp_neg, Real.exp_neg, hpowexp, hratioexp]
  have hpowne : (2 : ℝ) ^ (Fintype.card Y + 1) ≠ 0 := by positivity
  have hLne : (Fintype.card J : ℝ) ≠ 0 := ne_of_gt hL
  have hαne : α ≠ 0 := ne_of_gt hα0
  field_simp [hpowne, hLne, hαne]

/-- **P-STAT-01 clipped confidence radius.** For confidence level
`0 < α ≤ 1`, the simultaneous TV error of all fixed response cells exceeds
the frozen radius with probability at most `α`. If the analytic square-root
radius is larger than one, the clipping branch is discharged by the
deterministic probability-measure bound `D_TV ≤ 1`. -/
theorem p_stat_01_radius
    [Fintype J] [Nonempty J] [Fintype Y]
    {N : ℕ} (hN : 0 < N)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : J → Measure Y)
    (hp : ∀ j, IsProbabilityMeasure (p j))
    (sample : J → Fin N → Ω → Y)
    (hmeas : ∀ j n, Measurable (sample j n))
    (hindep : ∀ j, iIndepFun (sample j) μ)
    (hlaw : ∀ j n, μ.map (sample j n) = p j)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    μ.real {ω | ∃ j : J,
      pStat01Radius N (Fintype.card Y) (Fintype.card J) α <
        tvDist (p j) (empiricalMeasure hN (sample j) ω)} ≤ α := by
  let raw : ℝ := sqrt
    (((((Fintype.card Y + 1 : ℕ) : ℝ) * log 2 +
        log ((Fintype.card J : ℝ) / α)) /
      (2 * (N : ℝ))))
  have hraw_nonneg : 0 ≤ raw := by
    dsimp [raw]
    exact Real.sqrt_nonneg _
  by_cases hclip : raw ≤ 1
  · have hradius :
        pStat01Radius N (Fintype.card Y) (Fintype.card J) α = raw := by
      change min 1 raw = raw
      exact min_eq_right hclip
    rw [hradius]
    have htail := p_stat_01_tail (η := raw)
      hN μ p hp sample hmeas hindep hlaw hraw_nonneg
    exact htail.trans_eq (raw_tail_factor_eq_alpha hN hα0 hα1)
  · have hone_raw : (1 : ℝ) ≤ raw := le_of_lt (lt_of_not_ge hclip)
    have hradius :
        pStat01Radius N (Fintype.card Y) (Fintype.card J) α = 1 := by
      change min 1 raw = 1
      exact min_eq_left hone_raw
    rw [hradius]
    have hempty :
        {ω | ∃ j : J,
          (1 : ℝ) < tvDist (p j) (empiricalMeasure hN (sample j) ω)} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      push_neg
      intro j
      letI : IsProbabilityMeasure (p j) := hp j
      letI : IsProbabilityMeasure (empiricalMeasure hN (sample j) ω) :=
        empiricalMeasure_isProbability hN (sample j) ω
      exact tvDist_le_one (p j) (empiricalMeasure hN (sample j) ω)
    rw [hempty]
    simp [hα0.le]

end UEOT.V3.FiniteAlphabetPStat01Radius
