import UEOT.V3.BoundedLossTwoSided
import UEOT.V3.FiniteCandidateDiscovery
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# P-STAT-08 — finite-candidate discovery theorem

This is the source-facing closure of the finite-candidate validation argument.
For `m` fixed candidates, `[0,1]` losses, and `N` independent validation
observations, the radius

`u = sqrt (log (2m / α) / (2N))`

makes the simultaneous Hoeffding failure probability at most `α`.  The
verified deterministic ERM interpolation then gives excess true risk at most
`2u`.
-/

namespace UEOT.V3.FiniteCandidatePStat08

open MeasureTheory ProbabilityTheory Real
open UEOT.V3.BoundedLossSampling
open UEOT.V3.BoundedLossTwoSided
open UEOT.V3.FiniteCandidateDiscovery

universe uΩ uZ uF

variable {Ω : Type uΩ} {Z : Type uZ} {F : Type uF}
variable [MeasurableSpace Ω] [MeasurableSpace Z]

/-- The literal validation radius in frozen P-STAT-08. -/
noncomputable def pStat08Radius (N m : ℕ) (α : ℝ) : ℝ :=
  sqrt (log ((2 * (m : ℝ)) / α) / (2 * (N : ℝ)))

private theorem tail_factor_eq_alpha
    [Fintype F] [Nonempty F]
    {N : ℕ} (hN : 0 < N)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    (Fintype.card F : ℝ) *
        (2 * exp (-2 * (N : ℝ) *
          (pStat08Radius N (Fintype.card F) α) ^ 2)) = α := by
  have hmNat : 0 < Fintype.card F := Fintype.card_pos
  have hm : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hmNat
  have hmOneNat : 1 ≤ Fintype.card F := Nat.succ_le_iff.mpr hmNat
  have hmOne : (1 : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast hmOneNat
  have hnumPos : 0 < 2 * (Fintype.card F : ℝ) := mul_pos (by norm_num) hm
  have hratioPos : 0 < (2 * (Fintype.card F : ℝ)) / α :=
    div_pos hnumPos hα0
  have hratioOne : 1 ≤ (2 * (Fintype.card F : ℝ)) / α := by
    rw [le_div_iff₀ hα0]
    nlinarith
  have hlog : 0 ≤ log ((2 * (Fintype.card F : ℝ)) / α) :=
    Real.log_nonneg hratioOne
  have hden : 0 < 2 * (N : ℝ) := by positivity
  have hrad : 0 ≤
      log ((2 * (Fintype.card F : ℝ)) / α) / (2 * (N : ℝ)) :=
    div_nonneg hlog hden.le
  have hexponent :
      -2 * (N : ℝ) * (pStat08Radius N (Fintype.card F) α) ^ 2 =
        -log ((2 * (Fintype.card F : ℝ)) / α) := by
    unfold pStat08Radius
    rw [Real.sq_sqrt hrad]
    field_simp [ne_of_gt hden]
  rw [hexponent, Real.exp_neg, Real.exp_log hratioPos]
  have hmne : (Fintype.card F : ℝ) ≠ 0 := ne_of_gt hm
  have hαne : α ≠ 0 := ne_of_gt hα0
  field_simp [hmne, hαne]

/-- **P-STAT-08, source-facing finite-candidate discovery bound.**

The conclusion is written as a failure-probability bound, equivalent to the
source statement that with confidence at least `1 - α`, the empirical-risk
minimizer has true risk at most the best candidate risk plus twice the frozen
validation radius. -/
theorem p_stat_08
    [Fintype F] [Nonempty F]
    {N : ℕ} (hN : 0 < N)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Measure Z)
    (loss : F → Z → ℝ)
    (hloss : ∀ f, Measurable (loss f))
    (hloss01 : ∀ f z, loss f z ∈ Set.Icc (0 : ℝ) 1)
    (sample : Fin N → Ω → Z)
    (hmeas : ∀ n, Measurable (sample n))
    (hindep : iIndepFun sample μ)
    (hlaw : ∀ n, μ.map (sample n) = P)
    (fHat : Ω → F) (fStar : F)
    (hERM : ∀ ω f,
      empiricalRisk (loss (fHat ω)) sample ω ≤ empiricalRisk (loss f) sample ω)
    (hStar : ∀ f, trueRisk P (loss fStar) ≤ trueRisk P (loss f))
    {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    μ.real {ω |
      trueRisk P (loss (fHat ω)) >
        trueRisk P (loss fStar) +
          2 * pStat08Radius N (Fintype.card F) α} ≤ α := by
  let u := pStat08Radius N (Fintype.card F) α
  have hu : 0 ≤ u := by
    dsimp [u, pStat08Radius]
    exact Real.sqrt_nonneg _
  have hsubset :
      {ω |
        trueRisk P (loss (fHat ω)) >
          trueRisk P (loss fStar) + 2 * u} ⊆
      {ω | ∃ f : F,
        u < |empiricalRisk (loss f) sample ω - trueRisk P (loss f)|} := by
    intro ω hbad
    by_contra hnone
    have hUniform : ∀ f,
        |empiricalRisk (loss f) sample ω - trueRisk P (loss f)| ≤ u := by
      intro f
      apply le_of_not_gt
      intro hf
      exact hnone ⟨f, hf⟩
    have hgood := erm_excess_le_two_uniform_event
      (R := fun f => trueRisk P (loss f))
      (Rhat := fun ω f => empiricalRisk (loss f) sample ω)
      fHat fStar u hERM hStar hUniform
    exact (not_lt_of_ge hgood) hbad
  change μ.real {ω |
      trueRisk P (loss (fHat ω)) >
        trueRisk P (loss fStar) + 2 * u} ≤ α
  refine (measureReal_mono hsubset).trans ?_
  have htail := measure_exists_candidate_bad_le
    (F := F) hN μ P loss hloss hloss01 sample hmeas hindep hlaw hu
  exact htail.trans_eq (tail_factor_eq_alpha (F := F) hN hα0 hα1)

end UEOT.V3.FiniteCandidatePStat08
