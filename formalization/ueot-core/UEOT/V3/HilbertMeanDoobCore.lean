import Mathlib.Probability.Martingale.Basic
import Mathlib.Tactic

/-!
# P-STAT-06 — generic Doob martingale increment core

The source concentration proof is most robustly organized by keeping the Doob
martingale itself in abstract conditional-expectation form and using explicit
product-law continuation integrals only to prove sharp increment bounds.

This file defines the conditional-expectation process and its increments,
proves strong adaptedness of the increment sequence, and records the exact
finite telescoping identity needed by P-STAT-06.
-/

namespace UEOT.V3.HilbertMeanDoobCore

open MeasureTheory
open scoped BigOperators

universe uΩ

variable {Ω : Type uΩ} {mΩ : MeasurableSpace Ω}

/-- Doob value of a real statistic at filtration time `n`. -/
noncomputable def doobValue
    (μ : Measure Ω) (ℱ : Filtration ℕ mΩ) (F : Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  μ[F | ℱ n]

/-- Doob increments, with time zero centered by the unconditional mean. -/
noncomputable def doobIncrement
    (μ : Measure Ω) (ℱ : Filtration ℕ mΩ) (F : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun ω => doobValue μ ℱ F 0 ω - ∫ x, F x ∂μ
  | n + 1 => fun ω => doobValue μ ℱ F (n + 1) ω - doobValue μ ℱ F n ω

/-- The conditional-expectation process is a martingale whenever the filtration
is sigma-finite, directly reusing Mathlib's canonical theorem. -/
theorem doobValue_martingale
    (μ : Measure Ω) (ℱ : Filtration ℕ mΩ) [SigmaFiniteFiltration μ ℱ]
    (F : Ω → ℝ) :
    Martingale (doobValue μ ℱ F) ℱ μ := by
  simpa [doobValue] using martingale_condExp F ℱ μ

/-- The Doob increment sequence is strongly adapted to the same filtration. -/
theorem doobIncrement_stronglyAdapted
    (μ : Measure Ω) (ℱ : Filtration ℕ mΩ) (F : Ω → ℝ) :
    StronglyAdapted ℱ (doobIncrement μ ℱ F) := by
  intro n
  cases n with
  | zero =>
      exact stronglyMeasurable_condExp.sub stronglyMeasurable_const
  | succ n =>
      exact stronglyMeasurable_condExp.sub
        (stronglyMeasurable_condExp.mono (ℱ.mono (Nat.le_succ n)))

/-- Exact finite telescoping identity: the first `n+1` increments sum to the
Doob value at time `n` minus the unconditional mean. -/
theorem sum_doobIncrement_range_succ
    (μ : Measure Ω) (ℱ : Filtration ℕ mΩ) (F : Ω → ℝ)
    (n : ℕ) (ω : Ω) :
    (∑ i ∈ Finset.range (n + 1), doobIncrement μ ℱ F i ω) =
      doobValue μ ℱ F n ω - ∫ x, F x ∂μ := by
  induction n with
  | zero =>
      simp [doobIncrement]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [doobIncrement]
      ring

end UEOT.V3.HilbertMeanDoobCore
