import UEOT.V3.RecoveryDiscrete
import Mathlib.MeasureTheory.Function.ConditionalLExpectation
import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# P-REC-01 probability layer — nonnegative conditional drift

The source severity variables are nonnegative and only the initial expectation
is assumed finite.  We therefore use Mathlib's conditional *Lebesgue*
expectation for `ℝ≥0∞`-valued variables rather than silently assuming that
every future severity variable is already integrable.

This file proves the total-expectation recursion and propagates finiteness.
The final real-valued closed form and Markov tail wrapper are layered on top.
-/

namespace UEOT.V3.RecoveryProbability

open MeasureTheory
open scoped ENNReal

universe uΩ

variable {Ω : Type uΩ} {mΩ : MeasurableSpace Ω}

noncomputable def ennMean
    (P : Measure Ω) (R : ℕ → Ω → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, R n ω ∂P

/-- Taking total expectation of the source conditional drift gives the affine
recursion for nonnegative extended expectations, without assuming future
integrability in advance. -/
theorem ennMean_succ_le
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ mΩ)
    (R : ℕ → Ω → ℝ≥0∞)
    (κ η : ℝ≥0∞)
    (hR : ∀ n, Measurable (R n))
    (hcond : ∀ n,
      P⁻[R (n + 1) | ℱ n] ≤ᵐ[P]
        fun ω => κ * R n ω + η) :
    ∀ n, ennMean P R (n + 1) ≤ κ * ennMean P R n + η := by
  intro n
  calc
    ennMean P R (n + 1) =
        ∫⁻ ω, P⁻[R (n + 1) | ℱ n] ω ∂P := by
      symm
      exact lintegral_condLExp (ℱ.le n) P (R (n + 1))
    _ ≤ ∫⁻ ω, κ * R n ω + η ∂P :=
      lintegral_mono_ae (hcond n)
    _ = κ * ennMean P R n + η := by
      rw [lintegral_add_left]
      · rw [lintegral_const_mul κ (hR n)]
        simp [ennMean]
      · exact (hR n).const_mul κ

/-- The source hypothesis `E R₀ < ∞`, together with finite coefficients and
the conditional drift, forces every later expectation to remain finite. -/
theorem ennMean_lt_top
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ mΩ)
    (R : ℕ → Ω → ℝ≥0∞)
    (κ η : ℝ≥0∞)
    (hκ : κ < ∞) (hη : η < ∞)
    (hR : ∀ n, Measurable (R n))
    (hcond : ∀ n,
      P⁻[R (n + 1) | ℱ n] ≤ᵐ[P]
        fun ω => κ * R n ω + η)
    (h0 : ennMean P R 0 < ∞) :
    ∀ n, ennMean P R n < ∞ := by
  intro n
  induction n with
  | zero =>
      exact h0
  | succ n ih =>
      have hstep := ennMean_succ_le P ℱ R κ η hR hcond n
      exact hstep.trans_lt <|
        ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top hκ ih, hη⟩


/-- Markov tail bound in the same nonnegative extended-expectation model used
for the conditional-drift layer.  No extra integrability assumption is needed:
a finite positive threshold is enough for the standard `lintegral` Markov
inequality. -/
theorem ennMean_markov_tail
    (P : Measure Ω)
    (R : ℕ → Ω → ℝ≥0∞)
    (hR : ∀ n, Measurable (R n))
    (n : ℕ) {a : ℝ≥0∞}
    (ha0 : a ≠ 0) (hatop : a ≠ ∞) :
    P {ω | a ≤ R n ω} ≤ ennMean P R n / a := by
  simpa [ennMean] using
    (meas_ge_le_lintegral_div
      (μ := P) (hR n).aemeasurable ha0 hatop)


/-- Finite real expectation associated with the nonnegative extended-value
model.  Under the P-REC-01 hypotheses all these quantities are finite. -/
noncomputable def realMean
    (P : Measure Ω) (R : ℕ → Ω → ℝ≥0∞) (n : ℕ) : ℝ :=
  (ennMean P R n).toReal

/-- Total expectation turns the conditional drift into the literal real affine
recursion used in the manuscript. -/
theorem realMean_succ_le
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ mΩ)
    (R : ℕ → Ω → ℝ≥0∞)
    (κ η : NNReal)
    (hR : ∀ n, Measurable (R n))
    (hcond : ∀ n,
      P⁻[R (n + 1) | ℱ n] ≤ᵐ[P]
        fun ω => (κ : ℝ≥0∞) * R n ω + (η : ℝ≥0∞))
    (h0 : ennMean P R 0 < ∞) :
    ∀ n, realMean P R (n + 1) ≤
      (κ : ℝ) * realMean P R n + (η : ℝ) := by
  have hfin : ∀ n, ennMean P R n < ∞ :=
    ennMean_lt_top P ℱ R (κ : ℝ≥0∞) (η : ℝ≥0∞)
      ENNReal.coe_lt_top ENNReal.coe_lt_top hR hcond h0
  intro n
  have hstep :=
    ennMean_succ_le P ℱ R (κ : ℝ≥0∞) (η : ℝ≥0∞) hR hcond n
  have hrhs :
      (κ : ℝ≥0∞) * ennMean P R n + (η : ℝ≥0∞) ≠ ∞ :=
    ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top ENNReal.coe_ne_top (hfin n).ne,
        ENNReal.coe_ne_top⟩
  have hreal := ENNReal.toReal_mono hrhs hstep
  rw [ENNReal.toReal_add
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (hfin n).ne)
      ENNReal.coe_ne_top,
    ENNReal.toReal_mul] at hreal
  simpa [realMean] using hreal

/-- Source-facing mean bound of P-REC-01. -/
theorem p_rec_01_mean_bound
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ mΩ)
    (R : ℕ → Ω → ℝ≥0∞)
    (κ η : NNReal)
    (hκ : (κ : ℝ) < 1)
    (hR : ∀ n, Measurable (R n))
    (hcond : ∀ n,
      P⁻[R (n + 1) | ℱ n] ≤ᵐ[P]
        fun ω => (κ : ℝ≥0∞) * R n ω + (η : ℝ≥0∞))
    (h0 : ennMean P R 0 < ∞) :
    ∀ n, realMean P R n ≤
      (κ : ℝ) ^ n * realMean P R 0 +
        (η : ℝ) * ((1 - (κ : ℝ) ^ n) / (1 - (κ : ℝ))) := by
  apply RecoveryDiscrete.affine_recurrence_closed_bound
  · exact_mod_cast κ.2
  · exact hκ
  · exact realMean_succ_le P ℱ R κ η hR hcond h0

/-- Source-facing Markov tail clause of P-REC-01, with the same closed-form
numerator as the manuscript. -/
theorem p_rec_01_tail_bound
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ mΩ)
    (R : ℕ → Ω → ℝ≥0∞)
    (κ η a : NNReal)
    (hκ : (κ : ℝ) < 1)
    (ha : 0 < a)
    (hR : ∀ n, Measurable (R n))
    (hcond : ∀ n,
      P⁻[R (n + 1) | ℱ n] ≤ᵐ[P]
        fun ω => (κ : ℝ≥0∞) * R n ω + (η : ℝ≥0∞))
    (h0 : ennMean P R 0 < ∞) :
    ∀ n,
      P.real {ω | (a : ℝ≥0∞) ≤ R n ω} ≤
        ((κ : ℝ) ^ n * realMean P R 0 +
          (η : ℝ) * ((1 - (κ : ℝ) ^ n) / (1 - (κ : ℝ)))) / (a : ℝ) := by
  intro n
  have hmeanfinite : ennMean P R n < ∞ :=
    ennMean_lt_top P ℱ R (κ : ℝ≥0∞) (η : ℝ≥0∞)
      ENNReal.coe_lt_top ENNReal.coe_lt_top hR hcond h0 n
  have hmark :=
    ennMean_markov_tail P R hR n
      (a := (a : ℝ≥0∞))
      (by exact_mod_cast ha.ne')
      ENNReal.coe_ne_top
  have hdivfinite :
      ennMean P R n / (a : ℝ≥0∞) ≠ ∞ := by
    exact ENNReal.div_ne_top hmeanfinite.ne (by exact_mod_cast ha.ne')
  have hmarkReal := ENNReal.toReal_mono hdivfinite hmark
  have hbase :
      P.real {ω | (a : ℝ≥0∞) ≤ R n ω} ≤
        realMean P R n / (a : ℝ) := by
    simpa [Measure.real, realMean, ENNReal.toReal_div] using hmarkReal
  have hmean :=
    p_rec_01_mean_bound P ℱ R κ η hκ hR hcond h0 n
  exact hbase.trans (div_le_div_of_nonneg_right hmean (by exact_mod_cast ha.le))

end UEOT.V3.RecoveryProbability
