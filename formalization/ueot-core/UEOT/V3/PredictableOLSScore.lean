import UEOT.V3.PredictableOLSRadius
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic

/-!
# P-INV-05 — predictable score accumulation

This module moves the probability interface one layer closer to the frozen
source statement.  Instead of assuming directly that the final coordinate
score is sub-Gaussian, it uses Mathlib's conditional sub-Gaussian martingale
accumulation theorem to derive the final score law from one-step conditional
sub-Gaussian score increments.

The remaining source-specific bridge is intentionally isolated: prove that a
predictable bounded multiplier `phi_tj` times conditionally `sigma^2`-sub-
Gaussian noise `xi_t` is conditionally `(sigma * B)^2`-sub-Gaussian.
-/

namespace UEOT.V3.PredictableOLSScore

open MeasureTheory ProbabilityTheory
open UEOT.V3.PredictableOLSRadius
open scoped BigOperators NNReal

universe uΩ

variable {Ω : Type uΩ} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- One coordinate of the predictable-design OLS score process. -/
def scoreProcess {d : ℕ}
    (phi : ℕ → Ω → Fin d → ℝ) (xi : ℕ → Ω → ℝ) (j : Fin d) :
    ℕ → Ω → ℝ :=
  fun t ω => phi t ω j * xi t ω

/-- Frozen one-step variance proxy after a bounded predictable multiplier. -/
def incrementParam (sigma B : ℝ) : ℝ≥0 :=
  ⟨(sigma * B) ^ 2, sq_nonneg (sigma * B)⟩

@[simp] theorem coe_incrementParam (sigma B : ℝ) :
    (incrementParam sigma B : ℝ) = (sigma * B) ^ 2 := rfl

/-- Summing `N` identical one-step proxies gives the frozen coordinate score
proxy `N * (sigma * B)^2`. -/
theorem sum_incrementParam_range (N : ℕ) (sigma B : ℝ) :
    (∑ _i ∈ Finset.range N, incrementParam sigma B) =
      scoreParam N sigma B := by
  rw [Finset.sum_const]
  simp [incrementParam, scoreParam, nsmul_eq_mul]

/-- Conditional sub-Gaussian score increments accumulate to the exact frozen
coordinate proxy `N * (sigma * B)^2`.

This theorem is the martingale-accumulation half of the source proof.  The
predictable-multiplier half is deliberately not hidden inside the assumptions:
its output appears explicitly as `h0` and `h_subG` and is the next bridge to
close from the source assumptions.
-/
theorem coordScore_hasSubgaussianMGF
    {d N : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (phi : ℕ → Ω → Fin d → ℝ)
    (xi : ℕ → Ω → ℝ)
    (j : Fin d)
    (sigma B : ℝ)
    (h_adapted : StronglyAdapted ℱ (scoreProcess phi xi j))
    (h0 : HasSubgaussianMGF
      (scoreProcess phi xi j 0) (incrementParam sigma B) μ)
    (h_subG : ∀ i < N - 1,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i)
        (scoreProcess phi xi j (i + 1)) (incrementParam sigma B) μ) :
    HasSubgaussianMGF
      (fun ω => ∑ t ∈ Finset.range N, phi t ω j * xi t ω)
      (scoreParam N sigma B) μ := by
  have hsum := HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF
    (μ := μ) (cY := fun _ => incrementParam sigma B)
    h_adapted h0 N h_subG
  rw [sum_incrementParam_range N sigma B] at hsum
  simpa [scoreProcess] using hsum

/-- Coordinatewise packaging of `coordScore_hasSubgaussianMGF`. -/
theorem allCoordScore_hasSubgaussianMGF
    {d N : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (phi : ℕ → Ω → Fin d → ℝ)
    (xi : ℕ → Ω → ℝ)
    (sigma B : ℝ)
    (h_adapted : ∀ j : Fin d, StronglyAdapted ℱ (scoreProcess phi xi j))
    (h0 : ∀ j : Fin d, HasSubgaussianMGF
      (scoreProcess phi xi j 0) (incrementParam sigma B) μ)
    (h_subG : ∀ j : Fin d, ∀ i < N - 1,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i)
        (scoreProcess phi xi j (i + 1)) (incrementParam sigma B) μ) :
    ∀ j : Fin d,
      HasSubgaussianMGF
        (fun ω => ∑ t ∈ Finset.range N, phi t ω j * xi t ω)
        (scoreParam N sigma B) μ := by
  intro j
  exact coordScore_hasSubgaussianMGF
    μ ℱ phi xi j sigma B (h_adapted j) (h0 j) (h_subG j)

end UEOT.V3.PredictableOLSScore
