import UEOT.V3.RecoveryHittingRestart

/-!
# P-REC-03 — canonical recovery potential and Poisson equation

The frozen Core 3 source defines `V_A(x) = E_x τ_A` and proves, for `x ∉ A`
and finite `V_A(x)`, the first-step identity

`V_A(x) = 1 + E_x[V_A(X_1)]`

and hence `P V_A(x) - V_A(x) = -1`.

This file derives that identity from the canonical homogeneous Markov path law;
it does not assume the Poisson equation or a restart axiom.
-/

namespace UEOT.V3.RecoveryHittingPoisson

open Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder ProbabilityTheory
open UEOT.V3.DynamicsKernel
open UEOT.V3.RecoveryHitting
open UEOT.V3.RecoveryHittingNonnegative
open UEOT.V3.RecoveryHittingFirstStep
open UEOT.V3.RecoveryHittingInitial
open UEOT.V3.RecoveryHittingRestart
open scoped ENNReal ProbabilityTheory

universe uX

variable {X : Type uX} [MeasurableSpace X]

/-- Composing a kernel with a Dirac initial law evaluates the kernel at that
state. -/
theorem kernel_comp_dirac
    (P : Kernel X X) (x : X) :
    P ∘ₘ Measure.dirac x = P x := by
  exact Measure.dirac_bind (Kernel.measurable P) x

/-- Replacing only coordinate zero by `x` leaves the one-step-shifted path
unchanged. -/
theorem pathShift_update_initial
    (x : X) (ω : ℕ → X) :
    pathShift
        (updateFinset ω (Iic 0) (fun _ : Iic 0 => x)) =
      pathShift ω := by
  funext n
  simp [pathShift, updateFinset]

/-- Replacing coordinate zero by `x` really fixes the initial state to `x`. -/
theorem update_initial_zero
    (x : X) (ω : ℕ → X) :
    updateFinset ω (Iic 0) (fun _ : Iic 0 => x) 0 = x := by
  simp [updateFinset]

/-- **Canonical first-step identity in `ℝ≥0∞`.**  If the initial state lies
outside the target set, the canonical expected hitting time is one plus the
one-step expectation of the same canonical potential.

No finiteness assumption is required at this stage. -/
theorem expectedHittingTime_first_step_ennreal
    (P : Kernel X X) [IsMarkovKernel P]
    (x : X) (A : Set X) (hA : MeasurableSet A)
    (hx : x ∉ A) :
    expectedHittingTime P x A =
      1 + ∫⁻ y, expectedHittingTime P y A ∂P x := by
  letI : ∀ n, IsMarkovKernel (homHistoryKernel P n) :=
    fun n => isMarkovKernel_homHistoryKernel P n
  have hf : Measurable (hittingValue A) :=
    measurable_hittingValue hA
  unfold expectedHittingTime
  rw [homTrajMeasure_dirac_eq_markovPathLaw P x]
  unfold markovPathLaw
  change
    (∫⁻ ω, hittingValue A ω
      ∂Kernel.traj (X := fun _ : ℕ => X)
        (homHistoryKernel P) 0 (fun _ : Iic 0 => x)) = _
  rw [Kernel.lintegral_traj
    (κ := homHistoryKernel P) (fun _ : Iic 0 => x) hf]
  have hpoint : ∀ ω : ℕ → X,
      hittingValue A
          (updateFinset ω (Iic 0) (fun _ : Iic 0 => x)) =
        1 + hittingValue A (pathShift ω) := by
    intro ω
    have h0 :
        updateFinset ω (Iic 0) (fun _ : Iic 0 => x) 0 ∉ A := by
      rw [update_initial_zero x ω]
      exact hx
    calc
      hittingValue A
          (updateFinset ω (Iic 0) (fun _ : Iic 0 => x)) =
          1 + hittingValue A
            (pathShift
              (updateFinset ω (Iic 0) (fun _ : Iic 0 => x))) :=
        hittingValue_eq_one_add_shift A _ h0
      _ = 1 + hittingValue A (pathShift ω) := by
        rw [pathShift_update_initial x ω]
  simp_rw [hpoint]
  rw [lintegral_add_left measurable_const]
  simp only [lintegral_const, measure_univ, one_mul]
  have hmap :
      (∫⁻ ω, hittingValue A (pathShift ω)
        ∂Kernel.traj (X := fun _ : ℕ => X)
          (homHistoryKernel P) 0 (fun _ : Iic 0 => x)) =
      ∫⁻ ω, hittingValue A ω
        ∂(Kernel.traj (X := fun _ : ℕ => X)
          (homHistoryKernel P) 0 (fun _ : Iic 0 => x)).map pathShift := by
    symm
    exact lintegral_map hf measurable_pathShift
  rw [hmap]
  change
    1 + (∫⁻ ω, hittingValue A ω ∂(markovPathLaw P x).map pathShift) = _
  rw [← homTrajMeasure_dirac_eq_markovPathLaw P x,
    homTrajMeasure_shift (Measure.dirac x) P,
    kernel_comp_dirac P x,
    lintegral_hittingValue_homTrajMeasure_eq P (P x) hA]

/-- Finiteness of the canonical potential at `x` forces the one-step
expectation of the canonical potential to be finite as well.  This is the
integrability content used by the frozen source after first-step analysis. -/
theorem first_step_lintegral_ne_top
    (P : Kernel X X) [IsMarkovKernel P]
    (x : X) (A : Set X) (hA : MeasurableSet A)
    (hx : x ∉ A)
    (hfinite : expectedHittingTime P x A ≠ ∞) :
    (∫⁻ y, expectedHittingTime P y A ∂P x) ≠ ∞ := by
  intro htop
  apply hfinite
  rw [expectedHittingTime_first_step_ennreal P x A hA hx, htop]
  simp

/-- **P-REC-03 (canonical recovery-potential Poisson equation).**
For `x ∉ A`, if the canonical hitting-time potential is finite, then the
finite one-step expectation satisfies the literal real-valued source equation

`P V_A(x) - V_A(x) = -1`.

The kernel action is represented canonically as the `toReal` of the finite
nonnegative integral. -/
theorem p_rec_03
    (P : Kernel X X) [IsMarkovKernel P]
    (x : X) (A : Set X) (hA : MeasurableSet A)
    (hx : x ∉ A)
    (hfinite : expectedHittingTime P x A ≠ ∞) :
    (∫⁻ y, expectedHittingTime P y A ∂P x).toReal -
        (expectedHittingTime P x A).toReal = -1 := by
  have hstep := expectedHittingTime_first_step_ennreal P x A hA hx
  have hint : (∫⁻ y, expectedHittingTime P y A ∂P x) ≠ ∞ :=
    first_step_lintegral_ne_top P x A hA hx hfinite
  have hreal := congrArg ENNReal.toReal hstep
  rw [ENNReal.toReal_add (by simp) hint] at hreal
  norm_num at hreal ⊢
  linarith

end UEOT.V3.RecoveryHittingPoisson
