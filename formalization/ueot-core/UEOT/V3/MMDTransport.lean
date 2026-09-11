import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# P-STAT-07 — kernel transport covariance of MMD

The frozen source transports a kernel synchronously with a bimeasurable
bijection and states exact covariance of MMD.  This module formalizes the
kernel-expectation representation directly: each of the three expectations in
MMD squared is invariant under the common measurable equivalence.
-/

namespace UEOT.V3.MMDTransport

open MeasureTheory Real

universe uX uX'

variable {X : Type uX} {X' : Type uX'}
variable [MeasurableSpace X] [MeasurableSpace X']

/-- Mixed kernel expectation `E[k(X,Y)]` under laws `P` and `Q`. -/
noncomputable def kernelExpectation
    (k : X → X → ℝ) (P Q : Measure X) : ℝ :=
  ∫ x, ∫ y, k x y ∂Q ∂P

/-- Synchronous transport of a kernel through a bimeasurable bijection. -/
def transportedKernel (e : X ≃ᵐ X') (k : X → X → ℝ) : X' → X' → ℝ :=
  fun x' y' => k (e.symm x') (e.symm y')

/-- One mixed kernel expectation is exactly invariant under synchronous
transport of both laws and the kernel. -/
theorem kernelExpectation_map_equiv
    (e : X ≃ᵐ X') (k : X → X → ℝ) (P Q : Measure X) :
    kernelExpectation (transportedKernel e k) (P.map e) (Q.map e) =
      kernelExpectation k P Q := by
  unfold kernelExpectation
  rw [MeasureTheory.integral_map_equiv (μ := P) e]
  apply integral_congr_ae
  filter_upwards with x
  simpa [transportedKernel] using
    (MeasureTheory.integral_map_equiv (μ := Q) e
      (fun y' => transportedKernel e k (e x) y'))

/-- Standard three-expectation expression for MMD squared. -/
noncomputable def mmdSq
    (k : X → X → ℝ) (P Q : Measure X) : ℝ :=
  kernelExpectation k P P + kernelExpectation k Q Q -
    2 * kernelExpectation k P Q

/-- MMD represented as the nonnegative square root of the standard kernel
energy.  For positive-definite kernels with the usual integrability hypotheses,
this is the RKHS mean-embedding distance. -/
noncomputable def mmd
    (k : X → X → ℝ) (P Q : Measure X) : ℝ :=
  sqrt (mmdSq k P Q)

/-- The three-expectation MMD square is representation-covariant. -/
theorem mmdSq_map_equiv
    (e : X ≃ᵐ X') (k : X → X → ℝ) (P Q : Measure X) :
    mmdSq (transportedKernel e k) (P.map e) (Q.map e) =
      mmdSq k P Q := by
  simp [mmdSq, kernelExpectation_map_equiv]

/-- **P-STAT-07: kernel-transport covariance.**  Under a bimeasurable
bijection `e`, synchronously transporting the kernel and both probability laws
leaves MMD unchanged. -/
theorem p_stat_07
    (e : X ≃ᵐ X') (k : X → X → ℝ) (P Q : Measure X) :
    mmd (transportedKernel e k) (P.map e) (Q.map e) =
      mmd k P Q := by
  simp [mmd, mmdSq_map_equiv]

end UEOT.V3.MMDTransport
