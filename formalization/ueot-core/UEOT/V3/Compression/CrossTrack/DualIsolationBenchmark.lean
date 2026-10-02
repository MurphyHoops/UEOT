import UEOT.V3.Compression.CrossTrack.DualIsolationCanonical
import UEOT.V3.Compression.CrossTrack.ParentSemanticNoGo

/-!
# Dual Isolation — explicit finite sharp benchmark

This benchmark makes every constant in the dual-isolation chain explicit.
Two parent completions are represented by the two points `0` and `1`, the
diagnostic is that coordinate itself, and the parent dynamics are the Track-X
reset kernels.  The canonical binding conorm, parent-realization Lipschitz
constant, and semantic residual conorm are all exactly `1`.

At the midpoint observation with radius `1/2`, the dual-isolation upper bound
is exactly `1`, and the actual invariant-law TV distance is also exactly `1`.
-/

namespace UEOT.V3.Compression.CrossTrack

open UEOT.V3
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.TopologyChangingGoaL1ResidualConorm

noncomputable section

/-- Two-point assembly coordinate. -/
noncomputable def dualIsolationBenchmarkCoord : Bool → ℝ :=
  fun p => if p then 1 else 0

theorem dualIsolationBenchmarkCoord_injective :
    Function.Injective dualIsolationBenchmarkCoord := by
  intro p q h
  cases p <;> cases q <;>
    simp [dualIsolationBenchmarkCoord] at h ⊢

/-- The assembly metric is exactly the metric induced by the physical
coordinate `0/1`. -/
noncomputable local instance dualIsolationBenchmarkMetric : MetricSpace Bool :=
  MetricSpace.induced dualIsolationBenchmarkCoord
    dualIsolationBenchmarkCoord_injective inferInstance

/-- The benchmark diagnostic has unit lower gain. -/
theorem dualIsolationBenchmark_bindingIsolation_one :
    BindingIsolation dualIsolationBenchmarkCoord 1 := by
  constructor
  · norm_num
  · intro a b
    change 1 * dist (dualIsolationBenchmarkCoord a)
        (dualIsolationBenchmarkCoord b) ≤
      dist (dualIsolationBenchmarkCoord a) (dualIsolationBenchmarkCoord b)
    simp

/-- The canonical finite binding-isolation conorm is exactly one. -/
theorem dualIsolationBenchmark_bindingConorm_eq_one :
    bindingIsolationConorm dualIsolationBenchmarkCoord = 1 := by
  apply le_antisymm
  · have h := bindingIsolationConorm_le_pairGain
      dualIsolationBenchmarkCoord (show false ≠ true by simp)
    change bindingIsolationConorm dualIsolationBenchmarkCoord ≤
      dist (dualIsolationBenchmarkCoord false)
          (dualIsolationBenchmarkCoord true) /
        dist (dualIsolationBenchmarkCoord false)
          (dualIsolationBenchmarkCoord true) at h
    norm_num [dualIsolationBenchmarkCoord, Real.dist_eq] at h ⊢
    exact h
  · exact bindingIsolation_le_bindingIsolationConorm
      dualIsolationBenchmarkCoord 1
      dualIsolationBenchmark_bindingIsolation_one

/-- The reset-kernel realization is row-TV 1-Lipschitz with respect to the
two-point assembly metric. -/
noncomputable def dualIsolationBenchmarkBinding :
    ParentBindingLipschitz
      (fun p : Bool => p) x1Kernel x1Kernel_stochastic where
  L := 1
  L_nonneg := by norm_num
  row_lipschitz := by
    intro p q x
    cases p <;> cases q
    · unfold crossRowTV
      have h := UEOT.V3.TotalVariation.tvDist_self_eq_zero
        (rowPMF (x1Kernel false) (x1Kernel_stochastic false) x).toMeasure
      change UEOT.V3.TotalVariation.tvDist
          (rowPMF (x1Kernel false) (x1Kernel_stochastic false) x).toMeasure
          (rowPMF (x1Kernel false) (x1Kernel_stochastic false) x).toMeasure
          ≤ 1 * dist false false
      simpa using h.le
    · unfold crossRowTV
        UEOT.V3.FiniteDiscountedControl.FiniteProbabilityRow.tvDist
      have h := UEOT.V3.TotalVariation.tvDist_le_one
        (rowPMF (x1Kernel false) (x1Kernel_stochastic false) x).toMeasure
        (rowPMF (x1Kernel true) (x1Kernel_stochastic true) x).toMeasure
      change _ ≤ 1 * dist
        (dualIsolationBenchmarkCoord false) (dualIsolationBenchmarkCoord true)
      norm_num [dualIsolationBenchmarkCoord, Real.dist_eq]
      exact h
    · unfold crossRowTV
        UEOT.V3.FiniteDiscountedControl.FiniteProbabilityRow.tvDist
      have h := UEOT.V3.TotalVariation.tvDist_le_one
        (rowPMF (x1Kernel true) (x1Kernel_stochastic true) x).toMeasure
        (rowPMF (x1Kernel false) (x1Kernel_stochastic false) x).toMeasure
      change _ ≤ 1 * dist
        (dualIsolationBenchmarkCoord true) (dualIsolationBenchmarkCoord false)
      norm_num [dualIsolationBenchmarkCoord, Real.dist_eq]
      exact h
    · unfold crossRowTV
      have h := UEOT.V3.TotalVariation.tvDist_self_eq_zero
        (rowPMF (x1Kernel true) (x1Kernel_stochastic true) x).toMeasure
      change UEOT.V3.TotalVariation.tvDist
          (rowPMF (x1Kernel true) (x1Kernel_stochastic true) x).toMeasure
          (rowPMF (x1Kernel true) (x1Kernel_stochastic true) x).toMeasure
          ≤ 1 * dist true true
      simpa using h.le

@[simp] theorem dualIsolationBenchmarkBinding_L :
    dualIsolationBenchmarkBinding.L = 1 := rfl

/-- Both parent completions are exactly at diagnostic radius `1/2` from the
midpoint observation. -/
theorem dualIsolationBenchmark_midpoint_errors :
    dist (dualIsolationBenchmarkCoord false) (1 / 2 : ℝ) = 1 / 2 ∧
      dist (dualIsolationBenchmarkCoord true) (1 / 2 : ℝ) = 1 / 2 := by
  norm_num [dualIsolationBenchmarkCoord, Real.dist_eq, abs_of_nonneg,
    abs_of_nonpos]

/-- The dual-isolation theorem returns the exact sharp unit semantic bound on
the benchmark. -/
theorem dualIsolationBenchmark_bound_sharp :
    lawTV (x1Invariant false) (x1Invariant true) ≤ 1 ∧
      lawTV (x1Invariant false) (x1Invariant true) = 1 ∧
      bindingIsolationConorm dualIsolationBenchmarkCoord = 1 ∧
      (∀ p : Bool, l1ResidualConorm (x1Kernel p) = 1) := by
  have hbound := dualIsolation_pairwiseSemanticBound
    (P := Bool) (repr := fun p : Bool => p)
    dualIsolationBenchmarkCoord 1 (1 / 2 : ℝ)
    dualIsolationBenchmark_bindingIsolation_one (by norm_num)
    (1 / 2 : ℝ)
    x1Kernel x1Kernel_stochastic dualIsolationBenchmarkBinding
    x1Invariant x1Invariant_mem
    1 (by norm_num) (by norm_num)
    (p := false) (q := true)
    (by rw [dualIsolationBenchmark_midpoint_errors.1])
    (by rw [dualIsolationBenchmark_midpoint_errors.2])
    (by rw [x1Kernel_l1ResidualConorm_eq_one])
  have hunit :
      dualIsolationBenchmarkBinding.L * ((2 : ℝ) * (1 / 2) / 1) / 1 = 1 := by
    norm_num
  rw [hunit] at hbound
  exact ⟨hbound, x1Invariant_distance,
    dualIsolationBenchmark_bindingConorm_eq_one,
    x1Kernel_l1ResidualConorm_eq_one⟩

end

end UEOT.V3.Compression.CrossTrack
