import UEOT.V3.Compression.CrossTrack.DualIsolationPMetRealization
import UEOT.V3.Compression.CrossTrack.DualIsolationBenchmark
import UEOT.V3.InformationPacking

/-!
# Dual Isolation — P-MET realization benchmark

This module re-runs the sharp two-completion Dual-Isolation benchmark through
an actual P-MET-01 common-channel realization.

The assembly-level laws are the two invariant point masses, and every parent
row is obtained from the corresponding assembly law by the identity Markov
kernel.  Hence the benchmark's forward constant `L = 1` is now derived from
data processing rather than supplied manually.
-/

namespace UEOT.V3.Compression.CrossTrack

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
open UEOT.V3
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.TopologyChangingGoaFunctionalGraphClassification
open UEOT.V3.Compression.TopologyChangingGoaL1ResidualConorm

noncomputable section

noncomputable local instance dualIsolationPMetBenchmarkDecidableEq :
    DecidableEq Bool := Classical.decEq Bool
local instance dualIsolationPMetBenchmarkMeasurableSpace : MeasurableSpace Bool := ⊤
noncomputable local instance dualIsolationPMetBenchmarkMetric : MetricSpace Bool :=
  MetricSpace.induced dualIsolationBenchmarkCoord
    dualIsolationBenchmarkCoord_injective inferInstance

/-- Assembly-level law for the sharp benchmark. -/
noncomputable def dualIsolationPMetBenchmarkBaseLaw (p : Bool) : Measure Bool :=
  (simplexPMF (x1Invariant p)).toMeasure

theorem dualIsolationPMetBenchmarkBaseLaw_probability (p : Bool) :
    IsProbabilityMeasure (dualIsolationPMetBenchmarkBaseLaw p) := by
  unfold dualIsolationPMetBenchmarkBaseLaw
  infer_instance

/-- Every row of the reset kernel is exactly the matching assembly-level point
mass. -/
theorem dualIsolationPMetBenchmark_row_eq_baseLaw (p x : Bool) :
    (rowPMF (x1Kernel p) (x1Kernel_stochastic p) x).toMeasure =
      dualIsolationPMetBenchmarkBaseLaw p := by
  congr 1
  apply PMF.ext
  intro y
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  by_cases h : y = p
  · subst y
    simp [rowPMF_toReal, simplexPMF_toReal, x1Invariant, x1Kernel, detKernel,
      pureSimplex, Pi.single]
  · simp [rowPMF_toReal, simplexPMF_toReal, x1Invariant, x1Kernel, detKernel,
      pureSimplex, Pi.single, h]

/-- The induced assembly metric dominates (in fact equals on the nontrivial
pair) the TV distance of the benchmark assembly laws. -/
theorem dualIsolationPMetBenchmark_baseTV_le_dist (p q : Bool) :
    UEOT.V3.TotalVariation.tvDist
        (dualIsolationPMetBenchmarkBaseLaw p)
        (dualIsolationPMetBenchmarkBaseLaw q) ≤
      dist p q := by
  cases p <;> cases q
  · let _ : IsProbabilityMeasure (dualIsolationPMetBenchmarkBaseLaw false) :=
      dualIsolationPMetBenchmarkBaseLaw_probability false
    have h := UEOT.V3.TotalVariation.tvDist_self_eq_zero
      (dualIsolationPMetBenchmarkBaseLaw false)
    simpa using h.le
  · let _ : IsProbabilityMeasure (dualIsolationPMetBenchmarkBaseLaw false) :=
      dualIsolationPMetBenchmarkBaseLaw_probability false
    let _ : IsProbabilityMeasure (dualIsolationPMetBenchmarkBaseLaw true) :=
      dualIsolationPMetBenchmarkBaseLaw_probability true
    change lawTV (x1Invariant false) (x1Invariant true) ≤ _
    rw [x1Invariant_distance]
    change (1 : ℝ) ≤ dist
      (dualIsolationBenchmarkCoord false) (dualIsolationBenchmarkCoord true)
    norm_num [dualIsolationBenchmarkCoord, Real.dist_eq]
  · let _ : IsProbabilityMeasure (dualIsolationPMetBenchmarkBaseLaw true) :=
      dualIsolationPMetBenchmarkBaseLaw_probability true
    let _ : IsProbabilityMeasure (dualIsolationPMetBenchmarkBaseLaw false) :=
      dualIsolationPMetBenchmarkBaseLaw_probability false
    have hsym := UEOT.V3.InformationPacking.tvDist_symm
      (dualIsolationPMetBenchmarkBaseLaw true)
      (dualIsolationPMetBenchmarkBaseLaw false)
    have hft : UEOT.V3.TotalVariation.tvDist
        (dualIsolationPMetBenchmarkBaseLaw false)
        (dualIsolationPMetBenchmarkBaseLaw true) = 1 := by
      change lawTV (x1Invariant false) (x1Invariant true) = 1
      exact x1Invariant_distance
    rw [hsym, hft]
    change (1 : ℝ) ≤ dist
      (dualIsolationBenchmarkCoord true) (dualIsolationBenchmarkCoord false)
    norm_num [dualIsolationBenchmarkCoord, Real.dist_eq]
  · let _ : IsProbabilityMeasure (dualIsolationPMetBenchmarkBaseLaw true) :=
      dualIsolationPMetBenchmarkBaseLaw_probability true
    have h := UEOT.V3.TotalVariation.tvDist_self_eq_zero
      (dualIsolationPMetBenchmarkBaseLaw true)
    simpa using h.le

/-- The sharp benchmark is a genuine common-Markov parent realization, with
the identity Markov kernel as realization channel. -/
noncomputable def dualIsolationPMetBenchmarkRealization :
    CommonMarkovParentRealization Bool
      (fun p : Bool => p) x1Kernel x1Kernel_stochastic where
  baseLaw := dualIsolationPMetBenchmarkBaseLaw
  base_probability := dualIsolationPMetBenchmarkBaseLaw_probability
  metric_tv_le := dualIsolationPMetBenchmark_baseTV_le_dist
  channel := fun _ => Kernel.id
  channel_markov := fun _ => inferInstance
  row_realization := by
    intro p x
    rw [Measure.id_comp]
    exact dualIsolationPMetBenchmark_row_eq_baseLaw p x

/-- P-MET-01 derives the benchmark Parent-Binding constant exactly as one. -/
theorem dualIsolationPMetBenchmark_parentBinding_L_eq_one :
    (dualIsolationPMetBenchmarkRealization.toParentBinding
      (fun p : Bool => p) x1Kernel x1Kernel_stochastic).L = 1 := by
  simp

/-- **Mechanism-level sharpness.**

The same benchmark whose actual long-run semantic TV is one satisfies the
P-MET-derived pairwise Dual-Isolation upper bound with value exactly one. -/
theorem dualIsolationPMetBenchmark_pairwise_bound_sharp :
    lawTV (x1Invariant false) (x1Invariant true) = 1 ∧
    lawTV (x1Invariant false) (x1Invariant true) ≤ 1 ∧
    (dualIsolationPMetBenchmarkRealization.toParentBinding
      (fun p : Bool => p) x1Kernel x1Kernel_stochastic).L = 1 := by
  have hbound := dualIsolation_commonMarkov_pairwiseSemanticBound
    (X := Bool) (P := Bool) (A := Bool)
    (repr := fun p : Bool => p)
    dualIsolationBenchmarkCoord 1 (1 / 2 : ℝ)
    dualIsolationBenchmark_bindingIsolation_one (by norm_num)
    (1 / 2 : ℝ)
    x1Kernel x1Kernel_stochastic dualIsolationPMetBenchmarkRealization
    x1Invariant x1Invariant_mem
    1 (by norm_num) (by norm_num)
    (p := false) (q := true)
    (by rw [dualIsolationBenchmark_midpoint_errors.1])
    (by rw [dualIsolationBenchmark_midpoint_errors.2])
    (by rw [x1Kernel_l1ResidualConorm_eq_one])
  norm_num at hbound
  exact ⟨x1Invariant_distance, hbound,
    dualIsolationPMetBenchmark_parentBinding_L_eq_one⟩

end

end UEOT.V3.Compression.CrossTrack
