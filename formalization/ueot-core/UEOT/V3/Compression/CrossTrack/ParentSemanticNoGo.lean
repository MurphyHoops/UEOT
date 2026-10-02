import UEOT.V3.Compression.CrossTrack.ParentSemanticCore

/-!
# Track X — X1 cross-track no-go

Unique long-run semantics for every parent completion does not make that
semantics child-determined.
-/

namespace UEOT.V3.Compression.CrossTrack

open UEOT.V3
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.InvariantSetGaugeInvariance
open UEOT.V3.Compression.TopologyChangingGoaL1ResidualConorm
open UEOT.V3.Compression.TopologyChangingGoaL1ResetFamily
open UEOT.V3.Compression.TopologyChangingGoaFunctionalGraphClassification
open UEOT.V3.Compression.TopologyChangingGoaTrackSClosure

noncomputable section
noncomputable local instance x1BoolDecidableEq : DecidableEq Bool :=
  Classical.decEq Bool

/-- Both richer parent completions expose exactly the same child evidence. -/
def x1ChildProjection : Bool → Unit := fun _ => ()

/-- Completion `p` induces deterministic reset-to-`p` dynamics. -/
def x1Kernel (p : Bool) : Matrix Bool Bool ℝ :=
  detKernel (fun _ => p)

theorem x1Kernel_stochastic (p : Bool) :
    x1Kernel p ∈ Matrix.rowStochastic ℝ Bool := by
  exact detKernel_stochastic (fun _ => p)

/-- The stationary semantics of completion `p` is its matching point mass. -/
def x1Invariant (p : Bool) : stdSimplex ℝ Bool :=
  pureSimplex p

theorem x1Invariant_mem (p : Bool) :
    x1Invariant p ∈ invariantLawSet (x1Kernel p) (x1Kernel_stochastic p) := by
  rw [mem_invariantLawSet]
  apply Subtype.ext
  funext j
  rw [step_apply, Fintype.sum_bool]
  cases p <;> cases j <;>
    simp [x1Invariant, x1Kernel, detKernel, pureSimplex, Pi.single]

theorem x1Kernel_eq_constantRowMatrix (p : Bool) :
    x1Kernel p =
      constantRowMatrix (fun j : Bool => if j = p then 1 else 0) := by
  funext i j
  simp [x1Kernel, detKernel, constantRowMatrix]

theorem x1Kernel_l1ResidualConorm_eq_one (p : Bool) :
    l1ResidualConorm (x1Kernel p) = 1 := by
  rw [x1Kernel_eq_constantRowMatrix p]
  apply constantRowMatrix_l1ResidualConorm_eq_one
  norm_num

theorem x1Kernel_uniqueInvariant (p : Bool) :
    ∃! mu : stdSimplex ℝ Bool,
      mu ∈ invariantLawSet (x1Kernel p) (x1Kernel_stochastic p) := by
  apply
    (finite_markov_isolation_iff_unique_semantics
      (x1Kernel p) (x1Kernel_stochastic p) (by norm_num)).1
  rw [x1Kernel_l1ResidualConorm_eq_one]
  norm_num

theorem x1Invariant_distance :
    lawTV (x1Invariant false) (x1Invariant true) = 1 := by
  unfold lawTV UEOT.V3.FiniteDiscountedControl.FiniteProbabilityRow.tvDist
  rw [UEOT.V3.FiniteRecurrentDecompositionStability.pmf_tv_eq_half_sum_abs]
  simp_rw [simplexPMF_toReal]
  rw [Fintype.sum_bool]
  simp [x1Invariant, pureSimplex, Pi.single]
  norm_num

/-- **X1 — cross-track no-go.**

The two distinct parent completions have identical child evidence.  Each
completion separately has positive canonical residual isolation and a unique
invariant law, yet their long-run semantics are maximally separated in total
variation.

This is a G3 boundary theorem: assembly ambiguity survives dynamical
uniqueness. -/
theorem x1_uniquePerCompletion_not_childDetermined :
    x1ChildProjection false = x1ChildProjection true ∧
    (false : Bool) ≠ true ∧
    (∀ p : Bool, 0 < l1ResidualConorm (x1Kernel p)) ∧
    (∀ p : Bool, ∃! mu : stdSimplex ℝ Bool,
      mu ∈ invariantLawSet (x1Kernel p) (x1Kernel_stochastic p)) ∧
    x1Invariant false ∈
      invariantLawSet (x1Kernel false) (x1Kernel_stochastic false) ∧
    x1Invariant true ∈
      invariantLawSet (x1Kernel true) (x1Kernel_stochastic true) ∧
    lawTV (x1Invariant false) (x1Invariant true) = 1 := by
  refine
    ⟨rfl, by simp, ?_, x1Kernel_uniqueInvariant,
      x1Invariant_mem false, x1Invariant_mem true, x1Invariant_distance⟩
  intro p
  rw [x1Kernel_l1ResidualConorm_eq_one]
  norm_num

end

end UEOT.V3.Compression.CrossTrack
