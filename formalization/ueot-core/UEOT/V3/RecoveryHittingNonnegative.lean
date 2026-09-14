import UEOT.V3.RecoveryHitting
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# P-REC-04 — nonnegative hitting-time model

The source theorem assumes only a nonnegative Lyapunov potential.  This layer
therefore represents the potential and recovery-time expectation in `ℝ≥0∞`,
following the same nonnegative-expectation discipline already used by
`UEOT.V3.RecoveryProbability`.

A path survives through time `n` when none of its coordinates `0,...,n` lies in
the target set.  The truncated hitting time is the finite sum of those survival
indicators, and the full hitting time is their monotone supremum.  Thus a hit
at time `k` has value `k`, while a path that never hits has value `∞`.
-/

namespace UEOT.V3.RecoveryHittingNonnegative

open Finset Function MeasurableSpace MeasureTheory Preorder ProbabilityTheory Set
open UEOT.V3.DynamicsKernel
open scoped ENNReal ProbabilityTheory

universe uX

variable {X : Type uX} [MeasurableSpace X]

/-- Finite histories that have not entered the target set through time `n`. -/
def historySurvivalSet (A : Set X) (n : ℕ) :
    Set ((i : Iic n) → X) :=
  ⋂ i : Iic n, (fun h => h i) ⁻¹' Aᶜ

@[simp]
theorem mem_historySurvivalSet_iff
    (A : Set X) (n : ℕ) (h : (i : Iic n) → X) :
    h ∈ historySurvivalSet A n ↔ ∀ i : Iic n, h i ∉ A := by
  simp [historySurvivalSet]

theorem measurableSet_historySurvivalSet
    {A : Set X} (hA : MeasurableSet A) (n : ℕ) :
    MeasurableSet (historySurvivalSet A n) := by
  unfold historySurvivalSet
  exact MeasurableSet.iInter fun i =>
    hA.compl.preimage (measurable_pi_apply i)

/-- Full paths that have not entered `A` through time `n`. -/
def survivalSet (A : Set X) (n : ℕ) : Set (ℕ → X) :=
  frestrictLe n ⁻¹' historySurvivalSet A n

@[simp]
theorem mem_survivalSet_iff
    (A : Set X) (n : ℕ) (ω : ℕ → X) :
    ω ∈ survivalSet A n ↔ ∀ k ≤ n, ω k ∉ A := by
  constructor
  · intro h k hk
    have hp : frestrictLe n ω ∈ historySurvivalSet A n := h
    exact (mem_historySurvivalSet_iff A n _).1 hp
      ⟨k, mem_Iic.mpr hk⟩
  · intro h
    apply (mem_historySurvivalSet_iff A n _).2
    intro i
    simpa [frestrictLe_apply] using h i.1 (mem_Iic.mp i.2)

theorem measurableSet_survivalSet
    {A : Set X} (hA : MeasurableSet A) (n : ℕ) :
    MeasurableSet (survivalSet A n) := by
  exact (measurableSet_historySurvivalSet hA n).preimage
    (measurable_frestrictLe n)

/-- The source Lyapunov potential restricted to histories that have survived
through time `n`; it vanishes once the target has already been hit. -/
def historySurvivalPotential
    (A : Set X) (V : X → ℝ≥0∞) (n : ℕ)
    (h : (i : Iic n) → X) : ℝ≥0∞ :=
  (historySurvivalSet A n).indicator
    (fun h => V (h (lastHistoryIndex n))) h

theorem measurable_historySurvivalPotential
    {A : Set X} (hA : MeasurableSet A)
    {V : X → ℝ≥0∞} (hV : Measurable V) (n : ℕ) :
    Measurable (historySurvivalPotential A V n) := by
  exact (hV.comp (measurable_pi_apply (lastHistoryIndex n))).indicator
    (measurableSet_historySurvivalSet hA n)

/-- Prefix law at time `n` for the homogeneous Markov chain started from `x`. -/
noncomputable def prefixLaw
    (P : Kernel X X) [IsMarkovKernel P] (x : X) (n : ℕ) :
    Measure ((i : Iic n) → X) :=
  (homTrajMeasure (Measure.dirac x) P).map (frestrictLe n)

instance isProbabilityMeasure_prefixLaw
    (P : Kernel X X) [IsMarkovKernel P] (x : X) (n : ℕ) :
    IsProbabilityMeasure (prefixLaw P x n) := by
  unfold prefixLaw
  infer_instance

/-- Probability that the chain has not yet hit `A` by time `n`. -/
noncomputable def survivalProb
    (P : Kernel X X) [IsMarkovKernel P]
    (x : X) (A : Set X) (n : ℕ) : ℝ≥0∞ :=
  prefixLaw P x n (historySurvivalSet A n)

/-- Tail-sum expectation of the hitting time truncated at `N`. -/
noncomputable def truncatedExpectedHittingTime
    (P : Kernel X X) [IsMarkovKernel P]
    (x : X) (A : Set X) (N : ℕ) : ℝ≥0∞ :=
  ∑ n ∈ range N, survivalProb P x A n

/-- Pointwise truncated hitting time: the number of survival instants among
`0,...,N-1`.  This is exactly `τ_A ∧ N` for discrete time. -/
def truncatedHittingValue
    (A : Set X) (N : ℕ) (ω : ℕ → X) : ℝ≥0∞ :=
  ∑ n ∈ range N,
    (survivalSet A n).indicator (fun _ => (1 : ℝ≥0∞)) ω

theorem measurable_truncatedHittingValue
    {A : Set X} (hA : MeasurableSet A) (N : ℕ) :
    Measurable (truncatedHittingValue A N) := by
  unfold truncatedHittingValue
  fun_prop

/-- Extended hitting time obtained as the monotone limit of the source
truncations.  It is finite and equal to the first hit index when a hit occurs,
and is `∞` on paths that never hit. -/
noncomputable def hittingValue
    (A : Set X) (ω : ℕ → X) : ℝ≥0∞ :=
  ⨆ N : ℕ, truncatedHittingValue A N ω

/-- Literal nonnegative expectation of the recovery time under the Markov path
law.  The source-facing theorem will bound this quantity. -/
noncomputable def expectedHittingTime
    (P : Kernel X X) [IsMarkovKernel P]
    (x : X) (A : Set X) : ℝ≥0∞ :=
  ∫⁻ ω, hittingValue A ω ∂homTrajMeasure (Measure.dirac x) P

end UEOT.V3.RecoveryHittingNonnegative
