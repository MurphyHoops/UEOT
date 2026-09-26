/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
Modified for UEOT Core v3 integration in 2026: module import paths only.
-/
import UEOT.V3.ThirdParty.CrooksJarzynski.ContinuousTimeJumpFiniteGeneratorFullPath

/-!
# Real-time trajectories of finite jump paths

A `JumpPath` stores physical holding times, so their partial sums are the
actual jump times.  This module interprets the chart as a right-continuous
step trajectory and records the validity properties carried almost surely by
the fixed-initial finite-generator path law.
-/

open MeasureTheory
open scoped BigOperators ENNReal unitInterval

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump

universe u

namespace JumpPath

variable {Ω : Type u}

/-- The physical start time of holding interval `k`. -/
def jumpTimes {n : ℕ} (γ : JumpPath Ω n) (k : Fin (n + 1)) : ℝ :=
  ∑ i ∈ Finset.Iio k, (γ.2 i : ℝ)

@[simp]
theorem jumpTimes_zero {n : ℕ} (γ : JumpPath Ω n) :
    jumpTimes γ 0 = 0 := by
  unfold jumpTimes
  apply Finset.sum_eq_zero
  intro i hi
  simp at hi

theorem jumpTimes_nonneg {n : ℕ} (γ : JumpPath Ω n)
    (k : Fin (n + 1)) : 0 ≤ jumpTimes γ k := by
  exact Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _

theorem jumpTimes_le_totalHoldingTime {n : ℕ} (γ : JumpPath Ω n)
    (k : Fin (n + 1)) : jumpTimes γ k ≤ γ.totalHoldingTime := by
  unfold jumpTimes totalHoldingTime
  rw [NNReal.coe_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun _ _ _ => NNReal.coe_nonneg _

theorem jumpTimes_mono {n : ℕ} (γ : JumpPath Ω n) :
    Monotone (jumpTimes γ) := by
  intro i j hij
  unfold jumpTimes
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Iio_subset_Iio hij) fun _ _ _ => NNReal.coe_nonneg _

theorem jumpTimes_strictMono_of_pos {n : ℕ} (γ : JumpPath Ω n)
    (hpos : ∀ i : Fin n, 0 < γ.2 i.castSucc) : StrictMono (jumpTimes γ) := by
  intro i j hij
  unfold jumpTimes
  apply Finset.sum_lt_sum_of_subset (Finset.Iio_subset_Iio hij.le)
      (Finset.mem_Iio.mpr hij) (by simp)
  · have hi : i ≠ Fin.last n := by
      exact ne_of_lt (hij.trans_le (Fin.le_last _))
    simpa using hpos (i.castPred hi)
  · intro k _ _
    exact NNReal.coe_nonneg _

@[fun_prop]
theorem measurable_jumpTimes [MeasurableSpace Ω] {n : ℕ}
    (k : Fin (n + 1)) :
    Measurable (fun γ : JumpPath Ω n => jumpTimes γ k) := by
  unfold jumpTimes
  fun_prop

/-- Remove the terminal state and holding interval from a nonempty prefix. -/
def dropLast {n : ℕ} (γ : JumpPath Ω (n + 1)) : JumpPath Ω n :=
  (fun i => γ.1 i.castSucc, fun i => γ.2 i.castSucc)

@[fun_prop]
theorem measurable_dropLast [MeasurableSpace Ω] {n : ℕ} :
    Measurable (dropLast : JumpPath Ω (n + 1) → JumpPath Ω n) := by
  unfold dropLast
  fun_prop

/-- State occupied at real time `t`.  The recursion scans jump times from the
right, hence implements the maximum-index rule and resolves coincident jump
times in favor of the state on their right. -/
noncomputable def trajectory : {n : ℕ} → JumpPath Ω n → ℝ → Ω
  | 0, γ, _ => γ.1 0
  | n + 1, γ, t =>
      if jumpTimes γ (Fin.last (n + 1)) ≤ t then
        γ.1 (Fin.last (n + 1))
      else
        trajectory (dropLast γ) t

@[fun_prop]
theorem measurable_trajectory [MeasurableSpace Ω] (n : ℕ) (t : ℝ) :
    Measurable (fun γ : JumpPath Ω n => trajectory γ t) := by
  induction n with
  | zero =>
      simp only [trajectory]
      fun_prop
  | succ n ih =>
      unfold trajectory
      exact Measurable.ite
        (measurableSet_le
          (measurable_jumpTimes (Ω := Ω) (Fin.last (n + 1))) measurable_const)
        ((measurable_pi_apply (Fin.last (n + 1))).comp measurable_fst)
        (ih.comp measurable_dropLast)

private theorem continuousWithinAt_step_right [TopologicalSpace Ω]
    (f : ℝ → Ω) (a t : ℝ) (x : Ω)
    (hf : ContinuousWithinAt f (Set.Ici t) t) :
    ContinuousWithinAt (fun s => if a ≤ s then x else f s) (Set.Ici t) t := by
  by_cases h : a ≤ t
  · have hc : ContinuousWithinAt (fun _ : ℝ => x) (Set.Ici t) t :=
      continuousWithinAt_const
    exact hc.congr
      (fun s hs => by simp [h.trans hs])
      (by simp [h])
  · have ht : t < a := lt_of_not_ge h
    apply hf.congr_of_eventuallyEq
    · filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht)] with s hs
      have hsa : ¬a ≤ s := not_le.mpr hs
      simp [hsa]
    · simp [h]

/-- The maximum-index convention makes every sector trajectory right
continuous, including paths with coincident jump times. -/
theorem continuousWithinAt_trajectory [TopologicalSpace Ω]
    {n : ℕ} (γ : JumpPath Ω n) (t : ℝ) :
    ContinuousWithinAt (trajectory γ) (Set.Ici t) t := by
  induction n with
  | zero =>
      simp only [trajectory]
      exact continuousWithinAt_const
  | succ n ih =>
      simp only [trajectory]
      exact continuousWithinAt_step_right _ _ _ _ (ih (dropLast γ))

theorem jumpTimes_last_pos_of_pos {n : ℕ} (γ : JumpPath Ω (n + 1))
    (hpos : ∀ i : Fin (n + 1), 0 < γ.2 i.castSucc) :
    0 < jumpTimes γ (Fin.last (n + 1)) := by
  unfold jumpTimes
  apply Finset.sum_pos'
  · intro i _
    exact NNReal.coe_nonneg _
  · refine ⟨0, ?_, ?_⟩
    · simp
    · exact_mod_cast hpos 0

theorem trajectory_zero_of_pos {n : ℕ} (γ : JumpPath Ω n)
    (hpos : ∀ i : Fin n, 0 < γ.2 i.castSucc) :
    trajectory γ 0 = γ.1 0 := by
  induction n with
  | zero => simp [trajectory]
  | succ n ih =>
      have hlast := jumpTimes_last_pos_of_pos γ hpos
      simp only [trajectory, if_neg (not_le.mpr hlast)]
      exact ih (dropLast γ) fun i => hpos i.castSucc

theorem trajectory_eq_terminal_of_last_le {n : ℕ} (γ : JumpPath Ω n)
    (t : ℝ) (h : jumpTimes γ (Fin.last n) ≤ t) :
    trajectory γ t = γ.1 (Fin.last n) := by
  cases n with
  | zero => simp [trajectory]
  | succ n => simp [trajectory, h]

/-- A fixed-sector chart is valid for horizon `T` when every holding interval
before a jump has positive length and the final state is reached by time `T`.
The residual terminal interval may be degenerate. -/
def IsValid {n : ℕ} (T : NNReal) (γ : JumpPath Ω n) : Prop :=
  (∀ i : Fin n, 0 < γ.2 i.castSucc) ∧
    jumpTimes γ (Fin.last n) ≤ T

theorem measurableSet_isValid [MeasurableSpace Ω] {n : ℕ} (T : NNReal) :
    MeasurableSet {γ : JumpPath Ω n | IsValid T γ} := by
  have hpos : MeasurableSet
      ({γ : JumpPath Ω n | ∀ i : Fin n, 0 < γ.2 i.castSucc} :
      Set (JumpPath Ω n)) := by
    rw [show {γ : JumpPath Ω n | ∀ i : Fin n, 0 < γ.2 i.castSucc} =
        ⋂ i : Fin n, {γ : JumpPath Ω n | 0 < γ.2 (Fin.castSucc i)} by
          ext; simp]
    exact MeasurableSet.iInter fun _ =>
      measurableSet_lt measurable_const (by fun_prop)
  have hlast : MeasurableSet
      {γ : JumpPath Ω n | jumpTimes γ (Fin.last n) ≤ T} :=
    measurableSet_le (measurable_jumpTimes (Fin.last n)) measurable_const
  exact hpos.inter hlast

theorem trajectory_zero_of_isValid {n : ℕ} {T : NNReal}
    (γ : JumpPath Ω n) (hγ : IsValid T γ) :
    trajectory γ 0 = γ.1 0 :=
  trajectory_zero_of_pos γ hγ.1

theorem trajectory_horizon_of_isValid {n : ℕ} {T : NNReal}
    (γ : JumpPath Ω n) (hγ : IsValid T γ) :
    trajectory γ T = γ.1 (Fin.last n) :=
  trajectory_eq_terminal_of_last_le γ T hγ.2

theorem jumpTimes_strictMono_of_isValid {n : ℕ} {T : NNReal}
    (γ : JumpPath Ω n) (hγ : IsValid T γ) :
    StrictMono (jumpTimes γ) :=
  jumpTimes_strictMono_of_pos γ hγ.1

end JumpPath

namespace Simplex

private theorem volume_ae_coordinates_pos (n : ℕ) :
    ∀ᵐ u ∂(volume : Measure (Fin n → I)),
      ∀ i, 0 < (u i : ℝ) := by
  apply ae_all_iff.2
  intro i
  rw [volume_pi]
  filter_upwards [Measure.ae_eval_ne
    (fun _ : Fin n => (volume : Measure I)) i 0] with u hu
  exact lt_of_le_of_ne (u i).2.1 fun h =>
    hu (Subtype.ext h.symm)

/-- Under the conditioned simplex law, every free coordinate is positive
almost surely. -/
theorem freeSimplexProbability_ae_coordinates_pos (n : ℕ) :
    ∀ᵐ u ∂freeSimplexProbability n,
      ∀ i, 0 < (u i : ℝ) := by
  have hcoord := volume_ae_coordinates_pos n
  unfold freeSimplexProbability ProbabilityTheory.cond
  exact Measure.ae_smul_measure
    (Measure.absolutelyContinuous_restrict.ae_le hcoord) _

theorem rawPathProbability_ae_jumpHoldingTimes_pos
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ} (T : NNReal) (hT : 0 < T)
    (stateLaw : Measure (Fin (n + 1) → Ω)) :
    ∀ᵐ γ ∂rawPathProbability T stateLaw,
      ∀ i : Fin n, 0 < γ.2 i.castSucc := by
  have hset : MeasurableSet
      {γ : JumpPath Ω n | ∀ i : Fin n, 0 < γ.2 i.castSucc} := by
    rw [show {γ : JumpPath Ω n | ∀ i : Fin n, 0 < γ.2 i.castSucc} =
        ⋂ i : Fin n, {γ : JumpPath Ω n | 0 < γ.2 (Fin.castSucc i)} by
          ext; simp]
    exact MeasurableSet.iInter fun _ =>
      measurableSet_lt measurable_const (by fun_prop)
  have hpre : MeasurableSet
      {p : (Fin (n + 1) → Ω) × (Fin n → I) |
        ∀ i : Fin n, 0 < (assemblePath T p).2 i.castSucc} :=
    (measurable_assemblePath T) hset
  unfold rawPathProbability
  rw [ae_map_iff (measurable_assemblePath T).aemeasurable hset]
  apply (Measure.ae_prod_iff_ae_ae hpre).2
  refine ae_of_all stateLaw fun states => ?_
  exact (freeSimplexProbability_ae_coordinates_pos n).mono fun u hu i => by
    simp only [assemblePath, holdingTimesOfFree, Fin.snoc_castSucc]
    exact mul_pos hT (by exact_mod_cast hu i)

theorem rawPathProbability_ae_isValid
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (T : NNReal) (hT : 0 < T)
    (stateLaw : Measure (Fin (n + 1) → Ω)) :
    ∀ᵐ γ ∂rawPathProbability T stateLaw, JumpPath.IsValid T γ := by
  have hpos := rawPathProbability_ae_jumpHoldingTimes_pos T hT stateLaw
  have hhor := rawPathProbability_ae_horizon T stateLaw
  filter_upwards [hpos, hhor] with γ hγ hγT
  refine ⟨hγ, ?_⟩
  have htotal : γ.totalHoldingTime = T := by
    simpa [JumpPath.horizonSet] using hγT
  calc
    JumpPath.jumpTimes γ (Fin.last n) ≤ γ.totalHoldingTime :=
      JumpPath.jumpTimes_le_totalHoldingTime γ (Fin.last n)
    _ = T := by exact_mod_cast htotal

end Simplex

namespace FullPath

variable {Ω : Type u}

/-- The initial state recorded by a complete finite-jump path. -/
def initialState : FullPath Ω → Ω
  | ⟨_, γ⟩ => γ.1 0

@[fun_prop]
theorem measurable_initialState [MeasurableSpace Ω] :
    Measurable (initialState : FullPath Ω → Ω) := by
  intro s hs
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro n
  change MeasurableSet ((fun γ : JumpPath Ω n => γ.1 0) ⁻¹' s)
  exact ((measurable_pi_apply 0).comp measurable_fst) hs

/-- The right-continuous real-time step trajectory represented by a complete
finite-jump path. -/
noncomputable def trajectory : FullPath Ω → ℝ → Ω
  | ⟨_, γ⟩ => JumpPath.trajectory γ

@[fun_prop]
theorem measurable_trajectory [MeasurableSpace Ω] (t : ℝ) :
    Measurable (fun γ : FullPath Ω => trajectory γ t) := by
  intro s hs
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro n
  change MeasurableSet
    ((fun γ : JumpPath Ω n => JumpPath.trajectory γ t) ⁻¹' s)
  exact JumpPath.measurable_trajectory n t hs

theorem continuousWithinAt_trajectory [TopologicalSpace Ω]
    (γ : FullPath Ω) (t : ℝ) :
    ContinuousWithinAt (trajectory γ) (Set.Ici t) t := by
  rcases γ with ⟨n, γ⟩
  exact JumpPath.continuousWithinAt_trajectory γ t

/-- Sectorwise validity of a complete path at horizon `T`. -/
def IsValid (T : NNReal) : FullPath Ω → Prop
  | ⟨_, γ⟩ => JumpPath.IsValid T γ

theorem measurableSet_isValid [MeasurableSpace Ω] (T : NNReal) :
    MeasurableSet {γ : FullPath Ω | IsValid T γ} := by
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro n
  exact JumpPath.measurableSet_isValid T

theorem trajectory_zero_of_isValid {T : NNReal} (γ : FullPath Ω)
    (hγ : IsValid T γ) : trajectory γ 0 = initialState γ := by
  rcases γ with ⟨n, γ⟩
  exact JumpPath.trajectory_zero_of_isValid γ hγ

theorem trajectory_horizon_of_isValid {T : NNReal} (γ : FullPath Ω)
    (hγ : IsValid T γ) : trajectory γ T = terminalState γ := by
  rcases γ with ⟨n, γ⟩
  exact JumpPath.trajectory_horizon_of_isValid γ hγ

end FullPath

namespace FiniteJumpGenerator

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

omit [DecidableEq Ω] [MeasurableSingletonClass Ω] in
theorem rawCountingReference_ae_isValid
    (G : FiniteJumpGenerator Ω) (T : NNReal) (n : ℕ) :
    ∀ᵐ γ ∂G.rawCountingReference T n, JumpPath.IsValid T γ := by
  rcases eq_zero_or_pos T with hT | hT
  · subst T
    cases n with
    | zero =>
        refine ae_of_all _ fun γ => ⟨?_, ?_⟩
        · exact fun i => Fin.elim0 i
        · simp [JumpPath.jumpTimes_zero]
    | succ n =>
        have href : G.rawCountingReference 0 (n + 1) = 0 := by
          simp [rawCountingReference, simplexSectorMass]
        rw [href]
        simp
  · unfold rawCountingReference
    exact Measure.ae_smul_measure
      (Simplex.rawPathProbability_ae_isValid T hT
        (G.stateSequenceCountingReference n)) _

omit [MeasurableSingletonClass Ω] in
theorem sectorLawFrom_ae_isValid
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x : Ω) (n : ℕ) :
    ∀ᵐ γ ∂G.sectorLawFrom T x n, JumpPath.IsValid T γ := by
  have hraw := G.rawCountingReference_ae_isValid T n
  unfold sectorLawFrom pathMeasure
  exact (withDensity_absolutelyContinuous _ _).ae_le hraw

theorem sectorLawFrom_ae_initialState
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x : Ω) (n : ℕ) :
    ∀ᵐ γ ∂G.sectorLawFrom T x n, γ.1 0 = x := by
  have hdensity := G.measurable_rateDensity (fixedInitialWeight x) n
  unfold sectorLawFrom pathMeasure
  rw [ae_withDensity_iff hdensity]
  filter_upwards [] with γ hγ
  by_contra hne
  apply hγ
  unfold JumpPath.rateDensity JumpPath.density fixedInitialWeight
  simp [hne]

omit [MeasurableSingletonClass Ω] in
/-- The constructed full path law is concentrated on charts with positive
inter-jump holding times whose final state is reached by `T`. -/
theorem pathLawFrom_ae_isValid
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x : Ω) :
    ∀ᵐ γ ∂G.pathLawFrom T x, FullPath.IsValid T γ := by
  unfold pathLawFrom FullPath.measure
  apply Measure.ae_sum_iff.2
  intro n
  unfold FullPath.liftMeasure
  rw [ae_map_iff (FullPath.measurable_mk n).aemeasurable
    (FullPath.measurableSet_isValid T)]
  exact G.sectorLawFrom_ae_isValid T x n

theorem pathLawFrom_ae_initialState
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x : Ω) :
    ∀ᵐ γ ∂G.pathLawFrom T x, FullPath.initialState γ = x := by
  have hset : MeasurableSet
      {γ : FullPath Ω | FullPath.initialState γ = x} :=
    (FullPath.measurable_initialState.eq_const x).setOf
  unfold pathLawFrom FullPath.measure
  apply Measure.ae_sum_iff.2
  intro n
  unfold FullPath.liftMeasure
  rw [ae_map_iff (FullPath.measurable_mk n).aemeasurable hset]
  exact G.sectorLawFrom_ae_initialState T x n

/-- **The real-time path starts at the prescribed state almost surely.** -/
theorem pathLawFrom_ae_trajectory_zero
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x : Ω) :
    ∀ᵐ γ ∂G.pathLawFrom T x, FullPath.trajectory γ 0 = x := by
  filter_upwards [G.pathLawFrom_ae_isValid T x,
    G.pathLawFrom_ae_initialState T x] with γ hvalid hinitial
  rw [FullPath.trajectory_zero_of_isValid γ hvalid, hinitial]

omit [MeasurableSingletonClass Ω] in
/-- **The real-time path at the horizon is its recorded terminal state almost
surely.** -/
theorem pathLawFrom_ae_trajectory_horizon
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x : Ω) :
    (fun γ => FullPath.trajectory γ T) =ᵐ[G.pathLawFrom T x]
      FullPath.terminalState := by
  filter_upwards [G.pathLawFrom_ae_isValid T x] with γ hvalid
  exact FullPath.trajectory_horizon_of_isValid γ hvalid

/-- Endpoint consistency packages the chart-validity statement into the
paper-facing real-time trajectory claim. -/
theorem pathLawFrom_ae_trajectory_endpoints
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x : Ω) :
    ∀ᵐ γ ∂G.pathLawFrom T x,
      FullPath.trajectory γ 0 = x ∧
        FullPath.trajectory γ T = FullPath.terminalState γ :=
  (G.pathLawFrom_ae_trajectory_zero T x).and
    (G.pathLawFrom_ae_trajectory_horizon T x)

end FiniteJumpGenerator

end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
