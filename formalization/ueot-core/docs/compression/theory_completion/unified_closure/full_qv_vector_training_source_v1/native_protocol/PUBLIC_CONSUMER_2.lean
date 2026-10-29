import UEOT
open MeasureTheory ProbabilityTheory Set Filter
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianProjectiveSource BrownianPredictableInputs BrownianIntegralClosure BrownianIntegralFinitePaths
open BrownianIntegralContinuousVersion BrownianIntegralTimeEnergy BrownianIntegralGridL1 BrownianIntegralEnergyL1
open BrownianQuadraticVariation BrownianPartitionLeftInputs BrownianPartitionQV
open BrownianFiniteSpanLeftInputs BrownianContinuousAdaptedInputs
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

-- Explicit caller family retains a duplicated START and all remaining cells;
-- it is not the original uniformClock family with n+2 equal cells.
def duplicateStart (T : ℝ≥0) (n : ℕ) (i : Fin (n+3)) : ℝ≥0 :=
  ((i : ℕ)-1 : ℕ)*T/(n+1 : ℕ)

theorem duplicateStart_mono (T : ℝ≥0) (n : ℕ) : Monotone (duplicateStart T n) := by
  intro i j hij
  unfold duplicateStart
  gcongr
  exact hij

theorem duplicateStart_zero (T : ℝ≥0) (n : ℕ) : duplicateStart T n 0 = 0 := by
  simp [duplicateStart]

theorem duplicateStart_end (T : ℝ≥0) (n : ℕ) : duplicateStart T n (Fin.last (n+2)) = T := by
  simp only [duplicateStart,Fin.val_last]
  exact mul_div_cancel_left₀ T (by positivity : ((n+1 : ℕ) : ℝ≥0) ≠ 0)

theorem duplicateStart_mesh_le (T : ℝ≥0) (n : ℕ) : mesh (duplicateStart T n) ≤ T/(n+1 : ℕ) := by
  apply Finset.sup_le
  intro i _
  apply tsub_le_iff_right.mpr
  have hv : ((i : ℕ)+1)-1 ≤ ((i : ℕ)-1)+1 := by omega
  have h : ((((i : ℕ)+1)-1 : ℕ) : ℝ≥0)*T/(n+1 : ℕ) ≤
      ((((i : ℕ)-1 : ℕ) : ℝ≥0)+1)*T/(n+1 : ℕ) := by
    gcongr
    exact_mod_cast hv
  simpa only [duplicateStart,Fin.val_succ,Fin.val_castSucc,add_mul,one_mul,add_div,add_comm] using h

theorem duplicateStart_mesh_tendsto (T : ℝ≥0) :
    Tendsto (fun n => (mesh (duplicateStart T n) : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => (mesh _).coe_nonneg)
    (fun n => NNReal.coe_le_coe.mpr (duplicateStart_mesh_le T n))
  simpa only [uniformClock_mesh] using uniformClock_mesh_tendsto T

example : duplicateStart 1 0 0 = 0 ∧ duplicateStart 1 0 1 = 0 ∧ duplicateStart 1 0 2 = 1 := by
  norm_num [duplicateStart]

-- SAME arbitrary original full input consumes this actual repeated clock;
-- L1 limit and literal path-square in-measure limit share its actual energy.
example (T : ℝ≥0) (f : fullPredictableL2 T) :
    Tendsto (fun n => gridSquares T (duplicateStart T n) f) atTop (𝓝 (energyClass T T f)) ∧
    TendstoInMeasure sourceLaw (fun n ω => ∑ i : Fin (n+2),
      (continuousIntegralProcess T f (duplicateStart T n i.succ) ω-
        continuousIntegralProcess T f (duplicateStart T n i.castSucc) ω)^2) atTop (timeEnergy T f T) :=
  ⟨fullInput_partition_QV T (fun n => n+2) (duplicateStart T) (duplicateStart_mono T)
      (duplicateStart_zero T) (duplicateStart_end T) (duplicateStart_mesh_tendsto T) f,
    fullInput_partition_QV_inMeasure T (fun n => n+2) (duplicateStart T) (duplicateStart_mono T)
      (duplicateStart_zero T) (duplicateStart_end T) (duplicateStart_mesh_tendsto T) f⟩

-- Exact same caller class is approximated: this is not an assumed QV field.
example (T : ℝ≥0) (a : ElementaryInput T →₀ ℝ) :
    Tendsto (fun n => inputValue (sampleRecord T (duplicateStart T n) (duplicateStart_mono T n)
      (duplicateStart_zero T n) (duplicateStart_end T n) (clippedTrace T a) (clippedTrace_adapted T a)
      (spanBound T a) (clippedTrace_bound T a))) atTop (𝓝 (spanInput T a : Lp ℝ 2 (BrownianTimeIntegrand.inputLaw T))) :=
  finiteSpan_partition_inputClass_tendsto T (fun n => n+2) (duplicateStart T) (duplicateStart_mono T)
    (duplicateStart_zero T) (duplicateStart_end T) (duplicateStart_mesh_tendsto T) a

-- Empty caller partition is admissible at horizon0; no denominator is used.
example (f : fullPredictableL2 0) :
    Tendsto (fun _ : ℕ => gridSquares 0 (fun _ : Fin 1 => (0 : ℝ≥0)) f) atTop (𝓝 (energyClass 0 0 f)) := by
  apply fullInput_partition_QV 0 (fun _ => 0) (fun _ _ => 0)
  · intro _ i j _; exact le_rfl
  · intro _; rfl
  · intro _; rfl
  · simp [mesh]
