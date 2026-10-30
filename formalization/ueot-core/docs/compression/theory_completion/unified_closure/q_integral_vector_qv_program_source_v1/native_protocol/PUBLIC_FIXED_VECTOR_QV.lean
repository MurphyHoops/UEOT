import UEOT
namespace UEOTVectorFullPartitionIndependent
open MeasureTheory ProbabilityTheory Set Filter
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianFiniteProductSource BrownianVectorOneStepIntegral BrownianVectorTimeInput BrownianVectorIntegralClosure
open BrownianVectorPredictableInputs BrownianVectorPredictableDensity BrownianVectorIntegralContinuousVersion
open BrownianVectorIntegralTimeEnergy BrownianVectorIntegralEnergyL1 BrownianVectorPartitionQV
open scoped NNReal ENNReal Topology
noncomputable section
-- Explicit full native input from Gaussian START increments, supplied ONLY
-- through L2. No bounded ElementaryInput or L4 proof is an input.
def H (k : Fin 2) : Sample 2 → ℝ := coordinateIncrement 2 (if k=0 then 1 else 0) 0 1
theorem H_past (k : Fin 2) : StronglyMeasurable[jointNaturalFiltration 2 1] (H k) := by
  have hc (j : Fin 2) (u : ℝ≥0) : StronglyMeasurable[jointNaturalFiltration 2 u] (coordinate 2 j u) :=
    (EuclideanSpace.proj (𝕜:=ℝ) j).continuous.comp_stronglyMeasurable (vectorProcess_stronglyAdapted 2 u)
  exact (hc _ 1).sub ((hc _ 0).mono ((jointNaturalFiltration 2).mono (by norm_num : (0 : ℝ≥0)≤1)))
theorem H_L2 (k : Fin 2) : MemLp (H k) 2 (productLaw 2) := coordinateIncrement_memLp_two 2 _ 0 1
def F : ℝ × Sample 2 → EuclideanSpace ℝ (Fin 2) := BrownianVectorTimeInput.intervalInput 2 H 1 2
theorem F_L2 : MemLp F 2 (inputLaw 2 3) := by
  apply MemLp.of_eval_piLp
  intro k
  have hi : MemLp ((Ioc (1 : ℝ) 2).indicator (fun _ : ℝ => (1 : ℝ))) ∞
      (BrownianTimeIntegrand.timeLaw 3) := (memLp_top_const 1).indicator measurableSet_Ioc
  exact ((H_L2 k).comp_snd (BrownianTimeIntegrand.timeLaw 3)).mul (hi.comp_fst (productLaw 2))
def f : fullPredictableL2 2 3 := ⟨F_L2.toLp F,by
  apply mem_lpMeas_iff_aestronglyMeasurable.mpr
  exact (intervalInput_predictable 1 2 H_past).aestronglyMeasurable.congr F_L2.coeFn_toLp.symm⟩
-- This is the SAME fixed actual f for every supplied partition, with target
-- computed by its OWN actual timeEnergy; not a changing-record theorem.
example (N : ℕ → ℕ) (tau : (n : ℕ) → Fin (N n+1) → ℝ≥0)
    (hm : ∀ n, Monotone (tau n)) (hz : ∀ n, tau n 0=0)
    (he : ∀ n, tau n (Fin.last (N n))=3)
    (hmesh : Tendsto (fun n=>(BrownianQuadraticVariation.mesh (tau n) : ℝ)) atTop (𝓝 0)) :
    TendstoInMeasure (productLaw 2) (fun n w => ∑ i : Fin (N n),
      (continuousIntegralProcess 2 3 f (tau n i.succ) w-
        continuousIntegralProcess 2 3 f (tau n i.castSucc) w)^2) atTop (timeEnergy 2 3 f 3) :=
  fullInput_partition_QV_inMeasure 2 3 N tau hm hz he hmesh f
-- Universal original full-domain consumer: there is no caller L-infinity,
-- L4, supplied approximation, output-square limit or bracket field.
example (d : ℕ) (T : ℝ≥0) (N : ℕ → ℕ) (tau : (n : ℕ) → Fin (N n+1) → ℝ≥0)
    (hm : ∀ n, Monotone (tau n)) (hz : ∀ n, tau n 0=0)
    (he : ∀ n, tau n (Fin.last (N n))=T)
    (hmesh : Tendsto (fun n=>(BrownianQuadraticVariation.mesh (tau n) : ℝ)) atTop (𝓝 0))
    (g : fullPredictableL2 d T) := fullInput_partition_QV d T N tau hm hz he hmesh g
#print axioms F_L2
#print axioms BrownianVectorPartitionLeftInputs.finiteSpan_partition_input_tendsto
#print axioms finiteSpan_partition_QV
#print axioms fullInput_partition_QV
#print axioms fullInput_partition_QV_inMeasure
end
end UEOTVectorFullPartitionIndependent
namespace UEOTVectorFullPartitionIndependent
open MeasureTheory ProbabilityTheory Filter
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianFiniteProductSource BrownianVectorPredictableInputs BrownianVectorIntegralGridL1 BrownianVectorIntegralEnergyL1 BrownianVectorPartitionQV
open BrownianQuadraticVariation (mesh uniformClock uniformClock_mono uniformClock_zero uniformClock_end uniformClock_mesh_tendsto)
open scoped NNReal ENNReal Topology
noncomputable section
-- A nonvacuous actual clock family for the Gaussian-coefficient original f.
example : Tendsto (fun n=>gridSquares 2 3 (uniformClock 3 n) f) atTop (𝓝 (energyClass 2 3 3 f)) :=
  fullInput_partition_QV 2 3 (fun n=>n+1) (uniformClock 3) (uniformClock_mono 3)
    (uniformClock_zero 3) (uniformClock_end 3) (uniformClock_mesh_tendsto 3) f
example (d : ℕ) (g : fullPredictableL2 d 0) :
    Tendsto (fun _n : ℕ=>gridSquares d 0 (fun _ : Fin 1=>0) g) atTop (𝓝 (energyClass d 0 0 g)) := by
  apply fullInput_partition_QV d 0 (fun _=>0) (fun _ _=>0)
    (fun _ _ _ _=>le_rfl) (fun _=>rfl) (fun _=>rfl) _ g
  simp [mesh]
example (T : ℝ≥0) (g : fullPredictableL2 0 T) :
    Tendsto (fun n=>gridSquares 0 T (uniformClock T n) g) atTop (𝓝 (energyClass 0 T T g)) :=
  fullInput_partition_QV 0 T (fun n=>n+1) (uniformClock T) (uniformClock_mono T)
    (uniformClock_zero T) (uniformClock_end T) (uniformClock_mesh_tendsto T) g
end
end UEOTVectorFullPartitionIndependent
