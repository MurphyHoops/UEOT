import UEOT
namespace VectorCrossStateIndependent
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianFiniteProductSource BrownianVectorOneStepIntegral BrownianVectorTimeInput
open BrownianVectorIntegralClosure BrownianVectorPredictableInputs BrownianVectorPredictableDensity
open BrownianVectorIntegralTimeSource BrownianVectorIntegralConditionalSource BrownianVectorIntegralContinuousVersion
open BrownianVectorIntegralGridL1 BrownianVectorIntegralTimeEnergy BrownianVectorIntegralEnergyL1
open BrownianVectorCrossPartitionQV BrownianVectorFiniteStateCrossQV BrownianQuadraticVariation
open BrownianTimeIntegrand (timeLaw)
open scoped NNReal ENNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
-- Fresh nonsmooth coefficients, BOTH coordinates use the OTHER coordinate's
-- original START1 sigma. No own-coordinate scalar-filtration substitution.
def H (k : Fin 2) (w : Sample 2) : ℝ :=
  if k=0 then (if 0≤coordinate 2 1 1 w then 1 else -1)
  else (if 0≤coordinate 2 0 1 w then 2 else -2)
theorem H_past (k : Fin 2) : StronglyMeasurable[jointNaturalFiltration 2 1] (H k) := by
  have hc (j : Fin 2) : StronglyMeasurable[jointNaturalFiltration 2 1] (coordinate 2 j 1) :=
    (EuclideanSpace.proj (𝕜:=ℝ) j).continuous.comp_stronglyMeasurable (vectorProcess_stronglyAdapted 2 1)
  let : MeasurableSpace (Sample 2) := jointNaturalFiltration 2 1
  have hs (j : Fin 2) : MeasurableSet {w : Sample 2 | 0≤coordinate 2 j 1 w} :=
    measurableSet_le measurable_const (hc j).measurable
  unfold H
  split_ifs
  · exact (Measurable.ite (hs 1) measurable_const measurable_const).stronglyMeasurable
  · exact (Measurable.ite (hs 0) measurable_const measurable_const).stronglyMeasurable
theorem H_bounded (k : Fin 2) : MemLp (H k) ∞ (productLaw 2) := by
  apply memLp_top_of_bound ((H_past k).mono ((jointNaturalFiltration 2).le 1)).aestronglyMeasurable 2
  apply ae_of_all
  intro w
  unfold H
  split_ifs <;> norm_num
theorem H_norm (w : Sample 2) : ‖coefficient 2 H w‖^2=5 := by
  rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]
  simp only [coefficient_apply,H,show (1 : Fin 2) ≠ 0 by decide,ite_true,ite_false]
  split_ifs <;> norm_num

def f : fullPredictableL2 2 3 := intervalInput 2 3 1 2 (by norm_num) (by norm_num) H H_past H_bounded

-- g reads a genuinely different earlier history on its second actuator.
def G (k : Fin 2) (w : Sample 2) : ℝ :=
  if k=0 then -10 * H 0 w else (if 0≤coordinate 2 0 (1/2) w then -2 else 2)
theorem G_past (k : Fin 2) : StronglyMeasurable[jointNaturalFiltration 2 1] (G k) := by
  have hc : StronglyMeasurable[jointNaturalFiltration 2 1] (coordinate 2 0 (1/2)) :=
    ((EuclideanSpace.proj (𝕜:=ℝ) (0 : Fin 2)).continuous.comp_stronglyMeasurable
      (vectorProcess_stronglyAdapted 2 (1/2))).mono ((jointNaturalFiltration 2).mono (by norm_num))
  let : MeasurableSpace (Sample 2) := jointNaturalFiltration 2 1
  have hs : MeasurableSet {w : Sample 2 | 0≤coordinate 2 0 (1/2) w} :=
    measurableSet_le measurable_const hc.measurable
  unfold G
  split_ifs
  · exact stronglyMeasurable_const.mul (H_past 0)
  · exact (Measurable.ite hs measurable_const measurable_const).stronglyMeasurable
theorem G_bounded (k : Fin 2) : MemLp (G k) ∞ (productLaw 2) := by
  apply memLp_top_of_bound ((G_past k).mono ((jointNaturalFiltration 2).le 1)).aestronglyMeasurable 10
  apply ae_of_all
  intro w
  unfold G H
  split_ifs <;> norm_num at *
def g : fullPredictableL2 2 3 := intervalInput 2 3 1 2 (by norm_num) (by norm_num) G G_past G_bounded

theorem actual_inner_negative (w : Sample 2) : inner ℝ (coefficient 2 H w) (coefficient 2 G w)≤(-6 : ℝ) := by
  rw [PiLp.inner_apply,Fin.sum_univ_two]
  simp only [Real.inner_apply,coefficient_apply,H,G,show (1 : Fin 2) ≠ 0 by decide,ite_true,ite_false]
  split_ifs <;> norm_num

theorem actual_cross : crossTimeEnergy 2 3 f g 3 =ᵐ[productLaw 2]
    fun w=>inner ℝ (coefficient 2 H w) (coefficient 2 G w) := by
  have he : crossEnergyIntegrand 2 3 3 f g =ᵐ[inputLaw 2 3]
      fun p=>(Ioc (1 : ℝ) 2).indicator
        (fun t=>inner ℝ (coefficient 2 H p.2) (coefficient 2 G p.2)) p.1 := by
    filter_upwards [representative_ae 2 3 f,representative_ae 2 3 g,
      intervalInput_coe 2 3 1 2 (by norm_num) (by norm_num) H H_past H_bounded,
      intervalInput_coe 2 3 1 2 (by norm_num) (by norm_num) G G_past G_bounded,
      time_support_ae 2 3] with p hf hg hfi hgi ht
    have hp : p∈timeSet 2 3 3 := by
      simpa only [timeSet,min_self,mem_prod,mem_univ,and_true] using ht
    change (f : Lp (EuclideanSpace ℝ (Fin 2)) 2 (inputLaw 2 3)) p = _ at hfi
    change (g : Lp (EuclideanSpace ℝ (Fin 2)) 2 (inputLaw 2 3)) p = _ at hgi
    rw [crossEnergyIntegrand,Set.indicator_of_mem hp,←hf,←hg,hfi,hgi]
    by_cases hc : p.1∈Ioc (1 : ℝ) 2 <;> simp [BrownianVectorTimeInput.intervalInput,hc]
  have hs := Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ:=productLaw 2) (ν:=timeLaw 3)).quasiMeasurePreserving.ae he)
  filter_upwards [hs] with w hw
  dsimp only [Prod.swap] at hw
  unfold crossTimeEnergy
  rw [integral_congr_ae hw,integral_indicator measurableSet_Ioc,integral_const]
  have hm : (timeLaw 3).real (Ioc (1 : ℝ) 2)=1 := by
    rw [measureReal_def,BrownianTimeIntegrand.timeLaw,Measure.restrict_apply measurableSet_Ioc]
    have hsub : Ioc (1 : ℝ) 2⊆Icc (0 : ℝ) (3 : ℝ≥0) := by intro t ht; norm_num at *; constructor <;> linarith [ht.1,ht.2]
    rw [inter_eq_left.mpr hsub,Real.volume_Ioc]
    norm_num
  simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul]
  change ((timeLaw 3) (Ioc (1 : ℝ) 2)).toReal=1 at hm
  rw [hm,one_mul]

example : ∀ᵐ w ∂productLaw 2, crossTimeEnergy 2 3 f g 3 w≤(-6 : ℝ) :=
  actual_cross.mono (fun w hw=>hw.symm ▸ actual_inner_negative w)
example : TendstoInMeasure (productLaw 2) (fun n w=>∑ i : Fin (n+1),
    (continuousIntegralProcess 2 3 f (uniformClock 3 n i.succ) w-continuousIntegralProcess 2 3 f (uniformClock 3 n i.castSucc) w)*
    (continuousIntegralProcess 2 3 g (uniformClock 3 n i.succ) w-continuousIntegralProcess 2 3 g (uniformClock 3 n i.castSucc) w))
    atTop (fun w=>inner ℝ (coefficient 2 H w) (coefficient 2 G w)) :=
  TendstoInMeasure.congr (fun _=>Filter.EventuallyEq.rfl) actual_cross
    (fullInput_partition_crossVariation_inMeasure 2 3 (fun n=>n+1) (uniformClock 3)
      (uniformClock_mono 3) (uniformClock_zero 3) (uniformClock_end 3) (uniformClock_mesh_tendsto 3) f g)
example : ∀ᵐ w ∂productLaw 2, ∀ u, continuousIntegralProcess 2 3 (f-g) u w =
    continuousIntegralProcess 2 3 f u w-continuousIntegralProcess 2 3 g u w := continuousIntegralProcess_sub_path 2 3 f g
example : ∀ᵐ w ∂productLaw 2, Continuous (fun u=>crossTimeEnergy 2 3 f g u w) := crossTimeEnergy_continuous_ae 2 3 f g

def family : Fin 2→fullPredictableL2 2 3 := ![f,g]
def A : Matrix (Fin 2) (Fin 2) ℝ := !![0,2;-3,0]
example : StronglyAdapted (jointNaturalFiltration 2) (stateProcess 2 3 family) := stateProcess_stronglyAdapted 2 3 family
example : ∀ᵐ w ∂productLaw 2, Continuous (fun u=>stateProcess 2 3 family u w) := stateProcess_continuous 2 3 family
example : Measurable (Function.uncurry (stateProcess 2 3 family)) := stateProcess_measurable 2 3 family

theorem actual_weighted (w : Sample 2) : weightedTimeEnergy 2 3 A family w = -crossTimeEnergy 2 3 f g 3 w := by
  rw [weightedTimeEnergy,crossTimeEnergy,←integral_neg]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  simp only [Fin.sum_univ_two,family,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  unfold crossEnergyIntegrand
  by_cases ht : (t,w)∈timeSet 2 3 3
  · simp only [Set.indicator_of_mem ht]
    change 0 * inner ℝ (representative 2 3 f (t,w)) (representative 2 3 f (t,w)) +
      2 * inner ℝ (representative 2 3 f (t,w)) (representative 2 3 g (t,w)) +
      ((-3) * inner ℝ (representative 2 3 g (t,w)) (representative 2 3 f (t,w)) +
      0 * inner ℝ (representative 2 3 g (t,w)) (representative 2 3 g (t,w))) = _
    rw [real_inner_comm (representative 2 3 g (t,w)) (representative 2 3 f (t,w))]
    ring
  · simp [ht]
example : ∀ᵐ w ∂productLaw 2, 6≤weightedTimeEnergy 2 3 A family w := by
  filter_upwards [actual_cross] with w hw
  rw [actual_weighted,hw]
  linarith [actual_inner_negative w]
example : TendstoInMeasure (productLaw 2) (fun n=>weightedStateSum 2 3 A family (uniformClock 3 n))
    atTop (weightedTimeEnergy 2 3 A family) := weighted_state_partition_QV_inMeasure 2 3 A family
      (fun n=>n+1) (uniformClock 3) (uniformClock_mono 3) (uniformClock_zero 3)
      (uniformClock_end 3) (uniformClock_mesh_tendsto 3)
example (w : Sample 2) : ∀ v : Fin 2→ℝ, 0≤weightedTimeEnergy 2 3 (fun j k=>v j*v k) family w :=
  fun v=>weightedTimeEnergy_rankOne_nonneg 2 3 v family w
example (T : ℝ≥0) (h : Fin 0→fullPredictableL2 2 T) (u : ℝ≥0) (w : Sample 2) : stateProcess 2 T h u w=0 :=
  stateProcess_zero_dimension 2 T h u w
example (T : ℝ≥0) (h k : fullPredictableL2 0 T) :
    Tendsto (fun n=>gridCross 0 T (uniformClock T n) h k) atTop (𝓝 (crossEnergyClass 0 T T h k)) :=
  fullInput_partition_crossVariation 0 T (fun n=>n+1) (uniformClock T) (uniformClock_mono T)
    (uniformClock_zero T) (uniformClock_end T) (uniformClock_mesh_tendsto T) h k
example (h k : fullPredictableL2 2 0) :
    Tendsto (fun _n : ℕ=>gridCross 2 0 (fun _ : Fin 1=>0) h k) atTop (𝓝 (crossEnergyClass 2 0 0 h k)) := by
  apply fullInput_partition_crossVariation 2 0 (fun _=>0) (fun _ _=>0)
    (fun _ _ _ _=>le_rfl) (fun _=>rfl) (fun _=>rfl) _ h k
  simp [mesh]
example (s : ℝ≥0) (j k : Fin 2) (w : Sample 2) : stateCrossSum 2 3 family (fun _ : Fin 2=>s) j k w=0 := by
  simp [stateCrossSum]
#print axioms fullInput_partition_crossVariation
#print axioms fullInput_partition_crossVariation_inMeasure
#print axioms continuousIntegralProcess_add_path
#print axioms continuousIntegralProcess_sub_path
#print axioms crossTimeEnergy_continuous_ae
#print axioms stateProcess_stronglyAdapted
#print axioms stateProcess_continuous
#print axioms stateProcess_measurable
#print axioms matrix_partition_QV
#print axioms weighted_state_partition_QV_inMeasure
#print axioms weightedTimeEnergy_rankOne_nonneg
#print axioms actual_cross
#print axioms actual_weighted
end
end VectorCrossStateIndependent
