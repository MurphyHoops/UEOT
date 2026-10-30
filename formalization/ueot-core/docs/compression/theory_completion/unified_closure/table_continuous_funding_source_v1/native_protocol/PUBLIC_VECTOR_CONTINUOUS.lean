import UEOT
namespace VectorContinuousIndependent
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianFiniteProductSource BrownianVectorOneStepIntegral BrownianVectorTimeInput
open BrownianVectorIntegralClosure BrownianVectorPredictableInputs BrownianVectorPredictableDensity
open BrownianVectorIntegralTimeSource BrownianVectorIntegralConditionalSource
open BrownianVectorIntegralFinitePaths BrownianVectorIntegralMaximalControl BrownianVectorIntegralContinuousVersion
open scoped NNReal ENNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

-- Fresh coefficient: nonsmooth Borel sign of OTHER coordinate at START1.
-- It is not a time0/visibility-specialized/scalar-source coefficient.
def H (k : Fin 2) (w : Sample 2) : ℝ :=
  if k=0 then (if 0≤coordinate 2 1 1 w then 1 else -1) else 0

theorem H_past (k : Fin 2) : StronglyMeasurable[jointNaturalFiltration 2 1] (H k) := by
  have hc : StronglyMeasurable[jointNaturalFiltration 2 1] (coordinate 2 1 1) :=
    (EuclideanSpace.proj (𝕜:=ℝ) (1 : Fin 2)).continuous.comp_stronglyMeasurable (vectorProcess_stronglyAdapted 2 1)
  let : MeasurableSpace (Sample 2) := jointNaturalFiltration 2 1
  have hs : MeasurableSet {w : Sample 2 | 0≤coordinate 2 1 1 w} := measurableSet_le measurable_const hc.measurable
  unfold H
  split_ifs
  · exact (Measurable.ite hs measurable_const measurable_const).stronglyMeasurable
  · exact stronglyMeasurable_const

theorem H_bounded (k : Fin 2) : MemLp (H k) ∞ (productLaw 2) := by
  apply memLp_top_of_bound ((H_past k).mono ((jointNaturalFiltration 2).le 1)).aestronglyMeasurable 1
  apply ae_of_all
  intro w
  unfold H
  split_ifs <;> norm_num

theorem H_euclidean_norm (w : Sample 2) : ‖coefficient 2 H w‖^2=1 := by
  rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]
  norm_num [coefficient_apply,H]

def r : ElementaryInput 2 3 := intervalRecord 2 3 1 2 (by norm_num) (by norm_num) H H_past H_bounded

theorem actual_ALLtime_return : ∀ᵐ w ∂productLaw 2, ∀ u,
    continuousIntegralProcess 2 3 (literalPredictableInput 2 r) u w=
      oneStep 2 H 1 (BrownianCommonRefinement.clamp 1 2 u) w := by
  apply (continuousIntegralProcess_returns_literal 2 r).mono
  intro w h u
  rw [h u]
  change (∑ i : Fin 3, oneStep 2 (![fun _ _=>0,H,fun _ _=>0] i)
    (![0,1,2,3] i.castSucc) (BrownianCommonRefinement.clamp (![0,1,2,3] i.castSucc) (![0,1,2,3] i.succ) u) w)=_
  simp [Fin.sum_univ_succ,oneStep,component]

theorem actual_energy1 : (∫ w, continuousIntegralProcess 2 3 (literalPredictableInput 2 r) 3 w^2 ∂productLaw 2)=1 := by
  calc
    _ = ∫ w, oneStep 2 H 1 2 w^2 ∂productLaw 2 := by
      apply integral_congr_ae
      apply actual_ALLtime_return.mono
      intro w h
      change continuousIntegralProcess 2 3 (literalPredictableInput 2 r) 3 w^2=oneStep 2 H 1 2 w^2
      rw [h 3]
      norm_num [BrownianCommonRefinement.clamp]
    _ = ((2 : ℝ)-1)*(∫ w, ‖coefficient 2 H w‖^2 ∂productLaw 2) :=
      oneStep_isometry 1 2 (by norm_num) H_past H_bounded
    _ = 1 := by norm_num [H_euclidean_norm]

example : ∀ᵐ w ∂productLaw 2, continuousIntegralProcess 2 3 (literalPredictableInput 2 r) (1/2) w=0 := by
  apply actual_ALLtime_return.mono
  intro w h
  rw [h (1/2)]
  norm_num [BrownianCommonRefinement.clamp,oneStep,component,coordinateIncrement]

-- A literal repeated clock retains its zero-width coefficient permission atSTART1.
def repeated : ElementaryInput 2 3 where
  n := 4
  clock := ![0,1,1,2,3]
  coefficient := ![fun _ _=>0,H,H,fun _ _=>0]
  clock_mono := by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all; all_goals norm_num
  clock_zero := rfl
  clock_end := rfl
  coefficient_past := by intro i k; fin_cases i
                         · exact stronglyMeasurable_const
                         · exact H_past k
                         · exact H_past k
                         · exact stronglyMeasurable_const
  coefficient_bounded := by intro i k; fin_cases i
                            · exact MemLp.zero
                            · exact H_bounded k
                            · exact H_bounded k
                            · exact MemLp.zero
example : ∀ᵐ w ∂productLaw 2, ∀ u,
    continuousIntegralProcess 2 3 (literalPredictableInput 2 repeated) u w=oneStep 2 H 1 (BrownianCommonRefinement.clamp 1 2 u) w := by
  apply (continuousIntegralProcess_returns_literal 2 repeated).mono
  intro w h u
  rw [h u]
  change (∑ i : Fin 4, oneStep 2 (![fun _ _=>0,H,H,fun _ _=>0] i)
    (![0,1,1,2,3] i.castSucc) (BrownianCommonRefinement.clamp (![0,1,1,2,3] i.castSucc) (![0,1,1,2,3] i.succ) u) w)=_
  simp [Fin.sum_univ_succ,oneStep,component,coordinateIncrement,BrownianCommonRefinement.clamp]

-- Fixed-u natural sigma and progressive restricted-product sigma are BOTH actual.
example (d : ℕ) (T : ℝ≥0) (f : fullPredictableL2 d T) := continuousIntegralProcess_stronglyAdapted d T f
example (d : ℕ) (T : ℝ≥0) (f : fullPredictableL2 d T) := continuousIntegralProcess_isStronglyProgressive d T f
example (d : ℕ) (T : ℝ≥0) (f : fullPredictableL2 d T) := continuousIntegralProcess_measurable d T f

private theorem zero_ALLtime (d : ℕ) (T : ℝ≥0) (f : fullPredictableL2 d T)
    (hz : ∀ u, integralProcess d T f u =ᵐ[productLaw d] fun _=>0) :
    ∀ᵐ w ∂productLaw d, ∀ u, continuousIntegralProcess d T f u w=0 := by
  have hd : ∀ᵐ w ∂productLaw d, ∀ j, continuousIntegralProcess d T f (denseSeq ℝ≥0 j) w=0 :=
    ae_all_iff.mpr (fun j => (continuousIntegralProcess_eq_actual d T _ f).trans (hz _))
  filter_upwards [continuousIntegralProcess_continuous d T f,hd] with w hc hd
  exact congrFun ((denseRange_denseSeq ℝ≥0).equalizer hc continuous_const (funext hd))

example (T : ℝ≥0) (f : fullPredictableL2 0 T) : ∀ᵐ w ∂productLaw 0, ∀ u, continuousIntegralProcess 0 T f u w=0 := by
  apply zero_ALLtime
  intro u
  have hf : f=0 := Subtype.ext (Lp.ext (ae_of_all _ (fun _=>Subsingleton.elim _ _)))
  rw [hf]
  have h := integralProcess_eq_truncated 0 T u 0
  simp only [integralClassProcess,map_zero] at h
  exact h.trans (Lp.coeFn_zero ℝ 2 (productLaw 0))
example (d : ℕ) (f : fullPredictableL2 d 0) : ∀ᵐ w ∂productLaw d, ∀ u, continuousIntegralProcess d 0 f u w=0 := by
  apply zero_ALLtime
  intro u
  have hf : f=0 := Subtype.ext (Lp.ext (ae_iff.mpr (by simp [inputLaw_zero])))
  rw [hf]
  have h := integralProcess_eq_truncated d 0 u 0
  simp only [integralClassProcess,map_zero] at h
  exact h.trans (Lp.coeFn_zero ℝ 2 (productLaw d))

-- Finite family produces actual Euclidean OUTPUT (not a sup-norm substitute).
def tuplePath (d m : ℕ) (T : ℝ≥0) (f : Fin m → fullPredictableL2 d T) (u : ℝ≥0) (w : Sample d) : EuclideanSpace ℝ (Fin m) :=
  (EuclideanSpace.equiv (Fin m) ℝ).symm (fun j=>continuousIntegralProcess d T (f j) u w)
example (d m : ℕ) (T : ℝ≥0) (f : Fin m → fullPredictableL2 d T) :
    ∀ᵐ w ∂productLaw d, Continuous (fun u=>tuplePath d m T f u w) := by
  have hc : ∀ᵐ w ∂productLaw d, ∀ j, Continuous (fun u=>continuousIntegralProcess d T (f j) u w) :=
    ae_all_iff.mpr (fun j=>continuousIntegralProcess_continuous d T (f j))
  apply hc.mono
  intro w hw
  exact (EuclideanSpace.equiv (Fin m) ℝ).symm.continuous.comp (continuous_pi hw)
example (d m : ℕ) (T : ℝ≥0) (f : Fin m → fullPredictableL2 d T) :
    StronglyAdapted (jointNaturalFiltration d) (tuplePath d m T f) := by
  intro u
  let : MeasurableSpace (Sample d) := jointNaturalFiltration d u
  have hm : Measurable (fun w j=>continuousIntegralProcess d T (f j) u w) :=
    measurable_pi_lambda _ (fun j=>(continuousIntegralProcess_stronglyAdapted d T (f j) u).measurable)
  exact ((EuclideanSpace.equiv (Fin m) ℝ).symm.continuous.measurable.comp hm).stronglyMeasurable

-- Direct original single-union Doob consumer on an unsorted/repeating countable clock.
def unorderedClock (n : ℕ) : ℝ≥0 := if n%3=0 then 2 else if n%3=1 then 0 else 1
example := integralProcess_countable_maximum 2 3 (literalPredictableInput 2 r) unorderedClock 1
example (d m : ℕ) (T : ℝ≥0) (f : Fin m → fullPredictableL2 d T) :
    IsStronglyProgressive (jointNaturalFiltration d) (tuplePath d m T f) := by
  intro s
  let : MeasurableSpace (Iic s × Sample d) := Subtype.instMeasurableSpace.prod (jointNaturalFiltration d s)
  have hm : Measurable (fun p : Iic s × Sample d => fun j=>continuousIntegralProcess d T (f j) p.1 p.2) :=
    measurable_pi_lambda _ (fun j=>(continuousIntegralProcess_isStronglyProgressive d T (f j) s).measurable)
  exact ((EuclideanSpace.equiv (Fin m) ℝ).symm.continuous.measurable.comp hm).stronglyMeasurable
#print axioms approximation_eventually_uniform
#print axioms spanMaximumEvent_bound
#print axioms continuousIntegralProcess_energy
#print axioms continuousIntegralProcess_horizon
#print axioms actual_ALLtime_return
#print axioms actual_energy1
#print axioms integralProcess_countable_maximum
#print axioms continuousIntegralProcess_stronglyAdapted
#print axioms continuousIntegralProcess_continuous
#print axioms continuousIntegralProcess_eq_actual
#print axioms continuousIntegralProcess_isStronglyProgressive
#print axioms continuousIntegralProcess_returns_literal
end
end VectorContinuousIndependent
