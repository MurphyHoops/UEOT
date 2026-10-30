import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorPartitionQV
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralCrossVariation

/-!
Original commitment: finite state Itô consumers need cross variation of actual integrals driven by the SAME finite-dimensional noise.
Existing result: original joint-source continuous outputs and full native predictable Euclidean L2 diagonal QV on deterministic caller clocks.
Premise reduced: derive cross-increment limits with target the SAME-source actual dt inner-product energy, without external brackets or L4.
Model/witness: arbitrary finite noise dimension, arbitrary two full inputs, zero dimension/time and repeated deterministic clock cells included.
Consumer: actual finite state-family matrix and weighted cross terms; random partitions and state Itô remain separate obligations.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorCrossPartitionQV
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open BrownianFiniteProductSource BrownianVectorTimeInput BrownianVectorIntegralClosure
open BrownianVectorPredictableInputs BrownianVectorPredictableDensity BrownianVectorIntegralTimeSource
open BrownianVectorIntegralContinuousVersion BrownianVectorIntegralConditionalSource BrownianVectorIntegralTimeEnergy BrownianVectorIntegralEnergyL1
open BrownianVectorIntegralGridL1 BrownianQuadraticVariation BrownianVectorPartitionQV
open BrownianIntegralCrossVariation (productClass productClass_coe productClass_polarization)
open BrownianTimeIntegrand (timeLaw)
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

section NativeInner
variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Native Holder inner product on the actual input measure. -/
def innerClass (μ : Measure α) (f g : Lp E 2 μ) : Lp ℝ 1 μ :=
  (innerSL ℝ (E := E)).holderL μ 2 2 1 f g

theorem innerClass_coe (μ : Measure α) (f g : Lp E 2 μ) :
    innerClass μ f g =ᵐ[μ] fun a => inner ℝ (f a) (g a) := by
  simp only [innerClass,ContinuousLinearMap.holderL_apply_apply]
  apply ((innerSL ℝ (E := E)).coeFn_holder (r := 1) f g).trans
  exact ae_of_all μ (fun _ => rfl)

theorem innerClass_polarization (μ : Measure α) (f g : Lp E 2 μ) :
    innerClass μ f g = (1/4 : ℝ) • (normSquareClass μ (f+g)-normSquareClass μ (f-g)) := by
  apply Lp.ext
  filter_upwards [innerClass_coe μ f g,
    Lp.coeFn_smul (1/4 : ℝ) (normSquareClass μ (f+g)-normSquareClass μ (f-g)),
    Lp.coeFn_sub (normSquareClass μ (f+g)) (normSquareClass μ (f-g)),
    normSquareClass_coe μ (f+g),normSquareClass_coe μ (f-g),Lp.coeFn_add f g,Lp.coeFn_sub f g]
      with a hi hc hd hp hm ha hs
  simp only [Pi.smul_apply,smul_eq_mul,Pi.sub_apply,Pi.add_apply] at *
  rw [hi,hc,hd,hp,hm,ha,hs,← real_inner_self_eq_norm_sq,← real_inner_self_eq_norm_sq]
  rw [inner_add_left,inner_sub_left,inner_add_right,inner_add_right,inner_sub_right,inner_sub_right,
    real_inner_comm (g a) (f a)]
  ring
end NativeInner

variable (d : ℕ)

/-- Actual dt product of SAME original predictable representative inputs. -/
def crossEnergyIntegrand (T s : ℝ≥0) (f g : fullPredictableL2 d T) : ℝ × (Sample d) → ℝ :=
  (timeSet d T s).indicator (fun p => inner ℝ (representative d T f p) (representative d T g p))

theorem crossEnergyIntegrand_integrable (T s : ℝ≥0) (f g : fullPredictableL2 d T) :
    Integrable (crossEnergyIntegrand d T s f g) (inputLaw d T) := by
  have hi := L2.integrable_inner (𝕜 := ℝ)
    (f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T))
    (g : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T))
  apply (hi.congr ?_).indicator (timeSet_measurable d T s)
  filter_upwards [representative_ae d T f,representative_ae d T g] with p hf hg
  rw [hf,hg]

def crossTimeEnergy (T : ℝ≥0) (f g : fullPredictableL2 d T) (s : ℝ≥0) (ω : Sample d) : ℝ :=
  ∫ t, crossEnergyIntegrand d T s f g (t,ω) ∂timeLaw T

theorem crossTimeEnergy_integrable (T s : ℝ≥0) (f g : fullPredictableL2 d T) :
    Integrable (crossTimeEnergy d T f g s) (productLaw d) :=
  (crossEnergyIntegrand_integrable d T s f g).integral_prod_right

/-- Same actual native L1 target, constructed by actual time integration. -/
def crossEnergyClass (T s : ℝ≥0) (f g : fullPredictableL2 d T) : Lp ℝ 1 (productLaw d) :=
  timeMarginal d T (innerClass (inputLaw d T) (truncate d T s f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) (truncate d T s g : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)))

theorem crossEnergyClass_coe (T s : ℝ≥0) (f g : fullPredictableL2 d T) :
    crossEnergyClass d T s f g =ᵐ[(productLaw d)] crossTimeEnergy d T f g s := by
  have he : innerClass (inputLaw d T) (truncate d T s f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) (truncate d T s g : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) =ᵐ[inputLaw d T]
      crossEnergyIntegrand d T s f g := by
    filter_upwards [innerClass_coe (inputLaw d T) (truncate d T s f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) (truncate d T s g : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)),
      truncate_coe d T s f,truncate_coe d T s g,representative_ae d T f,representative_ae d T g]
      with p hp hf hg hrf hrg
    rw [hp,hf,hg]
    by_cases h : p ∈ timeSet d T s
    · simp only [Set.indicator_of_mem h,crossEnergyIntegrand,hrf,hrg]
    · simp only [Set.indicator_of_notMem h,crossEnergyIntegrand,inner_zero_left]
  have hs : ∀ᵐ ω ∂(productLaw d), (fun t => innerClass (inputLaw d T) (truncate d T s f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) (truncate d T s g : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) (t,ω))
      =ᵐ[timeLaw T] fun t => crossEnergyIntegrand d T s f g (t,ω) :=
    Measure.ae_ae_of_ae_prod ((Measure.measurePreserving_swap (μ := (productLaw d)) (ν := timeLaw T)).quasiMeasurePreserving.ae he)
  filter_upwards [timeMarginal_coe d T (innerClass (inputLaw d T) (truncate d T s f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) (truncate d T s g : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T))),hs]
    with ω hm hs
  exact hm.trans (integral_congr_ae hs)

theorem crossEnergyClass_polarization (T s : ℝ≥0) (f g : fullPredictableL2 d T) :
    crossEnergyClass d T s f g = (1/4 : ℝ) • (energyClass d T s (f+g)-energyClass d T s (f-g)) := by
  unfold crossEnergyClass
  rw [innerClass_polarization,map_smul,map_sub]
  simp only [energyClass_eq_marginal_normSquare,map_add,map_sub,Submodule.coe_add,Submodule.coe_sub]

/-- Actual native finite cross-increment sum of the two original integrals. -/
def gridCross (T : ℝ≥0) {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (f g : fullPredictableL2 d T) : Lp ℝ 1 (productLaw d) :=
  ∑ i : Fin n, productClass (productLaw d) (incrementAt d T (τ i.castSucc) (τ i.succ) f)
    (incrementAt d T (τ i.castSucc) (τ i.succ) g)

theorem gridCross_polarization (T : ℝ≥0) {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (f g : fullPredictableL2 d T) :
    gridCross d T τ f g = (1/4 : ℝ) • (gridSquares d T τ (f+g)-gridSquares d T τ (f-g)) := by
  simp only [gridCross,productClass_polarization,gridSquares,map_add,map_sub]
  rw [← Finset.smul_sum,Finset.sum_sub_distrib]

theorem gridCross_coe (T : ℝ≥0) {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (f g : fullPredictableL2 d T) :
    gridCross d T τ f g =ᵐ[(productLaw d)] fun ω => ∑ i : Fin n,
      (continuousIntegralProcess d T f (τ i.succ) ω-continuousIntegralProcess d T f (τ i.castSucc) ω)*
      (continuousIntegralProcess d T g (τ i.succ) ω-continuousIntegralProcess d T g (τ i.castSucc) ω) := by
  have hi : ∀ᵐ ω ∂(productLaw d), ∀ i : Fin n,
      productClass (productLaw d) (incrementAt d T (τ i.castSucc) (τ i.succ) f)
        (incrementAt d T (τ i.castSucc) (τ i.succ) g) ω =
      (continuousIntegralProcess d T f (τ i.succ) ω-continuousIntegralProcess d T f (τ i.castSucc) ω)*
      (continuousIntegralProcess d T g (τ i.succ) ω-continuousIntegralProcess d T g (τ i.castSucc) ω) := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [productClass_coe (productLaw d) (incrementAt d T (τ i.castSucc) (τ i.succ) f)
      (incrementAt d T (τ i.castSucc) (τ i.succ) g),
      incrementAt_coe d T (τ i.castSucc) (τ i.succ) f,incrementAt_coe d T (τ i.castSucc) (τ i.succ) g]
      with ω hp hf hg
    rw [hp,hf,hg]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin n => productClass (productLaw d)
    (incrementAt d T (τ i.castSucc) (τ i.succ) f) (incrementAt d T (τ i.castSucc) (τ i.succ) g)),hi]
    with ω hs hi
  simp only [Finset.sum_apply] at hs
  exact hs.trans (Finset.sum_congr rfl (fun i _ => hi i))

/-- Actual arbitrary deterministic vanishing-mesh cross variation of SAME
continuous integral outputs tends to SAME actual dt input-product energy. -/
theorem fullInput_partition_crossVariation (T : ℝ≥0) (N : ℕ → ℕ)
    (τ : (m : ℕ) → Fin (N m+1) → ℝ≥0) (hmono : ∀ m, Monotone (τ m))
    (hzero : ∀ m, τ m 0=0) (hend : ∀ m, τ m (Fin.last (N m))=T)
    (hmesh : Tendsto (fun m => (mesh (τ m) : ℝ)) atTop (𝓝 0)) (f g : fullPredictableL2 d T) :
    Tendsto (fun m => gridCross d T (τ m) f g) atTop (𝓝 (crossEnergyClass d T T f g)) := by
  simp_rw [gridCross_polarization,crossEnergyClass_polarization]
  exact ((fullInput_partition_QV d T N τ hmono hzero hend hmesh (f+g)).sub
    (fullInput_partition_QV d T N τ hmono hzero hend hmesh (f-g))).const_smul (1/4 : ℝ)

theorem fullInput_partition_crossVariation_inMeasure (T : ℝ≥0) (N : ℕ → ℕ)
    (τ : (m : ℕ) → Fin (N m+1) → ℝ≥0) (hmono : ∀ m, Monotone (τ m))
    (hzero : ∀ m, τ m 0=0) (hend : ∀ m, τ m (Fin.last (N m))=T)
    (hmesh : Tendsto (fun m => (mesh (τ m) : ℝ)) atTop (𝓝 0)) (f g : fullPredictableL2 d T) :
    TendstoInMeasure (productLaw d) (fun m ω => ∑ i : Fin (N m),
      (continuousIntegralProcess d T f (τ m i.succ) ω-continuousIntegralProcess d T f (τ m i.castSucc) ω)*
      (continuousIntegralProcess d T g (τ m i.succ) ω-continuousIntegralProcess d T g (τ m i.castSucc) ω))
      atTop (crossTimeEnergy d T f g T) :=
  TendstoInMeasure.congr (fun m => gridCross_coe d T (τ m) f g) (crossEnergyClass_coe d T T f g)
    (tendstoInMeasure_of_tendsto_Lp (fullInput_partition_crossVariation d T N τ hmono hzero hend hmesh f g))

/-- Actual fixed-time linearity of the SAME continuous versions, derived from
original continuous linear integral classes; no common uncountable AE intersection. -/
theorem continuousIntegralProcess_add_ae (T u : ℝ≥0) (f g : fullPredictableL2 d T) :
    continuousIntegralProcess d T (f+g) u =ᵐ[productLaw d]
      fun ω => continuousIntegralProcess d T f u ω+continuousIntegralProcess d T g u ω := by
  have ha := Lp.coeFn_add (integralAt d T u f) (integralAt d T u g)
  have hs : integralAt d T u (f+g) = integralAt d T u f+integralAt d T u g := map_add _ _ _
  have hf (h : fullPredictableL2 d T) : continuousIntegralProcess d T h u =ᵐ[productLaw d]
      (integralAt d T u h : Sample d → ℝ) :=
    (continuousIntegralProcess_eq_actual d T u h).trans (integralProcess_eq_truncated d T u h)
  rw [← hs] at ha
  filter_upwards [hf (f+g),hf f,hf g,ha] with ω hh hf hg ha
  exact hh.trans (ha.trans (congrArg₂ (fun x y : ℝ => x+y) hf.symm hg.symm))

theorem continuousIntegralProcess_sub_ae (T u : ℝ≥0) (f g : fullPredictableL2 d T) :
    continuousIntegralProcess d T (f-g) u =ᵐ[productLaw d]
      fun ω => continuousIntegralProcess d T f u ω-continuousIntegralProcess d T g u ω := by
  have ha := Lp.coeFn_sub (integralAt d T u f) (integralAt d T u g)
  have hs : integralAt d T u (f-g) = integralAt d T u f-integralAt d T u g := map_sub _ _ _
  have hf (h : fullPredictableL2 d T) : continuousIntegralProcess d T h u =ᵐ[productLaw d]
      (integralAt d T u h : Sample d → ℝ) :=
    (continuousIntegralProcess_eq_actual d T u h).trans (integralProcess_eq_truncated d T u h)
  rw [← hs] at ha
  filter_upwards [hf (f-g),hf f,hf g,ha] with ω hh hf hg ha
  exact hh.trans (ha.trans (congrArg₂ (fun x y : ℝ => x-y) hf.symm hg.symm))

/-- Original predictable inclusion gives genuine Fs permission for the real
cross integrand; proof-only clipping never changes its active support. -/
theorem crossEnergyIntegrand_stronglyMeasurable_past (T s : ℝ≥0) (f g : fullPredictableL2 d T) :
    StronglyMeasurable[MeasurableSpace.prod inferInstance (jointNaturalFiltration d s)] (crossEnergyIntegrand d T s f g) := by
  let : MeasurableSpace (Sample d) := jointNaturalFiltration d s
  let clip (t : ℝ) : Iic s := ⟨min (Real.toNNReal t) (min s T),by
    exact (min_le_right (Real.toNNReal t) (min s T)).trans (min_le_left s T)⟩
  have hc : Measurable clip := (measurable_id.real_toNNReal.min measurable_const).subtype_mk
  have hm (h : fullPredictableL2 d T) : StronglyMeasurable (fun p : ℝ × (Sample d) =>
      representative d T h (((clip p.1 : ℝ≥0) : ℝ),p.2)) :=
    ((representative_native_predictable d T h).isStronglyProgressive s).comp_measurable
      ((hc.comp measurable_fst).prodMk measurable_snd)
  have ht : MeasurableSet (timeSet d T s) := measurableSet_Ioc.prod MeasurableSet.univ
  have he : crossEnergyIntegrand d T s f g = (timeSet d T s).indicator
      (fun p : ℝ × (Sample d) => inner ℝ (representative d T f (((clip p.1 : ℝ≥0) : ℝ),p.2))
        (representative d T g (((clip p.1 : ℝ≥0) : ℝ),p.2))) := by
    ext p
    by_cases hp : p ∈ timeSet d T s
    · rw [crossEnergyIntegrand,Set.indicator_of_mem hp,Set.indicator_of_mem hp]
      have hn : Real.toNNReal p.1 ≤ min s T := (Real.toNNReal_le_iff_le_coe).mpr hp.1.2
      have heq : ((clip p.1 : ℝ≥0) : ℝ) = p.1 := by
        change ((min (Real.toNNReal p.1) (min s T) : ℝ≥0) : ℝ) = p.1
        rw [min_eq_left hn,Real.coe_toNNReal _ hp.1.1.le]
      rw [heq]
    · simp only [crossEnergyIntegrand,Set.indicator_of_notMem hp]
  rw [he]
  exact ((hm f).inner (hm g)).indicator ht

theorem crossTimeEnergy_stronglyAdapted (T : ℝ≥0) (f g : fullPredictableL2 d T) :
    StronglyAdapted (jointNaturalFiltration d) (crossTimeEnergy d T f g) := by
  intro s
  let : MeasurableSpace (Sample d) := jointNaturalFiltration d s
  exact (crossEnergyIntegrand_stronglyMeasurable_past d T s f g).integral_prod_left'
/-- Countably many fixed-time linearity identities and actual sample
continuity give addition of the SAME paths on ONE common full event. -/
theorem continuousIntegralProcess_add_path (T : ℝ≥0) (f g : fullPredictableL2 d T) :
    ∀ᵐ ω ∂productLaw d, ∀ u, continuousIntegralProcess d T (f+g) u ω =
      continuousIntegralProcess d T f u ω+continuousIntegralProcess d T g u ω := by
  have hd : ∀ᵐ ω ∂productLaw d, ∀ n, continuousIntegralProcess d T (f+g) (denseSeq ℝ≥0 n) ω =
      continuousIntegralProcess d T f (denseSeq ℝ≥0 n) ω+continuousIntegralProcess d T g (denseSeq ℝ≥0 n) ω :=
    ae_all_iff.mpr (fun n => continuousIntegralProcess_add_ae d T _ f g)
  filter_upwards [continuousIntegralProcess_continuous d T (f+g),
    continuousIntegralProcess_continuous d T f,continuousIntegralProcess_continuous d T g,hd] with ω ha hf hg hd
  exact congrFun ((denseRange_denseSeq ℝ≥0).equalizer ha (hf.add hg) (funext hd))

theorem continuousIntegralProcess_sub_path (T : ℝ≥0) (f g : fullPredictableL2 d T) :
    ∀ᵐ ω ∂productLaw d, ∀ u, continuousIntegralProcess d T (f-g) u ω =
      continuousIntegralProcess d T f u ω-continuousIntegralProcess d T g u ω := by
  have hd : ∀ᵐ ω ∂productLaw d, ∀ n, continuousIntegralProcess d T (f-g) (denseSeq ℝ≥0 n) ω =
      continuousIntegralProcess d T f (denseSeq ℝ≥0 n) ω-continuousIntegralProcess d T g (denseSeq ℝ≥0 n) ω :=
    ae_all_iff.mpr (fun n => continuousIntegralProcess_sub_ae d T _ f g)
  filter_upwards [continuousIntegralProcess_continuous d T (f-g),
    continuousIntegralProcess_continuous d T f,continuousIntegralProcess_continuous d T g,hd] with ω ha hf hg hd
  exact congrFun ((denseRange_denseSeq ℝ≥0).equalizer ha (hf.sub hg) (funext hd))

/-- Genuine integrability of the two original predictable representatives. -/
theorem representative_inner_integrable (T : ℝ≥0) (f g : fullPredictableL2 d T) :
    Integrable (fun p => inner ℝ (representative d T f p) (representative d T g p)) (inputLaw d T) := by
  have hi := L2.integrable_inner (𝕜 := ℝ)
    (f : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T))
    (g : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T))
  apply hi.congr
  filter_upwards [representative_ae d T f,representative_ae d T g] with p hf hg
  rw [hf,hg]

theorem crossTimeEnergy_eq_setIntegral (T s : ℝ≥0) (f g : fullPredictableL2 d T) (ω : Sample d) :
    crossTimeEnergy d T f g s ω = ∫ t in Ioc (0 : ℝ) (min s T : ℝ≥0),
      inner ℝ (representative d T f (t,ω)) (representative d T g (t,ω)) ∂timeLaw T := by
  unfold crossTimeEnergy
  have he : (fun t => crossEnergyIntegrand d T s f g (t,ω)) =
      (Ioc (0 : ℝ) (min s T : ℝ≥0)).indicator
        (fun t => inner ℝ (representative d T f (t,ω)) (representative d T g (t,ω))) := by
    ext t
    have hm : (t,ω)∈timeSet d T s ↔ t∈Ioc (0 : ℝ) (min s T : ℝ≥0) := by
      simp only [timeSet,mem_prod,mem_univ,and_true]
    by_cases ht : t ∈ Ioc (0 : ℝ) (min s T : ℝ≥0)
    · rw [crossEnergyIntegrand,Set.indicator_of_mem (hm.mpr ht),Set.indicator_of_mem ht]
    · rw [crossEnergyIntegrand,Set.indicator_of_notMem (fun h=>ht (hm.mp h)),Set.indicator_of_notMem ht]
  rw [he,integral_indicator measurableSet_Ioc]

/-- One Fubini section event gives actual ALL-time continuity; no
uncountable family of exceptional sets is intersected. -/
theorem crossTimeEnergy_continuous_ae (T : ℝ≥0) (f g : fullPredictableL2 d T) :
    ∀ᵐ ω ∂productLaw d, Continuous (fun s => crossTimeEnergy d T f g s ω) := by
  filter_upwards [(representative_inner_integrable d T f g).prod_left_ae] with ω hω
  let : NullSingletonClass (timeLaw T) := by unfold timeLaw; infer_instance
  have hc := hω.continuous_primitive (0 : ℝ)
  have ht : Continuous (fun s : ℝ≥0 => ((min s T : ℝ≥0) : ℝ)) :=
    continuous_subtype_val.comp (continuous_id.min continuous_const)
  convert hc.comp ht using 1
  ext s
  rw [Function.comp_apply,crossTimeEnergy_eq_setIntegral,intervalIntegral.integral_of_le (min s T).coe_nonneg]

theorem crossTimeEnergy_zero (T : ℝ≥0) (f g : fullPredictableL2 d T) :
    crossTimeEnergy d T f g 0 = 0 := by
  ext ω
  simp [crossTimeEnergy,crossEnergyIntegrand,timeSet]

/-- Native bilinearity and the actual original cutoff derive scaling, with
no change to the supplied input class or underlying source. -/
theorem crossEnergyClass_smul_right (T s : ℝ≥0) (f g : fullPredictableL2 d T) (c : ℝ) :
    crossEnergyClass d T s f (c • g) = c • crossEnergyClass d T s f g := by
  simp only [crossEnergyClass,innerClass,map_smul,Submodule.coe_smul]

theorem crossEnergyClass_self (T s : ℝ≥0) (f : fullPredictableL2 d T) :
    crossEnergyClass d T s f f = energyClass d T s f := by
  rw [energyClass_eq_marginal_normSquare]
  rfl

theorem crossTimeEnergy_self (T s : ℝ≥0) (f : fullPredictableL2 d T) :
    crossTimeEnergy d T f f s = timeEnergy d T f s := by
  ext ω
  simp only [crossTimeEnergy,timeEnergy,crossEnergyIntegrand,energyIntegrand,real_inner_self_eq_norm_sq]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorCrossPartitionQV
