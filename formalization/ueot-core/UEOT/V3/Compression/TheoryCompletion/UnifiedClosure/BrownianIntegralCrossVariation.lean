import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianPartitionQV

/-!
Original commitment: actual Ito consumers need cross variation of actual integral outputs, not only individual square brackets.
Existing result: full original predictable L2 QV on arbitrary caller clocks and native Holder/time-marginal maps.
Premise reduced: derive actual cross-increment limit and identify its target with SAME-source dt integral of original input products.
Model/witness: TWO original fullPredictableL2 T inputs on SAME scalar Brownian source, no L4 or new source field.
Consumer: scalar integration-by-parts/C2 cross terms; vector-source construction and general Ito/Girsanov remain separate.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralCrossVariation
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianTimeIntegrand BrownianPredictableInputs BrownianPredictableDensity
open BrownianIntegralTimeTruncation BrownianIntegralContinuousVersion BrownianIntegralSquareL1
open BrownianIntegralTimeEnergy BrownianIntegralEnergyL1 BrownianIntegralGridL1 BrownianQuadraticVariation BrownianPartitionQV
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- Actual same-measure native Holder product, with natural L1 scale. -/
def productClass {α : Type*} [MeasurableSpace α] (μ : Measure α) (f g : Lp ℝ 2 μ) : Lp ℝ 1 μ :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL μ 2 2 1 f g

theorem productClass_coe {α : Type*} [MeasurableSpace α] (μ : Measure α) (f g : Lp ℝ 2 μ) :
    productClass μ f g =ᵐ[μ] fun x => f x*g x := by
  simp only [productClass,ContinuousLinearMap.holderL_apply_apply]
  simpa only [ContinuousLinearMap.mul_apply'] using (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 1) f g

theorem productClass_polarization {α : Type*} [MeasurableSpace α] (μ : Measure α) (f g : Lp ℝ 2 μ) :
    productClass μ f g = (1/4 : ℝ) • (squareClass μ (f+g)-squareClass μ (f-g)) := by
  apply Lp.ext
  filter_upwards [productClass_coe μ f g,
    Lp.coeFn_smul (1/4 : ℝ) (squareClass μ (f+g)-squareClass μ (f-g)),
    Lp.coeFn_sub (squareClass μ (f+g)) (squareClass μ (f-g)),
    squareClass_coe μ (f+g),squareClass_coe μ (f-g),Lp.coeFn_add f g,Lp.coeFn_sub f g]
    with x hp hsm hdiff hadd hsub ha hs
  simp only [Pi.smul_apply,smul_eq_mul,Pi.sub_apply,Pi.add_apply] at *
  rw [hp,hsm,hdiff,hadd,hsub,ha,hs]
  ring

/-- Actual dt product of SAME original predictable representative inputs. -/
def crossEnergyIntegrand (T s : ℝ≥0) (f g : fullPredictableL2 T) : ℝ × (ℝ≥0 → ℝ) → ℝ :=
  (timeSet T s).indicator (fun p => representative T f p*representative T g p)

theorem crossEnergyIntegrand_integrable (T s : ℝ≥0) (f g : fullPredictableL2 T) :
    Integrable (crossEnergyIntegrand T s f g) (inputLaw T) :=
  ((representative_memLp_two T f).integrable_mul (representative_memLp_two T g)).indicator
    (timeSet_measurable T s)

def crossTimeEnergy (T : ℝ≥0) (f g : fullPredictableL2 T) (s : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ :=
  ∫ t, crossEnergyIntegrand T s f g (t,ω) ∂timeLaw T

theorem crossTimeEnergy_integrable (T s : ℝ≥0) (f g : fullPredictableL2 T) :
    Integrable (crossTimeEnergy T f g s) sourceLaw :=
  (crossEnergyIntegrand_integrable T s f g).integral_prod_right

/-- Same actual native L1 target, constructed by actual time integration. -/
def crossEnergyClass (T s : ℝ≥0) (f g : fullPredictableL2 T) : Lp ℝ 1 sourceLaw :=
  timeMarginal T (productClass (inputLaw T) (truncate T s f) (truncate T s g))

theorem crossEnergyClass_coe (T s : ℝ≥0) (f g : fullPredictableL2 T) :
    crossEnergyClass T s f g =ᵐ[sourceLaw] crossTimeEnergy T f g s := by
  have he : productClass (inputLaw T) (truncate T s f) (truncate T s g) =ᵐ[inputLaw T]
      crossEnergyIntegrand T s f g := by
    filter_upwards [productClass_coe (inputLaw T) (truncate T s f) (truncate T s g),
      truncate_coe T s f,truncate_coe T s g,representative_ae T f,representative_ae T g]
      with p hp hf hg hrf hrg
    rw [hp,hf,hg]
    by_cases h : p ∈ timeSet T s
    · simp only [Set.indicator_of_mem h,crossEnergyIntegrand,hrf,hrg]
    · simp only [Set.indicator_of_notMem h,crossEnergyIntegrand,zero_mul]
  have hs : ∀ᵐ ω ∂sourceLaw, (fun t => productClass (inputLaw T) (truncate T s f) (truncate T s g) (t,ω))
      =ᵐ[timeLaw T] fun t => crossEnergyIntegrand T s f g (t,ω) :=
    Measure.ae_ae_of_ae_prod ((Measure.measurePreserving_swap (μ := sourceLaw) (ν := timeLaw T)).quasiMeasurePreserving.ae he)
  filter_upwards [timeMarginal_coe T (productClass (inputLaw T) (truncate T s f) (truncate T s g)),hs]
    with ω hm hs
  exact hm.trans (integral_congr_ae hs)

theorem crossEnergyClass_polarization (T s : ℝ≥0) (f g : fullPredictableL2 T) :
    crossEnergyClass T s f g = (1/4 : ℝ) • (energyClass T s (f+g)-energyClass T s (f-g)) := by
  unfold crossEnergyClass
  rw [productClass_polarization,map_smul,map_sub]
  simp only [energyClass_eq_marginal_square,map_add,map_sub,Submodule.coe_add,Submodule.coe_sub]

/-- Actual native finite cross-increment sum of the two original integrals. -/
def gridCross (T : ℝ≥0) {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (f g : fullPredictableL2 T) : Lp ℝ 1 sourceLaw :=
  ∑ i : Fin n, productClass sourceLaw (incrementAt T (τ i.castSucc) (τ i.succ) f)
    (incrementAt T (τ i.castSucc) (τ i.succ) g)

theorem gridCross_polarization (T : ℝ≥0) {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (f g : fullPredictableL2 T) :
    gridCross T τ f g = (1/4 : ℝ) • (gridSquares T τ (f+g)-gridSquares T τ (f-g)) := by
  simp only [gridCross,productClass_polarization,gridSquares,map_add,map_sub]
  rw [← Finset.smul_sum,Finset.sum_sub_distrib]

private theorem lp_sum_coe {ι : Type*} (s : Finset ι) (F : ι → Lp ℝ 1 sourceLaw) :
    (∑ i ∈ s, F i : Lp ℝ 1 sourceLaw) =ᵐ[sourceLaw] fun ω => ∑ i ∈ s, F i ω := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℝ 1 sourceLaw] with ω hω
    simp only [Finset.sum_empty]
    exact hω
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (F i) (∑ j ∈ s, F j),ih] with ω ha hs
    simp only [Pi.add_apply] at ha
    rw [ha,hs]

theorem gridCross_coe (T : ℝ≥0) {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (f g : fullPredictableL2 T) :
    gridCross T τ f g =ᵐ[sourceLaw] fun ω => ∑ i : Fin n,
      (continuousIntegralProcess T f (τ i.succ) ω-continuousIntegralProcess T f (τ i.castSucc) ω)*
      (continuousIntegralProcess T g (τ i.succ) ω-continuousIntegralProcess T g (τ i.castSucc) ω) := by
  have hi : ∀ᵐ ω ∂sourceLaw, ∀ i : Fin n,
      productClass sourceLaw (incrementAt T (τ i.castSucc) (τ i.succ) f)
        (incrementAt T (τ i.castSucc) (τ i.succ) g) ω =
      (continuousIntegralProcess T f (τ i.succ) ω-continuousIntegralProcess T f (τ i.castSucc) ω)*
      (continuousIntegralProcess T g (τ i.succ) ω-continuousIntegralProcess T g (τ i.castSucc) ω) := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [productClass_coe sourceLaw (incrementAt T (τ i.castSucc) (τ i.succ) f)
      (incrementAt T (τ i.castSucc) (τ i.succ) g),
      incrementAt_coe T (τ i.castSucc) (τ i.succ) f,incrementAt_coe T (τ i.castSucc) (τ i.succ) g]
      with ω hp hf hg
    rw [hp,hf,hg]
  filter_upwards [lp_sum_coe Finset.univ (fun i : Fin n => productClass sourceLaw
    (incrementAt T (τ i.castSucc) (τ i.succ) f) (incrementAt T (τ i.castSucc) (τ i.succ) g)),hi]
    with ω hs hi
  exact hs.trans (Finset.sum_congr rfl (fun i _ => hi i))

/-- Actual arbitrary deterministic vanishing-mesh cross variation of SAME
continuous integral outputs tends to SAME actual dt input-product energy. -/
theorem fullInput_partition_crossVariation (T : ℝ≥0) (N : ℕ → ℕ)
    (τ : (m : ℕ) → Fin (N m+1) → ℝ≥0) (hmono : ∀ m, Monotone (τ m))
    (hzero : ∀ m, τ m 0=0) (hend : ∀ m, τ m (Fin.last (N m))=T)
    (hmesh : Tendsto (fun m => (mesh (τ m) : ℝ)) atTop (𝓝 0)) (f g : fullPredictableL2 T) :
    Tendsto (fun m => gridCross T (τ m) f g) atTop (𝓝 (crossEnergyClass T T f g)) := by
  simp_rw [gridCross_polarization,crossEnergyClass_polarization]
  exact ((fullInput_partition_QV T N τ hmono hzero hend hmesh (f+g)).sub
    (fullInput_partition_QV T N τ hmono hzero hend hmesh (f-g))).const_smul (1/4 : ℝ)

theorem fullInput_partition_crossVariation_inMeasure (T : ℝ≥0) (N : ℕ → ℕ)
    (τ : (m : ℕ) → Fin (N m+1) → ℝ≥0) (hmono : ∀ m, Monotone (τ m))
    (hzero : ∀ m, τ m 0=0) (hend : ∀ m, τ m (Fin.last (N m))=T)
    (hmesh : Tendsto (fun m => (mesh (τ m) : ℝ)) atTop (𝓝 0)) (f g : fullPredictableL2 T) :
    TendstoInMeasure sourceLaw (fun m ω => ∑ i : Fin (N m),
      (continuousIntegralProcess T f (τ m i.succ) ω-continuousIntegralProcess T f (τ m i.castSucc) ω)*
      (continuousIntegralProcess T g (τ m i.succ) ω-continuousIntegralProcess T g (τ m i.castSucc) ω))
      atTop (crossTimeEnergy T f g T) :=
  TendstoInMeasure.congr (fun m => gridCross_coe T (τ m) f g) (crossEnergyClass_coe T T f g)
    (tendstoInMeasure_of_tendsto_Lp (fullInput_partition_crossVariation T N τ hmono hzero hend hmesh f g))

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralCrossVariation
