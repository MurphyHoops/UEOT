import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteStateTaylorRemainder

/-!
Original commitment: P11 finite-dimensional consumers need Itô on actual SAME-source state, not an external chain-rule certificate.
Existing result: actual Euclidean finite integral state, real START integral and state-weighted cross-QV limits, and C2 Taylor remainder.
Premise reduced: assemble actual original derivative-generated input and actual Hessian/dt energy into the same-state Itô identity.
Model/witness: original full joint-predictable input family, finite state/noise dimensions, C2 observable with explicit global derivative/Hessian bounds for native L2 permission.
Consumer: actual bounded-derivative finite-state Itô; unbounded-C2 localization, added state drift and general SDE remain separate.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteStateItoSource
open MeasureTheory ProbabilityTheory Set Filter
open BrownianFiniteProductSource BrownianVectorTimeInput BrownianVectorPredictableInputs BrownianVectorPredictableDensity
open BrownianVectorIntegralContinuousVersion BrownianVectorFiniteStateCrossQV BrownianVectorPredictableMultiplier
open BrownianVectorLeftMultiplierBinding BrownianVectorWeightedCrossQV BrownianFiniteStateTaylorRemainder BrownianQuadraticVariation
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

def basisVector (j : Fin m) : E := EuclideanSpace.single j 1

theorem basisVector_norm (j : Fin m) : ‖basisVector j‖=1 := by simp [basisVector,PiLp.norm_single]

theorem basis_decomposition (x : E) : x=∑ j,x j • basisVector j := by
  ext k
  simp [basisVector,Pi.single_apply,Finset.sum_apply]

def gradientEntry (φ : E→ℝ) (j : Fin m) (x : E) : ℝ := fderiv ℝ φ x (basisVector j)
def hessianEntry (φ : E→ℝ) (j k : Fin m) (x : E) : ℝ := hessian φ x (basisVector j) (basisVector k)

theorem gradientEntry_continuous (φ : E→ℝ) (hφ : ContDiff ℝ 2 φ) (j : Fin m) : Continuous (gradientEntry φ j) :=
  (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem hessianEntry_continuous (φ : E→ℝ) (hφ : ContDiff ℝ 2 φ) (j k : Fin m) : Continuous (hessianEntry φ j k) :=
  ((hessian_continuous φ hφ).clm_apply continuous_const).clm_apply continuous_const

theorem gradientEntry_bound (φ : E→ℝ) (K : ℝ) (hb : ∀ x,‖fderiv ℝ φ x‖≤K) (j : Fin m) (x : E) :
    ‖gradientEntry φ j x‖≤K := by
  exact ((fderiv ℝ φ x).le_opNorm (basisVector j)).trans (by simpa only [basisVector_norm,mul_one] using hb x)

theorem hessianEntry_bound (φ : E→ℝ) (K : ℝ) (hb : ∀ x,‖hessian φ x‖≤K) (j k : Fin m) (x : E) :
    ‖hessianEntry φ j k x‖≤K := by
  calc
    _ ≤ ‖hessian φ x (basisVector j)‖*‖basisVector k‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (‖hessian φ x‖*‖basisVector j‖)*‖basisVector k‖ := by gcongr; exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ K := by simpa only [basisVector_norm,mul_one] using hb x

/-- Actual derivative terms in the true native Euclidean coordinates. -/
theorem derivative_coordinates (φ : E→ℝ) (x v : E) :
    fderiv ℝ φ x v = ∑ j,gradientEntry φ j x*v j := by
  conv_lhs => rw [basis_decomposition v]
  simp only [map_sum,map_smul,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem hessian_coordinates (φ : E→ℝ) (x v : E) :
    hessian φ x v v = ∑ j,∑ k,hessianEntry φ j k x*v j*v k := by
  calc
    _ = ∑ j,v j*(hessian φ x (basisVector j) v) := by
      conv_lhs => arg 1; arg 2; rw [basis_decomposition v]
      simp only [map_sum,map_smul,sum_apply,smul_apply,smul_eq_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      conv_lhs => arg 2; rw [basis_decomposition v]
      simp only [map_sum,map_smul,smul_eq_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      unfold hessianEntry
      ring

def firstSum (φ : E→ℝ) {n : ℕ} (τ : Fin (n+1)→ℝ≥0) (X : ℝ≥0→E) : ℝ :=
  ∑ j,∑ i : Fin n,gradientEntry φ j (X (τ i.castSucc))*(X (τ i.succ) j-X (τ i.castSucc) j)

def secondSum (φ : E→ℝ) {n : ℕ} (τ : Fin (n+1)→ℝ≥0) (X : ℝ≥0→E) : ℝ :=
  ∑ j,∑ k,∑ i : Fin n,hessianEntry φ j k (X (τ i.castSucc))*
    (X (τ i.succ) j-X (τ i.castSucc) j)*(X (τ i.succ) k-X (τ i.castSucc) k)

/-- Literal finite Taylor identity, before any stochastic limiting step. -/
theorem finite_taylor_telescope (φ : E→ℝ) {n : ℕ} (τ : Fin (n+1)→ℝ≥0) (X : ℝ≥0→E) :
    φ (X (τ (Fin.last n)))-φ (X (τ 0)) =
      firstSum φ τ X+(1/2 : ℝ)*secondSum φ τ X+remainderSum φ τ X := by
  have h0 := Fin.sum_univ_succ (fun j : Fin (n+1)=>φ (X (τ j)))
  have hN := Fin.sum_univ_castSucc (fun j : Fin (n+1)=>φ (X (τ j)))
  have htel : (∑ i : Fin n,(φ (X (τ i.succ))-φ (X (τ i.castSucc)))) = φ (X (τ (Fin.last n)))-φ (X (τ 0)) := by
    rw [Finset.sum_sub_distrib]
    linarith
  have hfirst : firstSum φ τ X = ∑ i : Fin n,fderiv ℝ φ (X (τ i.castSucc)) (X (τ i.succ)-X (τ i.castSucc)) := by
    simp only [firstSum,derivative_coordinates,PiLp.sub_apply]
    rw [Finset.sum_comm]
  have hsecond : secondSum φ τ X = ∑ i : Fin n,hessian φ (X (τ i.castSucc))
      (X (τ i.succ)-X (τ i.castSucc)) (X (τ i.succ)-X (τ i.castSucc)) := by
    simp only [secondSum,hessian_coordinates,PiLp.sub_apply]
    let A (i : Fin n) (j k : Fin m) := hessianEntry φ j k (X (τ i.castSucc))*
      (X (τ i.succ) j-X (τ i.castSucc) j)*(X (τ i.succ) k-X (τ i.castSucc) k)
    change (∑ j,∑ k,∑ i,A i j k)=(∑ i,∑ j,∑ k,A i j k)
    calc
      _ = ∑ j,∑ i,∑ k,A i j k := Finset.sum_congr rfl (fun j _=>Finset.sum_comm)
      _ = _ := Finset.sum_comm
  rw [hfirst,hsecond]
  symm
  unfold remainderSum
  rw [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  calc
    _ = ∑ i : Fin n,(φ (X (τ i.succ))-φ (X (τ i.castSucc))) := by
      apply Finset.sum_congr rfl
      intro i _
      unfold secondRemainder
      ring
    _ = _ := htel
variable (d : ℕ) (T : ℝ≥0)

private def readout (family : Fin m→fullPredictableL2 d T) (F : E→ℝ) (u : ℝ≥0) (ω : Sample d) : ℝ :=
  F (stateProcess d T family u ω)

private theorem readout_measurable (family : Fin m→fullPredictableL2 d T) (F : E→ℝ) (hF : Continuous F) :
    Measurable (Function.uncurry (readout d T family F)) := hF.measurable.comp (stateProcess_measurable d T family)

private theorem readout_adapted (family : Fin m→fullPredictableL2 d T) (F : E→ℝ) (hF : Continuous F) :
    StronglyAdapted (jointNaturalFiltration d) (readout d T family F) :=
  fun u=>hF.comp_stronglyMeasurable (stateProcess_stronglyAdapted d T family u)

private theorem readout_continuous (family : Fin m→fullPredictableL2 d T) (F : E→ℝ) (hF : Continuous F) :
    ∀ᵐ ω ∂productLaw d,Continuous (fun u=>readout d T family F u ω) :=
  (stateProcess_continuous d T family).mono (fun _ h=>hF.comp h)

private theorem source_sum_coe {ι : Type*} [Fintype ι] {p : ℝ≥0∞} [Fact (1≤p)] (F : ι→Lp ℝ p (productLaw d)) :
    (∑ i,F i : Lp ℝ p (productLaw d)) =ᵐ[productLaw d] fun ω=>∑ i,F i ω := by
  filter_upwards [Lp.coeFn_finsetSum Finset.univ F] with ω hs
  simpa only [Finset.sum_apply] using hs

/-- One original full input, generated literally from the original derivative
and original supplied state/input family, rather than a chosen Ito output. -/
def itoInput (family : Fin m→fullPredictableL2 d T) (φ : E→ℝ) (hφ : ContDiff ℝ 2 φ)
    (K : ℝ) (hb : ∀ x,‖fderiv ℝ φ x‖≤K) : fullPredictableL2 d T :=
  ∑ j,functionOfStateInput d T family (gradientEntry φ j) (gradientEntry_continuous φ hφ j)
    K (gradientEntry_bound φ K hb j) (family j)

/-- Exact SAME original input readout of the derivative-generated Ito input. -/
theorem itoInput_coe (family : Fin m→fullPredictableL2 d T) (φ : E→ℝ) (hφ : ContDiff ℝ 2 φ)
    (K : ℝ) (hb : ∀ x,‖fderiv ℝ φ x‖≤K) :
    (itoInput d T family φ hφ K hb : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) =ᵐ[inputLaw d T]
      fun p=>∑ j,gradientEntry φ j (stateProcess d T family (Real.toNNReal p.1) p.2) •
        (family j : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) p := by
  let V (j : Fin m) := functionOfStateInput d T family (gradientEntry φ j) (gradientEntry_continuous φ hφ j)
    K (gradientEntry_bound φ K hb j) (family j)
  change (∑ j,V j : fullPredictableL2 d T).val =ᵐ[inputLaw d T] _
  simp only [Submodule.coe_sum]
  have hi : ∀ᵐ p ∂inputLaw d T,∀ j,(V j : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) p =
      gradientEntry φ j (stateProcess d T family (Real.toNNReal p.1) p.2) •
        (family j : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) p :=
    ae_all_iff.mpr (fun j=>functionOfStateInput_coe d T family _ _ K _ (family j))
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun j=>(V j : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T))),hi]
    with p hs hi
  simp only [Finset.sum_apply] at hs
  exact hs.trans (Finset.sum_congr rfl (fun j _=>hi j))

private def sampledItoInput (family : Fin m→fullPredictableL2 d T) (φ : E→ℝ) (hφ : ContDiff ℝ 2 φ)
    (K : ℝ) (hb : ∀ x,‖fderiv ℝ φ x‖≤K) {n : ℕ} (τ : Fin (n+1)→ℝ≥0) (hm : Monotone τ) : fullPredictableL2 d T :=
  ∑ j,sampledMultiplier d T τ hm (readout d T family (gradientEntry φ j))
    (readout_adapted d T family _ (gradientEntry_continuous φ hφ j))
    K ((norm_nonneg (fderiv ℝ φ 0)).trans (hb 0)) (fun _ _=>gradientEntry_bound φ K hb j _) (family j)

private theorem firstSum_class_coe (family : Fin m→fullPredictableL2 d T) (φ : E→ℝ) (hφ : ContDiff ℝ 2 φ)
    (K : ℝ) (hb : ∀ x,‖fderiv ℝ φ x‖≤K) {n : ℕ} (τ : Fin (n+1)→ℝ≥0) (hm : Monotone τ) :
    (predictableIntegral d T (sampledItoInput d T family φ hφ K hb τ hm) : Sample d→ℝ) =ᵐ[productLaw d]
      fun ω=>firstSum φ τ (fun u=>stateProcess d T family u ω) := by
  unfold sampledItoInput
  rw [map_sum]
  have hi : ∀ᵐ ω ∂productLaw d,∀ j : Fin m,
      (predictableIntegral d T (sampledMultiplier d T τ hm (readout d T family (gradientEntry φ j))
        (readout_adapted d T family _ (gradientEntry_continuous φ hφ j)) K
        ((norm_nonneg (fderiv ℝ φ 0)).trans (hb 0)) (fun _ _=>gradientEntry_bound φ K hb j _) (family j)) : Sample d→ℝ) ω =
      weightedIncrementSum d T τ (readout d T family (gradientEntry φ j)) (family j) ω :=
    ae_all_iff.mpr (fun j=>sampledMultiplier_integral_coe d T τ hm _ _ _ _ _ _)
  filter_upwards [source_sum_coe d (fun j=>predictableIntegral d T (sampledMultiplier d T τ hm
    (readout d T family (gradientEntry φ j)) (readout_adapted d T family _ (gradientEntry_continuous φ hφ j)) K
      ((norm_nonneg (fderiv ℝ φ 0)).trans (hb 0)) (fun _ _=>gradientEntry_bound φ K hb j _) (family j))),hi] with ω hs hi
  exact hs.trans (Finset.sum_congr rfl (fun j _=>hi j))

variable (N : ℕ→ℕ) (τ : (n : ℕ)→Fin (N n+1)→ℝ≥0) (hm : ∀ n,Monotone (τ n))
  (h0 : ∀ n,τ n 0=0) (hT : ∀ n,τ n (Fin.last (N n))=T)
  (hmesh : Tendsto (fun n=>(mesh (τ n) : ℝ)) atTop (𝓝 0))
include hm h0 hT hmesh

private theorem firstSum_tendstoInMeasure (family : Fin m→fullPredictableL2 d T) (φ : E→ℝ) (hφ : ContDiff ℝ 2 φ)
    (K : ℝ) (hb : ∀ x,‖fderiv ℝ φ x‖≤K) :
    TendstoInMeasure (productLaw d) (fun n ω=>firstSum φ (τ n) (fun u=>stateProcess d T family u ω)) atTop
      (continuousIntegralProcess d T (itoInput d T family φ hφ K hb) T) := by
  have hL : Tendsto (fun n=>sampledItoInput d T family φ hφ K hb (τ n) (hm n)) atTop
      (𝓝 (itoInput d T family φ hφ K hb)) := by
    apply tendsto_finsetSum
    intro j _
    exact sampledMultiplier_tendsto d T N τ hm h0 hT hmesh _
      (readout_measurable d T family _ (gradientEntry_continuous φ hφ j))
      (readout_adapted d T family _ (gradientEntry_continuous φ hφ j))
      (readout_continuous d T family _ (gradientEntry_continuous φ hφ j))
      K ((norm_nonneg (fderiv ℝ φ 0)).trans (hb 0)) (fun _ _=>gradientEntry_bound φ K hb j _) (family j)
  exact TendstoInMeasure.congr (fun n=>firstSum_class_coe d T family φ hφ K hb (τ n) (hm n))
    (continuousIntegralProcess_horizon d T _).symm
    (tendstoInMeasure_of_tendsto_Lp (((predictableIntegral d T).continuous.tendsto _).comp hL))

/-- Literal original dt Hessian energy on SAME state and supplied inputs. -/
def itoSecondEnergy (family : Fin m→fullPredictableL2 d T) (φ : E→ℝ) (ω : Sample d) : ℝ :=
  ∑ j,∑ k,BrownianVectorWeightedCrossQV.weightedTimeEnergy d T
    (readout d T family (hessianEntry φ j k)) (family j) (family k) ω

private def secondGridClass (family : Fin m→fullPredictableL2 d T) (φ : E→ℝ) (hφ : ContDiff ℝ 2 φ)
    (K : ℝ) (hb : ∀ x,‖hessian φ x‖≤K) {n : ℕ} (σ : Fin (n+1)→ℝ≥0) (hs : Monotone σ) : Lp ℝ 1 (productLaw d) :=
  ∑ j,∑ k,BrownianVectorCrossPartitionQV.gridCross d T σ (family j)
    (sampledMultiplier d T σ hs (readout d T family (hessianEntry φ j k))
      (readout_adapted d T family _ (hessianEntry_continuous φ hφ j k)) K
      ((norm_nonneg (hessian φ 0)).trans (hb 0)) (fun _ _=>hessianEntry_bound φ K hb j k _) (family k))

private def secondEnergyClass (family : Fin m→fullPredictableL2 d T) (φ : E→ℝ) (hφ : ContDiff ℝ 2 φ)
    (K : ℝ) (hb : ∀ x,‖hessian φ x‖≤K) : Lp ℝ 1 (productLaw d) :=
  ∑ j,∑ k,BrownianVectorWeightedCrossQV.weightedEnergyClass d T (readout d T family (hessianEntry φ j k))
    (readout_measurable d T family _ (hessianEntry_continuous φ hφ j k)) K
    (fun _ _=>hessianEntry_bound φ K hb j k _) (family j) (family k)

omit hm h0 hT hmesh in
private theorem secondGridClass_coe (family : Fin m→fullPredictableL2 d T) (φ : E→ℝ) (hφ : ContDiff ℝ 2 φ)
    (K : ℝ) (hb : ∀ x,‖hessian φ x‖≤K) {n : ℕ} (σ : Fin (n+1)→ℝ≥0) (hs : Monotone σ) :
    secondGridClass d T family φ hφ K hb σ hs =ᵐ[productLaw d]
      fun ω=>secondSum φ σ (fun u=>stateProcess d T family u ω) := by
  let Q (j k : Fin m) := BrownianVectorCrossPartitionQV.gridCross d T σ (family j)
    (sampledMultiplier d T σ hs (readout d T family (hessianEntry φ j k))
      (readout_adapted d T family _ (hessianEntry_continuous φ hφ j k)) K
      ((norm_nonneg (hessian φ 0)).trans (hb 0)) (fun _ _=>hessianEntry_bound φ K hb j k _) (family k))
  have hi : ∀ᵐ ω ∂productLaw d,∀ j k,Q j k ω=
      weightedCrossSum d T σ (readout d T family (hessianEntry φ j k)) (family j) (family k) ω :=
    ae_all_iff.mpr (fun j=>ae_all_iff.mpr (fun k=>gridCross_sampled_coe d T σ hs _ _ K _ _ _ _))
  have hiSum : ∀ᵐ ω ∂productLaw d,∀ j,(∑ k,Q j k : Lp ℝ 1 (productLaw d)) ω=∑ k,Q j k ω :=
    ae_all_iff.mpr (fun j=>source_sum_coe d (Q j))
  filter_upwards [source_sum_coe d (fun j=>∑ k,Q j k),hiSum,hi] with ω ho hs hi
  exact ho.trans (Finset.sum_congr rfl (fun j _=>(hs j).trans (Finset.sum_congr rfl (fun k _=>hi j k))))

omit hm h0 hT hmesh in
private theorem secondEnergyClass_coe (family : Fin m→fullPredictableL2 d T) (φ : E→ℝ) (hφ : ContDiff ℝ 2 φ)
    (K : ℝ) (hb : ∀ x,‖hessian φ x‖≤K) :
    secondEnergyClass d T family φ hφ K hb =ᵐ[productLaw d] itoSecondEnergy d T family φ := by
  let Q (j k : Fin m) := BrownianVectorWeightedCrossQV.weightedEnergyClass d T (readout d T family (hessianEntry φ j k))
    (readout_measurable d T family _ (hessianEntry_continuous φ hφ j k)) K
    (fun _ _=>hessianEntry_bound φ K hb j k _) (family j) (family k)
  have hi : ∀ᵐ ω ∂productLaw d,∀ j k,Q j k ω=
      BrownianVectorWeightedCrossQV.weightedTimeEnergy d T (readout d T family (hessianEntry φ j k)) (family j) (family k) ω :=
    ae_all_iff.mpr (fun j=>ae_all_iff.mpr (fun k=>weightedEnergyClass_coe d T _ _ K _ _ _))
  have hiSum : ∀ᵐ ω ∂productLaw d,∀ j,(∑ k,Q j k : Lp ℝ 1 (productLaw d)) ω=∑ k,Q j k ω :=
    ae_all_iff.mpr (fun j=>source_sum_coe d (Q j))
  filter_upwards [source_sum_coe d (fun j=>∑ k,Q j k),hiSum,hi] with ω ho hs hi
  exact ho.trans (Finset.sum_congr rfl (fun j _=>(hs j).trans (Finset.sum_congr rfl (fun k _=>hi j k))))

private theorem secondSum_tendstoInMeasure (family : Fin m→fullPredictableL2 d T) (φ : E→ℝ) (hφ : ContDiff ℝ 2 φ)
    (K : ℝ) (hb : ∀ x,‖hessian φ x‖≤K) :
    TendstoInMeasure (productLaw d) (fun n ω=>secondSum φ (τ n) (fun u=>stateProcess d T family u ω)) atTop
      (itoSecondEnergy d T family φ) := by
  have hL : Tendsto (fun n=>secondGridClass d T family φ hφ K hb (τ n) (hm n)) atTop
      (𝓝 (secondEnergyClass d T family φ hφ K hb)) := by
    apply tendsto_finsetSum
    intro j _
    apply tendsto_finsetSum
    intro k _
    exact weightedCross_QV_class_tendsto d T N τ hm h0 hT hmesh _
      (readout_measurable d T family _ (hessianEntry_continuous φ hφ j k))
      (readout_adapted d T family _ (hessianEntry_continuous φ hφ j k))
      (readout_continuous d T family _ (hessianEntry_continuous φ hφ j k))
      K ((norm_nonneg (hessian φ 0)).trans (hb 0)) (fun _ _=>hessianEntry_bound φ K hb j k _) (family j) (family k)
  exact TendstoInMeasure.congr (fun n=>secondGridClass_coe d T family φ hφ K hb (τ n) (hm n))
    (secondEnergyClass_coe d T family φ hφ K hb) (tendstoInMeasure_of_tendsto_Lp hL)

omit hm h0 hT hmesh in
/-- Actual finite-state C2 Itô on SAME original source/input family.
Explicit original derivative bounds provide native L2 integral permission;
no chain rule, bracket, SDE solution or desired remainder is a premise. -/
theorem actual_state_ito (family : Fin m→fullPredictableL2 d T) (φ : E→ℝ) (hφ : ContDiff ℝ 2 φ)
    (K₁ K₂ : ℝ) (hb₁ : ∀ x,‖fderiv ℝ φ x‖≤K₁) (hb₂ : ∀ x,‖hessian φ x‖≤K₂) :
    (fun ω=>φ (stateProcess d T family T ω)) =ᵐ[productLaw d] fun ω=>
      φ 0+continuousIntegralProcess d T (itoInput d T family φ hφ K₁ hb₁) T ω+
        (1/2 : ℝ)*itoSecondEnergy d T family φ ω := by
  have hfirst := firstSum_tendstoInMeasure d T (fun n=>n+1) (uniformClock T) (uniformClock_mono T)
    (uniformClock_zero T) (uniformClock_end T) (uniformClock_mesh_tendsto T) family φ hφ K₁ hb₁
  have hsecond := secondSum_tendstoInMeasure d T (fun n=>n+1) (uniformClock T) (uniformClock_mono T)
    (uniformClock_zero T) (uniformClock_end T) (uniformClock_mesh_tendsto T) family φ hφ K₂ hb₂
  have hrem := actual_remainderSum_tendstoInMeasure d T family φ hφ (fun n=>n+1) (uniformClock T)
    (uniformClock_mono T) (uniformClock_zero T) (uniformClock_end T) (uniformClock_mesh_tendsto T)
  have hz : ∀ᵐ ω ∂productLaw d,stateProcess d T family 0 ω=0 := by
    have hi : ∀ᵐ ω ∂productLaw d,∀ j,continuousIntegralProcess d T (family j) 0 ω=0 :=
      ae_all_iff.mpr (fun j=>continuousIntegralProcess_zero d T (family j))
    filter_upwards [hi] with ω hi
    ext j
    exact hi j
  obtain ⟨ns,hns,hFa⟩ := hfirst.exists_seq_tendsto_ae
  obtain ⟨ms,hms,hSa⟩ := (hsecond.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  obtain ⟨ks,hks,hRa⟩ := (hrem.comp (hns.tendsto_atTop.comp hms.tendsto_atTop)).exists_seq_tendsto_ae
  filter_upwards [hFa,hSa,hRa,hz] with ω hf hs hr hz
  have hf' := hf.comp (hms.tendsto_atTop.comp hks.tendsto_atTop)
  have hs' := hs.comp hks.tendsto_atTop
  have htotal := (hf'.add (hs'.const_mul (1/2 : ℝ))).add hr
  have he (i : ℕ) :
      firstSum φ (uniformClock T (ns (ms (ks i)))) (fun u=>stateProcess d T family u ω)+
      (1/2 : ℝ)*secondSum φ (uniformClock T (ns (ms (ks i)))) (fun u=>stateProcess d T family u ω)+
      remainderSum φ (uniformClock T (ns (ms (ks i)))) (fun u=>stateProcess d T family u ω) =
      φ (stateProcess d T family T ω)-φ 0 := by
    have ht := finite_taylor_telescope φ (uniformClock T (ns (ms (ks i)))) (fun u=>stateProcess d T family u ω)
    rw [uniformClock_end,uniformClock_zero,hz] at ht
    exact ht.symm
  have hsame := (tendsto_congr' (Eventually.of_forall he)).mp htotal
  have heq : continuousIntegralProcess d T (itoInput d T family φ hφ K₁ hb₁) T ω+
      (1/2 : ℝ)*itoSecondEnergy d T family φ ω = φ (stateProcess d T family T ω)-φ 0 :=
    tendsto_nhds_unique (by simpa only [add_zero] using hsame) tendsto_const_nhds
  linarith


end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteStateItoSource
