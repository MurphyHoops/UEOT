import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorWeightedCrossQV
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianScalarTaylorRemainder

/-!
Original commitment: finite state Itô needs the actual C2 Taylor remainder of the SAME continuous Euclidean state to vanish.
Existing result: actual state/source continuity and original deterministic-clock diagonal/cross/weighted QV, without input L4.
Premise reduced: derive quadratic remainder control from native C2 derivatives on actual line segments, not a supplied error modulus.
Model/witness: finite Euclidean state, C2 real observable, SAME continuous state/inputs/source and caller partitions; zero dimensions/time included.
Consumer: actual state Taylor remainder limit and then state Itô; global derivative bounds are separate integral permissions, not Taylor premises.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteStateTaylorRemainder
open MeasureTheory ProbabilityTheory Set Filter
open BrownianFiniteProductSource BrownianVectorTimeInput BrownianVectorPredictableInputs
open BrownianVectorIntegralContinuousVersion BrownianVectorFiniteStateCrossQV BrownianVectorWeightedCrossQV
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

/-- Native second Fréchet derivative, with no desired Hessian field. -/
def hessian (φ : E→ℝ) (a : E) : E→L[ℝ] E→L[ℝ] ℝ := fderiv ℝ (fderiv ℝ φ) a

theorem derivative_contDiff (φ : E→ℝ) (hφ : ContDiff ℝ 2 φ) : ContDiff ℝ 1 (fderiv ℝ φ) :=
  (contDiff_succ_iff_fderiv (n := 1)).mp hφ |>.2.2

theorem hessian_continuous (φ : E→ℝ) (hφ : ContDiff ℝ 2 φ) : Continuous (hessian φ) :=
  (derivative_contDiff φ hφ).continuous_fderiv (by norm_num)

def lineFunction (φ : E→ℝ) (a h : E) (u : ℝ) := φ (a+u • h)

theorem lineFunction_contDiff (φ : E→ℝ) (hφ : ContDiff ℝ 2 φ) (a h : E) :
    ContDiff ℝ 2 (lineFunction φ a h) :=
  hφ.comp (contDiff_const.add (contDiff_id.smul contDiff_const))

theorem lineFunction_deriv (φ : E→ℝ) (hφ : ContDiff ℝ 2 φ) (a h : E) (u : ℝ) :
    deriv (lineFunction φ a h) u = fderiv ℝ φ (a+u • h) h := by
  have ha : HasDerivAt (fun v : ℝ=>a+v • h) h u := by
    simpa only [id_eq,one_smul] using ((hasDerivAt_id u).smul_const h).const_add a
  exact (((hφ.differentiable (by norm_num)) _).hasFDerivAt.comp_hasDerivAt u ha).deriv

theorem lineFunction_secondDeriv (φ : E→ℝ) (hφ : ContDiff ℝ 2 φ) (a h : E) (u : ℝ) :
    iteratedDeriv 2 (lineFunction φ a h) u = hessian φ (a+u • h) h h := by
  have he : deriv (lineFunction φ a h) = fun v=>fderiv ℝ φ (a+v • h) h :=
    funext (lineFunction_deriv φ hφ a h)
  rw [show (2 : ℕ)=1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one,he]
  have ha : HasDerivAt (fun v : ℝ=>a+v • h) h u := by
    simpa only [id_eq,one_smul] using ((hasDerivAt_id u).smul_const h).const_add a
  have hd := (((derivative_contDiff φ hφ).differentiable (by norm_num)) _).hasFDerivAt.comp_hasDerivAt u ha
  simpa only [hessian,map_zero,add_zero,Function.comp_apply] using (hd.clm_apply (hasDerivAt_const u h)).deriv

/-- Actual second-order remainder with original native derivatives. -/
def secondRemainder (φ : E→ℝ) (a b : E) : ℝ :=
  φ b-φ a-fderiv ℝ φ a (b-a)-(1/2 : ℝ)*hessian φ a (b-a) (b-a)

theorem secondRemainder_eq_line (φ : E→ℝ) (hφ : ContDiff ℝ 2 φ) (a b : E) :
    secondRemainder φ a b = BrownianScalarTaylorRemainder.secondRemainder (lineFunction φ a (b-a)) 0 1 := by
  rw [BrownianScalarTaylorRemainder.secondRemainder,lineFunction_deriv φ hφ,lineFunction_secondDeriv φ hφ]
  simp only [lineFunction,zero_smul,one_smul,add_zero,add_sub_cancel,sub_zero,one_pow,mul_one,secondRemainder]

/-- C2 line restriction and native operator norm derive the true local
quadratic remainder bound. Neither a third derivative nor a remainder field. -/
theorem secondRemainder_bound (φ : E→ℝ) (hφ : ContDiff ℝ 2 φ) (a b : E) (ε : ℝ)
    (hvar : ∀ u∈Icc (0 : ℝ) 1,‖hessian φ (a+u • (b-a))-hessian φ a‖≤ε) :
    ‖secondRemainder φ a b‖≤(ε/2)*‖b-a‖^2 := by
  rw [secondRemainder_eq_line φ hφ]
  have hb := BrownianScalarTaylorRemainder.secondRemainder_bound (lineFunction φ a (b-a))
    (lineFunction_contDiff φ hφ a (b-a)) 0 1 (ε*‖b-a‖^2) (by
      intro u hu
      rw [lineFunction_secondDeriv φ hφ,lineFunction_secondDeriv φ hφ]
      simp only [zero_smul,add_zero]
      have hv := hvar u (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ)≤1)] using hu)
      calc
        _ = ‖((hessian φ (a+u • (b-a))-hessian φ a) (b-a)) (b-a)‖ := rfl
        _ ≤ ‖(hessian φ (a+u • (b-a))-hessian φ a) (b-a)‖*‖b-a‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ (‖hessian φ (a+u • (b-a))-hessian φ a‖*‖b-a‖)*‖b-a‖ := by
          gcongr
          exact ContinuousLinearMap.le_opNorm _ _
        _ ≤ (ε*‖b-a‖)*‖b-a‖ := by gcongr
        _ = ε*‖b-a‖^2 := by ring)
  simpa only [sub_zero,one_pow,mul_one,div_mul_eq_mul_div,mul_div_assoc] using hb

/-- Pure deterministic mesh control in the actual Euclidean state norm. -/
theorem continuous_path_grid_increment_small (T : ℝ≥0) (N : ℕ→ℕ)
    (τ : (n : ℕ)→Fin (N n+1)→ℝ≥0) (hm : ∀ n,Monotone (τ n))
    (hT : ∀ n,τ n (Fin.last (N n))=T)
    (hmesh : Tendsto (fun n=>(BrownianQuadraticVariation.mesh (τ n) : ℝ)) atTop (𝓝 0))
    (X : ℝ≥0→E) (hX : Continuous X) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n in atTop,∀ i : Fin (N n),dist (X (τ n i.succ)) (X (τ n i.castSucc))<ε := by
  have huc : UniformContinuousOn X (Icc (0 : ℝ≥0) T) := isCompact_Icc.uniformContinuousOn_of_continuous hX.continuousOn
  obtain ⟨δ,hδ,hδX⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  have he : ∀ᶠ n in atTop,(BrownianQuadraticVariation.mesh (τ n) : ℝ)<δ := (tendsto_order.mp hmesh).2 δ hδ
  filter_upwards [he] with n hn
  intro i
  have hu (j : Fin (N n+1)) : τ n j∈Icc (0 : ℝ≥0) T :=
    ⟨bot_le,((hm n) (Fin.le_last j)).trans (hT n).le⟩
  exact hδX _ (hu _) _ (hu _) ((BrownianScalarTaylorRemainder.clockIncrement_dist_le_mesh (τ n) (hm n) i).trans_lt hn)

/-- Original C2 Hessian is uniformly continuous on a compact ball containing
all actual state segments. The ball/modulus are derived for each path. -/
theorem secondRemainder_grid_small (φ : E→ℝ) (hφ : ContDiff ℝ 2 φ)
    (T : ℝ≥0) (N : ℕ→ℕ) (τ : (n : ℕ)→Fin (N n+1)→ℝ≥0)
    (hm : ∀ n,Monotone (τ n)) (hT : ∀ n,τ n (Fin.last (N n))=T)
    (hmesh : Tendsto (fun n=>(BrownianQuadraticVariation.mesh (τ n) : ℝ)) atTop (𝓝 0))
    (X : ℝ≥0→E) (hX : Continuous X) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n in atTop,∀ i : Fin (N n),
      ‖secondRemainder φ (X (τ n i.castSucc)) (X (τ n i.succ))‖≤
        ε*‖X (τ n i.succ)-X (τ n i.castSucc)‖^2 := by
  have hcomp : IsCompact (X '' Icc (0 : ℝ≥0) T) := isCompact_Icc.image hX
  obtain ⟨R,hR,hbound⟩ := hcomp.isBounded.exists_pos_norm_le
  have hx {u : ℝ≥0} (hu : u∈Icc (0 : ℝ≥0) T) : X u∈Metric.closedBall (0 : E) R := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hbound (X u) ⟨u,hu,rfl⟩
  have huc : UniformContinuousOn (hessian φ) (Metric.closedBall (0 : E) R) :=
    (isCompact_closedBall (0 : E) R).uniformContinuousOn_of_continuous (hessian_continuous φ hφ).continuousOn
  obtain ⟨δ,hδ,hδφ⟩ := (Metric.uniformContinuousOn_iff (α := E) (β := E→L[ℝ] E→L[ℝ] ℝ)).mp huc (2*ε) (by positivity)
  filter_upwards [continuous_path_grid_increment_small T N τ hm hT hmesh X hX δ hδ] with n hn
  intro i
  have hu (j : Fin (N n+1)) : τ n j∈Icc (0 : ℝ≥0) T :=
    ⟨bot_le,((hm n) (Fin.le_last j)).trans (hT n).le⟩
  have hv : ∀ u∈Icc (0 : ℝ) 1,
      ‖hessian φ (X (τ n i.castSucc)+u • (X (τ n i.succ)-X (τ n i.castSucc)))-hessian φ (X (τ n i.castSucc))‖≤2*ε := by
    intro u hU
    have hz := (convex_closedBall (0 : E) R).add_smul_sub_mem (hx (hu i.castSucc)) (hx (hu i.succ)) hU
    have hd : dist (X (τ n i.castSucc)+u • (X (τ n i.succ)-X (τ n i.castSucc))) (X (τ n i.castSucc))<δ := by
      rw [dist_eq_norm,add_sub_cancel_left,norm_smul]
      have hUn : ‖u‖≤1 := by simpa only [Real.norm_eq_abs,abs_of_nonneg hU.1] using hU.2
      exact (mul_le_mul_of_nonneg_right hUn (norm_nonneg _)).trans_lt (by simpa only [one_mul,dist_eq_norm] using hn i)
    have hv := hδφ _ hz _ (hx (hu i.castSucc)) hd
    rw [dist_eq_norm (hessian φ (X (τ n i.castSucc)+u • (X (τ n i.succ)-X (τ n i.castSucc)))) (hessian φ (X (τ n i.castSucc)))] at hv
    exact hv.le
  have hb := secondRemainder_bound φ hφ (X (τ n i.castSucc)) (X (τ n i.succ)) (2*ε) hv
  simpa only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ)≠0)] using hb
/-- Literal normalized cell error, including exact zero increment. -/
def cellRatio (φ : E→ℝ) (a b : E) : ℝ≥0 := ‖secondRemainder φ a b‖₊/‖b-a‖₊^2

theorem cellRatio_mul_norm_sq (φ : E→ℝ) (a b : E) :
    (cellRatio φ a b : ℝ)*‖b-a‖^2=‖secondRemainder φ a b‖ := by
  by_cases h : b-a=0
  · have hab : b=a := sub_eq_zero.mp h
    subst b
    simp [cellRatio,secondRemainder]
  · simp only [cellRatio,NNReal.coe_div,NNReal.coe_pow,coe_nnnorm]
    exact div_mul_cancel₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr h))

theorem cellRatio_le_of_bound (φ : E→ℝ) (a b : E) (ε : ℝ≥0)
    (hb : ‖secondRemainder φ a b‖≤(ε : ℝ)*‖b-a‖^2) : cellRatio φ a b≤ε := by
  by_cases h : b-a=0
  · have hab : b=a := sub_eq_zero.mp h
    subst b
    simp [cellRatio,secondRemainder]
  · apply NNReal.coe_le_coe.mp
    simp only [cellRatio,NNReal.coe_div,NNReal.coe_pow,coe_nnnorm]
    exact (div_le_iff₀ (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr h))).mpr hb

def gridRatio (φ : E→ℝ) {n : ℕ} (τ : Fin (n+1)→ℝ≥0) (X : ℝ≥0→E) : ℝ≥0 :=
  Finset.univ.sup (fun i : Fin n=>cellRatio φ (X (τ i.castSucc)) (X (τ i.succ)))

def remainderSum (φ : E→ℝ) {n : ℕ} (τ : Fin (n+1)→ℝ≥0) (X : ℝ≥0→E) : ℝ :=
  ∑ i : Fin n,secondRemainder φ (X (τ i.castSucc)) (X (τ i.succ))

theorem remainderSum_norm_le (φ : E→ℝ) {n : ℕ} (τ : Fin (n+1)→ℝ≥0) (X : ℝ≥0→E) :
    ‖remainderSum φ τ X‖≤(gridRatio φ τ X : ℝ)*(∑ i : Fin n,‖X (τ i.succ)-X (τ i.castSucc)‖^2) := by
  calc
    _ ≤ ∑ i : Fin n,‖secondRemainder φ (X (τ i.castSucc)) (X (τ i.succ))‖ := norm_sum_le _ _
    _ = ∑ i : Fin n,(cellRatio φ (X (τ i.castSucc)) (X (τ i.succ)) : ℝ)*‖X (τ i.succ)-X (τ i.castSucc)‖^2 := by
      simp_rw [cellRatio_mul_norm_sq]
    _ ≤ ∑ i : Fin n,(gridRatio φ τ X : ℝ)*‖X (τ i.succ)-X (τ i.castSucc)‖^2 := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact NNReal.coe_le_coe.mpr (Finset.le_sup (f := fun j : Fin n=>cellRatio φ (X (τ j.castSucc)) (X (τ j.succ))) (Finset.mem_univ i))
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem gridRatio_tendsto (φ : E→ℝ) (hφ : ContDiff ℝ 2 φ)
    (T : ℝ≥0) (N : ℕ→ℕ) (τ : (n : ℕ)→Fin (N n+1)→ℝ≥0)
    (hm : ∀ n,Monotone (τ n)) (hT : ∀ n,τ n (Fin.last (N n))=T)
    (hmesh : Tendsto (fun n=>(BrownianQuadraticVariation.mesh (τ n) : ℝ)) atTop (𝓝 0))
    (X : ℝ≥0→E) (hX : Continuous X) : Tendsto (fun n=>(gridRatio φ (τ n) X : ℝ)) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨M,hM⟩ := eventually_atTop.mp (secondRemainder_grid_small φ hφ T N τ hm hT hmesh X hX (ε/2) (by positivity))
  refine ⟨M,fun n hn=>?_⟩
  have hr : gridRatio φ (τ n) X≤Real.toNNReal (ε/2) := by
    apply Finset.sup_le
    intro i _
    apply cellRatio_le_of_bound
    rw [Real.coe_toNNReal _ (by positivity : 0≤ε/2)]
    exact hM n hn i
  have hb := NNReal.coe_le_coe.mpr hr
  rw [Real.coe_toNNReal _ (by positivity : 0≤ε/2)] at hb
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (gridRatio φ (τ n) X).coe_nonneg]
  linarith

private theorem remainder_measurable {Ω : Type*} [MeasurableSpace Ω]
    (φ : E→ℝ) (hφ : ContDiff ℝ 2 φ) (X Y : Ω→E) (hX : Measurable X) (hY : Measurable Y) :
    Measurable (fun ω=>secondRemainder φ (X ω) (Y ω)) := by
  have hd : Continuous (fun p : E×E=>fderiv ℝ φ p.1 (p.2-p.1)) :=
    ((hφ.continuous_fderiv (by norm_num)).comp continuous_fst).clm_apply (continuous_snd.sub continuous_fst)
  have hdd : Continuous (fun p : E×E=>hessian φ p.1 (p.2-p.1) (p.2-p.1)) :=
    (((hessian_continuous φ hφ).comp continuous_fst).clm_apply (continuous_snd.sub continuous_fst)).clm_apply
      (continuous_snd.sub continuous_fst)
  have hc : Continuous (fun p : E×E=>secondRemainder φ p.1 p.2) :=
    (((hφ.continuous.comp continuous_snd).sub (hφ.continuous.comp continuous_fst)).sub hd).sub
      (continuous_const.mul hdd)
  exact hc.measurable.comp (hX.prodMk hY)

theorem remainderSum_measurable {Ω : Type*} [MeasurableSpace Ω]
    (φ : E→ℝ) (hφ : ContDiff ℝ 2 φ) {n : ℕ} (τ : Fin (n+1)→ℝ≥0)
    (X : ℝ≥0→Ω→E) (hX : ∀ u,Measurable (X u)) :
    Measurable (fun ω=>remainderSum φ τ (fun u=>X u ω)) :=
  Finset.measurable_fun_sum Finset.univ (fun i _=>remainder_measurable φ hφ _ _ (hX (τ i.castSucc)) (hX (τ i.succ)))

open BrownianVectorIntegralGridL1 BrownianVectorIntegralEnergyL1 BrownianVectorIntegralTimeEnergy BrownianVectorPartitionQV
variable (d : ℕ) (T : ℝ≥0)

/-- Actual Euclidean sum of squared increments, not the coordinate sup norm. -/
def stateSquareSum (family : Fin m→fullPredictableL2 d T) {n : ℕ} (τ : Fin (n+1)→ℝ≥0) (ω : Sample d) : ℝ :=
  ∑ i : Fin n,‖stateProcess d T family (τ i.succ) ω-stateProcess d T family (τ i.castSucc) ω‖^2

private theorem stateSquareClass_coe (family : Fin m→fullPredictableL2 d T) {n : ℕ} (τ : Fin (n+1)→ℝ≥0) :
    (∑ j,gridSquares d T τ (family j) : Lp ℝ 1 (productLaw d)) =ᵐ[productLaw d] stateSquareSum d T family τ := by
  have hi : ∀ᵐ ω ∂productLaw d,∀ j : Fin m,gridSquares d T τ (family j) ω =
      ∑ i : Fin n,(continuousIntegralProcess d T (family j) (τ i.succ) ω-continuousIntegralProcess d T (family j) (τ i.castSucc) ω)^2 :=
    ae_all_iff.mpr (fun j=>gridSquares_coe d T τ (family j))
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun j=>gridSquares d T τ (family j)),hi] with ω hs hi
  simp only [Finset.sum_apply] at hs
  rw [hs,Finset.sum_congr rfl (fun j _=>hi j),Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [EuclideanSpace.real_norm_sq_eq,PiLp.sub_apply,stateProcess_apply]

/-- The actual Euclidean finite state's total quadratic sums converge in
measure to original dt energies. This supplies a finite dominating quantity. -/
theorem stateSquareSum_tendstoInMeasure (family : Fin m→fullPredictableL2 d T) (N : ℕ→ℕ)
    (τ : (n : ℕ)→Fin (N n+1)→ℝ≥0) (hm : ∀ n,Monotone (τ n))
    (h0 : ∀ n,τ n 0=0) (hT : ∀ n,τ n (Fin.last (N n))=T)
    (hmesh : Tendsto (fun n=>(BrownianQuadraticVariation.mesh (τ n) : ℝ)) atTop (𝓝 0)) :
    TendstoInMeasure (productLaw d) (fun n=>stateSquareSum d T family (τ n)) atTop
      (fun ω=>∑ j,timeEnergy d T (family j) T ω) := by
  have hL : Tendsto (fun n=>∑ j,gridSquares d T (τ n) (family j)) atTop (𝓝 (∑ j,energyClass d T T (family j))) :=
    tendsto_finsetSum _ (fun j _=>fullInput_partition_QV d T N τ hm h0 hT hmesh (family j))
  have hA : (∑ j,energyClass d T T (family j) : Lp ℝ 1 (productLaw d)) =ᵐ[productLaw d]
      fun ω=>∑ j,timeEnergy d T (family j) T ω := by
    have hi : ∀ᵐ ω ∂productLaw d,∀ j,energyClass d T T (family j) ω=timeEnergy d T (family j) T ω :=
      ae_all_iff.mpr (fun j=>energyClass_coe d T T (family j))
    filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun j=>energyClass d T T (family j)),hi] with ω hs hi
    simp only [Finset.sum_apply] at hs
    exact hs.trans (Finset.sum_congr rfl (fun j _=>hi j))
  exact TendstoInMeasure.congr (fun n=>stateSquareClass_coe d T family (τ n)) hA (tendstoInMeasure_of_tendsto_Lp hL)

/-- Actual SAME-state Taylor remainders vanish for every specified caller
sequence. Only C2/path continuity and original L2 QV enter; no L4/global
derivative bound/third derivative or desired remainder certificate is input. -/
theorem actual_remainderSum_tendstoInMeasure (family : Fin m→fullPredictableL2 d T)
    (φ : E→ℝ) (hφ : ContDiff ℝ 2 φ) (N : ℕ→ℕ)
    (τ : (n : ℕ)→Fin (N n+1)→ℝ≥0) (hm : ∀ n,Monotone (τ n))
    (h0 : ∀ n,τ n 0=0) (hT : ∀ n,τ n (Fin.last (N n))=T)
    (hmesh : Tendsto (fun n=>(BrownianQuadraticVariation.mesh (τ n) : ℝ)) atTop (𝓝 0)) :
    TendstoInMeasure (productLaw d) (fun n ω=>remainderSum φ (τ n) (fun u=>stateProcess d T family u ω)) atTop
      (fun _=>(0 : ℝ)) := by
  apply BrownianScalarTaylorRemainder.tendstoInMeasure_of_ae_zero_domination (productLaw d) _
    (fun n ω=>(gridRatio φ (τ n) (fun u=>stateProcess d T family u ω) : ℝ))
    (fun n=>stateSquareSum d T family (τ n)) (fun ω=>∑ j,timeEnergy d T (family j) T ω)
  · intro n
    exact (remainderSum_measurable φ hφ (τ n) (stateProcess d T family)
      (fun u=>((stateProcess_stronglyAdapted d T family u).mono ((jointNaturalFiltration d).le u)).measurable)).aestronglyMeasurable
  · exact (stateProcess_continuous d T family).mono (fun ω h=>gridRatio_tendsto φ hφ T N τ hm hT hmesh _ h)
  · exact stateSquareSum_tendstoInMeasure d T family N τ hm h0 hT hmesh
  · intro n ω
    have hQ : 0≤stateSquareSum d T family (τ n) ω :=
      Finset.sum_nonneg (fun _ _=>sq_nonneg _)
    have hnorm : ‖stateSquareSum d T family (τ n) ω‖=stateSquareSum d T family (τ n) ω := by
      rw [Real.norm_eq_abs,abs_of_nonneg hQ]
    rw [hnorm]
    exact remainderSum_norm_le φ (τ n) (fun u=>stateProcess d T family u ω)


end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteStateTaylorRemainder
