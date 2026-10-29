import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataSource
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataPathBounds
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataNumericalBounds
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataSource
open MeasureTheory UEOT.V3.PathError UEOT.V3.TotalVariation
open UEOT.V3.FiniteDiscountedControl UEOT.V3.CoreOperationalAssembly
open FiniteActionRealizabilityCheck ConditionedActionTransportCheck FiniteDataPathBounds
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2000000

theorem selectedRow_real_safe (p : Param) (hp : Admissible p)
    (v : ℝ) (hv : 0 ≤ v ∧ v ≤ 1) (x : State) (hx : x ≠ 2) (z : State) :
    (selectedRow p hp v hv x z).toReal =
      ![v*(1-p.e0),(1-v)*(1-p.e1),v*p.e0+(1-v)*p.e1] z := by
  have h := congrFun (realRow_actionMixture ((model p hp).transitionPMF x) (selection v hv)) z
  simp only [realRow, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    selection_real, Model.transitionPMF_apply_toReal] at h
  change (selectedRow p hp v hv x z).toReal = _ at h
  rw [h]
  fin_cases x <;> fin_cases z <;> simp [model,transition,Fin.sum_univ_succ] at *

def preparationLoss (p : Param) (v : ℝ) : ℝ := v*p.e0+(1-v)*p.e1

theorem selected_row_tv (p : Param) (hp : Admissible p)
    (v : ℝ) (hv : 0 ≤ v ∧ v ≤ 1) (x : State) (hx : x ≠ 2) :
    tvDist (selectedRow p hp v hv x).toMeasure (safePMF v hv).toMeasure =
      preparationLoss p v := by
  rw [tvDist_eq_one_sub_pmfCommonMass]
  simp only [pmfCommonMass, selectedRow_real_safe p hp v hv x hx, safePMF_real]
  simp [Fin.sum_univ_succ]
  have he0 := hp.2.2.2.2.1
  have he1 := hp.2.2.2.2.2.2.1
  have h0 : v*(1-p.e0) ≤ v := by nlinarith [mul_nonneg hv.1 he0]
  have h1 : (1-v)*(1-p.e1) ≤ 1-v := by nlinarith [mul_nonneg (sub_nonneg.mpr hv.2) he1]
  have hd : 0 ≤ v*p.e0+(1-v)*p.e1 :=
    add_nonneg (mul_nonneg hv.1 he0) (mul_nonneg (sub_nonneg.mpr hv.2) he1)
  rw [min_eq_left h0,min_eq_left h1,min_eq_right hd]
  simp only [preparationLoss]
  ring

theorem prepared_eq_selected (p : Param) (hp : Admissible p)
    (v : ℝ) (hv : 0 ≤ v ∧ v ≤ 1) :
    prepared p hp v hv = selectedRow p hp v hv 0 := by
  apply PMF.ext
  intro z
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  change (actionMixture (selectedRow p hp v hv) initial z).toReal = _
  have h := congrFun (realRow_actionMixture (selectedRow p hp v hv) initial) z
  simp only [realRow, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
  rw [h]
  simp [initial, Fin.sum_univ_succ, selectedRow_real_safe p hp v hv 0 (by decide),
    selectedRow_real_safe p hp v hv 1 (by decide)]
  ring

theorem preparation_loss_le (p : Param) (_hp : Admissible p)
    (v : ℝ) (hv : 0 ≤ v ∧ v ≤ 1) : preparationLoss p v ≤ max p.e0 p.e1 := by
  have h0 := mul_le_mul_of_nonneg_left (le_max_left p.e0 p.e1) hv.1
  have h1 := mul_le_mul_of_nonneg_left (le_max_right p.e0 p.e1) (sub_nonneg.mpr hv.2)
  dsimp [preparationLoss]
  nlinarith

theorem prepared_tv_le (p : Param) (hp : Admissible p)
    (v : ℝ) (hv : 0 ≤ v ∧ v ≤ 1) :
    tvDist (prepared p hp v hv).toMeasure (safePMF v hv).toMeasure ≤ max p.e0 p.e1 := by
  rw [prepared_eq_selected, selected_row_tv p hp v hv 0 (by decide)]
  exact preparation_loss_le p hp v hv

/-- A safe-target row is genuinely unreachable at the cemetery, regardless of
empirical counts. This structural zero, not a zero sample count, justifies C. -/
theorem target_occupied_safe (estimate : Param) (he : Admissible estimate) (T n : ℕ)
    (x : State) (hx : x ∈ occupiedState (nu estimate he) (targetRow estimate he T) n) : x ≠ 2 := by
  obtain ⟨h,hpos,rfl⟩ := hx
  intro hz
  have hnu : nu estimate he 2 = 0 := by
    apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) ENNReal.zero_ne_top).mp
    simp [nu]
  have hfair : fair 2 = 0 := by
    apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) ENNReal.zero_ne_top).mp
    simp [fair,initial]
  cases n with
  | zero =>
    change h = (2 : State) at hz
    change nu estimate he h ≠ 0 at hpos
    exact hpos (hz.symm ▸ hnu)
  | succ n =>
    rcases h with ⟨g,z⟩
    change z = 2 at hz
    subst z
    change pmfExtend _ _ (g,2) ≠ 0 at hpos
    rw [pmfExtend_apply] at hpos
    apply hpos
    have hr : targetRow estimate he T n (currentState n g) 2 = 0 := by
      unfold targetRow
      split <;> assumption
    rw [hr,mul_zero]

/-- This actual same-table experiment includes the noisy preparation and
preserves all its failures. Its reference target is computed from the estimate. -/
theorem deployed_reference_bound (p : Param) (hp : Admissible p)
    (estimate : Param) (he : Admissible estimate) (T : ℕ) (hT : 0 < T) :
    tvDist (deployed p hp estimate he T).toMeasure (target estimate he T).toMeasure ≤
      min 1 (((T : ℝ)+1)*max p.e0 p.e1) := by
  have ht : T ≠ 0 := Nat.ne_of_gt hT
  have h := causal_path_tv_le
    (prepared p hp (tilt estimate) (tilt_valid estimate he)) (nu estimate he)
    (timeMixtureKernel (model p hp) observe (controller estimate he T))
    (fun n h => targetRow estimate he T n (currentState n h)) T
    (max p.e0 p.e1) (fun _ => max p.e0 p.e1)
    (prepared_tv_le p hp (tilt estimate) (tilt_valid estimate he)) (by
      intro n hn h hh
      have hs := target_occupied_safe estimate he T n (currentState n h) ⟨h,hh,rfl⟩
      by_cases hc : n+1<T
      · simp only [timeMixtureKernel,controller,targetRow,if_pos hc]
        change tvDist (selectedRow p hp (tilt estimate) (tilt_valid estimate he)
          (currentState n h)).toMeasure (safePMF (tilt estimate) (tilt_valid estimate he)).toMeasure ≤ _
        rw [selected_row_tv p hp (tilt estimate) (tilt_valid estimate he) _ hs]
        exact preparation_loss_le p hp (tilt estimate) (tilt_valid estimate he)
      · simp only [timeMixtureKernel,controller,targetRow,if_neg hc]
        change tvDist (selectedRow p hp (1/2) (by norm_num) (currentState n h)).toMeasure
          (safePMF (1/2) (by norm_num)).toMeasure ≤ _
        rw [selected_row_tv p hp (1/2) (by norm_num) _ hs]
        exact preparation_loss_le p hp (1/2) (by norm_num))
  simpa [deployed,target,ht,targetPath,Finset.sum_const,Finset.card_range,nsmul_eq_mul,
    add_mul,add_comm,add_left_comm,add_assoc] using h

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataSource
