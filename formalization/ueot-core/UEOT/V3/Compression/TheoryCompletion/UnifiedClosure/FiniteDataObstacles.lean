import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataSource
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataNumericalBounds

/-! Failure floors and initial barriers for the same three-state source.
All causal action randomizations are allowed in the negative conclusions;
the source, allowed actions, safety event and initial record remain fixed. -/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataObstacles
open MeasureTheory UEOT.V3.PathError UEOT.V3.TotalVariation
open UEOT.V3.FiniteDiscountedControl UEOT.V3.CoreOperationalAssembly
open FiniteDataSource FiniteDataNumericalBounds FiniteActionRealizabilityCheck
open ConditionedActionTransportCheck
open scoped BigOperators Classical
noncomputable section
local instance : MeasurableSpace State := ⊤

/-- Arbitrary history dependence only enlarges the class excluded below. -/
def allowedKernel (p : Param) (hp : Admissible p)
    (sigma : ∀ n, CausalHistory State State n → PMF Action) :
    ∀ n, CausalHistory State State n → PMF State :=
  fun n h => actionMixture ((model p hp).transitionPMF (currentState n h)) (sigma n h)

private theorem mixture_real (p : Param) (hp : Admissible p) (x z : State)
    (sigma : PMF Action) :
    (actionMixture ((model p hp).transitionPMF x) sigma z).toReal =
      ∑ a, (sigma a).toReal * transition p x a z := by
  have h := congrFun (realRow_actionMixture ((model p hp).transitionPMF x) sigma) z
  simpa [realRow, model] using h

/-- Every allowed action, including risk, obeys the stated source failure floor. -/
theorem action_failure_floor (p : Param) (hp : Admissible p) (l : ℝ)
    (hr0 : p.r0 ≤ 1-l) (hr1 : p.r1 ≤ 1-l)
    (he0 : l ≤ p.e0) (he1 : l ≤ p.e1) (x : State) (hx : x ≠ 2)
    (sigma : PMF Action) :
    l ≤ (actionMixture ((model p hp).transitionPMF x) sigma 2).toReal := by
  rw [mixture_real]
  have hf : ∀ a : Action, l ≤ transition p x a 2 := by
    intro a
    fin_cases x <;> fin_cases a <;> simp_all [transition] <;> linarith
  calc
    l = ∑ a : Action, (sigma a).toReal * l := by
      rw [← Finset.sum_mul, coverage_sum_toReal, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun a _ =>
      mul_le_mul_of_nonneg_left (hf a) ENNReal.toReal_nonneg

theorem mixture_dead_absorbing (p : Param) (hp : Admissible p) (sigma : PMF Action) :
    (actionMixture ((model p hp).transitionPMF 2) sigma 2).toReal = 1 := by
  rw [mixture_real]
  simp [transition, coverage_sum_toReal]

/-- Full path marginal survival, retaining every failed preparation/transition. -/
def survival (n : ℕ) (law : PMF (CausalHistory State State n)) : ℝ :=
  ∑ h, if currentState n h = 2 then 0 else (law h).toReal

private theorem survival_nonneg (n : ℕ) (law : PMF (CausalHistory State State n)) :
    0 ≤ survival n law := by
  apply Finset.sum_nonneg
  intro h _
  split_ifs <;> positivity

private theorem survival_le_one (n : ℕ) (law : PMF (CausalHistory State State n)) :
    survival n law ≤ 1 := by
  rw [← coverage_sum_toReal law]
  exact Finset.sum_le_sum fun h _ => by
    split_ifs <;> simp [ENNReal.toReal_nonneg]

private theorem survival_succ (n : ℕ) (law : PMF (CausalHistory State State n))
    (K : CausalHistory State State n → PMF State) :
    survival (n+1) (pmfExtend law K) =
      ∑ h, (law h).toReal * ((K h 0).toReal + (K h 1).toReal) := by
  unfold survival
  change (∑ h : CausalHistory State State n × State,
    if h.2 = 2 then 0 else (pmfExtend law K h).toReal) = _
  rw [← Finset.univ_product_univ, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro h _
  simp [Fin.sum_univ_succ, pmfExtend_apply, ENNReal.toReal_mul]
  ring

/-- The geometric contraction is derived from actual stochastic action rows. -/
theorem allowed_survival_step (p : Param) (hp : Admissible p) (l : ℝ)
    (hr0 : p.r0 ≤ 1-l) (hr1 : p.r1 ≤ 1-l)
    (he0 : l ≤ p.e0) (he1 : l ≤ p.e1)
    (sigma : ∀ n, CausalHistory State State n → PMF Action)
    (p0 : PMF State) (n : ℕ) :
    survival (n+1) (causalLaw p0 (allowedKernel p hp sigma) (n+1)) ≤
      (1-l) * survival n (causalLaw p0 (allowedKernel p hp sigma) n) := by
  change survival (n+1) (pmfExtend _ _) ≤ _
  rw [survival_succ, survival, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro h _
  let k := allowedKernel p hp sigma n h
  have hsum := coverage_sum_toReal k
  change (∑ z : Fin 3, (k z).toReal) = 1 at hsum
  norm_num [Fin.sum_univ_succ] at hsum
  by_cases hd : currentState n h = 2
  · have hdead : (k 2).toReal = 1 := by
      simp only [k, allowedKernel, hd]
      exact mixture_dead_absorbing p hp (sigma n h)
    have hz : (k 0).toReal + (k 1).toReal = 0 := by linarith
    simp only [hd, if_true, mul_zero]
    change (causalLaw p0 (allowedKernel p hp sigma) n h).toReal *
      ((k 0).toReal + (k 1).toReal) ≤ 0
    rw [hz, mul_zero]
  · have hfloor : l ≤ (k 2).toReal :=
      action_failure_floor p hp l hr0 hr1 he0 he1 _ hd (sigma n h)
    have hs : (k 0).toReal + (k 1).toReal ≤ 1-l := by linarith
    simp only [hd, if_false]
    change (causalLaw p0 (allowedKernel p hp sigma) n h).toReal *
      ((k 0).toReal + (k 1).toReal) ≤ _
    nlinarith [mul_nonneg (show 0 ≤ (causalLaw p0 (allowedKernel p hp sigma) n h).toReal
      from ENNReal.toReal_nonneg) (sub_nonneg.mpr hs)]

theorem allowed_survival_geometric (p : Param) (hp : Admissible p) (l : ℝ)
    (hl : l ≤ 1) (hr0 : p.r0 ≤ 1-l) (hr1 : p.r1 ≤ 1-l)
    (he0 : l ≤ p.e0) (he1 : l ≤ p.e1)
    (sigma : ∀ n, CausalHistory State State n → PMF Action)
    (p0 : PMF State) (T : ℕ) :
    survival T (causalLaw p0 (allowedKernel p hp sigma) T) ≤ (1-l)^T := by
  exact survival_le_geometric (fun n => survival n (causalLaw p0 (allowedKernel p hp sigma) n)) l hl (survival_le_one 0 p0)
    (allowed_survival_step p hp l hr0 hr1 he0 he1 sigma p0) T

/-- Finite PMF survival is exactly the actual measured safe terminal event. -/
private theorem survival_eq_measure (n : ℕ) (law : PMF (CausalHistory State State n)) :
    survival n law = law.toMeasure.real {h | currentState n h ≠ 2} := by
  let S := Finset.univ.filter (fun h : CausalHistory State State n => currentState n h ≠ 2)
  have hs : {h : CausalHistory State State n | currentState n h ≠ 2} = (S : Set _) := by
    ext h; simp [S]
  rw [hs, pmfMeasureReal_eq_sum_finset, show S = _ from rfl, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro h _
  by_cases hh : currentState n h = 2 <;> simp [hh]

private theorem safePMF_survival (v : ℝ) (hv : 0 ≤ v ∧ v ≤ 1) :
    survival 0 (safePMF v hv) = 1 := by
  change (∑ h : Fin 3, if h = 2 then 0 else (safePMF v hv h).toReal) = 1
  simp [Fin.sum_univ_succ]

/-- The same-source rank-one target has safe terminal marginal at every horizon. -/
theorem target_survival (p : Param) (hp : Admissible p) (T : ℕ) :
    survival T (target p hp T) = 1 := by
  cases T with
  | zero => simp [target, targetPath, causalLaw, initial, safePMF_survival]
  | succ n =>
    change survival (n+1) (pmfExtend _ _) = 1
    rw [survival_succ]
    have hrow : ∀ h : CausalHistory State State n,
        ((targetRow p hp (n+1) n (currentState n h)) 0).toReal +
        ((targetRow p hp (n+1) n (currentState n h)) 1).toReal = 1 := by
      intro h
      simp [targetRow, fair, initial]
    simp_rw [hrow, mul_one]
    exact coverage_sum_toReal _

/-- Actual failures lower-bound distance to this target, without exact source
knowledge by the selector. The target is the common source's conditioned law. -/
theorem allowed_path_tv_floor (p : Param) (hp : Admissible p) (l : ℝ)
    (hl : l ≤ 1) (hr0 : p.r0 ≤ 1-l) (hr1 : p.r1 ≤ 1-l)
    (he0 : l ≤ p.e0) (he1 : l ≤ p.e1)
    (sigma : ∀ n, CausalHistory State State n → PMF Action)
    (p0 : PMF State) (T : ℕ) :
    1-(1-l)^T ≤ tvDist (causalLaw p0 (allowedKernel p hp sigma) T).toMeasure
      (target p hp T).toMeasure := by
  have hevent := tvEvent_le (causalLaw p0 (allowedKernel p hp sigma) T).toMeasure
    (target p hp T).toMeasure {h | currentState T h ≠ 2} (Set.toFinite _).measurableSet
  rw [← survival_eq_measure, ← survival_eq_measure, target_survival] at hevent
  have hsurv := allowed_survival_geometric p hp l hl hr0 hr1 he0 he1 sigma p0 T
  have hneg := neg_le_abs (survival T (causalLaw p0 (allowedKernel p hp sigma) T)-1)
  linarith

/-- This initial marginal barrier allows every future causal state kernel. -/
theorem unprepared_path_initial_floor (p : Param) (hp : Admissible p)
    (T : ℕ) (hT : T ≠ 0)
    (K : ∀ n, CausalHistory State State n → PMF State) :
    |tilt p - 1/2| ≤ tvDist (causalLaw initial K T).toMeasure (target p hp T).toMeasure := by
  have h := initial_tv_le_path_tv initial K T (target p hp T)
  have hm : (target p hp T).map (initialRecord T) = nu p hp := by
    simp only [target, if_neg hT, targetPath]
    exact causalLaw_initial_marginal _ _ T
  rw [hm] at h
  have htv : tvDist initial.toMeasure (nu p hp).toMeasure = |tilt p - 1/2| := by
    rw [UEOT.V3.FiniteRecurrentDecompositionStability.pmf_tv_eq_half_sum_abs]
    simp [initial, nu, Fin.sum_univ_succ, abs_sub_comm]
    ring
  rwa [htv] at h

/-- The registered entire box has the stated initial lower bound, which is
smaller than the decision threshold and therefore does not reject the whole box. -/
theorem box_unprepared_path_floor (p : Param) (hb : Box p) (T : ℕ) (hT : T ≠ 0)
    (K : ∀ n, CausalHistory State State n → PMF State) :
    (1/6 : ℝ) ≤ tvDist (causalLaw initial K T).toMeasure
      (target p (box_admissible hb) T).toMeasure := by
  have ht := uniform_initial_tilt_gap hb.1 (box_admissible hb).2.2.1.le hb.2.2.2.1
  exact ht.trans (unprepared_path_initial_floor p (box_admissible hb) T hT K)

theorem main_unprepared_path_floor (p : Param) (hp : Admissible p)
    (hr0 : p.r0 = 3/4) (hr1 : p.r1 = 1/4) (T : ℕ) (hT : T ≠ 0)
    (K : ∀ n, CausalHistory State State n → PMF State) :
    (1/4 : ℝ) ≤ tvDist (causalLaw initial K T).toMeasure (target p hp T).toMeasure := by
  have h := unprepared_path_initial_floor p hp T hT K
  norm_num [tilt, hr0, hr1] at h
  exact h

/-- On Good, data provide a lower bound for every allowed action's failure.
This is a statistical conditional statement, not an exact known-parameter claim. -/
theorem statistical_path_floor (p estimate : Param) (hb : Box p)
    (hg : Good p estimate (1/250))
    (sigma : ∀ n, CausalHistory State State n → PMF Action)
    (p0 : PMF State) (T : ℕ) :
    1-(1-dataFailureFloor estimate.e0 estimate.e1)^T ≤
      tvDist (causalLaw p0 (allowedKernel p (box_admissible hb) sigma) T).toMeasure
        (target p (box_admissible hb) T).toMeasure := by
  let l := dataFailureFloor estimate.e0 estimate.e1
  have hl : l ≤ (1/6 : ℝ) := min_le_left _ _
  have he0 : l ≤ p.e0 := by
    have hg0 := hg (2 : Fin 4)
    change |p.e0 - estimate.e0| ≤ 1/250 at hg0
    have hh : estimate.e0 - 1/250 ≤ p.e0 := by
      have h := (abs_le.mp hg0).1
      linarith
    exact (min_le_right _ _).trans ((min_le_left _ _).trans (max_le hb.2.2.2.2.1 hh))
  have he1 : l ≤ p.e1 := by
    have hg1 := hg (3 : Fin 4)
    change |p.e1 - estimate.e1| ≤ 1/250 at hg1
    have hh : estimate.e1 - 1/250 ≤ p.e1 := by
      have h := (abs_le.mp hg1).1
      linarith
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (max_le hb.2.2.2.2.2.2.1 hh))
  exact allowed_path_tv_floor p (box_admissible hb) l (by linarith)
    (by linarith [hb.2.1]) (by linarith [hb.2.2.2.1]) he0 he1 sigma p0 T

/-- High registered noise defeats the threshold for every allowed causal policy. -/
theorem known_high_noise_no_go (p : Param) (hb : Box p)
    (he0 : p.e0 = 1/20) (he1 : p.e1 = 1/20)
    (sigma : ∀ n, CausalHistory State State n → PMF Action) (p0 : PMF State) :
    (1/5 : ℝ) < tvDist
      (causalLaw p0 (allowedKernel p (box_admissible hb) sigma) 10).toMeasure
      (target p (box_admissible hb) 10).toMeasure := by
  have hf := allowed_path_tv_floor p (box_admissible hb) (1/20) (by norm_num)
    (by linarith [hb.2.1]) (by linarith [hb.2.2.2.1])
    (by rw [he0]) (by rw [he1]) sigma p0 10
  rw [show (1-(1/20 : ℝ)) = 19/20 by norm_num] at hf
  exact high_noise_ten.trans_le hf

/-- At the low-noise main source, long windows fail even with preparation. -/
theorem known_low_noise_long_no_go (p : Param) (hb : Box p)
    (he0 : p.e0 = 1/200) (he1 : p.e1 = 1/200)
    (sigma : ∀ n, CausalHistory State State n → PMF Action) (p0 : PMF State) :
    (1/5 : ℝ) < tvDist
      (causalLaw p0 (allowedKernel p (box_admissible hb) sigma) 45).toMeasure
      (target p (box_admissible hb) 45).toMeasure := by
  have hf := allowed_path_tv_floor p (box_admissible hb) (1/200) (by norm_num)
    (by linarith [hb.2.1]) (by linarith [hb.2.2.2.1])
    (by rw [he0]) (by rw [he1]) sigma p0 45
  rw [show (1-(1/200 : ℝ)) = 199/200 by norm_num] at hf
  exact low_noise_forty_five.trans_le hf

/-- Uniform positive action risk forces actual finite-window survival to zero.
It does not promote a family of finite-horizon candidates to infinite safety. -/
theorem allowed_survival_tendsto_zero (p : Param) (hp : Admissible p) (l : ℝ)
    (hlpos : 0 < l) (hl : l ≤ 1) (hr0 : p.r0 ≤ 1-l) (hr1 : p.r1 ≤ 1-l)
    (he0 : l ≤ p.e0) (he1 : l ≤ p.e1)
    (sigma : ∀ n, CausalHistory State State n → PMF Action) (p0 : PMF State) :
    Filter.Tendsto (fun T => survival T (causalLaw p0 (allowedKernel p hp sigma) T))
      Filter.atTop (nhds 0) := by
  exact survival_tendsto_zero _ l hlpos hl (fun n => survival_nonneg n _)
    (survival_le_one 0 p0) (allowed_survival_step p hp l hr0 hr1 he0 he1 sigma p0)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataObstacles
