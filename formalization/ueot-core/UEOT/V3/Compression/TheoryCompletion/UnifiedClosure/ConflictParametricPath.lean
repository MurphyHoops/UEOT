import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ConflictParametricSource

/-!
# Actual full state-action paths of the book's theta-family
All probabilities below use the original micro Model.transitionPMF and the
same constant action PMF at every complete history. Conditioning retains
all state/action coordinates. The initial state and safe domain are fixed.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ConflictParametricPath
open UEOT.V3.PathError UEOT.V3.FiniteDiscountedControl
open ConflictParametricSource
open scoped BigOperators
noncomputable section

abbrev History := CausalHistory State (Bool × State)

def step (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) (n : ℕ) (h : History n) :
    PMF (Bool × State) := pmfExtend (actionLaw theta h0 h1) (M.transitionPMF (riskLastState n h))

def law (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) (n : ℕ) : PMF (History n) :=
  causalLaw (PMF.pure (true,false)) (step theta h0 h1) n

def survives : (n : ℕ) → History n → Prop
  | 0, x => x.1 = true
  | n+1, h => survives n h.1 ∧ h.2.2.1 = true

instance (n : ℕ) (h : History n) : Decidable (survives n h) := Classical.propDecidable _

theorem mass_succ (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (n : ℕ) (h : History n) (a : Bool) (z : State) :
    (law theta h0 h1 (n+1) (h,(a,z))).toReal =
      (law theta h0 h1 n h).toReal * actionWeight theta a *
        (if z.1 = a then (1/2 : ℝ) else 0) := by
  change (pmfExtend (law theta h0 h1 n) (step theta h0 h1 n) (h,(a,z))).toReal = _
  rw [pmfExtend_apply]
  change ((law theta h0 h1 n h) *
    (pmfExtend (actionLaw theta h0 h1) (M.transitionPMF (riskLastState n h)) (a,z))).toReal = _
  rw [pmfExtend_apply, ENNReal.toReal_mul, ENNReal.toReal_mul, actionLaw_real, transition_real]
  ring

/-- All positive zero-risk deployment records are actually safe, including time zero. -/
theorem zero_law_supported_safe : ∀ n (h : History n),
    (law 0 (by norm_num) (by norm_num) n h).toReal ≠ 0 → survives n h := by
  intro n
  induction n with
  | zero =>
      intro x hx
      change ((PMF.pure (true,false)) x).toReal ≠ 0 at hx
      by_cases he : x = (true,false)
      · subst x; rfl
      · have hz : (PMF.pure (true,false) : PMF State) x = 0 := PMF.pure_apply_of_ne (true,false) x he
        rw [hz] at hx
        simp at hx
  | succ n ih =>
      rintro ⟨h,a,b,u⟩ hx
      rw [mass_succ] at hx
      have hh : (law 0 (by norm_num) (by norm_num) n h).toReal ≠ 0 := by
        intro hz; simp [hz] at hx
      refine ⟨ih h hh, ?_⟩
      cases a <;> cases b <;> simp_all [actionWeight]

/-- Exact full-record density on the survival event, not only a terminal marginal. -/
theorem safe_mass_ratio (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    ∀ n (h : History n), survives n h →
      (law theta h0 h1 n h).toReal = (1-theta)^n *
        (law 0 (by norm_num) (by norm_num) n h).toReal := by
  intro n
  induction n with
  | zero =>
      intro h _
      change ((PMF.pure (true,false) : PMF State) h).toReal = 1 * ((PMF.pure (true,false) : PMF State) h).toReal
      rw [one_mul]
  | succ n ih =>
      rintro ⟨h,a,b,u⟩ ⟨hh,hb⟩
      cases b with
      | false => cases hb
      | true =>
          rw [mass_succ, mass_succ, ih h hh, pow_succ]
          cases a with
          | false => simp [actionWeight]
          | true => simp only [actionWeight, if_true]; ring

theorem restricted_mass (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (n : ℕ) (h : History n) :
    (if survives n h then (law theta h0 h1 n h).toReal else 0) =
      (1-theta)^n * (law 0 (by norm_num) (by norm_num) n h).toReal := by
  by_cases hs : survives n h
  · simp [hs, safe_mass_ratio theta h0 h1 n h hs]
  · have hz : (law 0 (by norm_num) (by norm_num) n h).toReal = 0 := by
      by_contra hz
      exact hs (zero_law_supported_safe n h hz)
    simp [hs,hz]

def survivalMass (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) (n : ℕ) : ℝ :=
  ∑ h : History n, if survives n h then (law theta h0 h1 n h).toReal else 0

theorem exact_survival_mass (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) (n : ℕ) :
    survivalMass theta h0 h1 n = (1-theta)^n := by
  unfold survivalMass
  simp_rw [restricted_mass]
  rw [← Finset.mul_sum, coverage_sum_toReal, mul_one]

/-- ENNReal form used by the original PMF conditioning API. -/
theorem restricted_ennreal (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (n : ℕ) (h : History n) :
    (if survives n h then law theta h0 h1 n h else 0) =
      ENNReal.ofReal ((1-theta)^n) * law 0 (by norm_num) (by norm_num) n h := by
  have hp : 0 ≤ (1-theta)^n := pow_nonneg (by linarith) _
  apply (ENNReal.toReal_eq_toReal_iff' (by split_ifs <;> simp [PMF.apply_ne_top])
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (PMF.apply_ne_top _ _))).mp
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hp, apply_ite, ENNReal.toReal_zero]
    using restricted_mass theta h0 h1 n h

theorem restricted_total (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) (n : ℕ) :
    (∑' h : History n, if survives n h then law theta h0 h1 n h else 0) =
      ENNReal.ofReal ((1-theta)^n) := by
  simp_rw [restricted_ennreal]
  rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]

theorem survival_supported (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta < 1) (n : ℕ) :
    ∃ h : History n, h ∈ {h | survives n h} ∧ h ∈ (law theta h0 h1.le n).support := by
  by_contra hn
  have hz : ∀ h : History n, (if survives n h then law theta h0 h1.le n h else 0) = 0 := by
    intro h
    by_cases hs : survives n h
    · have he : law theta h0 h1.le n h = 0 := by
        by_contra he
        exact hn ⟨h, hs, (PMF.mem_support_iff _ _).mpr he⟩
      simp [hs,he]
    · simp [hs]
  have he := restricted_total theta h0 h1.le n
  simp_rw [hz, tsum_zero] at he
  exact (ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos (sub_pos.mpr h1) n))) he.symm

/-- Entire actual state/action path conditioned on survival is exactly pi0's
    unconditioned complete record, for every horizon including zero. -/
theorem full_conditioned_path_eq_zero_policy
    (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta < 1) (n : ℕ) :
    (law theta h0 h1.le n).filter {h | survives n h}
      (survival_supported theta h0 h1 n) = law 0 (by norm_num) (by norm_num) n := by
  apply PMF.ext
  intro h
  rw [PMF.filter_apply]
  have hi : Set.indicator {h | survives n h} (law theta h0 h1.le n) =
      (fun h => if survives n h then law theta h0 h1.le n h else 0) := by
    funext h
    simp [Set.indicator_apply]
  rw [hi]
  dsimp only
  rw [restricted_ennreal, restricted_total]
  rw [mul_right_comm, ENNReal.mul_inv_cancel
    (ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos (sub_pos.mpr h1) n))) ENNReal.ofReal_ne_top, one_mul]

/-- This is also the existing observed-history production control kernel. -/
def observedPolicy (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    ∀ n, CausalHistory Bool (Bool × Bool) n → PMF Bool := fun _ _ => actionLaw theta h0 h1

theorem actual_record_law (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) (n : ℕ) :
    law theta h0 h1 n = causalLaw (PMF.pure (true,false))
      (riskMicroControlKernel Prod.fst (fun _ => M.transitionPMF) (observedPolicy theta h0 h1)) n := rfl

theorem actual_survival_probability (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) (n : ℕ) :
    (law theta h0 h1 n).toMeasure {h | survives n h} = ENNReal.ofReal ((1-theta)^n) := by
  rw [PMF.toMeasure_apply (law theta h0 h1 n) (Set.toFinite _).measurableSet]
  simpa [Set.indicator_apply] using restricted_total theta h0 h1 n

theorem actual_first_exit_probability (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) (n : ℕ) :
    (law theta h0 h1 n).toMeasure.real {h | ¬ survives n h} = 1-(1-theta)^n := by
  have hs : MeasurableSet {h : History n | survives n h} := (Set.toFinite _).measurableSet
  change (law theta h0 h1 n).toMeasure.real {h | survives n h}ᶜ = _
  rw [MeasureTheory.measureReal_compl hs, MeasureTheory.probReal_univ]
  rw [MeasureTheory.Measure.real, actual_survival_probability, ENNReal.toReal_ofReal (pow_nonneg (by linarith) _)]

/-- Actual row occupancy for THIS deployment policy, including null-history completion. -/
theorem actual_uncertified_occupancy (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) (n : ℕ) :
    (coverageDeploymentRowLaw (PMF.pure (true,false)) Prod.fst (fun _ => M.transitionPMF)
      (observedPolicy theta h0 h1) n).toMeasure.real {xa | ¬ (xa.2 = true)} = theta := by
  rw [← coverage_uncovered_indicator_expectation _ (fun xa : State × Bool => xa.2 = true),
    coverage_rowLaw_expectation]
  simp only [observedPolicy, actionLaw_real]
  simp only [Fintype.sum_bool, actionWeight, Bool.false_eq_true, if_false, if_true,
    mul_zero, mul_one, zero_add]
  rw [← Finset.sum_mul, coverage_sum_toReal, one_mul]

theorem all_rows_certified_zero_occupancy (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) (n : ℕ) :
    (coverageDeploymentRowLaw (PMF.pure (true,false)) Prod.fst (fun _ => M.transitionPMF)
      (observedPolicy theta h0 h1) n).toMeasure.real {_xa | ¬ True} = 0 := by simp

/-- An explicitly different reference kernel: all actions are recorded but its
    physical successor always uses the safe row. Only true is source-certified. -/
def referenceStep (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) (n : ℕ) (h : History n) :
    PMF (Bool × State) := pmfExtend (actionLaw theta h0 h1)
      (fun _ => M.transitionPMF (riskLastState n h) true)
def referenceLaw (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) (n : ℕ) : PMF (History n) :=
  causalLaw (PMF.pure (true,false)) (referenceStep theta h0 h1) n

theorem reference_correct_on_certified (x : State) (a : Bool) (ha : a = true) :
    M.transitionPMF x a = M.transitionPMF x true := by rw [ha]

theorem reference_supported_safe (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    ∀ n (h : History n), (referenceLaw theta h0 h1 n h).toReal ≠ 0 → survives n h := by
  intro n
  induction n with
  | zero =>
      intro h hh
      exact zero_law_supported_safe 0 h hh
  | succ n ih =>
      rintro ⟨h,a,b,u⟩ hh
      change (pmfExtend (referenceLaw theta h0 h1 n) (referenceStep theta h0 h1 n) (h,(a,(b,u)))).toReal ≠ 0 at hh
      rw [pmfExtend_apply] at hh
      change ((referenceLaw theta h0 h1 n h) *
        (pmfExtend (actionLaw theta h0 h1) (fun _ => M.transitionPMF (riskLastState n h) true) (a,(b,u)))).toReal ≠ 0 at hh
      rw [pmfExtend_apply, ENNReal.toReal_mul, ENNReal.toReal_mul, transition_real] at hh
      refine ⟨ih h (by intro hz; simp [hz] at hh), ?_⟩
      cases b with
      | false => simp at hh
      | true => rfl

theorem reference_zero_exit_probability (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) (n : ℕ) :
    (referenceLaw theta h0 h1 n).toMeasure.real {h | ¬ survives n h} = 0 := by
  rw [← coverage_uncovered_indicator_expectation _ (survives n)]
  apply Finset.sum_eq_zero
  intro h _
  by_cases hs : survives n h
  · simp [hs]
  · have hz : (referenceLaw theta h0 h1 n h).toReal = 0 := by
      by_contra hz
      exact hs (reference_supported_safe theta h0 h1 n h hz)
    simp [hz]

/-- Positive-horizon conditioning at theta=1 is undefined; no survivor is
    manufactured by reweighting the zero-mass event. -/
theorem theta_one_positive_survival_zero (n : ℕ) :
    (law 1 (by norm_num) (by norm_num) (n+1)).toMeasure {h | survives (n+1) h} = 0 := by
  rw [actual_survival_probability]
  simp

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ConflictParametricPath
