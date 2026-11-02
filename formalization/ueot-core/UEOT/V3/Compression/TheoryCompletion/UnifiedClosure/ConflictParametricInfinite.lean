import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ConflictParametricPath
import Mathlib.Probability.Independence.InfinitePi

/-! The same actual full state/action experiment, on its explicit IID event source.
Finite prefixes are proved equal to the original causal PMF, not only to a marginal.
The event source's two redundant visible coordinates are the actual action and next state.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ConflictParametricInfinite
open MeasureTheory ProbabilityTheory Set Filter
open UEOT.V3.PathError UEOT.V3.FiniteDiscountedControl
open ConflictParametricSource ConflictParametricPath
open scoped ENNReal Topology
noncomputable section
abbrev Symbol := Bool × State
abbrev Stream := ℕ → Symbol

def eventRow (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) : PMF Symbol :=
  step theta h0 h1 0 (true,false)

theorem step_eq_eventRow (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (n : ℕ) (h : History n) : step theta h0 h1 n h = eventRow theta h0 h1 := by
  rfl

def source (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) : Measure Stream :=
  Measure.infinitePi (fun _ : ℕ => (eventRow theta h0 h1).toMeasure)
instance source_probability (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    IsProbabilityMeasure (source theta h0 h1) := by unfold source; infer_instance

def recordPrefix : (n : ℕ) → Stream → History n
  | 0, _ => (true,false)
  | n+1, w => (recordPrefix n w,w n)

theorem measurable_prefix : ∀ n, Measurable (recordPrefix n) := by
  intro n
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact ih.prodMk (measurable_pi_apply n)

abbrev past (k : ℕ) : MeasurableSpace Stream :=
  ⨆ j : ℕ, ⨆ (_ : j < k), MeasurableSpace.comap (fun w : Stream => w j) inferInstance

theorem prefix_past (k : ℕ) : ∀ n, n ≤ k → Measurable[past k] (recordPrefix n) := by
  intro n
  induction n with
  | zero => intro _; exact measurable_const
  | succ n ih =>
      intro hn
      have hc : Measurable[past k] (fun w : Stream => w n) := by
        apply Measurable.of_comap_le
        exact le_iSup_of_le n (le_iSup_of_le (show n < k by omega) le_rfl)
      exact (ih (by omega)).prodMk hc

theorem current_independent_prefix (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) (n : ℕ) :
    IndepFun (recordPrefix n) (fun w : Stream => w n) (source theta h0 h1) := by
  have hd : Disjoint ({n} : Set ℕ) {j | j < n} := by simp
  have hi := indep_iSup_of_disjoint (fun j : ℕ => (measurable_pi_apply j).comap_le)
    (iIndepFun_infinitePi (P := fun _ : ℕ => (eventRow theta h0 h1).toMeasure)
      (X := fun _ x => x) (fun _ => measurable_id)).iIndep hd
  have hc : Indep (MeasurableSpace.comap (fun w : Stream => w n) inferInstance)
      (past n) (source theta h0 h1) := by
    simpa only [iSup_singleton,past,Set.mem_ofPred_eq,source] using hi
  change Indep (MeasurableSpace.comap (recordPrefix n) inferInstance)
    (MeasurableSpace.comap (fun w : Stream => w n) inferInstance) (source theta h0 h1)
  exact indep_of_indep_of_le hc.symm (prefix_past n n le_rfl).comap_le le_rfl

theorem constant_extend_toMeasure {H Z : Type*} [Fintype H] [Fintype Z]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    [MeasurableSpace Z] [MeasurableSingletonClass Z] (p : PMF H) (q : PMF Z) :
    (pmfExtend p (fun _ => q)).toMeasure = p.toMeasure.prod q.toMeasure := by
  apply Measure.ext_of_singleton
  rintro ⟨h,z⟩
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    ← Set.singleton_prod_singleton, Measure.prod_prod]
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  exact pmfExtend_apply p (fun _ => q) h z

/-- Every full finite cylinder is the actual production state/action causal law. -/
theorem finite_record_cylinder (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    ∀ n, (source theta h0 h1).map (recordPrefix n) = (law theta h0 h1 n).toMeasure := by
  intro n
  induction n with
  | zero =>
      change (source theta h0 h1).map (fun _ => (true,false)) = (PMF.pure (true,false)).toMeasure
      rw [Measure.map_const, PMF.toMeasure_pure]
      simp
  | succ n ih =>
      have hj := (current_independent_prefix theta h0 h1 n).map_prod_eq_prod_map_map
        (measurable_prefix n).aemeasurable (measurable_pi_apply n).aemeasurable
      have hc : (source theta h0 h1).map (fun w : Stream => w n) = (eventRow theta h0 h1).toMeasure :=
        Measure.infinitePi_map_eval _ n
      rw [ih,hc] at hj
      change (source theta h0 h1).map (fun w => (recordPrefix n w,w n)) =
        (pmfExtend (law theta h0 h1 n) (step theta h0 h1 n)).toMeasure
      rw [show step theta h0 h1 n = (fun _ => eventRow theta h0 h1) by
        funext h; exact step_eq_eventRow theta h0 h1 n h]
      rw [constant_extend_toMeasure]
      exact hj
/-- The chronological record projections are consistent on every source stream. -/
theorem record_prefix_consistent (n : ℕ) (w : Stream) :
    (recordPrefix (n+1) w).1 = recordPrefix n w := rfl

theorem actual_survival_cylinder (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) (n : ℕ) :
    source theta h0 h1 {w | survives n (recordPrefix n w)} = ENNReal.ofReal ((1-theta)^n) := by
  have hs : MeasurableSet {h : History n | survives n h} := (Set.toFinite _).measurableSet
  change source theta h0 h1 ((recordPrefix n) ⁻¹' {h | survives n h}) = _
  rw [← Measure.map_apply (measurable_prefix n) hs, finite_record_cylinder, actual_survival_probability]

/-- Positive risk at arbitrarily late horizons is one actual countable experiment,
    not unrelated finite deployments. -/
theorem persistent_survival_null (theta : ℝ) (h0 : 0 < theta) (h1 : theta ≤ 1) :
    source theta h0.le h1 {w | ∀ n, survives n (recordPrefix n w)} = 0 := by
  have hb : ∀ n : ℕ, source theta h0.le h1 {w | ∀ n, survives n (recordPrefix n w)} ≤
      ENNReal.ofReal ((1-theta)^n) := by
    intro n
    calc
      _ ≤ source theta h0.le h1 {w | survives n (recordPrefix n w)} :=
        measure_mono (show {w : Stream | ∀ n, survives n (recordPrefix n w)} ⊆
          {w | survives n (recordPrefix n w)} from fun w hw => hw n)
      _ = _ := actual_survival_cylinder theta h0.le h1 n
  have ht : Tendsto (fun n : ℕ => ENNReal.ofReal ((1-theta)^n)) atTop (nhds 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp
      (tendsto_pow_atTop_nhds_zero_of_lt_one (show 0 ≤ 1-theta by linarith) (show 1-theta < 1 by linarith))
  exact le_antisymm (ge_of_tendsto ht (Filter.Eventually.of_forall hb)) bot_le

theorem actual_eventual_failure_ae (theta : ℝ) (h0 : 0 < theta) (h1 : theta ≤ 1) :
    ∀ᵐ w ∂source theta h0.le h1, ∃ n, ¬ survives n (recordPrefix n w) := by
  rw [ae_iff]
  have he : {w : Stream | ¬ ∃ n, ¬ survives n (recordPrefix n w)} =
      {w | ∀ n, survives n (recordPrefix n w)} := by
    ext w
    simp
  rw [he]
  exact persistent_survival_null theta h0 h1

/-- The zero-reference certificate pays THIS policy's theta occupation each tick. -/
theorem actual_zero_reference_budget (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) (n : ℕ) :
    (law theta h0 h1 n).toMeasure.real {h | ¬ survives n h} ≤
      (referenceLaw theta h0 h1 n).toMeasure.real {h | ¬ survives n h} + n*theta := by
  rw [actual_first_exit_probability, reference_zero_exit_probability, zero_add]
  have h := UEOT.V3.PathError.one_sub_prod_one_sub_le_sum (fun _ => theta) (fun _ => h0) (fun _ => h1) n
  simpa using h

/-- The zero endpoint is a different actual infinite experiment and stays safe. -/
theorem zero_theta_survives_ae :
    ∀ᵐ w ∂source 0 (by norm_num) (by norm_num), ∀ n, survives n (recordPrefix n w) := by
  rw [ae_all_iff]
  intro n
  rw [ae_iff]
  have hs : MeasurableSet {w : Stream | survives n (recordPrefix n w)} :=
    (Set.toFinite {h : History n | survives n h}).measurableSet.preimage (measurable_prefix n)
  change source 0 (by norm_num) (by norm_num) {w | survives n (recordPrefix n w)}ᶜ = 0
  rw [measure_compl hs (measure_ne_top _ _), actual_survival_cylinder]
  simp

/-- Actual source row; the action label and next visible coordinate agree,
    and the hidden bit is freshly fair at either value. -/
theorem actual_event_mass (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (a b u : Bool) :
    (eventRow theta h0 h1 (a,(b,u))).toReal =
      actionWeight theta a * (if b = a then (1/2 : ℝ) else 0) := by
  change (pmfExtend (actionLaw theta h0 h1) (M.transitionPMF (true,false)) (a,(b,u))).toReal = _
  rw [pmfExtend_apply, ENNReal.toReal_mul, actionLaw_real, transition_real]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ConflictParametricInfinite
