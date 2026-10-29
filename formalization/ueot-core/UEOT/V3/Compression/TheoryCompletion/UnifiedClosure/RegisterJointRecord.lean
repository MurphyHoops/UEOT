import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismPurpose
import UEOT.V3.FiniteDiscountedApproxQuotient

/-! Actual finite execution records for the same register mechanism and causal
policy. The finite action/label words below are only the interpreter's literal
input tape, not a new general path framework. Memory can be arbitrary Type 0;
the given policy reads states/actions and does not receive the fresh birth label.
The parent persists; time-indexed transactions record each birth separately.
List Bool lineage addresses retain their original single-lineage limitation.
The registered child count counts successful birth transactions, not globally
distinct individual IDs across repeated Boolean birth labels. Physical dynamics
are the original action model here, without the later P5 environmental faults.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointRecord
open UEOT.V3.FiniteDiscountedControl
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose
open scoped BigOperators
noncomputable section

structure Record (n : ℕ) where
  parentBefore : Organism n
  action : Action
  label : Bool
  parentAfter : Organism n
  child : Option (Organism n)
  expenditure : ℝ

/-- Controlled action moves the actual parent; reproduction preserves that
parent's identity and copies its source program into the actual child. -/
def recordStep {n : ℕ} (i : Fin n) (m : Mechanism)
    (o : Organism n) (a : Action) (label : Bool) : Record n :=
  let post : Organism n := {o with physical := update i o.physical a}
  { parentBefore := o, action := a, label := label, parentAfter := post
    child := if post.physical i = o.program then some (birthEvent i label post) else none
    expenditure := cost m a }

@[simp] theorem record_parent_history {n : ℕ} (i : Fin n) (m : Mechanism)
    (o : Organism n) (a : Action) (label : Bool) :
    (recordStep i m o a label).parentAfter.history = o.history := rfl

@[simp] theorem record_parent_program {n : ℕ} (i : Fin n) (m : Mechanism)
    (o : Organism n) (a : Action) (label : Bool) :
    (recordStep i m o a label).parentAfter.program = o.program := rfl

theorem record_child_source {n : ℕ} (i : Fin n) (m : Mechanism)
    (o : Organism n) (a : Action) (label : Bool) (c : Organism n)
    (hc : (recordStep i m o a label).child = some c) :
    c = birthEvent i label (recordStep i m o a label).parentAfter ∧
      (lineage i).OffspringOf (recordStep i m o a label).parentAfter c ∧
      c.program = o.program := by
  dsimp only [recordStep] at hc ⊢
  split_ifs at hc with h
  · have he := Option.some.inj hc
    subst c
    exact ⟨rfl, birth_is_distinct_offspring i label _, rfl⟩

/-- The birth interpreter performs no additional physical write after the
successful allowed action: its repair test is already satisfied. -/
theorem record_child_physical {n : ℕ} (i : Fin n) (m : Mechanism)
    (o : Organism n) (a : Action) (label : Bool) (c : Organism n)
    (hc : (recordStep i m o a label).child = some c) :
    c.physical = (recordStep i m o a label).parentAfter.physical := by
  dsimp only [recordStep] at hc ⊢
  split_ifs at hc with h
  have he := Option.some.inj hc
  subst c
  change update i (update i o.physical a)
    ((substrate i).execute o.program (update i o.physical a)) = update i o.physical a
  rw [execute_compiled, if_pos h]
  rfl

def payoff {n : ℕ} (price : NNReal) (r : Record n) : ℝ :=
  childCount r.child - (price : ℝ) * r.expenditure

theorem record_payoff_eq {n : ℕ} (i : Fin n) (m : Mechanism) (price : NNReal)
    (o : Organism n) (a : Action) (label : Bool) (ho : o.program = m.goal) :
    payoff price (recordStep i m o a label) =
      (if update i o.physical a i = m.goal then 1 else 0) -
        (price : ℝ) * cost m a := by
  simp only [payoff, recordStep, ho]
  split_ifs <;> rfl

/-- A finite literal tape, with one actual allowed action and noise label per
stage. All tapes, including zero-weight and failed-birth tapes, are retained. -/
@[reducible] def Tape : ℕ → Type
  | 0 => Unit
  | k+1 => Action × Bool × Tape k

@[reducible] instance tapeFintype : (k : ℕ) → Fintype (Tape k)
  | 0 => inferInstanceAs (Fintype Unit)
  | k+1 => by
    letI := tapeFintype k
    exact inferInstanceAs (Fintype (Action × Bool × Tape k))

variable {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
variable (pi : CausalPolicy.{0,0,0} (State n) (fun _ => Action))

/-- Actual source trace: the next policy memory receives exactly the physical
successor, while the continuing parent and full birth/cost record are retained. -/
def records : (k : ℕ) → {t : ℕ} → pi.Memory t → Organism n → Tape k → List (Record n)
  | 0, _, _, _, _ => []
  | k+1, _, h, o, (a,label,rest) =>
      let r := recordStep i m o a label
      r :: records k (pi.advance h a r.parentAfter.physical) r.parentAfter rest

/-- Source likelihood from the SAME actual policy; no existential controller
or observation permission is substituted. -/
def weight : (k : ℕ) → {t : ℕ} → pi.Memory t → Organism n → Tape k → ℝ
  | 0, _, _, _, _ => 1
  | k+1, _, h, o, (a,label,rest) =>
      let r := recordStep i m o a label
      pi.actionProb h a * (noise label).toReal *
        weight k (pi.advance h a r.parentAfter.physical) r.parentAfter rest

theorem weight_nonneg : ∀ (k : ℕ) {t : ℕ} (h : pi.Memory t) (o : Organism n) (w : Tape k),
    0 ≤ weight i noise m pi k h o w := by
  intro k
  induction k with
  | zero => intros; exact zero_le_one
  | succ k ih =>
      rintro t h o ⟨a,label,rest⟩
      exact mul_nonneg (mul_nonneg (pi.actionProb_nonneg h a) ENNReal.toReal_nonneg) (ih _ _ _)

private theorem noise_sum : ∑ label, (noise label).toReal = 1 := by
  have h := congrArg ENNReal.toReal (PMF.tsum_coe noise)
  rw [tsum_fintype, ENNReal.toReal_sum (fun label _ => PMF.apply_ne_top _ label)] at h
  simpa using h

theorem weight_sum_one : ∀ (k : ℕ) {t : ℕ} (h : pi.Memory t) (o : Organism n),
    ∑ w : Tape k, weight i noise m pi k h o w = 1 := by
  intro k
  induction k with
  | zero => intros; simp [Tape, weight]
  | succ k ih =>
      intro t h o
      simp only [Tape, Fintype.sum_prod_type, weight]
      simp_rw [← Finset.mul_sum, ih, mul_one]
      simp_rw [← Finset.mul_sum, noise_sum, mul_one]
      exact pi.actionProb_sum_one h

/-- Existing trusted finite probability-row constructor supplies the actual
full-tape PMF from the proved normalized likelihood. -/
def tapeLaw (k : ℕ) {t : ℕ} (h : pi.Memory t) (o : Organism n) : PMF (Tape k) :=
  FiniteProbabilityRow.ofRealRow (weight i noise m pi k h o)
    (weight_nonneg i noise m pi k h o) (weight_sum_one i noise m pi k h o)

@[simp] theorem tapeLaw_real (k : ℕ) {t : ℕ} (h : pi.Memory t) (o : Organism n) (w : Tape k) :
    (tapeLaw i noise m pi k h o w).toReal = weight i noise m pi k h o w :=
  FiniteProbabilityRow.ofRealRow_apply_toReal _ _ _ _

/-- Actual recorded path law, retaining every child and actual expenditure. -/
def recordLaw (k : ℕ) {t : ℕ} (h : pi.Memory t) (o : Organism n) : PMF (List (Record n)) :=
  (tapeLaw i noise m pi k h o).map (records i m pi k h o)

def discountedPayoff {n : ℕ} (price : NNReal) (d : ℝ) : List (Record n) → ℝ
  | [] => 0
  | r :: rs => payoff price r + d * discountedPayoff price d rs

/-- Explicit finite-source expectation of the actual recorded discounted sum. -/
def actualExpectation (price : NNReal) (d : ℝ) (k : ℕ)
    {t : ℕ} (h : pi.Memory t) (o : Organism n) : ℝ :=
  ∑ w : Tape k, (tapeLaw i noise m pi k h o w).toReal *
    discountedPayoff price d (records i m pi k h o w)

private theorem weighted_affine {S : Type*} [Fintype S] (p : S → ℝ)
    (hm : ∑ w, p w = 1) (c d : ℝ) (v : S → ℝ) :
    (∑ w, p w * (c + d * v w)) = c + d * ∑ w, p w * v w := by
  calc
    _ = (∑ w, p w) * c + d * (∑ w, p w * v w) := by
      rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro w _
      ring
    _ = _ := by rw [hm, one_mul]

theorem actualExpectation_succ (price : NNReal) (d : ℝ)
    (k : ℕ) {t : ℕ} (h : pi.Memory t) (o : Organism n) (ho : o.program = m.goal) :
    actualExpectation i noise m pi price d (k+1) h o =
      ∑ a, pi.actionProb h a *
        (stage i noise price m o.physical a + d *
          actualExpectation i noise m pi price d k
            (pi.advance h a (update i o.physical a))
            {o with physical := update i o.physical a}) := by
  classical
  simp only [actualExpectation, tapeLaw_real]
  change (∑ w : Action × Bool × Tape k, _) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Fintype.sum_prod_type]
  simp only [tapeLaw, FiniteProbabilityRow.ofRealRow_apply_toReal]
  simp only [records, discountedPayoff, weight, record_payoff_eq i m price o a _ ho]
  dsimp only [recordStep]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [weighted_affine _ (weight_sum_one i noise m pi k _ _)]
  rw [← Finset.sum_mul, noise_sum, one_mul]
  rw [stage, expectedChildren_eq]

/-- The literal complete record law realizes the SAME supplied policy's
finite discounted value. Initial physical/program matching are explicit; the
expectation identity is a theorem, never a model field. -/
theorem actualExpectation_eq_truncatedValue (price : NNReal) (d : ℝ)
    (hd : 0 < d ∧ d < 1) :
    ∀ (k : ℕ) {t : ℕ} (h : pi.Memory t) (o : Organism n),
      o.physical = pi.current h → o.program = m.goal →
      actualExpectation i noise m pi price d k h o =
        pi.truncatedValue (model i noise price d hd m) k h := by
  intro k
  induction k with
  | zero =>
      intro t h o hx hp
      simp [actualExpectation, records, discountedPayoff, CausalPolicy.truncatedValue]
  | succ k ih =>
      intro t h o hx hp
      rw [actualExpectation_succ i noise m pi price d k h o hp,
        CausalPolicy.truncatedValue_succ]
      apply Finset.sum_congr rfl
      intro a _
      rw [ih (pi.advance h a (update i o.physical a))
        {o with physical := update i o.physical a}
        (pi.current_advance h a (update i o.physical a)).symm hp]
      rw [hx]
      have he := model_expect_eq_update i noise price d hd m
        (fun y => pi.truncatedValue (model i noise price d hd m) k (pi.advance h a y))
        (pi.current h) a
      change pi.actionProb h a *
        (stage i noise price m (pi.current h) a + d * _) =
        pi.actionProb h a * ((model i noise price d hd m).reward (pi.current h) a +
          d * (model i noise price d hd m).expect (pi.current h) a
            (fun y => pi.truncatedValue (model i noise price d hd m) k (pi.advance h a y)))
      rw [he]
      rfl

/-- The complete transaction list includes every stage, including failed births. -/
theorem records_length : ∀ (k : ℕ) {t : ℕ} (h : pi.Memory t) (o : Organism n) (w : Tape k),
    (records i m pi k h o w).length = k := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih =>
      rintro t h o ⟨a,label,rest⟩
      simp only [records, List.length_cons, ih]

/-- Every recorded birth has its real post-action parent and literal copied
program; the same ongoing parent identity persists throughout the record. -/
theorem records_source_semantics :
    ∀ (k : ℕ) {t : ℕ} (h : pi.Memory t) (o : Organism n) (w : Tape k),
    ∀ r ∈ records i m pi k h o w,
      r.parentBefore.history = o.history ∧ r.parentAfter.history = o.history ∧
      r.parentBefore.program = o.program ∧ r.parentAfter.program = o.program ∧
      (∀ c, r.child = some c → (lineage i).OffspringOf r.parentAfter c ∧ c.program = o.program) := by
  intro k
  induction k with
  | zero => intro t h o w r hr; cases hr
  | succ k ih =>
      rintro t h o ⟨a,label,rest⟩ r hr
      simp only [records, List.mem_cons] at hr
      rcases hr with he | hr
      · subst r
        refine ⟨rfl,rfl,rfl,rfl,?_⟩
        intro c hc
        exact (record_child_source i m o a label c hc).2
      · simpa only [record_parent_history, record_parent_program] using
          (ih (pi.advance h a (recordStep i m o a label).parentAfter.physical)
            (recordStep i m o a label).parentAfter rest r hr)

/-- Nondegenerate two-stage literal consumer: the actual compiled program
writes the bad register once, then idles; both births and the literal cost
remain in its complete record. The noise law is not replaced by one seed. -/
theorem compiled_two_stage_record (noise : PMF Bool) (c price : NNReal) (d : ℝ)
    (history : List Bool) (label0 label1 : Bool) :
    let m : Mechanism := ⟨true,c⟩
    let pi := selectorPolicy ((substrate (0 : Fin 1)).execute true)
    let o : Organism 1 := ⟨history, fun _ => false, true⟩
    let w : Tape 2 := (some true, label0, none, label1, ())
    (tapeLaw (0 : Fin 1) noise m pi 2 (t := 0) (fun _ => false) o w).toReal =
        (noise label0).toReal * (noise label1).toReal ∧
      discountedPayoff price d (records 0 m pi 2 (t := 0) (fun _ => false) o w) =
        (1 - (price : ℝ) * (c : ℝ)) + d := by
  dsimp only
  constructor
  · simp [tapeLaw, FiniteProbabilityRow.ofRealRow_apply_toReal, weight, selectorPolicy,
      recordStep, execute_compiled, update]
  · simp [records, discountedPayoff, payoff, recordStep, childCount, cost, update]

section Integral
open MeasureTheory
local instance tapeMeasurableSpace (k : ℕ) : MeasurableSpace (Tape k) := ⊤
local instance tapeSingletonClass (k : ℕ) : MeasurableSingletonClass (Tape k) := ⟨fun _ => trivial⟩
local instance recordMeasurableSpace : MeasurableSpace (List (Record n)) := ⊤
local instance recordSingletonClass : MeasurableSingletonClass (List (Record n)) := ⟨fun _ => trivial⟩

/-- The actual finite record payoff is integrable; the expectation below is
not relying on the default value of an undefined Bochner integral. -/
theorem recorded_payoff_integrable (price : NNReal) (d : ℝ) (k : ℕ)
    {t : ℕ} (h : pi.Memory t) (o : Organism n) :
    Integrable (discountedPayoff price d) (recordLaw i noise m pi k h o).toMeasure := by
  have hm : Measurable (records i m pi k h o) := measurable_of_finite _
  have hp : Measurable (discountedPayoff (n := n) price d) := by intro s hs; trivial
  rw [recordLaw, ← PMF.toMeasure_map _ _ hm]
  exact (integrable_map_measure hp.aestronglyMeasurable hm.aemeasurable).mpr Integrable.of_finite

/-- Actual record-law expectation, not just a terminal physical marginal. The
record uses the explicit discrete sigma algebra; each finite experiment has
finite support although record fields and policy memory need not be finite. -/
theorem integral_recordLaw_eq_actualExpectation (price : NNReal) (d : ℝ) (k : ℕ)
    {t : ℕ} (h : pi.Memory t) (o : Organism n) :
    (∫ rs, discountedPayoff price d rs ∂(recordLaw i noise m pi k h o).toMeasure) =
      actualExpectation i noise m pi price d k h o := by
  have hm : Measurable (records i m pi k h o) := measurable_of_finite _
  have hp : Measurable (discountedPayoff (n := n) price d) := by intro s hs; trivial
  rw [recordLaw, ← PMF.toMeasure_map _ _ hm, integral_map hm.aemeasurable hp.aestronglyMeasurable,
    PMF.integral_eq_sum]
  rfl

/-- Registered evaluation is the expectation of the actual full execution
record of the SAME supplied causal policy, at every finite horizon. -/
theorem actual_record_integral_eq_policy_value (price : NNReal) (d : ℝ)
    (hd : 0 < d ∧ d < 1) (k : ℕ) {t : ℕ} (h : pi.Memory t) (o : Organism n)
    (hx : o.physical = pi.current h) (hp : o.program = m.goal) :
    (∫ rs, discountedPayoff price d rs ∂(recordLaw i noise m pi k h o).toMeasure) =
      pi.truncatedValue (model i noise price d hd m) k h := by
  rw [integral_recordLaw_eq_actualExpectation,
    actualExpectation_eq_truncatedValue i noise m pi price d hd k h o hx hp]

/-- A source-level objective defined on actual recorded deployments. The
initial program is the mechanism's source, and the founder journal is retained. -/
def recordedObjective (history : List Bool) (price : NNReal) (d : ℝ) (k : ℕ) :
    UEOT.V3.Compression.TheoryCompletion.NumericalObjective (Deployment n) :=
  fun run => ∫ rs, discountedPayoff price d rs ∂
    (recordLaw i noise m run.1 k run.2 ⟨history, run.1.current run.2, m.goal⟩).toMeasure

theorem recordedObjective_eq_objective (history : List Bool) (price : NNReal) (d : ℝ)
    (hd : 0 < d ∧ d < 1) (k : ℕ) :
    recordedObjective i noise m history price d k = objective i noise price d hd k m := by
  funext run
  exact actual_record_integral_eq_policy_value i noise m run.1 price d hd k run.2
    ⟨history, run.1.current run.2, m.goal⟩ rfl rfl

/-- The original C6 identification consumer now applies to actual complete
record expectations, with the same evaluation price and source experiment. -/
theorem recorded_observation_identifies_purpose (history : List Bool) (price : NNReal)
    (d : ℝ) (hd : 0 < d ∧ d < 1) (k : ℕ) (m' : Mechanism)
    (he : observe i noise m = observe i noise m') :
    UEOT.V3.Compression.TheoryCompletion.TeleologicalObjectiveClass
      (recordedObjective i noise m history price d k) =
    UEOT.V3.Compression.TheoryCompletion.TeleologicalObjectiveClass
      (recordedObjective i noise m' history price d k) := by
  rw [recordedObjective_eq_objective i noise m history price d hd k,
    recordedObjective_eq_objective i noise m' history price d hd k]
  exact registered_observation_identifies_purpose i noise price d hd k m m' he

end Integral

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointRecord
