import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterRotatingBodySource
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Analysis.SpecificLimits.Basic

/-!
Original promise: time-varying body recovery must persist on an actual ongoing source, not a finite protocol padded with None.
Existing result: literal complete round execution and exact source BodyGoal probability are derived from old actions/modes/labels.
Reduced premise: construct SAME parent infinite round execution/complete record probability readout and derive exact nonoverlapping return tails from the original independent primitive product.
Model/boundary: registered Fin n sweep per round, full old body+clock observation, fixed b/cost/source; macro k means n*k actual transactions, n0 remains explicitly empty physical execution.
Consumer: actual complete ongoing records/body-return probabilities; original P10 kernel/hitting interface is a subsequent thin source consumer, not assumed here.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterRotatingBodyReturns
open MeasureTheory ProbabilityTheory Set Filter
open RegisterRepairSource RegisterRepairHistory RegisterFaultJointRecord
open RegisterRotatingBodySource
open scoped ENNReal Topology BigOperators
noncomputable section

abbrev RoundStream (n : ℕ) := ℕ → RoundRaw n

def infiniteLaw (n : ℕ) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) : Measure (RoundStream n) :=
  Measure.infinitePi (fun _ : ℕ=>roundLaw n noise epsilon he)
instance infiniteLaw_probability (n : ℕ) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) :
    IsProbabilityMeasure (infiniteLaw n noise epsilon he) := by unfold infiniteLaw;infer_instance

def bodyState {n : ℕ} (b : Bool) (raw : RoundRaw n) : State n:=fun j=>if (raw j).1 then b else !b

def closedParent {n : ℕ} (b : Bool) (raw : RoundRaw n) (o : Organism n) : Organism n :=
  ⟨o.history,bodyState b raw,o.program⟩

theorem round_parent_formula {n : ℕ} (b : Bool) (cost : NNReal) (raw : RoundRaw n) (o : Organism n) :
    roundParent b cost raw o=closedParent b raw o := by
  have hH : (roundParent b cost raw o).history=o.history:=runPorts_history _ _ _ _ _
  have hP : (roundParent b cost raw o).program=o.program:=runPorts_program _ _ _ _ _
  have hF : (roundParent b cost raw o).physical=bodyState b raw:=funext (round_physical b cost raw o)
  cases he : roundParent b cost raw o with
  | mk history physical program =>
    simp only [he] at hH hP hF
    subst history
    subst physical
    subst program
    rfl

def parentAt {n : ℕ} (b : Bool) (cost : NNReal) (o : Organism n) (w : RoundStream n) : ℕ→Organism n
  | 0=>o
  | k+1=>roundParent b cost (w k) (parentAt b cost o w k)

@[simp] theorem parent_program {n : ℕ} (b : Bool) (cost : NNReal) (o : Organism n) (w : RoundStream n) (k : ℕ) :
    (parentAt b cost o w k).program=o.program := by
  induction k with
  | zero=>rfl
  | succ k ih=>simp only [parentAt,roundParent,runPorts_program,ih]
@[simp] theorem parent_history {n : ℕ} (b : Bool) (cost : NNReal) (o : Organism n) (w : RoundStream n) (k : ℕ) :
    (parentAt b cost o w k).history=o.history := by
  induction k with
  | zero=>rfl
  | succ k ih=>simp only [parentAt,roundParent,runPorts_history,ih]

/-- The closed form is DERIVED from actual repeated execution. It is not an
executed body reset or a resampled replacement parent. -/
theorem actual_parent_closed {n : ℕ} (b : Bool) (cost : NNReal) (o : Organism n) (w : RoundStream n) (k : ℕ) :
    parentAt b cost o w (k+1)=closedParent b (w k) o := by
  rw [parentAt,round_parent_formula]
  simp only [closedParent,parent_history,parent_program]

/-- Chronological actual finite prefix, including ALL n transactions per round. -/
def recordsThrough {n : ℕ} (b : Bool) (cost : NNReal) (o : Organism n) (w : RoundStream n) : ℕ→List (ModeRecord n)
  | 0=>[]
  | k+1=>recordsThrough b cost o w k ++ roundTrace b cost (w k) (parentAt b cost o w k)

theorem actual_prefix_length {n : ℕ} (b : Bool) (cost : NNReal) (o : Organism n) (w : RoundStream n) (k : ℕ) :
    (recordsThrough b cost o w k).length=n*k := by
  induction k with
  | zero=>rfl
  | succ k ih=>rw [recordsThrough,List.length_append,ih,roundTrace,trace_length,List.length_finRange];simp only [Nat.mul_succ]

/-- Every (round,port-index) is an actual transaction. No default/None padding
is used; n0 has no index and hence no actual micro-transactions. -/
def recordAt {n : ℕ} (b : Bool) (cost : NNReal) (o : Organism n) (k : ℕ) (j : Fin n) (w : RoundStream n) : ModeRecord n :=
  (roundTrace b cost (w k) (parentAt b cost o w k)).get
    ⟨j,by simpa only [roundTrace,trace_length,List.length_finRange] using j.isLt⟩

local instance {n : ℕ} : MeasurableSpace (ModeRecord n) := ⊤
local instance {n : ℕ} : MeasurableSingletonClass (ModeRecord n) := ⟨fun _=>trivial⟩

/-- Actual fee/child records factor through a finite raw domain. Adjacent
round records share prior state, and are NOT asserted iid. -/
theorem measurable_recordAt {n : ℕ} (b : Bool) (cost : NNReal) (o : Organism n) (k : ℕ) (j : Fin n) :
    Measurable (recordAt b cost o k j) := by
  cases k with
  | zero=>
    let F : RoundRaw n→ModeRecord n:=fun raw=>(roundTrace b cost raw o).get
      ⟨j,by simpa only [roundTrace,trace_length,List.length_finRange] using j.isLt⟩
    exact (measurable_of_finite F).comp (measurable_pi_apply 0)
  | succ k=>
    let F : RoundRaw n×RoundRaw n→ModeRecord n:=fun raw=>(roundTrace b cost raw.2 (closedParent b raw.1 o)).get
      ⟨j,by simpa only [roundTrace,trace_length,List.length_finRange] using j.isLt⟩
    have he : recordAt b cost o (k+1) j=fun w=>F (w k,w (k+1)) := by
      funext w
      let G : Organism n→ModeRecord n:=fun parent=>(roundTrace b cost (w (k+1)) parent).get
        ⟨j,by simpa only [roundTrace,trace_length,List.length_finRange] using j.isLt⟩
      exact congrArg G (actual_parent_closed b cost o w k)
    rw [he]
    exact (measurable_of_finite F).comp ((measurable_pi_apply k).prodMk (measurable_pi_apply (k+1)))

def recordPathLaw {n : ℕ} (b : Bool) (cost : NNReal) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) (o : Organism n) :
    Measure (ℕ→Fin n→ModeRecord n) :=
  (infiniteLaw n noise epsilon he).map (fun w k j=>recordAt b cost o k j w)

instance recordPathLaw_probability {n : ℕ} (b : Bool) (cost : NNReal) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) (o : Organism n) :
    IsProbabilityMeasure (recordPathLaw b cost noise epsilon he o) := by
  apply Measure.isProbabilityMeasure_map
  apply Measurable.aemeasurable
  exact measurable_pi_lambda _ (fun k=>measurable_pi_lambda _ (fun j=>measurable_recordAt b cost o k j))

/-- SAME literal round prefix, not a chosen independent desired trace. -/
theorem actual_round_records {n : ℕ} (b : Bool) (cost : NNReal) (o : Organism n) (w : RoundStream n) (k : ℕ) :
    List.ofFn (fun j : Fin n=>recordAt b cost o k j w)=roundTrace b cost (w k) (parentAt b cost o w k) := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,roundTrace,trace_length,List.length_finRange]
  · intro j hj hl
    simp only [List.getElem_ofFn]
    rfl

def Good {n : ℕ} (raw : RoundRaw n) : Prop:=∀j,(raw j).1=true

theorem good_measurable (n : ℕ) : MeasurableSet {raw : RoundRaw n | Good raw} := (Set.toFinite _).measurableSet

theorem actual_macro_goal_iff {n : ℕ} (b : Bool) (cost : NNReal) (o : Organism n) (w : RoundStream n) (k : ℕ) :
    BodyGoal b (parentAt b cost o w (k+1)).physical ↔ Good (w k) :=
  actual_round_goal_iff b cost (w k) (parentAt b cost o w k)

def successMass (n : ℕ) (epsilon : NNReal) : ℝ≥0∞:=((1-epsilon : NNReal) : ℝ≥0∞)^n

theorem good_mass (n : ℕ) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) :
    roundLaw n noise epsilon he {raw | Good raw}=successMass n epsilon := by
  have h:=actual_body_probability (n:=n) true 0 noise epsilon he (⟨[],(fun _=>false),true⟩ : Organism n)
  simpa only [actual_round_goal_iff,Good,successMass] using h

theorem actual_round_law (n : ℕ) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) (k : ℕ) :
    (infiniteLaw n noise epsilon he).map (fun w=>w k)=roundLaw n noise epsilon he :=
  Measure.infinitePi_map_eval _ k

theorem actual_round_independent (n : ℕ) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) :
    iIndepFun (fun k (w : RoundStream n)=>w k) (infiniteLaw n noise epsilon he) :=
  iIndepFun_infinitePi (fun _=>measurable_id)

/-- Exact actual body-goal marginal at every positive macro clock. -/
theorem actual_body_mass {n : ℕ} (b : Bool) (cost : NNReal) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1)
    (o : Organism n) (k : ℕ) :
    infiniteLaw n noise epsilon he {w | BodyGoal b (parentAt b cost o w (k+1)).physical}=successMass n epsilon := by
  simp_rw [actual_macro_goal_iff]
  change infiniteLaw n noise epsilon he ((fun w : RoundStream n=>w k) ⁻¹' {raw | Good raw})=_
  rw [←Measure.map_apply (measurable_pi_apply k) (good_measurable n),actual_round_law,good_mass]

/-- Probability of missing every complete body goal in a registered finite
window of R complete rounds. Independence is only of disjoint raw rounds. -/
theorem actual_no_return_tail {n : ℕ} (b : Bool) (cost : NNReal) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1)
    (o : Organism n) (N R : ℕ) :
    infiniteLaw n noise epsilon he {w | ∀k∈Finset.range R,¬BodyGoal b (parentAt b cost o w (N+k+1)).physical}=
      (1-successMass n epsilon)^R := by
  let S : Set (RoundRaw n):={raw | Good raw}
  have hs : MeasurableSet S:=good_measurable n
  have hf : iIndepFun (fun k (w : RoundStream n)=>w (N+k)) (infiniteLaw n noise epsilon he) :=
    (actual_round_independent n noise epsilon he).precomp (by intro i j h;omega)
  have hmass (k : ℕ) : infiniteLaw n noise epsilon he {w | ¬Good (w (N+k))}=1-successMass n epsilon := by
    change infiniteLaw n noise epsilon he ((fun w : RoundStream n=>w (N+k)) ⁻¹' Sᶜ)=_
    rw [←Measure.map_apply (measurable_pi_apply (N+k)) hs.compl,actual_round_law,
      measure_compl hs (measure_ne_top _ _),good_mass]
    simp
  have hm := hf.meas_biInter (S:=Finset.range R) (s:=fun k=>{w : RoundStream n | ¬Good (w (N+k))})
    (fun k _=>hs.compl.preimage (measurable_iff_comap_le.mpr le_rfl))
  have he : {w | ∀k∈Finset.range R,¬BodyGoal b (parentAt b cost o w (N+k+1)).physical}=
      ⋂k∈Finset.range R,{w : RoundStream n | ¬Good (w (N+k))} := by
    ext w
    simp only [Set.mem_ofPred_eq,Set.mem_iInter,actual_macro_goal_iff]
  rw [he,hm]
  simp only [hmass,Finset.prod_const,Finset.card_range]

theorem successMass_pos (n : ℕ) (epsilon : NNReal) (he : epsilon<1) : 0<successMass n epsilon := by
  have hr : 0<(1-epsilon : NNReal):=tsub_pos_iff_lt.mpr he
  exact pos_iff_ne_zero.mpr (pow_ne_zero n (ENNReal.coe_pos.mpr hr).ne')

/-- Every finite body has a genuine complete-round return chance when the
original fault rate is below one. No retry/reinitialization protocol is added. -/
theorem actual_returns_forever {n : ℕ} (b : Bool) (cost : NNReal) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon<1)
    (o : Organism n) :
    ∀ᵐ w ∂infiniteLaw n noise epsilon he.le,∀N : ℕ,∃k≥N,BodyGoal b (parentAt b cost o w (k+1)).physical := by
  let mu:=infiniteLaw n noise epsilon he.le
  have hq : 1-successMass n epsilon<1:=ENNReal.sub_lt_self (by simp) (by simp) (successMass_pos n epsilon he).ne'
  have hz (N : ℕ) : mu {w | ∀k : ℕ,¬BodyGoal b (parentAt b cost o w (N+k+1)).physical}=0 := by
    apply le_antisymm _ bot_le
    have hb (R : ℕ) : mu {w | ∀k : ℕ,¬BodyGoal b (parentAt b cost o w (N+k+1)).physical}≤
        (1-successMass n epsilon)^R := by
      rw [←actual_no_return_tail b cost noise epsilon he.le o N R]
      exact measure_mono (by intro w hw k hk;exact hw k)
    exact ge_of_tendsto (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq) (Eventually.of_forall hb)
  have ha (N : ℕ) : ∀ᵐ w ∂mu,∃k : ℕ,BodyGoal b (parentAt b cost o w (N+k+1)).physical := by
    rw [ae_iff]
    simpa only [not_exists] using hz N
  filter_upwards [ae_all_iff.mpr ha] with w hw
  intro N
  obtain ⟨k,hk⟩:=hw N
  exact ⟨N+k,Nat.le_add_right N k,hk⟩

/-- Fault-rate-one boundary is SOURCE-AE, not a pointwise assertion about
zero-probability raw tuples. n0 is excluded because its body goal is vacuous. -/
theorem total_fault_no_body_round {n : ℕ} (hn : 0<n) (b : Bool) (cost : NNReal) (noise : PMF Bool) (o : Organism n) :
    ∀ᵐ w ∂infiniteLaw n noise 1 (by norm_num),∀k : ℕ,¬BodyGoal b (parentAt b cost o w (k+1)).physical := by
  apply ae_all_iff.mpr
  intro k
  rw [ae_iff]
  simp only [not_not]
  rw [actual_body_mass]
  simp [successMass,Nat.ne_of_gt hn]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterRotatingBodyReturns
