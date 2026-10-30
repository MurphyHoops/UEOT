import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterActuatorPopulationScale

/-!
Original commitment: actual serialized population work has a realizable shared resource account, compatible with owner/scale transport.
Existing result: P6 funds one registered continuation seed; no global funding of the population protocol was derived.
Premise reduced: derive every actual protocol-prefix balance from a literal idle-before-work compiler, not per-step supply or funding fields.
Model/counter: existing own-program faults/actions plus explicitly shared accounting and the existing open requested-idle port; closed zero-supply remains separate.
Consumer: SAME full raw outcomes, actual transactions/fees/valid-object credits, retained allocator/journal and actuator scale; no global optimality.

A credit g is delivered only when an ACTUAL addressed object receives a
requested idle. Invalid addresses execute no transaction, receive no credit,
and retain a failed tick. The shared ledger is a separately declared pooling
permission, in the existing abstract accounting units; no internal energy is
created. Each work transaction is preceded by a real idle on the same address.
Its literal or compiled work action is chosen after that idle's REAL state
transition. The new complete protocol is different from any old probe trace;
all idle births, failures, allocations and fees stay in the journal. No old
sample batch/threshold is changed and no empirical sampling occurs here.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterPopulationFundedProtocol
open MeasureTheory ProbabilityTheory
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.TheoryCompletion
open UEOT.V3.Compression.Objecthood.ResourceClosure
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultJointRecord
open RegisterTimestampedBirthSource (ClockedOrganism ClockedRecord)
open RegisterPopulationHistorySource (Store Request)
open RegisterActuatorScaleSource RegisterActuatorPopulationScale
noncomputable section

inductive Command where
  | compiled
  | literal (action : Action)
  deriving DecidableEq

structure Round where
  parent : ℕ
  command : Command
  idleMode : Bool
  idleLabel : Bool
  workMode : Bool
  workLabel : Bool
  deriving DecidableEq

def idleRequest (r : Round) : Request := ⟨r.parent,none,r.idleMode,r.idleLabel⟩
def middle {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (r : Round) : Store n :=
  RegisterOwnProgramPopulation.next i c s (idleRequest r)
def workAction {n : ℕ} (i : Fin n) (s : Store n) (j : ℕ) : Command → Action
  | .literal a => a
  | .compiled => (RegisterOwnProgramPopulation.compiledRequest i s j true true).action

def workRequest {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (r : Round) : Request :=
  ⟨r.parent,workAction i (middle i c s r) r.parent r.command,r.workMode,r.workLabel⟩
def roundNext {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (r : Round) : Store n :=
  RegisterOwnProgramPopulation.next i c (middle i c s r) (workRequest i c s r)

def requests {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) : List Round → List Request
  | [] => []
  | r::rs => idleRequest r :: workRequest i c s r :: requests i c (roundNext i c s r) rs

def completeTrace {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (rs : List Round) : List (Option (ClockedRecord n)) :=
  transactionTrace i c s (requests i c s rs)

/-- Undefined lookup earns no supply: credit reads an ACTUAL executed record. -/
def credit {n : ℕ} (g : ℝ) : Option (ClockedRecord n) → ℝ
  | none => 0
  | some r => if r.action=none then g else 0

def fee {n : ℕ} : Option (ClockedRecord n) → ℝ
  | none => 0
  | some r => r.expenditure

def balance {n : ℕ} (reserve g : ℝ) (ts : List (Option (ClockedRecord n))) : ℝ :=
  ts.foldl (fun R t => R+credit g t-fee t) reserve

@[simp] theorem balance_nil {n : ℕ} (reserve g : ℝ) : balance (n:=n) reserve g []=reserve := rfl
@[simp] theorem balance_cons {n : ℕ} (reserve g : ℝ) (t : Option (ClockedRecord n)) (ts) :
    balance reserve g (t::ts)=balance (reserve+credit g t-fee t) g ts := rfl

private theorem actual_fee_bounds {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (q : Request) :
    0 ≤ fee (RegisterOwnProgramPopulation.transaction i c s q) ∧
    fee (RegisterOwnProgramPopulation.transaction i c s q) ≤ (c : ℝ) := by
  unfold RegisterOwnProgramPopulation.transaction RegisterPopulationHistorySource.transaction
  cases hp : RegisterPopulationHistorySource.lookup s q.parent with
  | none => simp [fee]
  | some p =>
    cases hm : q.mode <;> cases ha : q.action <;>
      simp [fee,RegisterTimestampedBirthSource.step,modeRecordStep,RegisterJointRecord.recordStep,cost,
        RegisterOwnProgramPopulation.mechanism,hp]

private theorem actual_credit_nonneg {n : ℕ} (g : ℝ) (hg : 0 ≤ g) (t : Option (ClockedRecord n)) :
    0 ≤ credit g t := by
  cases t <;> simp [credit]; split <;> linarith

/-- Idle has no actual fee, including fault preemption, and its supply exists
iff a real lookup succeeds. This is NOT unconditional g per requested tick. -/
theorem idle_account {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (r : Round) (g : ℝ) :
    fee (RegisterOwnProgramPopulation.transaction i c s (idleRequest r))=0 ∧
    credit g (RegisterOwnProgramPopulation.transaction i c s (idleRequest r))=
      if (RegisterPopulationHistorySource.lookup s r.parent).isSome then g else 0 := by
  unfold RegisterOwnProgramPopulation.transaction RegisterPopulationHistorySource.transaction
  cases hp : RegisterPopulationHistorySource.lookup s r.parent with
  | none => simp [idleRequest,fee,credit,hp]
  | some p =>
    cases hm : r.idleMode <;>
      simp [idleRequest,fee,credit,RegisterTimestampedBirthSource.step,modeRecordStep,
        RegisterJointRecord.recordStep,hm,cost,hp]

/-- Appending a failed empty allocation cannot turn the same invalid address
into an object. No fictional object is credited before its work transaction. -/
theorem invalid_stays_invalid {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (r : Round)
    (h : RegisterPopulationHistorySource.lookup s r.parent=none) :
    RegisterPopulationHistorySource.lookup (middle i c s r) r.parent=none := by
  have hn := RegisterPopulationHistorySource.invalid_request i (RegisterOwnProgramPopulation.mechanism c s (idleRequest r))
    s (idleRequest r) h
  change RegisterPopulationHistorySource.lookup
    (RegisterPopulationHistorySource.next i (RegisterOwnProgramPopulation.mechanism c s (idleRequest r)) s (idleRequest r)) r.parent=none
  rw [hn.2.2]
  unfold RegisterPopulationHistorySource.lookup at *
  by_cases hj : r.parent < s.length
  · rw [List.getElem?_append_left hj]
    exact h
  · rw [List.getElem?_append_right (by omega)]
    cases r.parent-s.length <;> rfl

/-- Pathwise net account for a REAL pair. Each prefix gains at least zero,
and the full pair never lowers reserve, even with literal forced writes.
No actual cost<=same-tick supply condition is assumed. -/
theorem round_account {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (r : Round)
    (g reserve : ℝ) (hg : (c : ℝ) ≤ g) :
    reserve ≤ reserve+credit g (RegisterOwnProgramPopulation.transaction i c s (idleRequest r))-
      fee (RegisterOwnProgramPopulation.transaction i c s (idleRequest r)) ∧
    reserve ≤ balance reserve g
      [RegisterOwnProgramPopulation.transaction i c s (idleRequest r),
       RegisterOwnProgramPopulation.transaction i c (middle i c s r) (workRequest i c s r)] := by
  have hi := idle_account i c s r g
  have hg0 : 0 ≤ g := le_trans c.coe_nonneg hg
  have hn := actual_credit_nonneg g hg0 (RegisterOwnProgramPopulation.transaction i c (middle i c s r) (workRequest i c s r))
  have hf := actual_fee_bounds i c (middle i c s r) (workRequest i c s r)
  simp only [balance_cons,balance_nil,hi.1,sub_zero]
  cases hp : RegisterPopulationHistorySource.lookup s r.parent with
  | none =>
    have hh := invalid_stays_invalid i c s r hp
    have ht : RegisterOwnProgramPopulation.transaction i c (middle i c s r) (workRequest i c s r)=none := by
      simp [RegisterOwnProgramPopulation.transaction,RegisterPopulationHistorySource.transaction,workRequest,hh]
    rw [hp] at hi
    simp only [Option.isSome_none,Bool.false_eq_true,if_false] at hi
    rw [hi.2,ht]
    simp [fee,credit]
  | some p =>
    rw [hp] at hi
    simp only [Option.isSome_some,if_true] at hi
    rw [hi.2]
    constructor <;> linarith

/-- All complete real protocol prefixes are funded, uniformly in all raw
modes/labels and valid/invalid addresses. Initial reserve need only be >=0. -/
theorem every_prefix_balance {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (rs : List Round)
    (g reserve : ℝ) (hg : (c : ℝ) ≤ g) (k : ℕ) :
    reserve ≤ balance reserve g ((completeTrace i c s rs).take k) := by
  induction rs generalizing s reserve k with
  | nil => simp [completeTrace,requests,transactionTrace]
  | cons r rs ih =>
    cases k with
    | zero => simp
    | succ k =>
      have h := round_account i c s r g reserve hg
      cases k with
      | zero => simpa [completeTrace,requests,transactionTrace,balance] using h.1
      | succ k =>
        change reserve ≤ balance _ g ((completeTrace i c (roundNext i c s r) rs).take k)
        exact h.2.trans (ih _ _ k)

/-- Original accounting predicate P6 on the global serial journal. Truncation
outside the actual finite budget is not an additional supply event. -/
theorem all_prefixes_nonnegative {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (rs : List Round)
    (g reserve : ℝ) (hg : (c : ℝ) ≤ g) (hr : 0 ≤ reserve) :
    ∀ k, 0 ≤ balance reserve g ((completeTrace i c s rs).take k) :=
  fun k => hr.trans (every_prefix_balance i c s rs g reserve hg k)

/-- Finite actual journal, padded by absence (zero credit AND zero fee) only
for the original all-natural-time accounting predicate. -/
def recordAt {n : ℕ} (ts : List (Option (ClockedRecord n))) (k : ℕ) : Option (ClockedRecord n) := (ts[k]?).join

private theorem prefix_balance_eq_cumulative {n : ℕ} (ts : List (Option (ClockedRecord n))) (g reserve : ℝ) (k : ℕ) :
    balance reserve g (ts.take k)=cumulativeResourceBalance reserve
      (fun t => credit g (recordAt ts t)) (fun t => fee (recordAt ts t)) k := by
  induction ts generalizing reserve k with
  | nil => simp [recordAt,credit,fee,cumulativeResourceBalance]
  | cons t ts ih =>
    cases k with
    | zero => simp [cumulativeResourceBalance]
    | succ k =>
      rw [List.take_succ_cons,balance_cons,ih]
      simp only [cumulativeResourceBalance,Finset.sum_range_succ',recordAt,List.getElem?_cons_zero,
        List.getElem?_cons_succ,Option.join_some]
      ring

/-- Original P6 actually consumes the derived global balance, not a new
predicate called viability. Beyond the finite registered run there is no fee
and no external-port credit. -/
theorem actual_global_p6 {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (rs : List Round)
    (g reserve : ℝ) (hg : (c : ℝ) ≤ g) (hr : 0 ≤ reserve) :
    ResourceViable reserve (fun t => credit g (recordAt (completeTrace i c s rs) t))
      (fun t => fee (recordAt (completeTrace i c s rs) t)) := by
  intro k
  rw [← prefix_balance_eq_cumulative]
  exact all_prefixes_nonnegative i c s rs g reserve hg hr k

@[simp] theorem middle_transport {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (r : Round) :
    projectStore i (middle i c s r)=middle (0 : Fin 1) c (projectStore i s) r :=
  own_next_transport i c s (idleRequest r)

theorem work_action_transport {n : ℕ} (i : Fin n) (s : Store n) (j : ℕ) (cmd : Command) :
    workAction i s j cmd=workAction (0 : Fin 1) (projectStore i s) j cmd := by
  cases cmd with
  | literal a => rfl
  | compiled => exact congrArg Request.action (compiled_request_transport i s j true true)

theorem work_request_transport {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (r : Round) :
    workRequest i c s r=workRequest (0 : Fin 1) c (projectStore i s) r := by
  unfold workRequest
  rw [work_action_transport i (middle i c s r),middle_transport]

@[simp] theorem round_next_transport {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (r : Round) :
    projectStore i (roundNext i c s r)=roundNext (0 : Fin 1) c (projectStore i s) r := by
  unfold roundNext
  rw [own_next_transport,middle_transport,work_request_transport i c s r]

theorem protocol_requests_transport {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (rs : List Round) :
    requests i c s rs=requests (0 : Fin 1) c (projectStore i s) rs := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih =>
    simp only [requests]
    rw [work_request_transport i c s r,ih,round_next_transport]

theorem protocol_journal_transport {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (rs : List Round) :
    (completeTrace i c s rs).map (Option.map (projectClockedRecord i))=
      completeTrace (0 : Fin 1) c (projectStore i s) rs := by
  unfold completeTrace
  rw [transaction_trace_transport,protocol_requests_transport]

@[simp] theorem credit_transport {n : ℕ} (i : Fin n) (g : ℝ) (t : Option (ClockedRecord n)) :
    credit g (t.map (projectClockedRecord i))=credit g t := by cases t <;> rfl
@[simp] theorem fee_transport {n : ℕ} (i : Fin n) (t : Option (ClockedRecord n)) :
    fee (t.map (projectClockedRecord i))=fee t := by cases t <;> rfl

theorem balance_transport {n : ℕ} (i : Fin n) (g reserve : ℝ) (ts : List (Option (ClockedRecord n))) :
    balance reserve g (ts.map (Option.map (projectClockedRecord i)))=balance reserve g ts := by
  induction ts generalizing reserve with
  | nil => rfl
  | cons t ts ih => simp only [List.map_cons,balance_cons,credit_transport,fee_transport,ih]

/-- Same exact global balance at EACH retained chronological prefix, including
all invalid/failed ticks and idle births. This composes with exact source IDs
and parent journal transport; no ownership quotient is inferred. -/
theorem protocol_ledger_transport {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (rs : List Round)
    (g reserve : ℝ) (k : ℕ) :
    balance reserve g ((completeTrace i c s rs).take k)=
      balance reserve g ((completeTrace (0 : Fin 1) c (projectStore i s) rs).take k) := by
  have h := congrArg (fun ts => balance reserve g (ts.take k)) (protocol_journal_transport i c s rs)
  simpa only [← List.map_take,balance_transport] using h

abbrev Raw (N : ℕ) := Fin N × Bool → Bool × Bool

/-- Frozen N work positions and both actual primitive draws per position.
All modes/labels of both idle and work are present in the product. -/
def sourceLaw (noise : PMF Bool) (epsilon : NNReal) (he : epsilon ≤ 1) (N : ℕ) : Measure (Raw N) :=
  Measure.pi (fun _ : Fin N × Bool => (RegisterFaultFinitePurposeProbe.primitiveLaw noise epsilon he).toMeasure)
instance sourceLaw_probability (noise : PMF Bool) (epsilon : NNReal) (he : epsilon ≤ 1) (N : ℕ) :
    IsProbabilityMeasure (sourceLaw noise epsilon he N) := by unfold sourceLaw; infer_instance

def registeredRounds {N : ℕ} (plan : Fin N → ℕ × Command) (w : Raw N) : List Round :=
  List.ofFn (fun j => ⟨(plan j).1,(plan j).2,(w (j,false)).1,(w (j,false)).2,(w (j,true)).1,(w (j,true)).2⟩)

theorem complete_product_funded {n N : ℕ} (i : Fin n) (c : NNReal) (s : Store n)
    (noise : PMF Bool) (epsilon : NNReal) (he : epsilon ≤ 1) (plan : Fin N → ℕ × Command)
    (g reserve : ℝ) (hg : (c : ℝ) ≤ g) (hr : 0 ≤ reserve) :
    ∀ᵐ w ∂sourceLaw noise epsilon he N,
      ResourceViable reserve
        (fun t => credit g (recordAt (completeTrace i c s (registeredRounds plan w)) t))
        (fun t => fee (recordAt (completeTrace i c s (registeredRounds plan w)) t)) :=
  ae_of_all _ (fun _ => actual_global_p6 i c s _ g reserve hg hr)

local instance {d : ℕ} : MeasurableSpace (List (Option (ClockedRecord d))) := ⊤

/-- Equality of the SAME complete registered source journal laws. The
protocol's actions, physical states, fees, birth IDs and parents commute from
actual semantics; no success-conditioned or separately desired law is given. -/
theorem complete_source_journal_transport {n N : ℕ} (i : Fin n) (c : NNReal) (s : Store n)
    (noise : PMF Bool) (epsilon : NNReal) (he : epsilon ≤ 1) (plan : Fin N → ℕ × Command) :
    ((sourceLaw noise epsilon he N).map (fun w => completeTrace i c s (registeredRounds plan w))).map
      (List.map (Option.map (projectClockedRecord i)))=
      (sourceLaw noise epsilon he N).map (fun w => completeTrace (0 : Fin 1) c (projectStore i s) (registeredRounds plan w)) := by
  have hm : Measurable (List.map (Option.map (projectClockedRecord i))) := by intro t ht; trivial
  rw [Measure.map_map hm (measurable_of_finite _)]
  congr 1
  funext w
  exact protocol_journal_transport i c s _

/-- Source-computed actual IDs/parents of EVERY retained event. Together
with protocol_requests_transport this is the identical coarse protocol, not a
choice of another population run. Failures retain None and allocator ticks. -/
theorem protocol_actual_ID_parent_transport {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (rs : List Round)
    (k : Fin (requests i c s rs).length) :
    RegisterOwnProgramPopulation.observedChildID i c s (requests i c s rs) k=
      RegisterOwnProgramPopulation.observedChildID (0 : Fin 1) c (projectStore i s) (requests i c s rs) k ∧
    RegisterOwnProgramPopulation.actualParent i c s (requests i c s rs) k=
      RegisterOwnProgramPopulation.actualParent (0 : Fin 1) c (projectStore i s) (requests i c s rs) k :=
  actual_journal_transport i c s _ k

/-- Frozen formal N2 fixture, registered before evaluation, not a real draw. -/
def witnessPlan (j : Fin 2) : ℕ × Command := (if j=0 then 0 else 2,.compiled)
def witnessRaw : Raw 2 := fun j => (if j.1=0 then j.2 else !j.2,true)
def witnessRounds : List Round := registeredRounds witnessPlan witnessRaw
def witnessTrace : List (Option (ClockedRecord 1)) :=
  completeTrace (0 : Fin 1) 1 RegisterOwnProgramPopulation.witnessInitial witnessRounds

/-- Both OWN program types actually born, an idle fault and a later fault
remain, and the real write-false transaction pays1 after its actual idle.
Every credit is attached to an actual valid-object requested idle. -/
theorem two_type_paid_funded_witness :
    witnessTrace.map (fun t => (t.bind ClockedRecord.child).map (fun d => d.organism.program))=
      [none,some false,some true,none] ∧
    witnessTrace.map fee=[0,1,0,0] ∧ witnessTrace.map (credit 1)=[1,0,1,1] ∧
    balance 0 1 witnessTrace=2 ∧ balance 0 0 witnessTrace= -1 := by
  norm_num [witnessTrace,witnessRounds,witnessPlan,witnessRaw,registeredRounds,completeTrace,requests,
    transactionTrace,idleRequest,workRequest,workAction,middle,roundNext,RegisterOwnProgramPopulation.compiledRequest,
    RegisterOwnProgramPopulation.next,RegisterOwnProgramPopulation.transaction,RegisterOwnProgramPopulation.child,
    RegisterOwnProgramPopulation.mechanism,RegisterOwnProgramPopulation.witnessInitial,RegisterOwnProgramPopulation.witnessFounders,
    RegisterPopulationHistorySource.founders,RegisterPopulationHistorySource.next,RegisterPopulationHistorySource.transaction,
    RegisterPopulationHistorySource.child,RegisterPopulationHistorySource.lookup,RegisterTimestampedBirthSource.step,
    modeRecordStep,RegisterJointRecord.recordStep,birthEvent,repairEvent,execute_compiled,update,cost,fee,credit,balance,
    List.ofFn_succ]
  have hn : (some false : Action) ≠ none := by intro h; cases h
  constructor
  · exact hn
  · rw [if_neg hn]
    norm_num

theorem witness_mass :
    (sourceLaw (PMF.uniformOfFintype Bool) (1/4) (by exact_mod_cast (by norm_num : (1/4 : ℝ) ≤ 1)) 2).real {witnessRaw}=9/4096 := by
  rw [Measure.real,sourceLaw,Measure.pi_singleton,ENNReal.toReal_prod]
  simp_rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  norm_num [Fintype.prod_prod_type,Fin.prod_univ_succ,Fintype.prod_bool,witnessRaw,
    RegisterFaultFinitePurposeProbe.primitiveLaw_apply,ENNReal.toReal_mul,RegisterFaultControlModel.modeLaw,
    FiniteProbabilityRow.ofRealRow_apply_toReal,RegisterFaultControlModel.modeProbability,
    RegisterFaultControlModel.repairChance,PMF.uniformOfFintype_apply]

/-- Global serial funding needs the declared open port. This positive-source
word has a negative final closed balance at reserve0; the existing stronger
closed finite-reserve obstruction is retained unchanged in FeedbackResource. -/
theorem witness_closed_global_not_viable :
    ¬ ResourceViable 0 (fun t => credit 0 (recordAt witnessTrace t)) (fun t => fee (recordAt witnessTrace t)) := by
  intro h
  have hk := h witnessTrace.length
  rw [← prefix_balance_eq_cumulative,List.take_length] at hk
  have hh := two_type_paid_funded_witness.2.2.2.2
  linarith

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterPopulationFundedProtocol
