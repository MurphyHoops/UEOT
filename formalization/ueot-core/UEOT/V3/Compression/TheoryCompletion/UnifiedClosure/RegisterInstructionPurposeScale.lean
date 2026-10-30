import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterSemanticInstructionInfinite

/-!
Original promise: C4/P9 purpose ordering must follow the SAME parent's actual birth/fee execution under scale change.
Existing result: semantic synthesis returns the actual coarse AST and preserves complete records; Bellman optimality already covers all fine physical/action-history causal policies when price*cost ≤ 1.
Reduced premise: derive native actual AST event kernels, full record-law and discounted-value transport, then original P9 purpose preservation without a supplied ranking/factor certificate.
Family/boundary: original finite registers, one allowed write port, retained parent/history and fixed fault/label law; actual submitted/synthesized ASTs, with priced births as the declared evaluation.
Consumer: actual integrable infinite payoff, original PreservesPurpose/transport_object_property, and SAME compiled program dominance over the original full causal class; not all six semantics, journal-oracle policies, free funding or arbitrary price optimality.

The external Instruction remains a controller, not installed protected code.
The actual Organism is part of the object map, so parent history/program are
not reconstructed from a physical seed. Purpose here means the explicit
birth-minus-priced-fee discounted ordering of two actual executable programs.
This is an evaluation contract; its preservation is derived from their real
interpreter/event/readout laws. Physical restoration alone does not preserve
this order: an always-paid write and compiled repair have identical physical
updates but different actual fees and values. Fresh mode/label rights are the
original source's; causal policies see physical/action history, not a new raw
mode/label oracle. No actions, observations, initial permissions, resource port,
sampling, old protocol/data or failure events are changed.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterInstructionPurposeScale
open MeasureTheory ProbabilityTheory
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.TheoryCompletion
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultJointRecord
open RegisterActuatorScaleSource RegisterInstructionScaleSource RegisterSemanticInstructionScale
open RegisterFaultInfiniteRecord
open scoped ENNReal
noncomputable section

local instance {d : ℕ} : MeasurableSpace (ModeRecord d) := ⊤
local instance {d : ℕ} : MeasurableSingletonClass (ModeRecord d) := ⟨fun _ => trivial⟩

/-- Actual deterministic action from this submitted AST; no policy choice. -/
abbrev astPolicy {n : ℕ} (p : Instruction n) : CausalPolicy.{0,0,0} (State n) (fun _ => Action) :=
  selectorPolicy (interpret p)

def projectASTConfig {n : ℕ} (i : Fin n) (p : Instruction n) (q : Instruction 1)
    (c : Config (astPolicy p)) : Config (astPolicy q) :=
  ⟨c.1,projectState i c.2.1,projectOrganism i c.2.2⟩

@[simp] theorem actual_advance {n : ℕ} (i : Fin n) (m : Mechanism)
    (p : Instruction n) (q : Instruction 1) (c : Config (astPolicy p)) (e : Event) :
    projectASTConfig i p q (advance i m (astPolicy p) c e)=
      advance (0 : Fin 1) m (astPolicy q) (projectASTConfig i p q c) e := by
  rcases c with ⟨t,x,o⟩
  dsimp only [projectASTConfig,advance,astPolicy,selectorPolicy]
  rw [projected_physical_next,projected_parent]

@[simp] theorem actual_run {n : ℕ} (i : Fin n) (m : Mechanism)
    (p : Instruction n) (q : Instruction 1) (c : Config (astPolicy p)) (es : List Event) :
    projectASTConfig i p q (run i m (astPolicy p) c es)=
      run (0 : Fin 1) m (astPolicy q) (projectASTConfig i p q c) es := by
  induction es generalizing c with
  | nil => rfl
  | cons e es ih =>
    change projectASTConfig i p q (run i m (astPolicy p) (advance i m (astPolicy p) c e) es)=_
    rw [ih,actual_advance]
    rfl

@[simp] theorem actual_run_parent {n : ℕ} (i : Fin n) (m : Mechanism)
    (p : Instruction n) (q : Instruction 1) (c : Config (astPolicy p)) (es : List Event) :
    projectOrganism i (run i m (astPolicy p) c es).2.2=
      (run (0 : Fin 1) m (astPolicy q) (projectASTConfig i p q c) es).2.2 :=
  congrArg (fun c : Config (astPolicy q) => c.2.2) (actual_run i m p q c es)

section Source
variable {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
variable (epsilon : NNReal) (he : epsilon ≤ 1)
variable (p : Instruction n) (q : Instruction 1) (hs : synthesize i p=some q)

include hs in
/-- Equality of the actual action/mode/label row uses this returned q's
literal interpretation, not an abstract lifted policy or supplied factor. -/
theorem actual_eventLaw (c : Config (astPolicy p)) :
    eventLaw noise epsilon he (astPolicy p) c=
      eventLaw noise epsilon he (astPolicy q) (projectASTConfig i p q c) := by
  apply PMF.ext
  intro e
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [eventLaw_toReal,eventLaw_toReal]
  dsimp only [eventWeight,astPolicy,selectorPolicy,projectASTConfig]
  rw [(synthesize_actual i p q hs).2]

include hs in
theorem actual_wordRow (c : Config (astPolicy p)) (es : List Event) :
    wordRow i noise m epsilon he (astPolicy p) c es=
      wordRow (0 : Fin 1) noise m epsilon he (astPolicy q) (projectASTConfig i p q c) es := by
  unfold wordRow
  rw [actual_eventLaw i noise epsilon he p q hs,actual_run]

include hs in
theorem actual_wordKernel (c : Config (astPolicy p)) :
    wordKernel i noise m epsilon he (astPolicy p) c=
      wordKernel (0 : Fin 1) noise m epsilon he (astPolicy q) (projectASTConfig i p q c) := by
  ext es s hs'
  change (wordRow i noise m epsilon he (astPolicy p) c es).toMeasure s=_
  rw [actual_wordRow i noise m epsilon he p q hs]
  rfl

include hs in
theorem actual_wordPathLaw (c : Config (astPolicy p)) :
    wordPathLaw i noise m epsilon he (astPolicy p) c=
      wordPathLaw (0 : Fin 1) noise m epsilon he (astPolicy q) (projectASTConfig i p q c) := by
  simp only [wordPathLaw,actual_wordKernel i noise m epsilon he p q hs]

@[simp] theorem actual_native_record (c : Config (astPolicy p)) (z : ℕ → List Event) (k : ℕ) :
    projectModeRecord i (recordAt i m (astPolicy p) c z k)=
      recordAt (0 : Fin 1) m (astPolicy q) (projectASTConfig i p q c) z k := by
  simp only [recordAt,mode_step_transport]
  rw [actual_run_parent i m p q c (z k)]

include hs in
/-- Full continuing native source, retaining all failed/fault/birth/fee records.
Its probability/readout measurability are the original InfiniteRecord ones. -/
theorem actual_recordPathLaw (c : Config (astPolicy p)) :
    (recordPathLaw i noise m epsilon he (astPolicy p) c).map
      (fun (rs : ℕ → ModeRecord n) k => projectModeRecord i (rs k))=
      recordPathLaw (0 : Fin 1) noise m epsilon he (astPolicy q) (projectASTConfig i p q c) := by
  have hm : Measurable (fun (rs : ℕ → ModeRecord n) k => projectModeRecord i (rs k)) := by
    apply measurable_pi_lambda
    intro k
    have hf : Measurable (projectModeRecord i) := by intro s hs; trivial
    exact hf.comp (measurable_pi_apply k)
  rw [recordPathLaw,Measure.map_map hm (measurable_recordStream i m (astPolicy p) c),
    actual_wordPathLaw i noise m epsilon he p q hs]
  unfold recordPathLaw
  congr 1
  funext z k
  exact actual_native_record i m p q c z k
end Source

@[simp] theorem actual_streamPayoff {n : ℕ} (i : Fin n) (price : NNReal) (d : ℝ)
    (rs : ℕ → ModeRecord n) :
    streamPayoff price d (fun k => projectModeRecord i (rs k))=streamPayoff price d rs := by
  unfold streamPayoff
  congr 1
  funext k
  rw [payoff_transport]

/-- A value of the actual parent/controller execution, with explicit evaluation
and the SAME actual complete-record probability law. -/
def actualValue {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon ≤ 1) (price : NNReal) (d : ℝ)
    (o : Organism n) (p : Instruction n) : ℝ :=
  ∫ rs, streamPayoff price d rs ∂recordPathLaw i noise m epsilon he (astPolicy p) ⟨0,o.physical,o⟩

theorem actual_value_integrable {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon ≤ 1) (price : NNReal) (d : ℝ) (hd : 0<d ∧ d<1)
    (o : Organism n) (p : Instruction n) :
    Integrable (streamPayoff price d) (recordPathLaw i noise m epsilon he (astPolicy p) ⟨0,o.physical,o⟩) :=
  actual_recordPath_payoff_integrable i noise m epsilon he (astPolicy p) price d hd _

/-- Source-derived value equality of THIS submitted p and returned q. No value,
ranking, desired kernel or property-preservation field is supplied. -/
theorem actual_value_transport {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon ≤ 1) (price : NNReal) (d : ℝ)
    (o : Organism n) (p : Instruction n) (q : Instruction 1) (hs : synthesize i p=some q) :
    actualValue i noise m epsilon he price d o p=
      actualValue (0 : Fin 1) noise m epsilon he price d (projectOrganism i o) q := by
  unfold actualValue
  have hl:=actual_recordPathLaw i noise m epsilon he p q hs ⟨0,o.physical,o⟩
  change _ = ∫ rs, streamPayoff price d rs ∂recordPathLaw 0 noise m epsilon he (astPolicy q)
    (projectASTConfig i p q ⟨0,o.physical,o⟩)
  rw [←hl]
  have hm : Measurable (fun (rs : ℕ → ModeRecord n) k => projectModeRecord i (rs k)) :=
    RegisterSemanticInstructionInfinite.measurable_projectPath i
  have hi:=integral_map (μ:=recordPathLaw i noise m epsilon he (astPolicy p) ⟨0,o.physical,o⟩)
    hm.aemeasurable (measurable_streamPayoff price d).aestronglyMeasurable
  exact (hi.trans (by simp only [actual_streamPayoff])).symm

/-- The actual source integral is bound to this AST's original causal value.
The protected code condition belongs to the actual parent, not a new seed. -/
theorem actual_value_policy {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon ≤ 1) (price : NNReal) (d : ℝ) (hd : 0<d ∧ d<1)
    (o : Organism n) (hp : o.program=m.goal) (p : Instruction n) :
    actualValue i noise m epsilon he price d o p=
      (astPolicy p).infiniteValue (RegisterFaultControlModel.model i noise m price epsilon he d hd) (t:=0) o.physical :=
  actual_recordPath_integral_eq_policy_value i noise m epsilon he (astPolicy p) o.physical o price d hd rfl hp

/-- Actual objects retain the SAME parent/history plus both submitted programs
and the actual synthesis results; no program-only proxy for a parent. -/
abbrev PurposeObject {n : ℕ} (i : Fin n) := Organism n × Accepted i × Accepted i

def purposeScale {n : ℕ} (i : Fin n) :
    ObjectScaleMap (State n) (State 1) (PurposeObject i) (Organism 1 × Instruction 1 × Instruction 1) :=
  ⟨projectState i,fun obj => (projectOrganism i obj.1,obj.2.1.val.2,obj.2.2.val.2)⟩

def PurposeOrder {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon ≤ 1) (price : NNReal) (d : ℝ)
    (obj : Organism n × Instruction n × Instruction n) : Prop :=
  (0<d ∧ d<1) ∧ actualValue i noise m epsilon he price d obj.1 obj.2.2 ≤
    actualValue i noise m epsilon he price d obj.1 obj.2.1

/-- Original P9 purpose interface, derived from actual execution values. -/
theorem actual_preserves_purpose {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon ≤ 1) (price : NNReal) (d : ℝ) :
    PreservesPurpose (purposeScale i)
      (fun obj => PurposeOrder i noise m epsilon he price d (obj.1,obj.2.1.val.1,obj.2.2.val.1))
      (PurposeOrder (0 : Fin 1) noise m epsilon he price d) := by
  intro obj h
  simpa only [PurposeOrder,purposeScale,
    actual_value_transport i noise m epsilon he price d obj.1 _ _ obj.2.1.property,
    actual_value_transport i noise m epsilon he price d obj.1 _ _ obj.2.2.property] using h

/-- The original P9 consumer is really invoked for the actual returned pair. -/
theorem p9_actual_returned_purpose {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon ≤ 1) (price : NNReal) (d : ℝ) (obj : PurposeObject i)
    (h : PurposeOrder i noise m epsilon he price d (obj.1,obj.2.1.val.1,obj.2.2.val.1)) :
    PurposeOrder (0 : Fin 1) noise m epsilon he price d ((purposeScale i).objectMap obj) :=
  transport_object_property (purposeScale i) _ _ rfl
    (actual_preserves_purpose i noise m epsilon he price d) h


/-- SAME actual compiled AST value attains the original Bellman value; all
causal fine physical/action-history controllers are dominated, not only Bool
program candidates or controllers factoring through the retained actuator. -/
theorem actual_compiled_optimal {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon ≤ 1) (price : NNReal) (d : ℝ) (hd : 0<d ∧ d<1)
    (hc : (price : ℝ)*m.writeCost≤1) (o : Organism n) (hp : o.program=m.goal) :
    actualValue i noise m epsilon he price d o (compile i m.goal)=
      (RegisterFaultControlModel.model i noise m price epsilon he d hd).optimalValue o.physical := by
  rw [actual_value_policy i noise m epsilon he price d hd o hp]
  exact (RegisterFaultControlModel.compiled_optimal_against_all_causal.{0}
    i noise m price epsilon he d hd hc).1 (t:=0) o.physical

/-- The original ALL-causal comparison is an actual complete-record integral
comparison on the SAME parent; current-state/initial-code agreement is explicit.
There is no additional raw mode/label/journal observation permission. -/
theorem actual_compiled_dominates_all_causal {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon ≤ 1) (price : NNReal) (d : ℝ) (hd : 0<d ∧ d<1)
    (hc : (price : ℝ)*m.writeCost≤1) (o : Organism n) (hp : o.program=m.goal)
    (pi : CausalPolicy.{0,0,0} (State n) (fun _ => Action)) {t : ℕ} (h : pi.Memory t)
    (hx : o.physical=pi.current h) :
    (∫ rs, streamPayoff price d rs ∂recordPathLaw i noise m epsilon he pi ⟨t,h,o⟩) ≤
      actualValue i noise m epsilon he price d o (compile i m.goal) := by
  rw [actual_recordPath_integral_eq_policy_value i noise m epsilon he pi h o price d hd hx hp,
    actual_compiled_optimal i noise m epsilon he price d hd hc o hp,hx]
  exact (RegisterFaultControlModel.compiled_optimal_against_all_causal.{0}
    i noise m price epsilon he d hd hc).2 pi h

/-- At price*cost=1, always writing target earns exactly zero on EVERY actual
source transaction: one birth minus one paid fee on repair, zero on fault. -/
theorem paid_target_step_zero {n : ℕ} (i : Fin n) (b : Bool) (o : Organism n)
    (hp : o.program=b) (mode label : Bool) :
    RegisterJointRecord.payoff 1 (modeRecordStep i ⟨b,1⟩ o (some b) mode label).transaction=0 := by
  cases mode <;>
    simp [modeRecordStep,RegisterJointRecord.payoff,RegisterJointRecord.recordStep,
      update,hp,childCount,cost]


/-- SAME actual paid-write program, any fault/label law and registered parent:
the original evaluation is zero; no independent desired value is assumed. -/
theorem always_paid_actual_zero {n : ℕ} (i : Fin n) (noise : PMF Bool) (b : Bool)
    (epsilon : NNReal) (he : epsilon≤1) (d : ℝ) (hd : 0<d ∧ d<1)
    (o : Organism n) (hp : o.program=b) :
    actualValue i noise ⟨b,1⟩ epsilon he 1 d o (.emit (some b))=0 := by
  rw [actual_value_policy i noise ⟨b,1⟩ epsilon he 1 d hd o hp]
  have hzero : ∀ (k t : ℕ) (x : State n),
      (astPolicy (.emit (some b))).truncatedValue
        (RegisterFaultControlModel.model i noise ⟨b,1⟩ 1 epsilon he d hd) k (t:=t) x=0 := by
    intro k
    induction k with
    | zero => intros; rfl
    | succ k ih =>
      intro t x
      rw [selector_truncatedValue_succ]
      simp only [ih,mul_zero,Finset.sum_const_zero,add_zero]
      change RegisterFaultControlModel.expectedModePayoff i noise ⟨b,1⟩ 1 epsilon he x (some b)=0
      rw [RegisterFaultControlModel.expectedModePayoff_eq,stage,expectedChildren_eq]
      simp [update,cost]
  exact tendsto_nhds_unique
    (CausalPolicy.truncatedValue_tendsto_infiniteValue (astPolicy (.emit (some b)))
      (RegisterFaultControlModel.model i noise ⟨b,1⟩ 1 epsilon he d hd) (t:=0) o.physical)
    (by simpa only [hzero] using (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0)))


/-- The ordinary compiler passes the same finite semantic synthesis algorithm.
The result is the algorithm's literal returnedProgram, not another AST chosen
from an existence theorem. -/
theorem compiled_synthesis {n : ℕ} (i : Fin n) (b : Bool) :
    synthesize i (compile i b)=some (returnedProgram i (compile i b)) := by
  simp [synthesize,finiteCheck,compile,interpret,representative,projectState]

/-- Actual common consumer: original ALL-fine-causal Bellman comparison
produces the fine purpose property, then original P9 transports it to the
actual returned controllers on the SAME projected parent/history. -/
theorem compiled_actual_p9_purpose {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (price : NNReal) (d : ℝ) (hd : 0<d ∧ d<1)
    (hc : (price : ℝ)*m.writeCost≤1) (o : Organism n) (hp : o.program=m.goal)
    (pq : Accepted i) :
    actualValue (0 : Fin 1) noise m epsilon he price d (projectOrganism i o) pq.val.2 ≤
      actualValue (0 : Fin 1) noise m epsilon he price d (projectOrganism i o)
        (returnedProgram i (compile i m.goal)) := by
  let comp : Accepted i := ⟨(compile i m.goal,returnedProgram i (compile i m.goal)),compiled_synthesis i m.goal⟩
  have h : PurposeOrder i noise m epsilon he price d (o,comp.val.1,pq.val.1) :=
    ⟨hd,actual_compiled_dominates_all_causal i noise m epsilon he price d hd hc o hp
      (astPolicy pq.val.1) (t:=0) o.physical rfl⟩
  exact (p9_actual_returned_purpose i noise m epsilon he price d (o,comp,pq) h).2

/-- Strict nonzero-fault ordering under the SAME source and actual parent.
Physical repair equality does not imply birth/fee value equality. -/
theorem strict_paid_write_boundary (noise : PMF Bool) (history : List Bool) :
    let he : (1/4 : NNReal)≤1 := by exact_mod_cast (by norm_num : (1/4 : ℝ)≤1)
    let o : Organism 1 := ⟨history,(fun _ => true),true⟩
    actualValue 0 noise ⟨true,1⟩ (1/4) he 1 (1/2) o (compile 0 true)=21/16 ∧
    actualValue 0 noise ⟨true,1⟩ (1/4) he 1 (1/2) o (.emit (some true))=0 ∧
    actualValue 0 noise ⟨true,1⟩ (1/4) he 1 (1/2) o (.emit (some true)) <
      actualValue 0 noise ⟨true,1⟩ (1/4) he 1 (1/2) o (compile 0 true) := by
  dsimp only
  have hc : actualValue (0 : Fin 1) noise ⟨true,1⟩ (1/4)
      (by exact_mod_cast (by norm_num : (1/4 : ℝ)≤1)) 1 (1/2)
      ⟨history,(fun _ => true),true⟩ (compile 0 true)=21/16 := by
    rw [actual_compiled_optimal 0 noise ⟨true,1⟩ _ _ 1 (1/2) (by norm_num) (by norm_num) _ rfl,
      ←RegisterFaultControlModel.value_eq_optimal 0 noise ⟨true,1⟩ 1 _ _ (1/2) (by norm_num) (by norm_num)]
    norm_num [RegisterFaultControlModel.value,RegisterFaultControlModel.goodValue,
      RegisterFaultControlModel.repairChance]
  have hw:=always_paid_actual_zero (0 : Fin 1) noise true (1/4)
    (by exact_mod_cast (by norm_num : (1/4 : ℝ)≤1)) (1/2) (by norm_num)
    ⟨history,(fun _ => true),true⟩ rfl
  exact ⟨hc,hw,by rw [hc,hw]; norm_num⟩


/-- Strict ordering above is not caused by a different physical repair map:
both literal controllers induce the SAME update at every fine state. -/
theorem same_repair_different_value_physical {n : ℕ} (i : Fin n) (b : Bool) (x : State n) :
    update i x (interpret (compile i b) x)=update i x (interpret (.emit (some b)) x) := by
  by_cases hx : x i=b
  · simp only [compile,interpret,if_pos hx,update]
    ext j
    by_cases hj : j=i
    · subst j; simpa using hx
    · simp [Function.update_of_ne hj]
  · simp [compile,interpret,hx]

/-- Even the entire actual retained-parent path agrees under every primitive
stream; the complete paid-action records and their purpose values still differ.
This is not a claim that all same-physical kernels preserve purpose. -/
theorem same_actual_parent_path {n : ℕ} (i : Fin n) (b : Bool) (cost : NNReal)
    (o : Organism n) (w : RegisterSemanticInstructionInfinite.Stream) (t : ℕ) :
    RegisterSemanticInstructionInfinite.parentAt i ⟨b,cost⟩ (compile i b) o w t=
      RegisterSemanticInstructionInfinite.parentAt i ⟨b,cost⟩ (.emit (some b)) o w t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [RegisterSemanticInstructionInfinite.parentAt,ih]
    cases hm : (w t).1 <;>
      simp only [modeRecordStep,Bool.false_eq_true,if_false,if_true]
    dsimp only [RegisterJointRecord.recordStep]
    rw [same_repair_different_value_physical]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterInstructionPurposeScale
