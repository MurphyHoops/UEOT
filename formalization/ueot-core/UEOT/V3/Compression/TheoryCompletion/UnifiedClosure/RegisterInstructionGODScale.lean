import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterInstructionPurposeScale
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterInstructionRecoveryScale
import UEOT.V3.Compression.TheoryCompletion.GOD

/-!
Original promise: GOD means the original set-valued Bellman action correspondence for the SAME actual object and evaluation.
Existing premises: actual submitted/returned AST complete-record values transport; original Bellman optimum covers all fine causal competitors at price*cost≤1.
Reduced premise: derive optimal action-value/selector correspondence from the SAME actual active-row source, then original PreservesGOD/P9 and actual returned-q value optimality.
Family/boundary: original finite register/retained-parent/history/action/source/evaluation rights; an actual zero-price hidden-test GOD selector refutes descent of EVERY optimal fine strategy.
Consumer: original IsBellmanGODSelector, selector_infiniteValue_eq_optimal and PreservesGOD/transport_object_property; GOA invariant-law/occupation semantics remains a separate long-run source obligation.

The object retains its actual parent/history and actual synthesize pair. The
existence of one compilable optimum is not universal factorability of every
fine optimum. ALL-fine-causal comparison uses the original model's physical/
action-history information rights, not fresh mode/label access. The boundary
uses the separately stated legal price-zero parameter instance; it does not
change the prior positive-price fixture, action set or source protocol.
No six-semantics closure, population optimum, energy funding, sampling, new
control action, program installation or reset is claimed.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterInstructionGODScale
open MeasureTheory ProbabilityTheory
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.TheoryCompletion
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultJointRecord
open RegisterActuatorScaleSource RegisterInstructionScaleSource RegisterSemanticInstructionScale
open RegisterInstructionPurposeScale RegisterInstructionRecoveryScale
noncomputable section

section Source
variable {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
variable (price epsilon : NNReal) (he : epsilon≤1) (d : ℝ) (hd : 0<d ∧ d<1)
variable (hc : (price : ℝ)*m.writeCost≤1)
include hc

/-- Native optimal values depend only on the retained actuator; this is
DERIVED from the original SAME-source Bellman solution. -/
theorem optimal_value_projection (x : State n) :
    (RegisterFaultControlModel.model i noise m price epsilon he d hd).optimalValue x=
      (RegisterFaultControlModel.model (0 : Fin 1) noise m price epsilon he d hd).optimalValue (projectState i x) := by
  rw [←RegisterFaultControlModel.value_eq_optimal i noise m price epsilon he d hd hc,
    ←RegisterFaultControlModel.value_eq_optimal 0 noise m price epsilon he d hd hc]
  rfl

/-- This is the actual primitive-mode active row and actual reward. No desired
Bellman factor/optimality equality is a structure field or input. -/
theorem optimal_qValue_projection (x : State n) (a : Action) :
    (RegisterFaultControlModel.model i noise m price epsilon he d hd).qValue
      (RegisterFaultControlModel.model i noise m price epsilon he d hd).optimalValue x a=
    (RegisterFaultControlModel.model (0 : Fin 1) noise m price epsilon he d hd).qValue
      (RegisterFaultControlModel.model (0 : Fin 1) noise m price epsilon he d hd).optimalValue (projectState i x) a := by
  rw [←RegisterFaultControlModel.value_eq_optimal i noise m price epsilon he d hd hc,
    ←RegisterFaultControlModel.value_eq_optimal 0 noise m price epsilon he d hd hc,
    RegisterFaultControlModel.qValue_source,RegisterFaultControlModel.qValue_source]
  simp only [RegisterFaultControlModel.value,active_update,projectState_apply,
    Function.update_apply]

/-- The full original set-valued GOD action correspondence is preserved; no
uniqueness or particular greedy tie breaking is assumed. -/
theorem actual_god_action_iff (x : State n) (a : Action) :
    a∈BellmanGODCorrespondence (RegisterFaultControlModel.model i noise m price epsilon he d hd) x ↔
    a∈BellmanGODCorrespondence (RegisterFaultControlModel.model (0 : Fin 1) noise m price epsilon he d hd) (projectState i x) := by
  simp only [mem_bellmanGODCorrespondence_iff,
    optimal_qValue_projection i noise m price epsilon he d hd hc,
    optimal_value_projection i noise m price epsilon he d hd hc]

/-- Global GOD compatibility of this actual p is equivalent to that of its
actual returned q. Surjectivity is the original computed representative. -/
theorem actual_god_selector_iff (p : Instruction n) (q : Instruction 1)
    (hs : synthesize i p=some q) :
    IsBellmanGODSelector (RegisterFaultControlModel.model i noise m price epsilon he d hd) (interpret p) ↔
    IsBellmanGODSelector (RegisterFaultControlModel.model (0 : Fin 1) noise m price epsilon he d hd) (interpret q) := by
  constructor
  · intro h y
    have hh:=(actual_god_action_iff i noise m price epsilon he d hd hc
      (representative i y) (interpret p (representative i y))).mp (h _)
    have ha : interpret q y=interpret p (representative i y) := by
      simpa using (synthesize_actual i p q hs).2 (representative i y)
    have hy : projectState i (representative i y)=y := by
      ext j
      have hj : j=(0 : Fin 1) := Subsingleton.elim _ _
      subst j
      simp [projectState,representative]
    rw [hy,←ha] at hh
    exact hh
  · intro h x
    have hh:=h (projectState i x)
    rw [(synthesize_actual i p q hs).2] at hh
    exact (actual_god_action_iff i noise m price epsilon he d hd hc x (interpret p x)).mpr hh

/-- One actual original compiler is a GOD selector against the original full
fine state/action model, rather than a new chosen or merely quotient policy. -/
theorem actual_compiled_god :
    IsBellmanGODSelector (RegisterFaultControlModel.model i noise m price epsilon he d hd)
      (interpret (compile i m.goal)) := by
  intro x
  rw [mem_bellmanGODCorrespondence_iff,
    ←RegisterFaultControlModel.value_eq_optimal i noise m price epsilon he d hd hc]
  exact RegisterFaultControlModel.compiled_attains_value i noise m price epsilon he d hd x
end Source

/-- A native GOD selector has this actual complete-record value, by the
original selector theorem and previously derived actual integral binding. -/
theorem actual_god_value {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (price epsilon : NNReal) (he : epsilon≤1) (d : ℝ) (hd : 0<d ∧ d<1)
    (o : Organism n) (hp : o.program=m.goal) (p : Instruction n)
    (hg : IsBellmanGODSelector (RegisterFaultControlModel.model i noise m price epsilon he d hd) (interpret p)) :
    actualValue i noise m epsilon he price d o p=
      (RegisterFaultControlModel.model i noise m price epsilon he d hd).optimalValue o.physical := by
  rw [actual_value_policy i noise m epsilon he price d hd o hp]
  exact selector_infiniteValue_eq_optimal _ _ hg (t:=0) o.physical

abbrev GODObject {n : ℕ} (i : Fin n) := Organism n × Accepted i

def godScale {n : ℕ} (i : Fin n) :
    ObjectScaleMap (State n) (State 1) (GODObject i) (Organism 1 × Instruction 1) :=
  ⟨projectState i,fun obj => (projectOrganism i obj.1,obj.2.val.2)⟩

/-- Original P9 GOD is consumed with its REAL original Bellman semantics. -/
theorem actual_preserves_god {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (price epsilon : NNReal) (he : epsilon≤1) (d : ℝ) (hd : 0<d ∧ d<1)
    (hc : (price : ℝ)*m.writeCost≤1) :
    PreservesGOD (godScale i)
      (fun obj => IsBellmanGODSelector (RegisterFaultControlModel.model i noise m price epsilon he d hd) (interpret obj.2.val.1))
      (fun obj => IsBellmanGODSelector (RegisterFaultControlModel.model (0 : Fin 1) noise m price epsilon he d hd) (interpret obj.2)) := by
  intro obj h
  exact (actual_god_selector_iff i noise m price epsilon he d hd hc _ _ obj.2.property).mp h

/-- Common consumer constructs the actual compiled pair, derives its GOD
property, invokes original P9, and returns the SAME q's actual optimal value. -/
theorem compiled_actual_p9_god {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (price epsilon : NNReal) (he : epsilon≤1) (d : ℝ) (hd : 0<d ∧ d<1)
    (hc : (price : ℝ)*m.writeCost≤1) (o : Organism n) (hp : o.program=m.goal) :
    IsBellmanGODSelector (RegisterFaultControlModel.model (0 : Fin 1) noise m price epsilon he d hd)
      (interpret (returnedProgram i (compile i m.goal))) ∧
    actualValue (0 : Fin 1) noise m epsilon he price d (projectOrganism i o) (returnedProgram i (compile i m.goal))=
      (RegisterFaultControlModel.model i noise m price epsilon he d hd).optimalValue o.physical := by
  let comp : Accepted i := ⟨(compile i m.goal,returnedProgram i (compile i m.goal)),compiled_synthesis i m.goal⟩
  have hf:=actual_compiled_god i noise m price epsilon he d hd hc
  have hq : IsBellmanGODSelector (RegisterFaultControlModel.model (0 : Fin 1) noise m price epsilon he d hd)
      (interpret comp.val.2) :=
    transport_object_property (godScale i)
      (fun obj => IsBellmanGODSelector (RegisterFaultControlModel.model i noise m price epsilon he d hd) (interpret obj.2.val.1))
      (fun obj => IsBellmanGODSelector (RegisterFaultControlModel.model (0 : Fin 1) noise m price epsilon he d hd) (interpret obj.2))
      (fine:= (o,comp)) (coarse:=((godScale i).objectMap (o,comp))) rfl (actual_preserves_god i noise m price epsilon he d hd hc) hf
  refine ⟨hq,?_⟩
  have hv:=actual_value_transport i noise m epsilon he price d o
    (compile i m.goal) (returnedProgram i (compile i m.goal)) (compiled_synthesis i m.goal)
  exact hv.symm.trans (actual_compiled_optimal i noise m epsilon he price d hd hc o hp)

/-- At separately registered price zero, any ACTUAL restoration-checked AST
is GOD-compatible. This does not give it an actuator-only implementation. -/
theorem zero_price_restoring_god {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (d : ℝ) (hd : 0<d ∧ d<1)
    (p : Instruction n) (hc : restorationCheck i m.goal p=true) :
    IsBellmanGODSelector (RegisterFaultControlModel.model i noise m 0 epsilon he d hd) (interpret p) := by
  intro x
  rw [mem_bellmanGODCorrespondence_iff,
    ←RegisterFaultControlModel.value_eq_optimal i noise m 0 epsilon he d hd (by simp)]
  have hu : update i x (interpret p x)=update i x ((substrate i).execute m.goal x) := by
    rw [checked_update_eq_write i m.goal p hc]
    exact (same_repair_different_value_physical i m.goal x).symm
  have heq : (RegisterFaultControlModel.model i noise m 0 epsilon he d hd).qValue
      (RegisterFaultControlModel.value i m 0 epsilon d) x (interpret p x)=
      (RegisterFaultControlModel.model i noise m 0 epsilon he d hd).qValue
        (RegisterFaultControlModel.value i m 0 epsilon d) x ((substrate i).execute m.goal x) := by
    rw [RegisterFaultControlModel.qValue_source,RegisterFaultControlModel.qValue_source]
    simp only [NNReal.coe_zero,zero_mul,sub_zero,hu]
  rw [heq]
  exact RegisterFaultControlModel.compiled_attains_value i noise m 0 epsilon he d hd x

/-- The hidden branch really changes the actual action on good states, while
both branches restore the same target. Price zero makes both GOD actions. -/
def hiddenOptimal : Instruction 2 :=
  .test 0 true (.test 1 true (.emit none) (.emit (some true))) (.emit (some true))

theorem hiddenOptimal_restores : restorationCheck (0 : Fin 2) true hiddenOptimal=true := by
  rw [restorationCheck_iff]
  intro x
  cases hx : x 0 <;> cases hy : x 1 <;> simp [hiddenOptimal,interpret,hx,hy,update]

/-- Strict obstruction: even global GOD-optimality with positive fault noise
DOES NOT force the actual fine policy to descend on every coarse fiber. -/
theorem hiddenOptimal_no_factor :
    synthesize (0 : Fin 2) hiddenOptimal=none ∧
    ¬∃ f : State 1 → Action, ∀ x, f (projectState (0 : Fin 2) x)=interpret hiddenOptimal x := by
  have hn : ¬∃ f : State 1 → Action, ∀ x, f (projectState (0 : Fin 2) x)=interpret hiddenOptimal x := by
    rintro ⟨f,hf⟩
    let x : State 2:=fun _ => true
    let y : State 2:=fun j => if j=0 then true else false
    have hh : projectState (0 : Fin 2) x=projectState 0 y := rfl
    have h:=hf x
    rw [hh,hf y] at h
    have hx : interpret hiddenOptimal x=none := rfl
    have hy : interpret hiddenOptimal y=some true := rfl
    rw [hx,hy] at h
    cases h
  refine ⟨?_,hn⟩
  cases hs : synthesize (0 : Fin 2) hiddenOptimal with
  | none => rfl
  | some q => exact False.elim (hn ⟨interpret q,fun x => (synthesize_actual 0 hiddenOptimal q hs).2 x⟩)

/-- Nonzero-fault common boundary: this actual hidden-sensitive AST is globally
GOD-optimal but has NO coarse implementation of its actual actions. -/
theorem positive_fault_hidden_god (noise : PMF Bool) :
    let he : (1/4 : NNReal)≤1 := by exact_mod_cast (by norm_num : (1/4 : ℝ)≤1)
    IsBellmanGODSelector (RegisterFaultControlModel.model (0 : Fin 2) noise ⟨true,1⟩ 0 (1/4) he (1/2) (by norm_num))
      (interpret hiddenOptimal) ∧ synthesize (0 : Fin 2) hiddenOptimal=none := by
  dsimp only
  exact ⟨zero_price_restoring_god 0 noise ⟨true,1⟩ _ _ (1/2) (by norm_num) hiddenOptimal hiddenOptimal_restores,
    hiddenOptimal_no_factor.1⟩

/-- The rejected hidden-sensitive AST really attains the actual source optimum
from ANY registered parent of protected program true, not merely a formal tie. -/
theorem positive_fault_hidden_actual_value (noise : PMF Bool) (o : Organism 2) (hp : o.program=true) :
    let he : (1/4 : NNReal)≤1 := by exact_mod_cast (by norm_num : (1/4 : ℝ)≤1)
    actualValue (0 : Fin 2) noise ⟨true,1⟩ (1/4) he 0 (1/2) o hiddenOptimal=3/2 := by
  dsimp only
  rw [actual_god_value 0 noise ⟨true,1⟩ 0 (1/4) _ (1/2) (by norm_num) o hp hiddenOptimal
    (positive_fault_hidden_god noise).1,
    ←RegisterFaultControlModel.value_eq_optimal 0 noise ⟨true,1⟩ 0 (1/4) _ (1/2) (by norm_num) (by simp)]
  norm_num [RegisterFaultControlModel.value,RegisterFaultControlModel.goodValue,
    RegisterFaultControlModel.badValue,RegisterFaultControlModel.repairChance]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterInstructionGODScale
