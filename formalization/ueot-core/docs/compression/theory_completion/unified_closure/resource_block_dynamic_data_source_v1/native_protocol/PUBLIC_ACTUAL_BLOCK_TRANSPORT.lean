import UEOT
namespace IndependentBlockFormation
open MeasureTheory ProbabilityTheory Set
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultJointRecord
open RegisterRotatingBodySource RegisterBlockFormationTransport
open scoped ENNReal
noncomputable section
local instance {n : ℕ} : MeasurableSpace (ModeRecord n):=⊤
local instance {n : ℕ} : MeasurableSpace (List (ModeRecord n)):=⊤

def block : Fin 3 ↪ Fin 5 := ⟨fun j=>if j=0 then 4 else if j=1 then 2 else 0,by decide⟩
@[simp] theorem block_zero : block 0=4 :=rfl
@[simp] theorem block_one : block 1=2 :=rfl
@[simp] theorem block_two : block 2=0 :=rfl

def ready : Organism 5:=⟨[true,false,true],fun j=>decide (j=0 ∨ j=2 ∨ j=4),false⟩
def bad : Organism 5:=⟨[true,false,true],fun _=>true,false⟩
def z : RoundRaw 5:=fun _=>(true,false)
def birthRecord : ModeRecord 5:=transaction (block 1) false 4 ready (true,false)
def child : Organism 5:=birthEvent (block 1) false birthRecord.transaction.parentAfter

theorem born_actual : RegisterActuatorScaleSource.birthFormation (block 1) 4 (some false) true false ready child :=rfl

-- The original formation/binding consumer uses the SAME literal child at a
-- DIFFERENT next port and keeps its fault/failedbirth/zerocharge record.
theorem common_birth_next_binding :
    RegisterActuatorScaleSource.birthFormation (1 : Fin 3) 4 (some false) true false (organism block ready) (organism block child) ∧
    RegisterActuatorScaleSource.ownBinding (2 : Fin 3) 4 (some false) false true (organism block child)=
      modeRecord block (RegisterActuatorScaleSource.ownBinding (block 2) 4 (some false) false true child) :=
  actual_birth_next_port_binding block 1 2 4 (some false) (some false) true false false true ready child born_actual

example : child.program=false ∧ child.history=[true,false,true,false] :=⟨rfl,rfl⟩
example : (RegisterActuatorScaleSource.ownBinding (block 2) 4 (some false) false true child).transaction.child=none ∧
    (RegisterActuatorScaleSource.ownBinding (block 2) 4 (some false) false true child).transaction.expenditure=0 :=⟨rfl,rfl⟩
example : (RegisterActuatorScaleSource.ownBinding (block 2) 4 (some false) true true child).transaction.expenditure=4 :=rfl

example : organism block (runPorts false 4 z ready ((List.finRange 3).map block))=
    runPorts false 4 (raw block z) (organism block ready) (List.finRange 3) :=
  run_transport block false 4 z ready (List.finRange 3)
example : (tracePorts false 4 z ready ((List.finRange 3).map block)).map (modeRecord block)=
    tracePorts false 4 (raw block z) (organism block ready) (List.finRange 3) :=
  trace_transport block false 4 z ready (List.finRange 3)
example : (tracePorts false 4 z ready ((List.finRange 3).map block)).map (fun r=>r.transaction.expenditure)=[4,4,4] :=rfl
example : (tracePorts false 4 z ready ((List.finRange 3).map block)).map (fun r=>r.transaction.child.isSome)=[true,true,true] :=rfl

example : state block ready.physical=state block bad.physical :=by
  ext j
  fin_cases j <;> rfl
example : BodyGoal false (state block (runPorts false 4 z bad ((List.finRange 3).map block)).physical) :=
  (block_round_goal_iff block false 4 z bad).mpr (fun _=>rfl)
example : ¬BodyGoal false (runPorts false 4 z bad ((List.finRange 3).map block)).physical :=by
  intro h
  have hx:=((full_body_after_block_iff block false 4 z bad).mp h).2 (1 : Fin 5)
    (by decide)
  change true=false at hx
  cases hx
example : BodyGoal false (runPorts false 4 z ready ((List.finRange 3).map block)).physical :=by
  apply (full_body_after_block_iff block false 4 z ready).mpr
  refine ⟨fun _=>rfl,?_⟩
  intro l hl
  fin_cases l
  · exact False.elim (hl ⟨2,rfl⟩)
  · rfl
  · exact False.elim (hl ⟨1,rfl⟩)
  · rfl
  · exact False.elim (hl ⟨0,rfl⟩)

-- A repeated visit reuses its actual per-port outcome, preserves the real
-- retained parent, and therefore idles for zero fee after prior repair.
example : (tracePorts false 4 z ready ([2,0,2,1].map block)).map (modeRecord block)=
    tracePorts false 4 (raw block z) (organism block ready) [2,0,2,1] :=
  trace_transport block false 4 z ready [2,0,2,1]
example : (tracePorts false 4 z ready ([2,0,2,1].map block)).map (fun r=>r.transaction.expenditure)=[4,4,0,4] :=rfl

theorem eps_ok : (2/7 : NNReal)≤1 :=by exact_mod_cast (by norm_num : (2/7 : ℝ)≤1)
example : (roundLaw 5 (PMF.pure false) (2/7) eps_ok).map (raw block)=roundLaw 3 (PMF.pure false) (2/7) eps_ok :=
  raw_source_law block (PMF.pure false) (2/7) eps_ok

theorem common_actual_trace_law :
    ((roundLaw 5 (PMF.pure false) (2/7) eps_ok).map
      (fun zz=>tracePorts false 4 zz ready ((List.finRange 3).map block))).map (fun rs=>rs.map (modeRecord block))=
        roundRecordLaw false 4 (PMF.pure false) (2/7) eps_ok (organism block ready) :=
  block_round_record_law block false 4 (PMF.pure false) (2/7) eps_ok ready

example (price : NNReal) : RegisterJointRecord.payoff price (modeRecord block birthRecord).transaction=
    RegisterJointRecord.payoff price birthRecord.transaction :=payoff_transport block price birthRecord
example : (lineage (1 : Fin 3)).OffspringOf (organism block birthRecord.transaction.parentAfter) (organism block child) :=
  offspring_transport block 1 _ child (birth_is_distinct_offspring (block 1) false _)
example : (lineage (2 : Fin 3)).SameObject (organism block child) (organism block (repairEvent (block 2) child)) :=by
  apply (same_object_iff block 2 child (repairEvent (block 2) child)).mpr
  exact (repair_same_object (block 2) child).symm

def emptyBlock (n : ℕ) : Fin 0 ↪ Fin n:=⟨Fin.elim0,by intro j; exact Fin.elim0 j⟩
example : tracePorts false 4 z ready ((List.finRange 0).map (emptyBlock 5))=[] :=rfl
example : BodyGoal false (runPorts false 4 z ready ((List.finRange 0).map (emptyBlock 5))).physical ↔
    BodyGoal false ready.physical :=Iff.rfl
example : (roundLaw 5 (PMF.pure false) (2/7) eps_ok).map (raw (emptyBlock 5))=roundLaw 0 (PMF.pure false) (2/7) eps_ok :=
  raw_source_law (emptyBlock 5) (PMF.pure false) (2/7) eps_ok
example (zz : RoundRaw 0) (o : Organism 0) :
    BodyGoal false (runPorts false 4 zz o ((List.finRange 0).map (emptyBlock 0))).physical :=by
  intro j
  exact Fin.elim0 j
example (zz : RoundRaw 0) (o : Organism 0) (r : ModeRecord 0) : r∉tracePorts false 4 zz o [] :=by simp [tracePorts]

example : ¬∃ next : State 1→State 1,∀ o : Organism 2,
    RegisterActuatorScaleSource.projectState 1 (transaction 0 true 1 o (true,false)).transaction.parentAfter.physical=
      next (RegisterActuatorScaleSource.projectState 0 o.physical) :=next_port_information_obstruction

#print axioms common_birth_next_binding
#print axioms common_actual_trace_law
#print axioms full_body_after_block_iff
end
end IndependentBlockFormation
