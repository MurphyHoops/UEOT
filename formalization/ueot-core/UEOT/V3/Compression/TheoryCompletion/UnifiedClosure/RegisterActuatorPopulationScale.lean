import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterActuatorScaleSource

/-!
Original commitment: a scale representation must preserve actual formation, owner identity, purpose execution and resources together.
Existing premises: actuator/source path transport is proved, but actual population lookup, allocator and ledger transport were independent.
Premise reduced: derive these from the SAME retained-actuator map, slot-preserving store, literal transaction and complete history.
Model/counter: existing serialized own-program-fault population and existing requested-idle open resource port; passive coordinates only are forgotten.
Consumer: actual child/parent journals and fixed old-address offspring, compiled paid repair, and original P6 viability on the SAME lifted infinite path.

No owner is merged: slots (including None), identities, timestamps, protected
program/history, failure ticks, all costs and labels are retained. The explicit
own-program fault model and open resource port are the already registered new
models; no environmental target or supply permission is silently changed.
Schedulers must factor through these retained fields; this proves the literal
compiled scheduler does. Arbitrary policies reading hidden registers and a
whole-population bank/optimality theorem remain outside this source.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterActuatorPopulationScale
open MeasureTheory ProbabilityTheory
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.TheoryCompletion
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose
open RegisterFaultControlModel RegisterFaultJointRecord RegisterFaultInfiniteRecord
open RegisterTimestampedBirthSource (ClockedOrganism ClockedRecord)
open RegisterPopulationHistorySource (Store Request)
open RegisterActuatorScaleSource
noncomputable section


def projectClocked {n : ℕ} (i : Fin n) (p : ClockedOrganism n) : ClockedOrganism 1 :=
  ⟨projectOrganism i p.organism,p.identity,p.clock⟩
def projectClockedRecord {n : ℕ} (i : Fin n) (r : ClockedRecord n) : ClockedRecord 1 :=
  ⟨projectClocked i r.parentBefore,r.action,r.repairMode,r.label,projectClocked i r.parentAfter,
    r.child.map (projectClocked i),r.expenditure⟩
def projectStore {n : ℕ} (i : Fin n) (s : Store n) : Store 1 := s.map (Option.map (projectClocked i))

@[simp] theorem projectStore_length {n : ℕ} (i : Fin n) (s : Store n) :
    (projectStore i s).length=s.length := by simp [projectStore]

@[simp] theorem lookup_transport {n : ℕ} (i : Fin n) (s : Store n) (j : ℕ) :
    RegisterPopulationHistorySource.lookup (projectStore i s) j=(RegisterPopulationHistorySource.lookup s j).map (projectClocked i) := by
  simp only [RegisterPopulationHistorySource.lookup,projectStore,List.getElem?_map]
  cases s[j]? with
  | none => rfl
  | some p => cases p <;> rfl

@[simp] theorem timestamp_transport {n : ℕ} (i : Fin n) (m : Mechanism) (p : ClockedOrganism n)
    (a : Action) (mode label : Bool) :
    projectClockedRecord i (RegisterTimestampedBirthSource.step i m p a mode label)=
      RegisterTimestampedBirthSource.step (0 : Fin 1) m (projectClocked i p) a mode label := by
  simp only [RegisterTimestampedBirthSource.step,projectClocked]
  rw [← mode_step_transport i m p.organism a mode label]
  simp only [projectClockedRecord,projectModeRecord,projectRecord,projectClocked,Option.map_map]
  rfl

@[simp] theorem clocked_erasure {n : ℕ} (i : Fin n) (r : ClockedRecord n) :
    RegisterTimestampedBirthSource.eraseRecord (projectClockedRecord i r)=
      projectModeRecord i (RegisterTimestampedBirthSource.eraseRecord r) := by
  cases r
  simp [RegisterTimestampedBirthSource.eraseRecord,projectClockedRecord,projectClocked,projectModeRecord,projectRecord,Option.map_map]
  rfl

@[simp] theorem fixed_transaction_transport {n : ℕ} (i : Fin n) (m : Mechanism) (s : Store n) (q : Request) :
    (RegisterPopulationHistorySource.transaction i m s q).map (projectClockedRecord i)=RegisterPopulationHistorySource.transaction (0 : Fin 1) m (projectStore i s) q := by
  simp only [RegisterPopulationHistorySource.transaction,lookup_transport,Option.map_map]
  congr 1
  funext p
  simpa only [projectStore_length,projectClocked,Function.comp_apply] using timestamp_transport i m {p with clock:=s.length} q.action q.mode q.label

@[simp] theorem fixed_child_transport {n : ℕ} (i : Fin n) (m : Mechanism) (s : Store n) (q : Request) :
    (RegisterPopulationHistorySource.child i m s q).map (projectClocked i)=RegisterPopulationHistorySource.child (0 : Fin 1) m (projectStore i s) q := by
  unfold RegisterPopulationHistorySource.child
  rw [← fixed_transaction_transport]
  cases RegisterPopulationHistorySource.transaction i m s q with
  | none => rfl
  | some r => rfl

@[simp] theorem fixed_next_transport {n : ℕ} (i : Fin n) (m : Mechanism) (s : Store n) (q : Request) :
    projectStore i (RegisterPopulationHistorySource.next i m s q)=RegisterPopulationHistorySource.next (0 : Fin 1) m (projectStore i s) q := by
  unfold RegisterPopulationHistorySource.next
  rw [← fixed_transaction_transport,← fixed_child_transport]
  cases RegisterPopulationHistorySource.transaction i m s q with
  | none => simp [projectStore]
  | some r => simp [projectStore,projectClockedRecord,List.map_set]

@[simp] theorem own_mechanism_transport {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (q : Request) :
    RegisterOwnProgramPopulation.mechanism c (projectStore i s) q=RegisterOwnProgramPopulation.mechanism c s q := by
  unfold RegisterOwnProgramPopulation.mechanism
  rw [lookup_transport]
  cases RegisterPopulationHistorySource.lookup s q.parent <;> rfl

@[simp] theorem own_transaction_transport {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (q : Request) :
    (RegisterOwnProgramPopulation.transaction i c s q).map (projectClockedRecord i)=RegisterOwnProgramPopulation.transaction (0 : Fin 1) c (projectStore i s) q := by
  simp only [RegisterOwnProgramPopulation.transaction,own_mechanism_transport,fixed_transaction_transport]

@[simp] theorem own_child_transport {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (q : Request) :
    (RegisterOwnProgramPopulation.child i c s q).map (projectClocked i)=RegisterOwnProgramPopulation.child (0 : Fin 1) c (projectStore i s) q := by
  simp only [RegisterOwnProgramPopulation.child,own_mechanism_transport,fixed_child_transport]

@[simp] theorem own_next_transport {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (q : Request) :
    projectStore i (RegisterOwnProgramPopulation.next i c s q)=RegisterOwnProgramPopulation.next (0 : Fin 1) c (projectStore i s) q := by
  simp only [RegisterOwnProgramPopulation.next,own_mechanism_transport,fixed_next_transport]

/-- Any registered sequence of dispatches has the SAME complete retained store.
Invalid lookup and failed births still append None, so allocator time is exact. -/
theorem own_run_transport {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (es : List Request) :
    projectStore i (RegisterOwnProgramPopulation.run i c s es)=RegisterOwnProgramPopulation.run (0 : Fin 1) c (projectStore i s) es := by
  induction es generalizing s with
  | nil => rfl
  | cons q es ih =>
    change projectStore i (RegisterOwnProgramPopulation.run i c (RegisterOwnProgramPopulation.next i c s q) es)=_
    rw [ih,own_next_transport]
    rfl

/-- Complete chronological journal, including invalid None transactions;
no successful-child filtering or final-store-only account. -/
def transactionTrace {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) : List Request → List (Option (ClockedRecord n))
  | [] => []
  | q::es => RegisterOwnProgramPopulation.transaction i c s q ::
    transactionTrace i c (RegisterOwnProgramPopulation.next i c s q) es

theorem transaction_trace_transport {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (es : List Request) :
    (transactionTrace i c s es).map (Option.map (projectClockedRecord i))=
      transactionTrace (0 : Fin 1) c (projectStore i s) es := by
  induction es generalizing s with
  | nil => rfl
  | cons q es ih => simp only [transactionTrace,List.map_cons,own_transaction_transport,ih,own_next_transport]

/-- The ACTUAL compiled parent controller is admissible under this scale map;
lookup/program/current actuator, rather than an independently supplied factor. -/
theorem compiled_request_transport {n : ℕ} (i : Fin n) (s : Store n) (j : ℕ) (mode label : Bool) :
    RegisterOwnProgramPopulation.compiledRequest i s j mode label=RegisterOwnProgramPopulation.compiledRequest (0 : Fin 1) (projectStore i s) j mode label := by
  simp only [RegisterOwnProgramPopulation.compiledRequest,lookup_transport]
  cases RegisterPopulationHistorySource.lookup s j <;> rfl

theorem childAt_transport {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (es : List Request) (k : Fin es.length) :
    (RegisterOwnProgramPopulation.childAt i c s es k).map (projectClocked i)=RegisterOwnProgramPopulation.childAt (0 : Fin 1) c (projectStore i s) es k := by
  simp only [RegisterOwnProgramPopulation.childAt,RegisterOwnProgramPopulation.storeBefore,← own_run_transport,← own_child_transport]

/-- Numeric IDs and actual parents agree EXACTLY, not merely up to an assumed
renaming. The same failures are None on both sides of the original P12 source. -/
theorem actual_journal_transport {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (es : List Request) (k : Fin es.length) :
    RegisterOwnProgramPopulation.observedChildID i c s es k=RegisterOwnProgramPopulation.observedChildID (0 : Fin 1) c (projectStore i s) es k ∧
    RegisterOwnProgramPopulation.actualParent i c s es k=RegisterOwnProgramPopulation.actualParent (0 : Fin 1) c (projectStore i s) es k := by
  simp only [RegisterOwnProgramPopulation.observedChildID,RegisterOwnProgramPopulation.actualParent,projectStore_length,← childAt_transport,Option.map_map]
  constructor <;> rfl

/-- The existing actual-parent source theorem is consumed after transport. -/
theorem same_childID_same_actual_parent {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (es : List Request)
    (j k : Fin es.length) (h : RegisterOwnProgramPopulation.observedChildID i c s es j=RegisterOwnProgramPopulation.observedChildID i c s es k) :
    RegisterOwnProgramPopulation.actualParent (0 : Fin 1) c (projectStore i s) es j=RegisterOwnProgramPopulation.actualParent (0 : Fin 1) c (projectStore i s) es k := by
  rw [← (actual_journal_transport i c s es j).2,← (actual_journal_transport i c s es k).2]
  exact RegisterOwnProgramPopulation.parent_eq_of_childID i c s es j k h

/-- Same frozen OLD-address cohort, not all occupants of the final store. -/
theorem cohort_offspring_transport {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n)
    (actions : ℕ → Action) (modes labels : ℕ → Bool) (j : Fin s.length) :
    (RegisterOwnProgramPopulation.offspring i c s actions modes labels j).map (projectClocked i)=
      RegisterOwnProgramPopulation.offspring (0 : Fin 1) c (projectStore i s) actions modes labels
        ⟨j,by simp only [projectStore_length]; exact j.isLt⟩ := by
  unfold RegisterOwnProgramPopulation.offspring RegisterOwnProgramPopulation.before
  simp only [RegisterPopulationTypePrice.cohortRequests,projectStore_length,
    ← own_run_transport,← own_child_transport]

/-- Actual inherited program array, including None, is identical. Thus the
existing nonempty-offspring normalization/Price source can be reused; no new
transmission kernel or ratio-of-expectations premise is introduced. -/
theorem cohort_type_array_transport {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n)
    (actions : ℕ → Action) (modes labels : ℕ → Bool) (j : Fin s.length) :
    (RegisterOwnProgramPopulation.offspring i c s actions modes labels j).map (fun d => d.organism.program)=
      (RegisterOwnProgramPopulation.offspring (0 : Fin 1) c (projectStore i s) actions modes labels
        ⟨j,by simp only [projectStore_length]; exact j.isLt⟩).map (fun d => d.organism.program) := by
  rw [← cohort_offspring_transport,Option.map_map]
  rfl

/-- Nonempty offspring is exactly preserved; zero generations remain zero.
This transports the original domain of normalization, not an E-ratio identity. -/
theorem nonempty_cohort_transport {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n)
    (actions : ℕ → Action) (modes labels : ℕ → Bool) (b : Bool) :
    0 < RegisterPopulationTypePrice.birthCount i ⟨b,c⟩ s actions modes labels ↔
    0 < RegisterPopulationTypePrice.birthCount (0 : Fin 1) ⟨b,c⟩ (projectStore i s) actions modes labels := by
  have hborn (j : Fin s.length) :
      RegisterPopulationTypePrice.born i ⟨b,c⟩ s actions modes labels j ↔
      RegisterPopulationTypePrice.born (0 : Fin 1) ⟨b,c⟩ (projectStore i s) actions modes labels
        ⟨j,by simp only [projectStore_length]; exact j.isLt⟩ := by
    have h := congrArg Option.isSome (cohort_offspring_transport i c s actions modes labels j)
    simp only [Option.isSome_map,RegisterOwnProgramPopulation.offspring_eq_old i c s actions modes labels b,
      RegisterOwnProgramPopulation.offspring_eq_old (0 : Fin 1) c (projectStore i s) actions modes labels b] at h
    exact Bool.eq_iff_iff.mp h
  unfold RegisterPopulationTypePrice.birthCount
  rw [Fintype.card_pos_iff,Fintype.card_pos_iff]
  constructor
  · rintro ⟨⟨j,hj⟩⟩
    exact ⟨⟨⟨j,by simp only [projectStore_length]; exact j.isLt⟩,(hborn j).mp hj⟩⟩
  · rintro ⟨⟨j,hj⟩⟩
    let k : Fin s.length := ⟨j,by simpa only [projectStore_length] using j.isLt⟩
    exact ⟨⟨k,(hborn k).mpr hj⟩⟩

/-- A serialized schedule of addresses/modes/labels, with each requested action
computed from the actual retained store. No hidden-bit policy-factor premise. -/
def compiledEpisode {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) : List (ℕ × Bool × Bool) → List Request
  | [] => []
  | (j,mode,label)::es =>
    let q := RegisterOwnProgramPopulation.compiledRequest i s j mode label
    q :: compiledEpisode i c (RegisterOwnProgramPopulation.next i c s q) es

theorem compiled_episode_transport {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (es : List (ℕ × Bool × Bool)) :
    compiledEpisode i c s es=compiledEpisode (0 : Fin 1) c (projectStore i s) es := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih =>
    rcases e with ⟨j,mode,label⟩
    simp only [compiledEpisode]
    rw [ih,own_next_transport,compiled_request_transport]

/-- All outcomes of ANY primitive draw law transport, not just a positive
success word. Requests may depend on the complete raw episode. -/
theorem population_pmf_transport {n : ℕ} {Ω : Type} (i : Fin n) (c : NNReal) (s : Store n)
    (law : PMF Ω) (requests : Ω → List Request) :
    (law.map (fun w => RegisterOwnProgramPopulation.run i c s (requests w))).map (projectStore i)=
      law.map (fun w => RegisterOwnProgramPopulation.run (0 : Fin 1) c (projectStore i s) (requests w)) := by
  rw [PMF.map_comp]
  congr 1
  funext w
  exact own_run_transport i c s (requests w)

open RegisterFaultFeedbackResource
open UEOT.V3.Compression.Objecthood.ResourceClosure

@[simp] theorem idle_inflow_transport {n : ℕ} (i : Fin n) (g : ℝ) (r : ModeRecord n) :
    idleInflow g (projectModeRecord i r)=idleInflow g r := rfl

@[simp] theorem cushion_transport {n : ℕ} (i : Fin n) (m : Mechanism) (x : State n) :
    cushion (0 : Fin 1) m (projectState i x)=cushion i m x := rfl

/-- SAME initial reserve and actual complete balance; no free hidden reserve,
new energy permission, or paid-write/fault record is discarded by projection. -/
theorem list_balance_transport {n : ℕ} (i : Fin n) (reserve g : ℝ) (rs : List (ModeRecord n)) :
    listBalance reserve g (rs.map (projectModeRecord i))=listBalance reserve g rs := by
  simp only [listBalance,List.map_map]
  rfl

/-- Exact pathwise resource predicate; validity is reflected as well as
preserved because every literal action and fee survives. -/
theorem resource_viable_transport {n : ℕ} (i : Fin n) (reserve g : ℝ) (rs : ℕ → ModeRecord n) :
    ResourceViable reserve (fun t => idleInflow g (projectModeRecord i (rs t)))
      (fun t => (projectModeRecord i (rs t)).transaction.expenditure) ↔
    ResourceViable reserve (fun t => idleInflow g (rs t)) (fun t => (rs t).transaction.expenditure) := Iff.rfl

local instance {d : ℕ} : MeasurableSpace (ModeRecord d) := ⊤
local instance {d : ℕ} : MeasurableSingletonClass (ModeRecord d) := ⟨fun _ => trivial⟩

/-- Original P6 on the SAME actual fine infinite path and specified lifted
compiled program. The existing open idle port and initial reserve rights are
explicit; this does not finance an unspecified population or training stage. -/
theorem lifted_actual_resource_viable {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon ≤ 1) (g reserve : ℝ) (hg : (m.writeCost : ℝ) ≤ g)
    (hr : (m.writeCost : ℝ) ≤ reserve) (o : Organism n) :
    let pi := selectorPolicy ((substrate (0 : Fin 1)).execute m.goal)
    ∀ᵐ rs ∂recordPathLaw i noise m epsilon he (liftPolicy i pi)
      ⟨0,(o.physical,projectState i o.physical),o⟩,
      ResourceViable reserve (fun t => idleInflow g (rs t)) (fun t => (rs t).transaction.expenditure) := by
  dsimp only
  let pi := selectorPolicy ((substrate (0 : Fin 1)).execute m.goal)
  let cfg : Config (liftPolicy i pi) := ⟨0,(o.physical,projectState i o.physical),o⟩
  have h := RegisterFaultFeedbackResource.actual_recordPath_resource_viable (0 : Fin 1) noise m epsilon he
    g reserve hg hr (projectOrganism i o)
  have hm : Measurable (fun (rs : ℕ → ModeRecord n) k => projectModeRecord i (rs k)) := by
    apply measurable_pi_lambda
    intro k
    have hf : Measurable (projectModeRecord i) := by intro s hs; trivial
    exact hf.comp (measurable_pi_apply k)
  have hmap := RegisterActuatorScaleSource.recordPathLaw_transport i m pi noise epsilon he cfg
  dsimp only at h
  have heq : projectConfig i pi cfg=⟨0,(projectOrganism i o).physical,projectOrganism i o⟩ := rfl
  rw [heq] at hmap
  rw [← hmap] at h
  have hh := h
  exact ae_of_ae_map hm.aemeasurable hh

/-- A genuine three-register realization with the protected actuator at port1.
Passive coordinates can vary independently of the actual control program. -/
def embedClocked (hidden : Bool) (p : ClockedOrganism 1) : ClockedOrganism 3 :=
  ⟨⟨p.organism.history,fun j => if j=1 then p.organism.physical 0 else hidden,p.organism.program⟩,p.identity,p.clock⟩

@[simp] theorem project_embed (hidden : Bool) (p : ClockedOrganism 1) :
    projectClocked (1 : Fin 3) (embedClocked hidden p)=p := by
  cases p with
  | mk o id t =>
    cases o with
    | mk history physical program =>
      change (⟨⟨history,projectState (1 : Fin 3) (fun j => if j=1 then physical 0 else hidden),program⟩,id,t⟩ : ClockedOrganism 1)=_
      congr 2
      funext j
      have hj : j=(0 : Fin 1) := Subsingleton.elim _ _
      subst j
      rfl

def witnessStore (hidden : Bool) : Store 3 :=
  RegisterOwnProgramPopulation.witnessInitial.map (Option.map (embedClocked hidden))

@[simp] theorem project_witnessStore (hidden : Bool) :
    projectStore (1 : Fin 3) (witnessStore hidden)=RegisterOwnProgramPopulation.witnessInitial := by
  simp only [projectStore,witnessStore,List.map_map]
  have h : (fun p : Option (ClockedOrganism 1) => Option.map (projectClocked (1 : Fin 3))
      (Option.map (embedClocked hidden) p))=id := by
    funext p
    cases p <;> simp
  change List.map (fun p => Option.map (projectClocked (1 : Fin 3)) (Option.map (embedClocked hidden) p)) _ = _
  rw [h,List.map_id]

/-- All256 original primitive population words, with the REAL fourth paid
request computed from the actual prefix. This is not success-conditioned. -/
theorem witness_full_population_source (hidden : Bool) (w : Fin 4 → Bool × Bool) :
    projectStore (1 : Fin 3) (RegisterOwnProgramPopulation.run (1 : Fin 3) 1 (witnessStore hidden)
      (RegisterOwnProgramPopulation.fourStepRequests w))=
      RegisterOwnProgramPopulation.run (0 : Fin 1) 1 RegisterOwnProgramPopulation.witnessInitial
        (RegisterOwnProgramPopulation.fourStepRequests w) := by
  rw [own_run_transport,project_witnessStore]

/-- The requested actions used in that four-step source are themselves
computed identically from the actual fine parent, including the adaptive fourth
request after the first three actual events. -/
theorem witness_actual_requests (hidden : Bool) (past : List Request) (j : ℕ) (mode label : Bool) :
    RegisterOwnProgramPopulation.compiledRequest (1 : Fin 3)
      (RegisterOwnProgramPopulation.run (1 : Fin 3) 1 (witnessStore hidden) past) j mode label=
    RegisterOwnProgramPopulation.compiledRequest (0 : Fin 1)
      (RegisterOwnProgramPopulation.run (0 : Fin 1) 1 RegisterOwnProgramPopulation.witnessInitial past) j mode label := by
  rw [compiled_request_transport,own_run_transport,project_witnessStore]

/-- Actual fine experiment keeps the same failure slot, two inherited program
types and subsequent paid repair, without new initial-state preparation. -/
theorem witness_two_types_failure_and_fee (hidden : Bool) :
    let s := RegisterOwnProgramPopulation.run (1 : Fin 3) 1 (witnessStore hidden)
      RegisterOwnProgramPopulation.witnessEpisode
    (RegisterPopulationHistorySource.lookup s 3).map (fun d => d.organism.program)=some false ∧
    (RegisterPopulationHistorySource.lookup s 5).map (fun d => d.organism.program)=some true ∧
    RegisterPopulationHistorySource.lookup s 4=none ∧
    (RegisterOwnProgramPopulation.transaction (1 : Fin 3) 1 s
      (RegisterOwnProgramPopulation.compiledRequest (1 : Fin 3) s 1 true true)).map ClockedRecord.expenditure=some 1 := by
  dsimp only
  let s := RegisterOwnProgramPopulation.run (1 : Fin 3) 1 (witnessStore hidden)
    RegisterOwnProgramPopulation.witnessEpisode
  have hp : projectStore (1 : Fin 3) s=RegisterOwnProgramPopulation.witnessAfterCohort := by
    simp only [s,own_run_transport,project_witnessStore,RegisterOwnProgramPopulation.witnessAfterCohort]
  have h3 := congrArg (fun t => (RegisterPopulationHistorySource.lookup t 3).map (fun d => d.organism.program)) hp
  have h5 := congrArg (fun t => (RegisterPopulationHistorySource.lookup t 5).map (fun d => d.organism.program)) hp
  have h4 := congrArg (fun t => RegisterPopulationHistorySource.lookup t 4) hp
  simp only [lookup_transport,Option.map_map] at h3 h5 h4
  have hw := RegisterOwnProgramPopulation.two_type_paid_repair_witness
  have hc : RegisterOwnProgramPopulation.compiledRequest (1 : Fin 3) s 1 true true=
      RegisterOwnProgramPopulation.witnessRepair := by
    rw [compiled_request_transport,hp]
    rfl
  have hf := congrArg (Option.map ClockedRecord.expenditure)
    (own_transaction_transport (1 : Fin 3) 1 s (RegisterOwnProgramPopulation.compiledRequest (1 : Fin 3) s 1 true true))
  rw [hp,hc] at hf
  simp only [Option.map_map] at hf
  refine ⟨h3.trans hw.2.1,h5.trans hw.2.2.1,?_,?_⟩
  · cases hh : RegisterPopulationHistorySource.lookup s 4 <;> simp_all
  · exact hf.trans hw.2.2.2.2.2.2.2.1

open UEOT.V3.EvolutionPrice
open RegisterOwnProgramPopulation (actualCensusMean actualFertility witnessActions witnessModes)

/-- SAME fine population's actual offspring consumes original Core Price.
Nonemptiness comes from the very same projected episode, not an external
fertility or normalized transmission certificate. Census is offspring-only. -/
theorem witness_actual_price (hidden : Bool) (z : Bool → ℝ) :
    actualCensusMean (1 : Fin 3) 1 (witnessStore hidden) witnessActions witnessModes (fun _ => true) false z -
      weightedMean (RegisterPopulationTypePrice.frequency (witnessStore hidden))
        (RegisterPopulationTypePrice.parentTrait (witnessStore hidden) z) =
    weightedCov (RegisterPopulationTypePrice.frequency (witnessStore hidden))
      (actualFertility (1 : Fin 3) 1 (witnessStore hidden) witnessActions witnessModes (fun _ => true))
      (RegisterPopulationTypePrice.parentTrait (witnessStore hidden) z) /
    weightedMean (RegisterPopulationTypePrice.frequency (witnessStore hidden))
      (actualFertility (1 : Fin 3) 1 (witnessStore hidden) witnessActions witnessModes (fun _ => true)) := by
  apply RegisterOwnProgramPopulation.own_program_type_price
  apply (nonempty_cohort_transport (1 : Fin 3) 1 (witnessStore hidden) witnessActions witnessModes (fun _ => true) false).mpr
  rw [project_witnessStore,RegisterOwnProgramPopulation.witness_birthCount]
  norm_num

local instance {d : ℕ} : MeasurableSpace (ClockedRecord d) := ⊤
local instance {d : ℕ} : MeasurableSpace (List (Option (ClockedRecord d))) := ⊤

/-- The original fourDrawLaw drives ALL fine transactions. The complete
journal law, including failures and paid actions, projects to the original
own-program source law; no positive-word conditioning or re-draw. -/
theorem witness_complete_journal_law (hidden : Bool) :
    ((RegisterOwnProgramPopulation.fourDrawLaw).map (fun w =>
      transactionTrace (1 : Fin 3) 1 (witnessStore hidden) (RegisterOwnProgramPopulation.fourStepRequests w))).map
      (List.map (Option.map (projectClockedRecord (1 : Fin 3))))=
    (RegisterOwnProgramPopulation.fourDrawLaw).map (fun w =>
      transactionTrace (0 : Fin 1) 1 RegisterOwnProgramPopulation.witnessInitial (RegisterOwnProgramPopulation.fourStepRequests w)) := by
  have hm : Measurable (List.map (Option.map (projectClockedRecord (1 : Fin 3)))) := by intro t ht; trivial
  rw [Measure.map_map hm (measurable_of_finite _)]
  congr 1
  funext w
  simp only [Function.comp_apply,transaction_trace_transport,project_witnessStore]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterActuatorPopulationScale
