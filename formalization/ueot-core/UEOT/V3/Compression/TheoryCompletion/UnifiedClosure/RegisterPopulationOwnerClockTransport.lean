import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicProbeHistoryPrice
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicProbeClocked

/-!
Original promise: one actual returned program's population keeps an explicitly registered source owner/time view.
Existing inputs: same post-probe parent/AST, serial single founder and literal timestamp interpreter; owner is not read by Batch.
Premise reduced: derive registration and finite execution transport rather than stipulate owner/clock matching.
Class/boundary: every finite request word, actual failures/invalid slots/fees; newborn clock0 is retained, not uniformly shifted.
Consumer: actual P8 parent/fresh slot and history-depth Price, then the finite-generation P12 common consumer; not fixed-parent native/global GOD.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterPopulationOwnerClockTransport
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultJointRecord
open RegisterTimestampedBirthSource (ClockedOrganism ClockedRecord Identity)
open RegisterPopulationHistorySource (Store Request)
open RegisterFaultDynamicProbePopulation
noncomputable section

/-- Serial founder marker; later real dispatch timestamps are strictly positive. -/
def root : Identity := [(0,false)]

def shiftEvent (R : ℕ) (e : ℕ×Bool) : ℕ×Bool := (R+e.1,e.2)

/-- On reachable root++positive suffix this is exactly f++shift(R,suffix).
The total flatMap definition also makes the literal step proof independent of
an externally supplied complete genealogy list. -/
def ownerView (f : Identity) (R : ℕ) (id : Identity) : Identity :=
  id.flatMap (fun e=>if e=(0,false) then f else [shiftEvent R e])

/-- A newborn has its real zero local clock. Root registration and positive
last-update counters are rebased; dispatch epoch is proved separately below. -/
def parentView {n : ℕ} (f : Identity) (R : ℕ) (o : ClockedOrganism n) : ClockedOrganism n :=
  ⟨o.organism,ownerView f R o.identity,
    if o.clock=0 ∧ o.identity≠root then 0 else R+o.clock⟩

def recordView {n : ℕ} (f : Identity) (R : ℕ) (r : ClockedRecord n) : ClockedRecord n :=
  ⟨parentView f R r.parentBefore,r.action,r.repairMode,r.label,
    parentView f R r.parentAfter,r.child.map (parentView f R),r.expenditure⟩

def storeView {n : ℕ} (f : Identity) (R : ℕ) (s : Store n) : Store n :=
  s.map (Option.map (parentView f R))

@[simp] theorem storeView_length {n : ℕ} (f : Identity) (R : ℕ) (s : Store n) :
    (storeView f R s).length=s.length :=by simp [storeView]

@[simp] theorem lookup_view {n : ℕ} (f : Identity) (R : ℕ) (s : Store n) (j : ℕ) :
    RegisterPopulationHistorySource.lookup (storeView f R s) j=
      (RegisterPopulationHistorySource.lookup s j).map (parentView f R) :=by
  simp only [RegisterPopulationHistorySource.lookup,storeView,List.getElem?_map]
  cases s[j]? with
  | none=>rfl
  | some o=>cases o <;> rfl

private theorem appended_not_root (id : Identity) (k : ℕ) (hk : 0<k) (b : Bool) :
    id++[(k,b)]≠root :=by
  intro h
  cases id with
  | nil=>simp [root] at h;omega
  | cons e es=>
    have hl:=congrArg List.length h
    simp [root] at hl

theorem ownerView_append (f id : Identity) (R k : ℕ) (hk : 0<k) (b : Bool) :
    ownerView f R (id++[(k,b)])=ownerView f R id++[(R+k,b)] :=by
  have hn : (k,b)≠(0,false):=by intro h;have :=congrArg Prod.fst h;omega
  simp [ownerView,List.flatMap_append,hn,shiftEvent]

/-- TRUE literal step covariance, on the positive clock used by an actual
valid serial dispatch. Both newborn clocks remain zero. -/
theorem step_view {n : ℕ} (i : Fin n) (m : Mechanism) (f : Identity) (R : ℕ)
    (o : ClockedOrganism n) (hc : 0<o.clock) (a : Action) (mode label : Bool) :
    recordView f R (RegisterTimestampedBirthSource.step i m o a mode label)=
      RegisterTimestampedBirthSource.step i m (parentView f R o) a mode label :=by
  have hz : o.clock≠0:=Nat.ne_of_gt hc
  have hi:=appended_not_root o.identity o.clock hc label
  have ho:=ownerView_append f o.identity R o.clock hc label
  cases hchild : (modeRecordStep i m o.organism a mode label).transaction.child with
  | none=>
    simp [recordView,parentView,RegisterTimestampedBirthSource.step,hz,hchild,Nat.add_assoc]
  | some child=>
    simp [recordView,parentView,RegisterTimestampedBirthSource.step,hz,hchild,hi,ho,Nat.add_assoc]

/-- Original uniform +R proposal is FALSE whenever there is a real birth and R>0. -/
theorem newborn_rejects_uniform_clock_shift {n : ℕ} (i : Fin n) (m : Mechanism)
    (o other child : ClockedOrganism n) (a : Action) (mode label : Bool)
    (hc : (RegisterTimestampedBirthSource.step i m o a mode label).child=some child)
    (R : ℕ) (hR : 0<R) :
    (RegisterTimestampedBirthSource.step i m other a mode label).child≠
      (RegisterTimestampedBirthSource.step i m o a mode label).child.map
        (fun d=>{d with clock:=R+d.clock}) :=by
  intro h
  rw [hc,Option.map_some] at h
  have hz:=(RegisterTimestampedBirthSource.actual_child_source i m o child a mode label hc).2.2
  have hb:=(RegisterTimestampedBirthSource.actual_child_source i m other _ a mode label h).2.2
  change R+child.clock=0 at hb
  omega

/-- Same physical interpreter, own stored code and request. Only dispatch
metadata uses the explicitly declared population epoch R.
Store.length labels dispatch stages (the founder occupies stage0); newborn
local clocks are zero and stored last-update clocks are separate. This does
not identify these metadata with the old fixed-parent continuous native clock. -/
def transaction {n : ℕ} (i : Fin n) (c : NNReal) (R : ℕ) (s : Store n) (q : Request) :
    Option (ClockedRecord n) :=
  (RegisterPopulationHistorySource.lookup s q.parent).map (fun p=>
    RegisterTimestampedBirthSource.step i (RegisterOwnProgramPopulation.mechanism c s q)
      {p with clock:=R+s.length} q.action q.mode q.label)

def child {n : ℕ} (i : Fin n) (c : NNReal) (R : ℕ) (s : Store n) (q : Request) :=
  (transaction i c R s q).bind ClockedRecord.child

def next {n : ℕ} (i : Fin n) (c : NNReal) (R : ℕ) (s : Store n) (q : Request) : Store n :=
  (match transaction i c R s q with
  | none=>s
  | some r=>s.set q.parent (some r.parentAfter))++[child i c R s q]

private theorem lookup_length_pos {n : ℕ} (s : Store n) (j : ℕ) (p : ClockedOrganism n)
    (hp : RegisterPopulationHistorySource.lookup s j=some p) : 0<s.length :=by
  cases s with
  | nil=>simp [RegisterPopulationHistorySource.lookup] at hp
  | cons a s=>simp

theorem mechanism_view {n : ℕ} (c : NNReal) (f : Identity) (R : ℕ) (s : Store n) (q : Request) :
    RegisterOwnProgramPopulation.mechanism c (storeView f R s) q=
      RegisterOwnProgramPopulation.mechanism c s q :=by
  unfold RegisterOwnProgramPopulation.mechanism
  rw [lookup_view]
  cases RegisterPopulationHistorySource.lookup s q.parent <;> rfl

/-- Literal record fields, child failure, action and fee transport together. -/
theorem transaction_view {n : ℕ} (i : Fin n) (c : NNReal) (f : Identity) (R : ℕ)
    (s : Store n) (q : Request) :
    transaction i c R (storeView f R s) q=
      (RegisterOwnProgramPopulation.transaction i c s q).map (recordView f R) :=by
  unfold transaction RegisterOwnProgramPopulation.transaction RegisterPopulationHistorySource.transaction
  rw [lookup_view,mechanism_view,storeView_length]
  cases hp : RegisterPopulationHistorySource.lookup s q.parent with
  | none=>rfl
  | some p=>
    have hlen:=lookup_length_pos s q.parent p hp
    have hv:=step_view i (RegisterOwnProgramPopulation.mechanism c s q) f R
      {p with clock:=s.length} hlen q.action q.mode q.label
    have hc : parentView f R {p with clock:=s.length}=
        {parentView f R p with clock:=R+s.length} :=by
      simp [parentView,Nat.ne_of_gt hlen]
    simpa only [Option.map_some,hc] using congrArg some hv.symm


theorem child_view {n : ℕ} (i : Fin n) (c : NNReal) (f : Identity) (R : ℕ)
    (s : Store n) (q : Request) :
    child i c R (storeView f R s) q=(RegisterOwnProgramPopulation.child i c s q).map (parentView f R) :=by
  unfold child RegisterOwnProgramPopulation.child RegisterPopulationHistorySource.child
  rw [transaction_view]
  change ((RegisterOwnProgramPopulation.transaction i c s q).map (recordView f R)).bind ClockedRecord.child=
    ((RegisterOwnProgramPopulation.transaction i c s q).bind ClockedRecord.child).map (parentView f R)
  cases RegisterOwnProgramPopulation.transaction i c s q <;> rfl

theorem next_view {n : ℕ} (i : Fin n) (c : NNReal) (f : Identity) (R : ℕ)
    (s : Store n) (q : Request) :
    next i c R (storeView f R s) q=storeView f R (RegisterOwnProgramPopulation.next i c s q) :=by
  change (match transaction i c R (storeView f R s) q with
    | none=>storeView f R s | some r=>(storeView f R s).set q.parent (some r.parentAfter))++
      [child i c R (storeView f R s) q]=
    storeView f R ((match RegisterOwnProgramPopulation.transaction i c s q with
      | none=>s | some r=>s.set q.parent (some r.parentAfter))++[RegisterOwnProgramPopulation.child i c s q])
  rw [transaction_view,child_view]
  cases RegisterOwnProgramPopulation.transaction i c s q with
  | none=>simp [storeView]
  | some r=>simp [storeView,recordView,List.map_set]

def run {n : ℕ} (i : Fin n) (c : NNReal) (R : ℕ) : Store n→List Request→Store n
  | s,[]=>s
  | s,q::es=>run i c R (next i c R s q) es

def trace {n : ℕ} (i : Fin n) (c : NNReal) (R : ℕ) : Store n→List Request→List (Option (ClockedRecord n))
  | _,[]=>[]
  | s,q::es=>transaction i c R s q::trace i c R (next i c R s q) es

theorem run_view {n : ℕ} (i : Fin n) (c : NNReal) (f : Identity) (R : ℕ)
    (s : Store n) (es : List Request) :
    run i c R (storeView f R s) es=storeView f R (RegisterOwnProgramPopulation.run i c s es) :=by
  induction es generalizing s with
  | nil=>rfl
  | cons q es ih=>
    change run i c R (next i c R (storeView f R s) q) es=_
    rw [next_view,ih]
    rfl

theorem trace_view {n : ℕ} (i : Fin n) (c : NNReal) (f : Identity) (R : ℕ)
    (s : Store n) (es : List Request) :
    trace i c R (storeView f R s) es=
      (RegisterActuatorPopulationScale.transactionTrace i c s es).map (Option.map (recordView f R)) :=by
  induction es generalizing s with
  | nil=>rfl
  | cons q es ih=>
    simp only [trace,RegisterActuatorPopulationScale.transactionTrace,List.map_cons]
    rw [transaction_view,next_view,ih]

theorem ast_request_view {n : ℕ} (p : Instruction n)
    (f : Identity) (R : ℕ) (s : Store n) (j : ℕ) (mode label : Bool) :
    astRequest p (storeView f R s) j mode label=astRequest p s j mode label :=by
  unfold astRequest
  rw [lookup_view]
  cases RegisterPopulationHistorySource.lookup s j <;> rfl

/-- Registration starts at THIS true clocked post-probe source parent. -/
theorem actual_registered_postClocked {n N : ℕ} (i : Fin n) (m : Mechanism)
    (omega : RegisterFaultFinitePurposeProbe.Coordinate N→Bool×Bool) (o : ClockedOrganism n) :
    storeView o.identity (o.clock+2*N) (registeredParent i m omega o.organism)=
      [some (RegisterFaultDynamicProbeClocked.postClocked i m omega o)] :=by
  have he : RegisterFaultDynamicProbeClocked.postClocked i m omega o=
      ⟨RegisterFaultFinitePurposeInfinite.postProbeParent i m omega o.organism,o.identity,o.clock+2*N⟩ :=by
    rw [←RegisterFaultDynamicProbeClocked.actual_post_erase i m omega o,
      ←RegisterFaultDynamicProbeClocked.actual_post_identity i m omega o,
      ←RegisterFaultDynamicProbeClocked.actual_post_clock i m omega o]
  rw [he]
  simp [storeView,registeredParent,RegisterPopulationHistorySource.founders,parentView,ownerView,root]


def astEpisode {n : ℕ} (p : Instruction n) (i : Fin n) (c : NNReal) (R : ℕ) :
    Store n→List (ℕ×Bool×Bool)→List Request
  | _,[]=>[]
  | s,(j,mode,label)::es=>
    let q:=astRequest p s j mode label
    q::astEpisode p i c R (next i c R s q) es

theorem ast_episode_view {n : ℕ} (p : Instruction n) (i : Fin n) (c : NNReal)
    (f : Identity) (R : ℕ) (s : Store n) (plan : List (ℕ×Bool×Bool)) :
    astEpisode p i c R (storeView f R s) plan=
      RegisterFaultDynamicProbePopulation.astEpisode p i c s plan :=by
  induction plan generalizing s with
  | nil=>rfl
  | cons q es ih=>
    rcases q with ⟨j,mode,label⟩
    simp only [astEpisode,RegisterFaultDynamicProbePopulation.astEpisode]
    rw [ast_request_view,next_view,ih]

/-- Exact actual UID/parent readouts: None failures are not successful births. -/
def childAt {n : ℕ} (i : Fin n) (c : NNReal) (R : ℕ) (s : Store n)
    (es : List Request) (k : Fin es.length) : Option (ClockedOrganism n) :=
  child i c R (run i c R s (es.take k)) (RegisterPopulationHistorySource.requestAt es k)

def observedChildID {n : ℕ} (i : Fin n) (c : NNReal) (R : ℕ) (s : Store n)
    (es : List Request) (k : Fin es.length) : Option ℕ :=
  (childAt i c R s es k).map (fun _=>s.length+k)

def actualParent {n : ℕ} (i : Fin n) (c : NNReal) (R : ℕ) (s : Store n)
    (es : List Request) (k : Fin es.length) : Option ℕ :=
  (childAt i c R s es k).map (fun _=>(RegisterPopulationHistorySource.requestAt es k).parent)

theorem childAt_view {n : ℕ} (i : Fin n) (c : NNReal) (f : Identity) (R : ℕ)
    (s : Store n) (es : List Request) (k : Fin es.length) :
    childAt i c R (storeView f R s) es k=
      (RegisterOwnProgramPopulation.childAt i c s es k).map (parentView f R) :=by
  simp only [childAt,run_view,child_view,RegisterOwnProgramPopulation.childAt,
    RegisterOwnProgramPopulation.storeBefore]

theorem actual_ID_parent_view {n : ℕ} (i : Fin n) (c : NNReal) (f : Identity) (R : ℕ)
    (s : Store n) (es : List Request) (k : Fin es.length) :
    observedChildID i c R (storeView f R s) es k=RegisterOwnProgramPopulation.observedChildID i c s es k ∧
    actualParent i c R (storeView f R s) es k=RegisterOwnProgramPopulation.actualParent i c s es k :=by
  simp only [observedChildID,actualParent,childAt_view,storeView_length,
    RegisterOwnProgramPopulation.observedChildID,RegisterOwnProgramPopulation.actualParent,Option.map_map]
  constructor <;> rfl

/-- The renamed child is still an ORIGINAL literal P8 offspring, derived from
that same interpreted birth, with a different identity; not a token-only edge. -/
theorem actual_birth_view {n : ℕ} (i : Fin n) (m : Mechanism) (f : Identity) (R : ℕ)
    (o d : ClockedOrganism n) (hk : 0<o.clock) (a : Action) (mode label : Bool)
    (hd : (RegisterTimestampedBirthSource.step i m o a mode label).child=some d) :
    (RegisterTimestampedBirthSource.step i m (parentView f R o) a mode label).child=some (parentView f R d) ∧
      (RegisterTimestampedBirthSource.lineage i m).OffspringOf (parentView f R o) (parentView f R d) :=by
  have h:=congrArg ClockedRecord.child (step_view i m f R o hk a mode label)
  change (RegisterTimestampedBirthSource.step i m o a mode label).child.map (parentView f R)=_ at h
  rw [hd,Option.map_some] at h
  exact ⟨h.symm,RegisterTimestampedBirthSource.actual_child_offspring i m _ _ _ _ _ h.symm⟩

/-- Same computed Batch AST and same entire future3 input, now beginning at the
true registered postClocked source owner. This is a finite serial protocol,
not the old fixed-parent native continuation law. -/
theorem actual_history_episode_view {n N : ℕ} (i : Fin n) (m : Mechanism)
    (price width d u : ℚ) (omega : RegisterFaultFinitePurposeProbe.Coordinate N→Bool×Bool)
    (o : ClockedOrganism n) (w : Fin 3→Bool×Bool) :
    let p:=RegisterFaultDynamicProbe.returnedAST i
      (RegisterFaultDynamicProbe.classify price width d u (RegisterFaultFinitePurposeProbe.sourceData m width omega))
    let R:=o.clock+2*N
    trace i m.writeCost R [some (RegisterFaultDynamicProbeClocked.postClocked i m omega o)]
      (astEpisode p i m.writeCost R [some (RegisterFaultDynamicProbeClocked.postClocked i m omega o)]
        [(0,(w 0).1,(w 0).2),(0,(w 1).1,(w 1).2),(1,(w 2).1,(w 2).2)])=
    (RegisterActuatorPopulationScale.transactionTrace i m.writeCost (registeredParent i m omega o.organism)
      (RegisterFaultDynamicProbeHistoryPrice.requests i m price width d u omega o.organism w)).map
        (Option.map (recordView o.identity R)) :=by
  dsimp only
  rw [←actual_registered_postClocked i m omega o,ast_episode_view,trace_view,
    RegisterFaultDynamicProbeHistoryPrice.requests_actual_ast]


/-- The sole registered root followed by real positive dispatch timestamps. -/
def SerialID (id : Identity) : Prop :=
  ∃suffix : Identity,id=(0,false)::suffix ∧ ∀e∈suffix,0<e.1

def SerialStore {n : ℕ} (s : Store n) : Prop :=
  ∀j p,RegisterPopulationHistorySource.lookup s j=some p→SerialID p.identity

private theorem serial_append (id : Identity) (h : SerialID id) (k : ℕ) (hk : 0<k) (b : Bool) :
    SerialID (id++[(k,b)]) :=by
  rcases h with ⟨suffix,rfl,hs⟩
  refine ⟨suffix++[(k,b)],rfl,?_⟩
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact hs e he
  · have heq : e=(k,b):=List.mem_singleton.mp he
    simpa [heq] using hk

private theorem lookup_bound {n : ℕ} (s : Store n) (j : ℕ) (p : ClockedOrganism n)
    (hp : RegisterPopulationHistorySource.lookup s j=some p) : j<s.length :=by
  by_contra hn
  simp [RegisterPopulationHistorySource.lookup,List.getElem?_eq_none (by omega : s.length≤j)] at hp

theorem serial_single_founder {n : ℕ} (o : Organism n) :
    SerialStore (RegisterPopulationHistorySource.founders [o]) :=by
  intro j p hp
  cases j with
  | zero=>
    simp [RegisterPopulationHistorySource.founders,RegisterPopulationHistorySource.lookup] at hp
    subst p
    exact ⟨[],rfl,by simp⟩
  | succ j=>simp [RegisterPopulationHistorySource.founders,RegisterPopulationHistorySource.lookup] at hp

theorem serial_fixed_child {n : ℕ} (i : Fin n) (m : Mechanism) (s : Store n)
    (hs : SerialStore s) (q : Request) (d : ClockedOrganism n)
    (hd : RegisterPopulationHistorySource.child i m s q=some d) : SerialID d.identity :=by
  unfold RegisterPopulationHistorySource.child RegisterPopulationHistorySource.transaction at hd
  cases hp : RegisterPopulationHistorySource.lookup s q.parent with
  | none=>simp [hp] at hd
  | some p=>
    simp only [hp,Option.map_some,Option.bind_some] at hd
    have hc:=RegisterTimestampedBirthSource.actual_child_source i m {p with clock:=s.length} d q.action q.mode q.label hd
    rw [hc.2.1]
    exact serial_append _ (hs _ _ hp) _ (lookup_length_pos _ _ _ hp) _

theorem serial_fixed_next {n : ℕ} (i : Fin n) (m : Mechanism) (s : Store n)
    (hs : SerialStore s) (q : Request) : SerialStore (RegisterPopulationHistorySource.next i m s q) :=by
  intro j d hd
  have hb:=lookup_bound _ j d hd
  rw [RegisterPopulationHistorySource.next_length] at hb
  by_cases hj : j<s.length
  · by_cases hq : q.parent=j
    · subst j
      cases hp : RegisterPopulationHistorySource.lookup s q.parent with
      | none=>
        rw [(RegisterPopulationHistorySource.invalid_request i m s q hp).2.2] at hd
        simp only [RegisterPopulationHistorySource.lookup,List.getElem?_append_left hj] at hd
        change RegisterPopulationHistorySource.lookup s q.parent=some d at hd
        rw [hp] at hd
        cases hd
      | some p=>
        rw [(RegisterPopulationHistorySource.retained_parent_identity i m s q p hp).1] at hd
        have he:=Option.some.inj hd
        subst d
        change SerialID p.identity
        exact hs _ _ hp
    · rw [RegisterPopulationHistorySource.next_other_slot i m s q j hj hq] at hd
      exact hs _ _ hd
  · have he : j=s.length:=by omega
    subst j
    rw [RegisterPopulationHistorySource.next_new_slot] at hd
    exact serial_fixed_child i m s hs q d hd

theorem serial_fixed_run {n : ℕ} (i : Fin n) (m : Mechanism) (s : Store n)
    (hs : SerialStore s) (es : List Request) : SerialStore (RegisterPopulationHistorySource.run i m s es) :=by
  induction es generalizing s with
  | nil=>exact hs
  | cons q es ih=>exact ih _ (serial_fixed_next i m s hs q)

theorem serial_own_run {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n)
    (hs : SerialStore s) (es : List Request) : SerialStore (RegisterOwnProgramPopulation.run i c s es) :=by
  induction es generalizing s with
  | nil=>exact hs
  | cons q es ih=>exact ih _ (serial_fixed_next i (RegisterOwnProgramPopulation.mechanism c s q) s hs q)

/-- Thus the actual population identities have the intended prefix formula;
this condition is derived by serial_* above, not read by the data selector. -/
theorem ownerView_serial (f : Identity) (R : ℕ) (id : Identity) (hs : SerialID id) :
    ownerView f R id=f++(id.drop 1).map (shiftEvent R) :=by
  rcases hs with ⟨suffix,rfl,hs⟩
  simp only [ownerView,List.flatMap_cons,List.drop_succ_cons,List.drop_zero]
  congr 1
  induction suffix with
  | nil=>rfl
  | cons e es ih=>
    have he : e≠(0,false):=by intro h;have :=hs e (by simp);simp [h] at this
    simp only [List.flatMap_cons,if_neg he,List.singleton_append,List.map_cons]
    exact congrArg (List.cons _) (ih (fun e he=>hs e (by simp [he])))

theorem ownerView_depth (f : Identity) (R : ℕ) (id : Identity) (hs : SerialID id) :
    ((ownerView f R id).length : ℝ)=(id.length : ℝ)+(f.length : ℝ)-1 :=by
  rw [ownerView_serial f R id hs]
  rcases hs with ⟨suffix,rfl,_⟩
  simp
  ring


open UEOT.V3.EvolutionPrice RegisterFaultDynamicProbeHistoryPrice
open scoped BigOperators

def depthOffset (f : Identity) : ℝ := (f.length : ℝ)-1

def viewedParentDepth {n : ℕ} (f : Identity) (R : ℕ) (s : Store n) (j : Fin s.length) : ℝ :=
  ((RegisterPopulationHistorySource.lookup (storeView f R s) j).map
    (fun node=>(node.identity.length : ℝ))).getD 0

/-- Actual new-source cohort child, at the unchanged frozen old address.
It runs the new interpreter, not a declared transformed offspring list. -/
def viewedOffspring {n : ℕ} (i : Fin n) (c : NNReal) (f : Identity) (R : ℕ) (s : Store n)
    (actions : ℕ→Action) (modes labels : ℕ→Bool) (j : Fin s.length) :
    Option (ClockedOrganism n) :=
  child i c R (run i c R (storeView f R s)
    ((RegisterPopulationTypePrice.cohortRequests s actions modes labels).take j))
    (RegisterPopulationTypePrice.request actions modes labels j)

theorem viewedOffspring_actual {n : ℕ} (i : Fin n) (c : NNReal) (f : Identity) (R : ℕ) (s : Store n)
    (actions : ℕ→Action) (modes labels : ℕ→Bool) (j : Fin s.length) :
    viewedOffspring i c f R s actions modes labels j=
      (RegisterOwnProgramPopulation.offspring i c s actions modes labels j).map (parentView f R) :=by
  simp only [viewedOffspring,run_view,child_view,RegisterOwnProgramPopulation.offspring,
    RegisterOwnProgramPopulation.before]

def actualCohortDepth {n : ℕ} (i : Fin n) (m : Mechanism) (f : Identity) (R : ℕ) (s : Store n)
    (actions : ℕ→Action) (modes labels : ℕ→Bool)
    (d : RegisterPopulationTypePrice.Children i m s actions modes labels) : ℝ :=
  ((viewedOffspring i m.writeCost f R s actions modes labels d.val).map
    (fun node=>(node.identity.length : ℝ))).getD 0

theorem actual_cohort_depth_shift {n : ℕ} (i : Fin n) (m : Mechanism) (f : Identity) (R : ℕ)
    (s : Store n) (hs : SerialStore s) (actions : ℕ→Action) (modes labels : ℕ→Bool)
    (d : RegisterPopulationTypePrice.Children i m s actions modes labels) :
    actualCohortDepth i m f R s actions modes labels d=
      childDepth i m s actions modes labels d+depthOffset f :=by
  have hserial : SerialID (RegisterPopulationTypePrice.childObject i m s actions modes labels d).identity :=by
    apply serial_fixed_child i m (RegisterPopulationTypePrice.before i m s actions modes labels d.val)
      (serial_fixed_run i m s hs _) (RegisterPopulationTypePrice.request actions modes labels d.val) _
    exact (Option.some_get d.property).symm
  unfold actualCohortDepth
  rw [viewedOffspring_actual,RegisterOwnProgramPopulation.census_child_actual i m.writeCost s actions modes labels m.goal d]
  simp only [Option.map_some,Option.getD_some,parentView]
  rw [ownerView_depth f R _ hserial]
  unfold childDepth depthOffset
  ring

private theorem weighted_parent_depth_term {n : ℕ} (f : Identity) (R : ℕ) (s : Store n)
    (hs : SerialStore s) (j : Fin s.length) :
    RegisterPopulationTypePrice.frequency s j*viewedParentDepth f R s j=
      RegisterPopulationTypePrice.frequency s j*(parentDepth s j+depthOffset f) :=by
  cases hp : RegisterPopulationHistorySource.lookup s j with
  | none=>simp [viewedParentDepth,parentDepth,lookup_view,hp,RegisterPopulationTypePrice.frequency,
      RegisterPopulationTypePrice.occupied]
  | some p=>
    have hd:=ownerView_depth f R p.identity (hs _ _ hp)
    simp only [viewedParentDepth,lookup_view,hp,Option.map_some,Option.getD_some,parentDepth,parentView]
    rw [hd]
    unfold depthOffset
    ring

private theorem weightedMean_add_const {J : Type*} [Fintype J] (p z : J→ℝ) (C : ℝ)
    (hp : ∑j,p j=1) : weightedMean p (fun j=>z j+C)=weightedMean p z+C :=by
  simp only [weightedMean,mul_add,Finset.sum_add_distrib,←Finset.sum_mul,hp,one_mul]

theorem actual_parent_mean_shift {n : ℕ} (i : Fin n) (m : Mechanism) (f : Identity) (R : ℕ)
    (s : Store n) (hs : SerialStore s) (actions : ℕ→Action) (modes labels : ℕ→Bool)
    (hB : 0<RegisterPopulationTypePrice.birthCount i m s actions modes labels) :
    weightedMean (RegisterPopulationTypePrice.frequency s) (viewedParentDepth f R s)=
      weightedMean (RegisterPopulationTypePrice.frequency s) (parentDepth s)+depthOffset f :=by
  calc
    _=weightedMean (RegisterPopulationTypePrice.frequency s) (fun j=>parentDepth s j+depthOffset f) :=by
      apply Finset.sum_congr rfl
      intro j _
      exact weighted_parent_depth_term f R s hs j
    _=_:=weightedMean_add_const _ _ _ (RegisterPopulationTypePrice.frequency_sum i m s actions modes labels hB)

theorem actual_selection_covariance_same {n : ℕ} (i : Fin n) (m : Mechanism) (f : Identity) (R : ℕ)
    (s : Store n) (hs : SerialStore s) (actions : ℕ→Action) (modes labels : ℕ→Bool)
    (hB : 0<RegisterPopulationTypePrice.birthCount i m s actions modes labels) :
    weightedCov (RegisterPopulationTypePrice.frequency s) (RegisterPopulationTypePrice.fertility i m s actions modes labels)
      (viewedParentDepth f R s)=
    weightedCov (RegisterPopulationTypePrice.frequency s) (RegisterPopulationTypePrice.fertility i m s actions modes labels)
      (parentDepth s) :=by
  let p:=RegisterPopulationTypePrice.frequency s
  let b:=RegisterPopulationTypePrice.fertility i m s actions modes labels
  have ht (j : Fin s.length) : p j*(b j*viewedParentDepth f R s j)=
      p j*(b j*parentDepth s j)+depthOffset f*(p j*b j) :=by
    calc
      _=b j*(p j*viewedParentDepth f R s j) :=by ring
      _=b j*(p j*(parentDepth s j+depthOffset f)) :=by rw [weighted_parent_depth_term f R s hs j]
      _=_:=by ring
  have hm : weightedMean p (fun j=>b j*viewedParentDepth f R s j)=
      weightedMean p (fun j=>b j*parentDepth s j)+depthOffset f*weightedMean p b :=by
    simp only [weightedMean,ht,Finset.sum_add_distrib,Finset.mul_sum]
  unfold weightedCov
  rw [hm,actual_parent_mean_shift i m f R s hs actions modes labels hB]
  ring


def actualViewedMean {n : ℕ} (i : Fin n) (m : Mechanism) (f : Identity) (R : ℕ) (s : Store n)
    (actions : ℕ→Action) (modes labels : ℕ→Bool) : ℝ :=
  ∑d : RegisterPopulationTypePrice.Children i m s actions modes labels,
    (1/(RegisterPopulationTypePrice.birthCount i m s actions modes labels : ℝ))*
      actualCohortDepth i m f R s actions modes labels d

theorem actual_child_mean_shift {n : ℕ} (i : Fin n) (m : Mechanism) (f : Identity) (R : ℕ)
    (s : Store n) (hs : SerialStore s) (actions : ℕ→Action) (modes labels : ℕ→Bool)
    (hB : 0<RegisterPopulationTypePrice.birthCount i m s actions modes labels) :
    actualViewedMean i m f R s actions modes labels=actualMeanDepth i m s actions modes labels+depthOffset f :=by
  have hold : actualMeanDepth i m s actions modes labels=
      ∑d : RegisterPopulationTypePrice.Children i m s actions modes labels,
        (1/(RegisterPopulationTypePrice.birthCount i m s actions modes labels : ℝ))*childDepth i m s actions modes labels d :=by
    unfold actualMeanDepth
    apply Finset.sum_congr rfl
    intro d _
    rw [RegisterOwnProgramPopulation.census_child_actual i m.writeCost s actions modes labels m.goal d]
    rfl
  rw [hold]
  unfold actualViewedMean
  simp_rw [actual_cohort_depth_shift i m f R s hs actions modes labels,mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  change (RegisterPopulationTypePrice.birthCount i m s actions modes labels : ℝ)*
    (1/(RegisterPopulationTypePrice.birthCount i m s actions modes labels : ℝ)*depthOffset f)=depthOffset f
  have hn : (RegisterPopulationTypePrice.birthCount i m s actions modes labels : ℝ)≠0 :=by exact_mod_cast Nat.ne_of_gt hB
  field_simp

theorem actual_price_increment_same {n : ℕ} (i : Fin n) (m : Mechanism) (f : Identity) (R : ℕ)
    (s : Store n) (hs : SerialStore s) (actions : ℕ→Action) (modes labels : ℕ→Bool)
    (hB : 0<RegisterPopulationTypePrice.birthCount i m s actions modes labels) :
    actualViewedMean i m f R s actions modes labels-
      weightedMean (RegisterPopulationTypePrice.frequency s) (viewedParentDepth f R s)=
    actualMeanDepth i m s actions modes labels-
      weightedMean (RegisterPopulationTypePrice.frequency s) (parentDepth s) :=by
  rw [actual_child_mean_shift i m f R s hs actions modes labels hB,
    actual_parent_mean_shift i m f R s hs actions modes labels hB]
  ring

private theorem transmitted_add_const {I J : Type*} [Fintype J]
    (K : I→J→ℝ) (z : J→ℝ) (C : ℝ) (hK : ∀i,∑j,K i j=1) (i : I) :
    transmittedTrait K (fun j=>z j+C) i=transmittedTrait K z i+C :=by
  simp only [transmittedTrait,mul_add,Finset.sum_add_distrib,←Finset.sum_mul,hK,one_mul]

/-- The actual mapped offspring census and mapped parent depth yield the
same REALIZED transmission term; normalized fallback rows are not births. -/
theorem actual_transmission_term_same {n : ℕ} (i : Fin n) (m : Mechanism) (f : Identity) (R : ℕ)
    (s : Store n) (hs : SerialStore s) (actions : ℕ→Action) (modes labels : ℕ→Bool)
    (hB : 0<RegisterPopulationTypePrice.birthCount i m s actions modes labels) :
    weightedMean (RegisterPopulationTypePrice.frequency s)
      (fun j=>RegisterPopulationTypePrice.fertility i m s actions modes labels j *
        (transmittedTrait (RegisterPopulationTypePrice.transmission i m s actions modes labels hB)
          (actualCohortDepth i m f R s actions modes labels) j-viewedParentDepth f R s j)) /
      weightedMean (RegisterPopulationTypePrice.frequency s) (RegisterPopulationTypePrice.fertility i m s actions modes labels)=
    weightedMean (RegisterPopulationTypePrice.frequency s)
      (fun j=>RegisterPopulationTypePrice.fertility i m s actions modes labels j *
        (transmittedTrait (RegisterPopulationTypePrice.transmission i m s actions modes labels hB)
          (childDepth i m s actions modes labels) j-parentDepth s j)) /
      weightedMean (RegisterPopulationTypePrice.frequency s) (RegisterPopulationTypePrice.fertility i m s actions modes labels) :=by
  have hfun : actualCohortDepth i m f R s actions modes labels=
      fun d=>childDepth i m s actions modes labels d+depthOffset f :=
    funext (actual_cohort_depth_shift i m f R s hs actions modes labels)
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : RegisterPopulationTypePrice.born i m s actions modes labels j
  · let d : RegisterPopulationTypePrice.Children i m s actions modes labels:=⟨j,hj⟩
    obtain ⟨p,hp,_⟩:=RegisterPopulationTypePrice.offspring_program i m s actions modes labels j
      (RegisterPopulationTypePrice.childObject i m s actions modes labels d) (Option.some_get d.property).symm
    have hz : viewedParentDepth f R s j=parentDepth s j+depthOffset f :=by
      simp only [viewedParentDepth,lookup_view,parentDepth,hp,Option.map_some,Option.getD_some,parentView]
      rw [ownerView_depth f R _ (hs _ _ hp)]
      unfold depthOffset
      ring
    rw [hfun]
    dsimp only
    rw [transmitted_add_const _ (childDepth i m s actions modes labels) (depthOffset f)
      (RegisterPopulationTypePrice.transmission_sum i m s actions modes labels hB) j,hz]
    ring
  · simp [RegisterPopulationTypePrice.fertility,hj]

/-- Actual registration has the original source's nonzero ancestry increment,
not a new pedigree coefficient. -/
theorem actual_transmission_one {n : ℕ} (i : Fin n) (m : Mechanism) (f : Identity) (R : ℕ)
    (s : Store n) (hs : SerialStore s) (actions : ℕ→Action) (modes labels : ℕ→Bool)
    (hB : 0<RegisterPopulationTypePrice.birthCount i m s actions modes labels) :
    weightedMean (RegisterPopulationTypePrice.frequency s)
      (fun j=>RegisterPopulationTypePrice.fertility i m s actions modes labels j *
        (transmittedTrait (RegisterPopulationTypePrice.transmission i m s actions modes labels hB)
          (actualCohortDepth i m f R s actions modes labels) j-viewedParentDepth f R s j)) /
      weightedMean (RegisterPopulationTypePrice.frequency s) (RegisterPopulationTypePrice.fertility i m s actions modes labels)=1 :=by
  rw [actual_transmission_term_same i m f R s hs actions modes labels hB]
  exact actual_history_transmission_one i m s actions modes labels hB


/-- Complete physical/program/history/action/mode/label/birth/fee erasure,
including the child's real zero clock behind the view, is unchanged. -/
theorem record_erasure_view {n : ℕ} (f : Identity) (R : ℕ) (r : ClockedRecord n) :
    RegisterTimestampedBirthSource.eraseRecord (recordView f R r)=RegisterTimestampedBirthSource.eraseRecord r :=by
  simp [RegisterTimestampedBirthSource.eraseRecord,recordView,parentView,Option.map_map]
  rfl

theorem actual_fees_view {n : ℕ} (i : Fin n) (c : NNReal) (f : Identity) (R : ℕ)
    (s : Store n) (es : List Request) :
    (trace i c R (storeView f R s) es).map (fun r=>r.map (fun r=>r.expenditure))=
      (RegisterActuatorPopulationScale.transactionTrace i c s es).map (fun r=>r.map (fun r=>r.expenditure)) :=by
  rw [trace_view,List.map_map]
  congr 1
  funext r
  cases r <;> rfl

open MeasureTheory ProbabilityTheory
local instance {n : ℕ} : MeasurableSpace (List (Option (ClockedRecord n))) :=⊤

/-- Exactly the original complete training×future3 source, with no acceptance
conditioning and no parent/newborn filtering. Registration is a source view. -/
def experimentRecords {n N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (price width d u : ℚ) (o : ClockedOrganism n) :
    Measure (List (Option (ClockedRecord n))) :=
  (RegisterFaultDynamicProbeHistoryPrice.experimentLaw noise epsilon he N).map (fun z=>
    let p:=RegisterFaultDynamicProbe.returnedAST i
      (RegisterFaultDynamicProbe.classify price width d u (RegisterFaultFinitePurposeProbe.sourceData m width z.1))
    let R:=o.clock+2*N
    let s:=[some (RegisterFaultDynamicProbeClocked.postClocked i m z.1 o)]
    trace i m.writeCost R s (astEpisode p i m.writeCost R s
      [(0,(z.2 0).1,(z.2 0).2),(0,(z.2 1).1,(z.2 1).2),(1,(z.2 2).1,(z.2 2).2)]))

instance experimentRecords_probability {n N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (price width d u : ℚ) (o : ClockedOrganism n) :
    IsProbabilityMeasure (experimentRecords (N:=N) i noise m epsilon he price width d u o) :=
  Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable

/-- Full finite journal law transport, not merely equality of marginals. -/
theorem actual_experiment_records_view {n N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (price width d u : ℚ) (o : ClockedOrganism n) :
    experimentRecords (N:=N) i noise m epsilon he price width d u o=
      (RegisterFaultDynamicProbeHistoryPrice.experimentRecords (N:=N) i noise m epsilon he price width d u o.organism).map
        (fun rs=>rs.map (Option.map (recordView o.identity (o.clock+2*N)))) :=by
  have hm : Measurable (fun rs : List (Option (ClockedRecord n))=>
      rs.map (Option.map (recordView o.identity (o.clock+2*N)))) :=fun _ _=>trivial
  unfold experimentRecords
  rw [RegisterFaultDynamicProbeHistoryPrice.experimentRecords,Measure.map_map hm (measurable_of_finite _)]
  congr 1
  funext z
  exact actual_history_episode_view i m price width d u z.1 o z.2


/-- The unchanged address incidence really counts this new interpreter's
births, including zero-birth branches; no positive B is an input here. -/
theorem actual_cohort_born_same {n : ℕ} (i : Fin n) (m : Mechanism) (f : Identity) (R : ℕ)
    (s : Store n) (actions : ℕ→Action) (modes labels : ℕ→Bool) (j : Fin s.length) :
    (viewedOffspring i m.writeCost f R s actions modes labels j).isSome=
      (RegisterPopulationTypePrice.offspring i m s actions modes labels j).isSome :=by
  rw [viewedOffspring_actual,RegisterOwnProgramPopulation.offspring_eq_old i m.writeCost s actions modes labels m.goal j]
  cases RegisterPopulationTypePrice.offspring i m s actions modes labels j <;> rfl

theorem actual_cohort_count_same {n : ℕ} (i : Fin n) (m : Mechanism) (f : Identity) (R : ℕ)
    (s : Store n) (actions : ℕ→Action) (modes labels : ℕ→Bool) :
    (Finset.univ.filter (fun j : Fin s.length=>
      (viewedOffspring i m.writeCost f R s actions modes labels j).isSome)).card=
        RegisterPopulationTypePrice.birthCount i m s actions modes labels :=by
  unfold RegisterPopulationTypePrice.birthCount
  rw [Fintype.card_subtype]
  simp only [actual_cohort_born_same,RegisterPopulationTypePrice.born]
  rfl

/-- ORIGINAL Core Price through the existing actual-history caller, now for
this registered source's actual offspring census and parent history depth. -/
theorem actual_registered_price {n : ℕ} (i : Fin n) (m : Mechanism) (f : Identity) (R : ℕ)
    (s : Store n) (hs : SerialStore s) (actions : ℕ→Action) (modes labels : ℕ→Bool)
    (hB : 0<RegisterPopulationTypePrice.birthCount i m s actions modes labels) :
    actualViewedMean i m f R s actions modes labels-
      weightedMean (RegisterPopulationTypePrice.frequency s) (viewedParentDepth f R s)=
    weightedCov (RegisterPopulationTypePrice.frequency s) (RegisterPopulationTypePrice.fertility i m s actions modes labels)
      (viewedParentDepth f R s) /
      weightedMean (RegisterPopulationTypePrice.frequency s) (RegisterPopulationTypePrice.fertility i m s actions modes labels)+
    weightedMean (RegisterPopulationTypePrice.frequency s)
      (fun j=>RegisterPopulationTypePrice.fertility i m s actions modes labels j *
        (transmittedTrait (RegisterPopulationTypePrice.transmission i m s actions modes labels hB)
          (actualCohortDepth i m f R s actions modes labels) j-viewedParentDepth f R s j)) /
      weightedMean (RegisterPopulationTypePrice.frequency s) (RegisterPopulationTypePrice.fertility i m s actions modes labels) :=by
  rw [actual_price_increment_same i m f R s hs actions modes labels hB,
    actual_selection_covariance_same i m f R s hs actions modes labels hB,
    actual_transmission_term_same i m f R s hs actions modes labels hB]
  exact actual_history_price i m s actions modes labels hB

/-- P8 is consumed on the actual dispatch parent, and every actual child has
its own genuine zero clock. This is not a fixed-parent native path assertion. -/
theorem actual_birth_source {n : ℕ} (i : Fin n) (c : NNReal) (R : ℕ) (s : Store n)
    (q : Request) (d : ClockedOrganism n) (hd : child i c R s q=some d) :
    ∃p : ClockedOrganism n,RegisterPopulationHistorySource.lookup s q.parent=some p ∧
      (RegisterTimestampedBirthSource.lineage i (RegisterOwnProgramPopulation.mechanism c s q)).OffspringOf
        {p with clock:=R+s.length} d ∧ d.clock=0 :=by
  unfold child transaction at hd
  cases hp : RegisterPopulationHistorySource.lookup s q.parent with
  | none=>simp [hp] at hd
  | some p=>
    simp only [hp,Option.map_some,Option.bind_some] at hd
    exact ⟨p,rfl,RegisterTimestampedBirthSource.actual_child_offspring i _ _ _ _ _ _ hd,
      (RegisterTimestampedBirthSource.actual_child_source i _ _ _ _ _ _ hd).2.2⟩


/-- No two reachable serial identities are collapsed by the registered owner
prefix. The sole dropped marker is known from real registration, not Batch. -/
theorem ownerView_injective_serial (f : Identity) (R : ℕ) (x y : Identity)
    (hx : SerialID x) (hy : SerialID y) (h : ownerView f R x=ownerView f R y) : x=y :=by
  rw [ownerView_serial f R x hx,ownerView_serial f R y hy] at h
  have hm:=List.append_cancel_left h
  have hinj : Function.Injective (shiftEvent R) :=by
    intro a b h
    have h1 : R+a.1=R+b.1:=by simpa only [shiftEvent] using congrArg (fun e : ℕ×Bool=>e.1) h
    have h2 : a.2=b.2:=by simpa only [shiftEvent] using congrArg (fun e : ℕ×Bool=>e.2) h
    exact Prod.ext (Nat.add_left_cancel h1) h2
  have hd:=List.map_injective_iff.mpr hinj hm
  rcases hx with ⟨sx,rfl,_⟩
  rcases hy with ⟨sy,rfl,_⟩
  simpa using congrArg (List.cons (0,false)) hd

/-- SAME-object comparison for actual serial identities is preserved AND
reflected; it is not inferred from physical or program equality. -/
theorem sameObject_view_iff {n : ℕ} (i : Fin n) (m : Mechanism) (f : Identity) (R : ℕ)
    (x y : ClockedOrganism n) (hx : SerialID x.identity) (hy : SerialID y.identity) :
    (RegisterTimestampedBirthSource.lineage i m).SameObject (parentView f R x) (parentView f R y)↔
      (RegisterTimestampedBirthSource.lineage i m).SameObject x y :=by
  change ownerView f R x.identity=ownerView f R y.identity ↔ x.identity=y.identity
  exact ⟨ownerView_injective_serial f R _ _ hx hy,congrArg (ownerView f R)⟩

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterPopulationOwnerClockTransport
