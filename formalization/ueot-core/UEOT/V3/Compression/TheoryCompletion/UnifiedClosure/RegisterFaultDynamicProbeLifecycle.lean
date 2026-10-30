import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicProbeResource
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterInstructionHomeostasis

/-!
Original promise: learned repair, retained-parent identity and resources concern the SAME source parent.
Existing facts: original dynamic Batch returns an actual p/q pair and funds its complete training/deployment records.
Reduced premises: derive that computed repair AST's actual restoration/homeostasis, and the actual post-parent's P5 carrier/P12 identity bridge.
Models: arbitrary register count, target, actual history and complete probe word; accepted repair differs from accepted idle, and Batch alone cannot identify parent history.
Consumers: actual p/q source homeostasis/P9, original P12 maintained-parent endpoint, and unchanged funded joint-law pipeline.

No physical reset, program installation, transaction, new observation or sample
is added. The P5 organizational clock is NOT identified with literal one-tick
instruction execution; literal p/q homeostasis uses its original source. The
original finite-individual normalized strict reproductive interface cannot hold
for actual append histories (no_finite_normalized_strict_birth); it is not
instantiated by a fake finite cyclic lineage here.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicProbeLifecycle
open MeasureTheory ProbabilityTheory Set Filter Topology
open UEOT.V3.Compression.TheoryCompletion UEOT.V3.Compression.Objecthood
open UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
open UEOT.V3.Compression.Objecthood.JointHomeostasis
open UEOT.V3.Compression.Objecthood.OntogeneticConstruction UEOT.V3.ViabilityKernel
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose
open RegisterFaultJointRecord RegisterFaultFinitePurposeProbe RegisterFaultFinitePurposeInfinite
open RegisterFaultDynamicProbe RegisterFaultDynamicProbeInfinite RegisterFaultSource
open RegisterInstructionRecoveryScale RegisterInstructionHomeostasis
open RegisterSemanticInstructionScale RegisterActuatorScaleSource
noncomputable section

/-- Every actual probe preserves the retained parent's identity, including
faults and failed births. Child history is not continuing-parent history. -/
@[simp] theorem postProbeParent_history {n N : ℕ} (i : Fin n) (m : Mechanism)
    (omega : Coordinate N → Bool × Bool) (o : Organism n) :
    (postProbeParent i m omega o).history=o.history := by
  have h (js : List (Coordinate N)) (parent : Organism n) :
      (js.foldl (fun p j =>
        (modeRecordStep i m p (some j.1) (omega j).1 (omega j).2).transaction.parentAfter) parent).history=parent.history := by
    induction js generalizing parent with
    | nil => rfl
    | cons j js ih => exact (ih _).trans (step_history i m parent _ _ _)
  exact h _ _

/-- The SAME original batch cannot distinguish actual parent histories. This
is independent of raw word, sample size, noise, or threshold choices. -/
theorem no_batch_decoder_of_distinct_parent_histories {n N : ℕ} (i : Fin n)
    (m : Mechanism) (width : ℚ) (omega : Coordinate N → Bool × Bool)
    (o₁ o₂ : Organism n) (hh : o₁.history ≠ o₂.history) :
    ¬ ∃ decode : Batch N → List Bool,
      decode (sourceData m width omega)=(postProbeParent i m omega o₁).history ∧
      decode (sourceData m width omega)=(postProbeParent i m omega o₂).history := by
  simp only [postProbeParent_history]
  rintro ⟨decode,h₁,h₂⟩
  exact hh (h₁.symm.trans h₂)

/-- Probability-level source obstruction: even almost-sure perfect recovery
for BOTH actual histories is impossible under their identical full batch law.
The complete original raw distribution is retained, not one selected word. -/
theorem no_batch_ae_decoder_of_distinct_parent_histories {n : ℕ} (N : ℕ) (i : Fin n)
    (noise : PMF Bool) (m : Mechanism) (epsilon : NNReal) (he : epsilon≤1)
    (width : ℚ) (o₁ o₂ : Organism n) (hh : o₁.history ≠ o₂.history) :
    ¬ ∃ decode : Batch N → List Bool,
      (∀ᵐ omega ∂rawLaw noise epsilon he N,
        decode (sourceData m width omega)=(postProbeParent i m omega o₁).history) ∧
      (∀ᵐ omega ∂rawLaw noise epsilon he N,
        decode (sourceData m width omega)=(postProbeParent i m omega o₂).history) := by
  rintro ⟨decode,h₁,h₂⟩
  obtain ⟨omega,ha,hb⟩ := (h₁.and h₂).exists
  exact no_batch_decoder_of_distinct_parent_histories i m width omega o₁ o₂ hh ⟨decode,ha,hb⟩

/-- Quantitative version on the ENTIRE registered raw source. A batch-only
parent estimator has error sum at least one for two distinct initial histories;
in particular the original small purpose-risk budget cannot be silently reused
as a uniform parent-discovery guarantee. -/
theorem batch_parent_error_sum_ge_one {n : ℕ} (N : ℕ) (i : Fin n)
    (noise : PMF Bool) (m : Mechanism) (epsilon : NNReal) (he : epsilon≤1)
    (width : ℚ) (o₁ o₂ : Organism n) (hh : o₁.history ≠ o₂.history)
    (decode : Batch N → List Bool) :
    1 ≤ (rawLaw noise epsilon he N).real
        {omega | decode (sourceData m width omega)≠(postProbeParent i m omega o₁).history} +
      (rawLaw noise epsilon he N).real
        {omega | decode (sourceData m width omega)≠(postProbeParent i m omega o₂).history} := by
  simp only [postProbeParent_history]
  have hcover : {omega | decode (sourceData m width omega)≠o₁.history} ∪
      {omega | decode (sourceData m width omega)≠o₂.history}=Set.univ := by
    ext omega
    simp only [Set.mem_union,Set.mem_ofPred_eq,Set.mem_univ,iff_true]
    by_contra h
    simp only [not_or,not_not] at h
    exact hh (h.1.symm.trans h.2)
  have h:=(measureReal_union_le (μ:=rawLaw noise epsilon he N)
    {omega | decode (sourceData m width omega)≠o₁.history}
    {omega | decode (sourceData m width omega)≠o₂.history})
  rwa [hcover,probReal_univ] at h

/-- A real positive birth identifies the returned repair bit. Calibration is
needed for optimality, not for this mechanism-level provenance equality. -/
theorem accepted_repair_bit {N : ℕ} (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N → Bool × Bool) (b : Bool)
    (hs : classify price width d u (sourceData m width omega)=.repair b) : b=m.goal := by
  cases hx : firstBirth (sourceData m width omega) (registration N) with
  | none => simp [classify,hx] at hs
  | some q =>
    rcases q with ⟨g,k⟩
    have hi:=first_birth_source m width omega _ g k hx
    simp only [classify,hx] at hs
    split_ifs at hs with h₁ h₂
    · exact (Verdict.repair.inj hs).symm.trans hi.1

/-- THIS computed AST restores the actual source target from every state. -/
theorem accepted_repair_restores {n N : ℕ} (i : Fin n) (m : Mechanism)
    (price width d u : ℚ) (omega : Coordinate N → Bool × Bool) (b : Bool)
    (hs : classify price width d u (sourceData m width omega)=.repair b) :
    restorationCheck i m.goal (returnedAST i (classify price width d u (sourceData m width omega)))=true := by
  rw [hs,returnedAST,accepted_repair_bit m price width d u omega b hs]
  apply (restorationCheck_iff _ _ _).mpr
  intro x
  by_cases hx : x i=m.goal <;> simp [compile,interpret,hx,update]

/-- Actual native p/q quantitative homeostasis, starting at the literal final
probe parent, including a damaged final parent. No optimizer premise substitutes
for repairability. Accepted idle deliberately has no such assertion. -/
theorem accepted_repair_actual_homeostasis {n N : ℕ} (i : Fin n) (noise : PMF Bool)
    (m : Mechanism) (epsilon : NNReal) (he : epsilon≤1) (price width d u : ℚ)
    (omega : Coordinate N → Bool × Bool) (o : Organism n) (ho : o.program=m.goal)
    (b : Bool) (hs : classify price width d u (sourceData m width omega)=.repair b) :
    let parent:=postProbeParent i m omega o
    let p:=returnedAST i (classify price width d u (sourceData m width omega))
    let q:=returnedProgram i p
    QuantitativeHomeostasis i m.goal m.writeCost parent noise epsilon he p ∧
    QuantitativeHomeostasis (0 : Fin 1) m.goal m.writeCost (projectOrganism i parent) noise epsilon he q := by
  have hp:=(postProbeParent_program i m omega o).trans ho
  have hc:=accepted_repair_restores i m price width d u omega b hs
  have hsyn:=returned_synthesis i (classify price width d u (sourceData m width omega))
  exact ⟨actual_quantitative_homeostasis i m.goal m.writeCost _ hc _ hp noise epsilon he,
    p9_actual_returned_homeostasis i m.goal m.writeCost ⟨⟨(_, _),hsyn⟩,hc⟩ _ hp noise epsilon he⟩

/-- Honest negative branch: a data-accepted idle program may be GOD, but it
cannot restore the original target from arbitrary damage. No fault threshold
or cost is modified to turn that optimality result into a repair theorem. -/
theorem accepted_idle_not_restoring {n N : ℕ} (i : Fin n) (m : Mechanism)
    (price width d u : ℚ) (omega : Coordinate N→Bool×Bool) (b : Bool)
    (hs : classify price width d u (sourceData m width omega)=.idle b) :
    restorationCheck i m.goal (returnedAST i (classify price width d u (sourceData m width omega)))=false := by
  rw [hs,returnedAST]
  exact (idle_valid_not_restoring i m.goal).2

section LiteralParent
open UEOT.V3.FiniteDiscountedControl
open RegisterFaultInfiniteRecord RegisterInstructionPurposeScale RegisterFaultDynamicProbeResource
open UEOT.V3.Compression.Objecthood.ResourceClosure
local instance {n : ℕ} : MeasurableSpace (ModeRecord n) := ⊤
local instance {n : ℕ} : MeasurableSingletonClass (ModeRecord n) := ⟨fun _=>trivial⟩

/-- Both endpoints of every retained-parent transaction have this identity. -/
def SameParentTrace {n : ℕ} (history : List Bool) : Set (ℕ→ModeRecord n) :=
  {rs | ∀t,(rs t).transaction.parentBefore.history=history ∧
    (rs t).transaction.parentAfter.history=history}

private theorem measurable_sameParentTrace {n : ℕ} (history : List Bool) :
    MeasurableSet (SameParentTrace (n:=n) history) := by
  have heq : SameParentTrace (n:=n) history=⋂t : ℕ,{rs | (rs t).transaction.parentBefore.history=history ∧
      (rs t).transaction.parentAfter.history=history}:=by ext rs;simp [SameParentTrace]
  rw [heq]
  exact MeasurableSet.iInter fun t=>(show MeasurableSet {r : ModeRecord n |
    r.transaction.parentBefore.history=history ∧ r.transaction.parentAfter.history=history} from trivial).preimage
      (measurable_pi_apply t)

private theorem step_before_history {n : ℕ} (i : Fin n) (m : Mechanism)
    (o : Organism n) (a : Action) (mode label : Bool) :
    (modeRecordStep i m o a mode label).transaction.parentBefore.history=o.history := by
  cases mode <;> rfl

private theorem run_history {n : ℕ} (i : Fin n) (m : Mechanism)
    (pi : CausalPolicy.{0,0,0} (State n) (fun _=>Action)) (c : Config pi) (es : List Event) :
    (run i m pi c es).2.2.history=c.2.2.history := by
  induction es generalizing c with
  | nil=>rfl
  | cons e es ih=>exact (ih (advance i m pi c e)).trans (step_history i m c.2.2 _ _ _)

private theorem native_same_parent {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (pi : CausalPolicy.{0,0,0} (State n) (fun _=>Action)) (c : Config pi) :
    ∀ᵐ rs ∂(RegisterFaultInfiniteRecord.recordPathLaw i noise m epsilon he pi c),rs∈SameParentTrace c.2.2.history := by
  change ∀ᵐ rs ∂(wordPathLaw i noise m epsilon he pi c).map (fun z k=>RegisterFaultInfiniteRecord.recordAt i m pi c z k),_
  apply (ae_map_iff (measurable_recordStream i m pi c).aemeasurable (measurable_sameParentTrace _)).mpr
  apply ae_of_all
  intro z t
  exact ⟨(step_before_history i m _ _ _ _).trans (run_history i m pi c (z t)),
    (step_history i m _ _ _ _).trans (run_history i m pi c (z t))⟩

private theorem training_same_parent {n N : ℕ} (i : Fin n) (m : Mechanism)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (js : List (Coordinate N))
    (r : ModeRecord n) (hr : r∈probeTrace i m omega o js) :
    r.transaction.parentBefore.history=o.history ∧ r.transaction.parentAfter.history=o.history := by
  induction js generalizing o with
  | nil=>simp [probeTrace] at hr
  | cons j js ih=>
    simp only [probeTrace,List.mem_cons] at hr
    rcases hr with heq | hr
    · subst r;exact ⟨step_before_history i m o _ _ _,step_history i m o _ _ _⟩
    · have h:=ih _ hr
      simpa only [step_history] using h

private theorem prepend_same_parent {n : ℕ} (history : List Bool) (pre : List (ModeRecord n)) (rs : ℕ→ModeRecord n)
    (hp : ∀r∈pre,r.transaction.parentBefore.history=history ∧ r.transaction.parentAfter.history=history)
    (hf : rs∈SameParentTrace history) : RegisterFaultFundedProbe.prepend pre rs∈SameParentTrace history := by
  induction pre with
  | nil=>exact hf
  | cons r pre ih=>
    intro t
    cases t with
    | zero=>exact hp r (by simp)
    | succ t=>exact ih (fun r hr=>hp r (by simp [hr])) t

/-- SAME original joint law: ALL registered training and actual infinite
returned-policy records retain the same parent, including faults/UNKNOWN. This
is native source identity, not inferred from an observed posterior or margin. -/
theorem actual_joint_same_parent {n N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (price width d u : ℚ) (o : Organism n) :
    ∀ᵐ p ∂jointLaw (N:=N) i noise m epsilon he price width d u o,
      wholeRecords i m o p∈SameParentTrace o.history := by
  apply Measure.ae_compProd_of_ae_ae ((measurable_sameParentTrace _).preimage (measurable_wholeRecords i m o))
  apply ae_of_all
  intro omega
  have hf:=native_same_parent i noise m epsilon he
    (astPolicy (returnedAST i (classify price width d u (sourceData m width omega))))
    ⟨0,(postProbeParent i m omega o).physical,postProbeParent i m omega o⟩
  simp only [postProbeParent_history] at hf
  filter_upwards [hf] with rs hrs
  exact prepend_same_parent _ _ _ (fun r hr=>training_same_parent i m omega o _ r hr) hrs

/-- Common original source consumer: both actual endpoints of every paid or
failed transaction are the same parent AND this exact complete trace is P6
viable/prepay funded. No selected-success event is used. -/
theorem funded_joint_same_parent {n N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (price width d u : ℚ) (o : Organism n)
    (cap g initial : ℝ) (hcap : (m.writeCost : ℝ)≤cap) (hg : cap≤g) (hi : 0 ≤ initial) :
    ∀ᵐ p ∂jointLaw (N:=N) i noise m epsilon he price width d u o,
      wholeRecords i m o p∈SameParentTrace o.history ∧
      ResourceViable initial (fun _=>g) (fun t=>(wholeRecords i m o p t).transaction.expenditure) ∧
      ∀t,(wholeRecords i m o p t).transaction.expenditure≤balance i m o initial g p t+g := by
  filter_upwards [actual_joint_same_parent i noise m epsilon he price width d u o,
    actual_joint_prepay_funded i noise m epsilon he price width d u o cap g initial hcap hg hi] with p hparent hfund
  exact ⟨hparent,hfund⟩
end LiteralParent

section ParentCarrier
variable {n : ℕ} [MeasurableSpace (State n)] [MeasurableSingletonClass (State n)]
local instance : Fintype (RepairOrganizationState (State n) Action Bool) := repairOrganizationStateFintype
local instance : MeasurableSpace (RepairOrganizationState (State n) Action Bool) := ⊤
local instance : MeasurableSingletonClass (RepairOrganizationState (State n) Action Bool) := ⟨fun _=>trivial⟩

/-- Registered identity plus organizational physical/program coordinates. -/
def parentView (history : List Bool) (s : RepairOrganizationState (State n) Action Bool) : Organism n :=
  ⟨history,s.physical,s.repairProgram⟩

/-- Consume the original P12 maintained-parent endpoint. Recoverable-carrier
entry holds even if the actual final probe damaged the parent. No target/reset
premise is supplied. The explicit P5 view is not a literal-record law equality. -/
theorem actual_post_parent_p12_carrier (i : Fin n) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) {N : ℕ}
    (omega : Coordinate N → Bool × Bool) (o : Organism n) (ho : o.program=m.goal) :
    let parent:=postProbeParent i m omega o
    let seed : OntogeneticSeed (State n) Bool:=⟨parent.physical,m.goal⟩
    let initial:=PMF.pure (assembleRepairOrganization (substrate i) codec seed)
    let S:=finiteJointRecurrentHomeostasisSystem
      (physical i) (target i m.goal) (target_fixed i m.goal) (certificate i m.goal)
      (substrate i) codec m.goal (compiled_dynamics_implements i m.goal)
      (fault i) epsilon he (actual_fault_envelope i m.goal)
    parentView o.history (assembleRepairOrganization (substrate i) codec seed)=parent ∧
    StaysIn initial S.carrier ∧
    ∀ k s, s ∈ (homeostaticMarginal S.mixedKernel initial k).support →
      (lineage i).SameObject (parentView o.history s) parent := by
  dsimp only
  have hp:=(postProbeParent_program i m omega o).trans ho
  have hstay : StaysIn
      (PMF.pure (assembleRepairOrganization (substrate i) codec
        (⟨(postProbeParent i m omega o).physical,m.goal⟩ : OntogeneticSeed (State n) Bool)))
      (finiteJointRepairCarrier (physical i) (target i m.goal) (certificate i m.goal)
        (substrate i) codec m.goal) := by
    intro s hs
    have heq : s=assembleRepairOrganization (substrate i) codec
        (⟨(postProbeParent i m omega o).physical,m.goal⟩ : OntogeneticSeed (State n) Bool) := by simpa using hs
    rw [heq]
    apply (carrier_iff_program i m.goal _).mpr
    rfl
  refine ⟨?_,hstay,?_⟩
  · cases hp' : postProbeParent i m omega o with
    | mk hist x prog =>
      have hh : hist=o.history:=by simpa [hp'] using postProbeParent_history i m omega o
      have hb : prog=m.goal:=by simpa [hp'] using hp
      simp [parentView,assembleRepairOrganization,canonicalRepairOrganizationState,RegisterFaultSource.codec,hh,hb]
  · apply homeostaticMarginals_preserve_lifecycleParent (lineage i)
      (parentView o.history) (postProbeParent i m omega o) _ _ hstay
    intro s hs
    change o.history=(postProbeParent i m omega o).history
    exact (postProbeParent_history i m omega o).symm
end ParentCarrier
end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicProbeLifecycle
