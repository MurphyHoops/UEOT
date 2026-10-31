import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicProbeNativeHomeostasis
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterActuatorPopulationScale

/-!
Actual source identity for the P9 common consumer: run the EXISTING timestamp
interpreter on the SAME complete probe events and native continuation words.
The founder identity/start clock are the existing timestamp protocol's explicit
source coordinates, never read or reconstructed by the old Batch selector.
Erasure proves the original probe/native laws, fees, failures and parent unchanged.
No new population dispatch, owner allocation, observation, reset or P5 clock.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicProbeClocked
open MeasureTheory ProbabilityTheory
open UEOT.V3.FiniteDiscountedControl
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultJointRecord
open RegisterFaultInfiniteRecord RegisterFaultFinitePurposeProbe RegisterFaultFinitePurposeInfinite
open RegisterInstructionScaleSource RegisterInstructionPurposeScale
open RegisterTimestampedBirthSource (ClockedOrganism ClockedRecord Identity)
open scoped ENNReal
noncomputable section
local instance {n : ℕ} : MeasurableSpace (ClockedRecord n):=⊤
local instance {n : ℕ} : MeasurableSpace (ModeRecord n):=⊤

/-- Exactly the original registered literal write probes, including faults. -/
def probeEvents {N : ℕ} (omega : Coordinate N→Bool×Bool) (js : List (Coordinate N)) : List Event:=
  js.map (fun j=>(some j.1,(omega j).1,(omega j).2))

def postClocked {n N : ℕ} (i : Fin n) (m : Mechanism) (omega : Coordinate N→Bool×Bool)
    (o : ClockedOrganism n) : ClockedOrganism n:=
  RegisterTimestampedBirthSource.runParent i m o (probeEvents omega (registration N))

theorem actual_probe_trace_erase {n N : ℕ} (i : Fin n) (m : Mechanism) (omega : Coordinate N→Bool×Bool)
    (o : ClockedOrganism n) (js : List (Coordinate N)) :
    (RegisterTimestampedBirthSource.trace i m o (probeEvents omega js)).map RegisterTimestampedBirthSource.eraseRecord=
      probeTrace i m omega o.organism js :=by
  induction js generalizing o with
  | nil=>rfl
  | cons j js ih=>
    simp only [probeEvents,List.map_cons,RegisterTimestampedBirthSource.trace,List.map_cons,
      RegisterTimestampedBirthSource.step_erase,probeTrace]
    congr 1
    exact ih _

theorem actual_post_erase {n N : ℕ} (i : Fin n) (m : Mechanism) (omega : Coordinate N→Bool×Bool)
    (o : ClockedOrganism n) : (postClocked i m omega o).organism=postProbeParent i m omega o.organism :=by
  have h (js : List (Coordinate N)) (o : ClockedOrganism n) :
      (RegisterTimestampedBirthSource.runParent i m o (probeEvents omega js)).organism=
        js.foldl (fun p j=>(modeRecordStep i m p (some j.1) (omega j).1 (omega j).2).transaction.parentAfter) o.organism :=by
    induction js generalizing o with
    | nil=>rfl
    | cons j js ih=>exact ih _
  exact h _ _

theorem actual_post_identity {n N : ℕ} (i : Fin n) (m : Mechanism) (omega : Coordinate N→Bool×Bool)
    (o : ClockedOrganism n) : (postClocked i m omega o).identity=o.identity :=
  RegisterTimestampedBirthSource.runParent_identity i m o _

theorem actual_post_clock {n N : ℕ} (i : Fin n) (m : Mechanism) (omega : Coordinate N→Bool×Bool)
    (o : ClockedOrganism n) : (postClocked i m omega o).clock=o.clock+2*N :=by
  rw [postClocked,RegisterTimestampedBirthSource.runParent_clock]
  simp [probeEvents,registration,List.length_finRange,two_mul]

private theorem run_erases {n : ℕ} (i : Fin n) (m : Mechanism)
    (pi : CausalPolicy.{0,0,0} (State n) (fun _=>Action)) (c : Config pi) (o : ClockedOrganism n)
    (ho : o.organism=c.2.2) (es : List Event) :
    (RegisterTimestampedBirthSource.runParent i m o es).organism=(run i m pi c es).2.2 :=by
  induction es generalizing c o with
  | nil=>exact ho
  | cons e es ih=>
    apply ih
    simpa only [RegisterTimestampedBirthSource.step_parent_organism,advance] using
      congrArg (fun parent=>(modeRecordStep i m parent e.1 e.2.1 e.2.2).transaction.parentAfter) ho

/-- The original native word law supplies every real action/mode/label. -/
def recordAt {n : ℕ} (i : Fin n) (m : Mechanism) (o : ClockedOrganism n)
    (z : ℕ→List Event) (t : ℕ) : ClockedRecord n:=
  let e:=eventAt z t
  RegisterTimestampedBirthSource.step i m (RegisterTimestampedBirthSource.runParent i m o (z t)) e.1 e.2.1 e.2.2

theorem actual_record_erases {n : ℕ} (i : Fin n) (m : Mechanism) (p : Instruction n)
    (o : ClockedOrganism n) (z : ℕ→List Event) (t : ℕ) :
    RegisterTimestampedBirthSource.eraseRecord (recordAt i m o z t)=
      RegisterFaultInfiniteRecord.recordAt i m (astPolicy p) ⟨0,o.organism.physical,o.organism⟩ z t :=by
  rw [recordAt,RegisterTimestampedBirthSource.step_erase]
  rw [run_erases i m (astPolicy p) ⟨0,o.organism.physical,o.organism⟩ o rfl]
  rfl

theorem measurable_records {n : ℕ} (i : Fin n) (m : Mechanism) (o : ClockedOrganism n) :
    Measurable (recordAt i m o) :=by
  apply measurable_pi_lambda
  intro t
  let F : List Event×List Event→ClockedRecord n:=fun es=>
    let e:=es.2.getLastD (none,false,false)
    RegisterTimestampedBirthSource.step i m (RegisterTimestampedBirthSource.runParent i m o es.1) e.1 e.2.1 e.2.2
  change Measurable (fun z : ℕ→List Event=>F (z t,z (t+1)))
  exact (measurable_of_countable F).comp ((measurable_pi_apply t).prodMk (measurable_pi_apply (t+1)))

def pathLaw {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism) (epsilon : NNReal) (he : epsilon≤1)
    (p : Instruction n) (o : ClockedOrganism n) : Measure (ℕ→ClockedRecord n):=
  (wordPathLaw i noise m epsilon he (astPolicy p) ⟨0,o.organism.physical,o.organism⟩).map (recordAt i m o)

instance pathLaw_probability {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (p : Instruction n) (o : ClockedOrganism n) :
    IsProbabilityMeasure (pathLaw i noise m epsilon he p o):=
  Measure.isProbabilityMeasure_map (measurable_records i m o).aemeasurable

/-- Exact full-law erasure, not a supplied identity matching condition. -/
theorem actual_path_erases {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism) (epsilon : NNReal) (he : epsilon≤1)
    (p : Instruction n) (o : ClockedOrganism n) :
    (pathLaw i noise m epsilon he p o).map (fun rs t=>RegisterTimestampedBirthSource.eraseRecord (rs t))=
      recordPathLaw i noise m epsilon he (astPolicy p) ⟨0,o.organism.physical,o.organism⟩ :=by
  have hm : Measurable (fun (rs : ℕ→ClockedRecord n) t=>RegisterTimestampedBirthSource.eraseRecord (rs t)) :=
    measurable_pi_lambda _ (fun t=>(show Measurable RegisterTimestampedBirthSource.eraseRecord from fun _ _=>trivial).comp (measurable_pi_apply t))
  rw [pathLaw,Measure.map_map hm (measurable_records i m o),recordPathLaw]
  congr 1
  funext z t
  exact actual_record_erases i m p o z t

/-- Identity is the actual existing timestamp source ID at both endpoints,
not the organism's Bool history or an ID inferred from Batch. -/
theorem actual_native_parent_id {n : ℕ} (i : Fin n) (m : Mechanism) (o : ClockedOrganism n)
    (z : ℕ→List Event) (t : ℕ) :
    (recordAt i m o z t).parentBefore.identity=o.identity ∧
    (recordAt i m o z t).parentAfter.identity=o.identity :=by
  exact ⟨RegisterTimestampedBirthSource.runParent_identity i m o (z t),
    RegisterTimestampedBirthSource.runParent_identity i m o (z t)⟩

/-- Literal native clock, including every failure, on one genuine full-measure
source event; no organization-step clock is substituted. -/
theorem actual_native_clock {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (p : Instruction n) (o : ClockedOrganism n) :
    ∀ᵐ z ∂wordPathLaw i noise m epsilon he (astPolicy p) ⟨0,o.organism.physical,o.organism⟩,
      ∀t : ℕ,(recordAt i m o z t).parentBefore.clock=o.clock+t ∧
        (recordAt i m o z t).parentAfter.clock=o.clock+t+1 :=by
  filter_upwards [wordPathLaw_ae_coherent i noise m epsilon he (astPolicy p) ⟨0,o.organism.physical,o.organism⟩] with z hz
  have hlen (t : ℕ) : (z t).length=t :=by
    induction t with
    | zero=>rw [hz.1];rfl
    | succ t ih=>
      obtain ⟨e,he⟩:=hz.2 t
      rw [he,List.length_append,List.length_singleton,ih]
  intro t
  change (RegisterTimestampedBirthSource.runParent i m o (z t)).clock=o.clock+t ∧
    (RegisterTimestampedBirthSource.runParent i m o (z t)).clock+1=o.clock+t+1
  rw [RegisterTimestampedBirthSource.runParent_clock,hlen]
  exact ⟨rfl,rfl⟩

/-- Extra source coordinates are not granted to the old data selector:
two registered owners can give the SAME entire original Batch. -/
theorem no_batch_owner_decoder {n N : ℕ} (i : Fin n) (m : Mechanism) (width : ℚ)
    (omega : Coordinate N→Bool×Bool) (o q : ClockedOrganism n) (hid : o.identity≠q.identity) :
    ¬∃decode : Batch N→Identity,
      decode (sourceData m width omega)=(postClocked i m omega o).identity ∧
      decode (sourceData m width omega)=(postClocked i m omega q).identity :=by
  rintro ⟨decode,ho,hq⟩
  rw [actual_post_identity] at ho hq
  exact hid (ho.symm.trans hq)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicProbeClocked
