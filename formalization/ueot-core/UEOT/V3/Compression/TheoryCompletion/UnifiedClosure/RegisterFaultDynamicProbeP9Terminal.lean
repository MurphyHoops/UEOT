import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicProbeClocked
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterInstructionGOASource
import UEOT.V3.Compression.TheoryCompletion.ObjectScaleCalculus

/-!
Original promise: original P9's SIX meanings hold on ONE actual data-returned parent/program scale.
Existing source: actual timestamp/native erasure, original Batch/postparent/p/q, value/GOD/GOA/recovery/native life.
Premise reduced: construct six real properties and source-derived bridges on the existing clocked-parent/program product; no World or desired-property fields.
Family: accepted-repair p/actual q, separate actual idle comparator, non-total fault, original evaluation and timestamp source ID/clock; Batch gets no ID read.
Consumer: ORIGINAL p9_terminal_objectScale_semantic_transport and SAME native joint parent/resource/life source; a common concrete consumer, not universal six-semantics closure.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicProbeP9Terminal
open MeasureTheory ProbabilityTheory Set Filter
open UEOT.V3.FiniteDiscountedControl UEOT.V3.Compression.TheoryCompletion
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultControlModel
open RegisterFaultJointRecord RegisterFaultInfiniteRecord RegisterInstructionScaleSource RegisterInstructionPurposeScale
open RegisterActuatorScaleSource RegisterActuatorPopulationScale RegisterSemanticInstructionScale RegisterInstructionRecoveryScale RegisterInstructionGOASource
open RegisterFaultFinitePurposeProbe RegisterFaultFinitePurposeInfinite RegisterFaultDynamicProbe RegisterFaultDynamicProbeInfinite
open RegisterFaultDynamicProbeLifecycle RegisterFaultDynamicProbeNativeHomeostasis RegisterFaultDynamicPriceProgram
open RegisterTimestampedBirthSource (ClockedOrganism Identity)
open RegisterFaultDynamicProbeClocked (postClocked actual_post_erase actual_post_identity actual_post_clock)
open scoped ENNReal Topology
noncomputable section
local instance {n : ℕ} : MeasurableSpace (ModeRecord n):=⊤
local instance {n : ℕ} : MeasurableSingletonClass (ModeRecord n):=⟨fun _=>trivial⟩

/-- Existing products, with the source's REAL clocked parent retained. -/
abbrev Carrier {n : ℕ} (i : Fin n):=ClockedOrganism n×Accepted i×Accepted i

def clockedScale {n : ℕ} (i : Fin n) :
    ObjectScaleMap (State n) (State 1) (Carrier i) (ClockedOrganism 1×Instruction 1×Instruction 1):=
  ⟨projectState i,fun obj=>(projectClocked i obj.1,obj.2.1.val.2,obj.2.2.val.2)⟩

def forget {n : ℕ} (i : Fin n) (obj : Carrier i) : PurposeObject i:=
  (obj.1.organism,obj.2.1,obj.2.2)

def erase {n : ℕ} (obj : ClockedOrganism n×Instruction n×Instruction n) : Organism n×Instruction n×Instruction n:=
  (obj.1.organism,obj.2.1,obj.2.2)

def view {n : ℕ} (i : Fin n) (obj : Carrier i) : Organism n×Instruction n×Instruction n:=
  (obj.1.organism,obj.2.1.val.1,obj.2.2.val.1)

/-- Real source ID and actual transaction clock, not inferred Bool history. -/
def IdentityAt {n : ℕ} (id : Identity) (clock : ℕ) (b : Bool) (o : ClockedOrganism n) : Prop:=
  o.identity=id ∧ o.clock=clock ∧ o.organism.program=b

def NativeRate {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (obj : Organism n×Instruction n) : Prop:=
  ∀ᵐ rs ∂recordPathLaw i noise m epsilon he (astPolicy obj.2) ⟨0,obj.1.physical,obj.1⟩,rs∈frequency i epsilon

/-- Positive maintenance, not the frequency-zero dead-source boundary. -/
def LiveNativeRate {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (obj : Organism n×Instruction n) : Prop:=
  epsilon<1 ∧ NativeRate i noise m epsilon he obj

/-- Actual six predicates: purpose compares selected program with another
actual comparator; GOA is the ORIGINAL invariant-law predicate. -/
def Six {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism) (price epsilon : NNReal)
    (he : epsilon≤1) (d : ℝ) (hd : 0<d ∧ d<1) (id : Identity) (clock : ℕ)
    (obj : ClockedOrganism n×Instruction n×Instruction n) : Prop:=
  IdentityAt id clock m.goal obj.1 ∧
  PurposeOrder i noise m epsilon he price d (erase obj) ∧
  IsBellmanGODSelector (model i noise m price epsilon he d hd) (interpret obj.2.1) ∧
  ActualGOA i noise m price epsilon he d hd (obj.1.organism,obj.2.1) ∧
  RecoversEverywhere i m.goal obj.2.1 ∧
  LiveNativeRate i noise m epsilon he (obj.1.organism,obj.2.1)

theorem preserves_identity {n : ℕ} (i : Fin n) (id : Identity) (clock : ℕ) (b : Bool) :
    PreservesIdentity (clockedScale i)
      (fun obj=>IdentityAt id clock b obj.1) (fun obj=>IdentityAt id clock b obj.1) :=by
  intro obj h
  exact h

theorem preserves_purpose {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (price epsilon : NNReal) (he : epsilon≤1) (d : ℝ) :
    PreservesPurpose (clockedScale i)
      (fun obj=>PurposeOrder i noise m epsilon he price d (view i obj))
      (fun obj=>PurposeOrder 0 noise m epsilon he price d (erase obj)) :=by
  intro obj h
  exact actual_preserves_purpose i noise m epsilon he price d (forget i obj) h

theorem preserves_god {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism) (price epsilon : NNReal)
    (he : epsilon≤1) (d : ℝ) (hd : 0<d ∧ d<1) :
    PreservesGOD (clockedScale i)
      (fun obj=>IsBellmanGODSelector (model i noise m price epsilon he d hd) (interpret obj.2.1.val.1))
      (fun obj=>IsBellmanGODSelector (model (0 : Fin 1) noise m price epsilon he d hd) (interpret obj.2.1)) :=by
  intro obj h
  exact (actual_all_price_god_selector i noise m price epsilon he d hd _ _ obj.2.1.property).mp h

theorem preserves_goa {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism) (price epsilon : NNReal)
    (he : epsilon≤1) (d : ℝ) (hd : 0<d ∧ d<1) :
    PreservesGOA (clockedScale i)
      (fun obj=>restorationCheck i m.goal obj.2.1.val.1=true ∧
        ActualGOA i noise m price epsilon he d hd (obj.1.organism,obj.2.1.val.1))
      (fun obj=>ActualGOA (0 : Fin 1) noise m price epsilon he d hd (obj.1.organism,obj.2.1)) :=by
  intro obj h
  exact p9_actual_returned_goa i noise m price epsilon he d hd (obj.1.organism,⟨obj.2.1,h.1⟩)

theorem preserves_recovery {n : ℕ} (i : Fin n) (b : Bool) :
    PreservesRepairability (clockedScale i)
      (fun obj=>restorationCheck i b obj.2.1.val.1=true ∧ RecoversEverywhere i b obj.2.1.val.1)
      (fun obj=>RecoversEverywhere (0 : Fin 1) b obj.2.1) :=by
  intro obj h
  exact p9_actual_returned_recovery i b ⟨obj.2.1,h.1⟩

theorem preserves_native_rate {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) :
    PreservesHomeostasis (clockedScale i)
      (fun obj=>LiveNativeRate i noise m epsilon he (obj.1.organism,obj.2.1.val.1))
      (fun obj=>LiveNativeRate (0 : Fin 1) noise m epsilon he (obj.1.organism,obj.2.1)) :=by
  intro obj hf
  refine ⟨hf.1,?_⟩
  have hl : (recordPathLaw i noise m epsilon he (astPolicy obj.2.1.val.1)
      ⟨0,obj.1.organism.physical,obj.1.organism⟩).map (RegisterSemanticInstructionInfinite.projectPath i)=
      recordPathLaw (0 : Fin 1) noise m epsilon he (astPolicy obj.2.1.val.2)
        ⟨0,(projectOrganism i obj.1.organism).physical,projectOrganism i obj.1.organism⟩ :=
    actual_recordPathLaw i noise m epsilon he _ _ obj.2.1.property ⟨0,obj.1.organism.physical,obj.1.organism⟩
  change ∀ᵐ rs ∂recordPathLaw (0 : Fin 1) noise m epsilon he (astPolicy obj.2.1.val.2)
    ⟨0,(projectOrganism i obj.1.organism).physical,projectOrganism i obj.1.organism⟩,rs∈frequency 0 epsilon
  rw [←hl]
  apply (ae_map_iff (RegisterSemanticInstructionInfinite.measurable_projectPath i).aemeasurable (measurable_frequency 0 epsilon)).2
  filter_upwards [hf.2] with rs hr
  exact (projected_frequency i epsilon rs).mpr hr

/-- This GOA simplex is the actual native positive-time physical marginal,
not an unrelated invariant measure supplied to the terminal. -/
theorem native_goa_marginal {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (p : Instruction n)
    (hc : restorationCheck i m.goal p=true) (o : Organism n) (t : ℕ) :
    (recordPathLaw i noise m epsilon he (astPolicy p) ⟨0,o.physical,o⟩).map
      (fun rs=>(rs t).transaction.parentAfter.physical)=
        (sourceLaw i m epsilon he o.physical).toMeasure :=by
  have hm : Measurable (fun rs : ℕ→ModeRecord n=>(rs t).transaction.parentAfter.physical) :=
    (show Measurable (fun r : ModeRecord n=>r.transaction.parentAfter.physical) from fun _ _=>trivial).comp (measurable_pi_apply t)
  rw [RegisterInstructionNativeSource.native_record_law,RegisterSemanticInstructionInfinite.recordPathLaw,
    Measure.map_map hm (RegisterSemanticInstructionInfinite.measurable_recordPath i m p o)]
  exact actual_positive_time_law i noise m epsilon he p hc o t

/-- ORIGINAL P9 terminal with six source-derived bridges on ONE map. -/
theorem actual_p9_terminal {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism) (price epsilon : NNReal)
    (he : epsilon≤1) (d : ℝ) (hd : 0<d ∧ d<1) (id : Identity) (clock : ℕ) (obj : Carrier i)
    (hc : restorationCheck i m.goal obj.2.1.val.1=true)
    (hi : IdentityAt id clock m.goal obj.1)
    (hp : PurposeOrder i noise m epsilon he price d (view i obj))
    (hg : IsBellmanGODSelector (model i noise m price epsilon he d hd) (interpret obj.2.1.val.1))
    (hh : LiveNativeRate i noise m epsilon he (obj.1.organism,obj.2.1.val.1)) :
    Six (0 : Fin 1) noise m price epsilon he d hd id clock ((clockedScale i).objectMap obj) :=by
  apply p9_terminal_objectScale_semantic_transport (clockedScale i)
    (fun obj=>IdentityAt id clock m.goal obj.1)
    (fun obj=>PurposeOrder i noise m epsilon he price d (view i obj))
    (fun obj=>IsBellmanGODSelector (model i noise m price epsilon he d hd) (interpret obj.2.1.val.1))
    (fun obj=>restorationCheck i m.goal obj.2.1.val.1=true ∧ ActualGOA i noise m price epsilon he d hd (obj.1.organism,obj.2.1.val.1))
    (fun obj=>restorationCheck i m.goal obj.2.1.val.1=true ∧ RecoversEverywhere i m.goal obj.2.1.val.1)
    (fun obj=>LiveNativeRate i noise m epsilon he (obj.1.organism,obj.2.1.val.1))
    (fun obj=>IdentityAt id clock m.goal obj.1)
    (fun obj=>PurposeOrder 0 noise m epsilon he price d (erase obj))
    (fun obj=>IsBellmanGODSelector (model (0 : Fin 1) noise m price epsilon he d hd) (interpret obj.2.1))
    (fun obj=>ActualGOA (0 : Fin 1) noise m price epsilon he d hd (obj.1.organism,obj.2.1))
    (fun obj=>RecoversEverywhere (0 : Fin 1) m.goal obj.2.1)
    (fun obj=>LiveNativeRate (0 : Fin 1) noise m epsilon he (obj.1.organism,obj.2.1))
    (fine:=obj) rfl (preserves_identity i id clock m.goal)
    (preserves_purpose i noise m price epsilon he d)
    (preserves_god i noise m price epsilon he d hd)
    (preserves_goa i noise m price epsilon he d hd)
    (preserves_recovery i m.goal) (preserves_native_rate i noise m epsilon he)
  exact ⟨hi,hp,hg,⟨hc,actual_invariant_goa i noise m price epsilon he d hd _ hc obj.1.organism.physical⟩,
    ⟨hc,actual_recoverable i m.goal _ hc⟩,hh⟩

/-- Baseline is an actual accepted idle AST, not the selected program itself. -/
def idleAccepted {n : ℕ} (i : Fin n) : Accepted i:=
  ⟨(.emit none,returnedProgram i (.emit none)),returned_synthesis i (.idle false)⟩

def dataObject {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : ClockedOrganism n) : Carrier i:=
  (postClocked i m omega o,
    ⟨(returnedAST i (classify price width d u (sourceData m width omega)),
      returnedProgram i (returnedAST i (classify price width d u (sourceData m width omega)))),
      returned_synthesis i (classify price width d u (sourceData m width omega))⟩,
    idleAccepted i)

/-- All fine premises are DERIVED from this actual source Batch and its
actual computed repair AST; no six-property certificate is an input. -/
theorem data_actual_p9_six {n N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon<1) (price width d u : ℚ)
    (hp : 0≤price) (hw : 0<width) (hd : 0<d ∧ d<1)
    (omega : Coordinate N→Bool×Bool) (o : ClockedOrganism n) (ho : o.organism.program=m.goal)
    (hgood : omega∈Good noise m epsilon he.le N width (u : ℝ)) (b : Bool)
    (hs : classify price width d u (sourceData m width omega)=.repair b) :
    Six (0 : Fin 1) noise m (priceValue price hp) epsilon he.le (d : ℝ) (by exact_mod_cast hd)
      o.identity (o.clock+2*N) ((clockedScale i).objectMap (dataObject i m price width d u omega o)) :=by
  have hdr : 0<(d : ℝ) ∧ (d : ℝ)<1:=by exact_mod_cast hd
  have ha : classify price width d u (sourceData m width omega)≠.unknown:=by rw [hs];simp
  have hsource:=actual_good_returned_program i noise m epsilon he.le price width d u hp hw hd omega o.organism ho hgood ha
  have hc:=accepted_repair_restores i m price width d u omega b hs
  have hparent:=(postProbeParent_program i m omega o.organism).trans ho
  apply actual_p9_terminal i noise m (priceValue price hp) epsilon he.le (d : ℝ) hdr
    o.identity (o.clock+2*N) (dataObject i m price width d u omega o) hc
  · exact ⟨actual_post_identity i m omega o,actual_post_clock i m omega o,by
      change (postClocked i m omega o).organism.program=m.goal
      rw [actual_post_erase,postProbeParent_program]
      exact ho⟩
  · change PurposeOrder i noise m epsilon he.le (priceValue price hp) (d : ℝ)
      ((postClocked i m omega o).organism,
        returnedAST i (classify price width d u (sourceData m width omega)),.emit none)
    rw [actual_post_erase]
    refine ⟨hdr,?_⟩
    rw [hsource.2.2.2.2.1,actual_value_policy i noise m epsilon he.le (priceValue price hp) (d : ℝ) hdr _ hparent]
    exact (astPolicy (.emit none)).infiniteValue_le_optimal _ _
  · exact hsource.2.1
  · change LiveNativeRate i noise m epsilon he.le ((postClocked i m omega o).organism,
      returnedAST i (classify price width d u (sourceData m width omega)))
    refine ⟨he,?_⟩
    rw [actual_post_erase]
    exact (accepted_repair_native_pair i noise m epsilon he.le price width d u omega o.organism ho b hs).2.1

/-- No parameter oracle/extra guard: total fault produces UNKNOWN AE on the
ORIGINAL training source. An impossible raw word cannot be used to infer this. -/
theorem repair_non_total_ae (noise : PMF Bool) (m : Mechanism) (epsilon : NNReal) (he : epsilon≤1)
    (N : ℕ) (price width d u : ℚ) :
    ∀ᵐ omega ∂rawLaw noise epsilon he N,∀b : Bool,
      classify price width d u (sourceData m width omega)=.repair b→epsilon<1 :=by
  by_cases hlt : epsilon<1
  · exact ae_of_all _ (fun _ _ _=>hlt)
  · have heq : epsilon=1:=le_antisymm he (not_lt.mp hlt)
    subst epsilon
    filter_upwards [RegisterFaultDynamicProbe.total_fault_unknown_ae noise m N price width d u] with omega hunknown
    intro b hb
    rw [hunknown] at hb
    cases hb

theorem supported_repair_non_total {N : ℕ} (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (price width d u : ℚ) (omega : Coordinate N→Bool×Bool)
    (hpos : 0<rawLaw noise epsilon he N {omega}) (b : Bool)
    (hs : classify price width d u (sourceData m width omega)=.repair b) : epsilon<1 :=by
  by_contra hbad
  have hle : rawLaw noise epsilon he N {omega}≤rawLaw noise epsilon he N
      {w | ¬∀b : Bool,classify price width d u (sourceData m width w)=.repair b→epsilon<1} :=by
    apply measure_mono
    intro w hw h
    rcases Set.mem_singleton_iff.mp hw with rfl
    exact hbad (h b hs)
  rw [ae_iff.mp (repair_non_total_ae noise m epsilon he N price width d u)] at hle
  exact (ne_of_gt hpos) (le_antisymm hle bot_le)

/-- Native same-joint parent/P6/prepay plus the SAME data-selected P9 terminal.
Only Good supplies the registered optimal-order premise; no accepted paths are
filtered from the actual training/deployment source. -/
theorem actual_joint_funded_p9_six {n N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (price width d u : ℚ)
    (hp : 0≤price) (hw : 0<width) (hd : 0<d ∧ d<1)
    (o : ClockedOrganism n) (ho : o.organism.program=m.goal)
    (cap g initial : ℝ) (hcap : (m.writeCost : ℝ)≤cap) (hg : cap≤g) (hi : 0 ≤ initial) :
    ∀ᵐ z ∂jointLaw (N:=N) i noise m epsilon he price width d u o.organism,
      RegisterFaultDynamicProbeResource.wholeRecords i m o.organism z∈SameParentTrace o.organism.history ∧
      UEOT.V3.Compression.Objecthood.ResourceClosure.ResourceViable initial (fun _=>g)
        (fun t=>(RegisterFaultDynamicProbeResource.wholeRecords i m o.organism z t).transaction.expenditure) ∧
      (∀t,(RegisterFaultDynamicProbeResource.wholeRecords i m o.organism z t).transaction.expenditure≤
        RegisterFaultDynamicProbeResource.balance i m o.organism initial g z t+g) ∧
      (∀b : Bool,classify price width d u (sourceData m width z.1)=.repair b→
        z.2∈frequency i epsilon ∧
        RegisterSemanticInstructionInfinite.projectPath i z.2∈frequency 0 epsilon ∧
        ∀N : ℕ,∃t≥N,Legitimate i (z.2 t).transaction.parentAfter) ∧
      (z.1∈Good noise m epsilon he N width (u : ℝ)→∀b : Bool,
        classify price width d u (sourceData m width z.1)=.repair b→
        Six (0 : Fin 1) noise m (priceValue price hp) epsilon he (d : ℝ) (by exact_mod_cast hd)
          o.identity (o.clock+2*N) ((clockedScale i).objectMap (dataObject i m price width d u z.1 o))) :=by
  have hraw:=repair_non_total_ae noise m epsilon he N price width d u
  rw [←actual_joint_training_marginal (N:=N) i noise m epsilon he price width d u o.organism] at hraw
  have hnon:=ae_of_ae_map measurable_fst.aemeasurable hraw
  filter_upwards [funded_joint_repair_long_run (N:=N) i noise m epsilon he price width d u o.organism ho cap g initial hcap hg hi,
    hnon] with z hz hparam
  refine ⟨hz.1,hz.2.1,hz.2.2.1,?_,fun hgood b hb=>data_actual_p9_six i noise m epsilon (hparam b hb)
    price width d u hp hw hd z.1 o ho hgood b hb⟩
  intro b hb
  have hlife:=hz.2.2.2 b hb
  exact ⟨hlife.1,hlife.2.1,hlife.2.2.1 (hparam b hb)⟩

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicProbeP9Terminal
