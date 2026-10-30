import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterInstructionHomeostasis
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterInstructionPurposeScale
import UEOT.V3.RecoveryHittingRestart

/-!
Original promise: actual returned AST homeostasis belongs to the SAME native deployment law.
Existing source: native growing action/mode/label words and separately interpreted IID primitive records.
Premise reduced: prove source-law identity from actual sampler and interpreter, not an assumed law equality.
Family: original deterministic AST, original parent and native fixed-port clock; all faults/labels/fees retained.
Consumer: native recordPathLaw and data-selected training/deployment joint law; no reset or altered sampling.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterInstructionNativeSource
open MeasureTheory ProbabilityTheory Set Filter
open UEOT.V3.FiniteDiscountedControl UEOT.V3.DynamicsKernel
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultJointRecord
open RegisterFaultInfiniteRecord RegisterInstructionScaleSource RegisterInstructionPurposeScale
open RegisterFaultFinitePurposeProbe (primitiveLaw)
open RegisterSemanticInstructionInfinite (Stream Primitive)
open scoped ENNReal Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance {n : ℕ} : MeasurableSpace (ModeRecord n):=⊤
local instance {n : ℕ} : MeasurableSingletonClass (ModeRecord n):=⟨fun _=>trivial⟩

/-- Actual native event row has exactly the original primitive marginal,
for ANY causal policy and its actual memory. -/
theorem event_primitive_law {n : ℕ} (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1)
    (pi : CausalPolicy.{0,0,0} (State n) (fun _=>Action)) (c : Config pi) :
    (eventLaw noise epsilon he pi c).map Prod.snd=primitiveLaw noise epsilon he :=by
  apply PMF.ext
  rintro ⟨mode,label⟩
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [PMF.map_apply,tsum_fintype,ENNReal.toReal_sum (by
    intro e _
    split_ifs
    · exact PMF.apply_ne_top _ _
    · exact ENNReal.zero_ne_top)]
  simp only [Fintype.sum_prod_type]
  simp only [apply_ite,ENNReal.toReal_zero]
  simp only [Prod.mk.injEq]
  simp_rw [eventLaw_toReal]
  simp only [eventWeight]
  cases mode <;> cases label <;>
    simp [RegisterFaultFinitePurposeProbe.primitiveLaw_apply,ENNReal.toReal_mul,ite_and,
      ←Finset.sum_mul,pi.actionProb_sum_one]

/-- A constant native kernel with its own marginal is the actual product law. -/
theorem constant_canonical_iid (mu : Measure Primitive) [IsProbabilityMeasure mu] :
    homTrajMeasure mu (Kernel.const Primitive mu)=Measure.infinitePi (fun _ : ℕ=>mu) :=by
  have hk : homHistoryKernel (Kernel.const Primitive mu)=fun r=>Kernel.const ((j : Finset.Iic r)→Primitive) mu :=by
    funext r
    ext h S hS
    rfl
  have hinit : mu.map (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0=>Primitive)).symm=
      Measure.pi (fun _ : Finset.Iic 0=>mu) :=by
    exact ((measurePreserving_piUnique (fun _ : Finset.Iic 0=>mu)).symm _).map_eq
  have h := (Measure.isProjectiveLimit_infinitePiNat (fun _ : ℕ=>mu)).unique
    (Measure.isProjectiveLimit_infinitePi (fun _ : ℕ=>mu))
  simpa only [homTrajMeasure,Kernel.trajMeasure,hk,hinit,Measure.infinitePiNat] using h

def lastPrimitive (es : List Event) : Primitive:=(es.getLastD (none,false,false)).2

theorem word_primitive_row {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1)
    (pi : CausalPolicy.{0,0,0} (State n) (fun _=>Action)) (c : Config pi) (es : List Event) :
    (wordKernel i noise m epsilon he pi c es).map lastPrimitive=(primitiveLaw noise epsilon he).toMeasure :=by
  change ((eventLaw noise epsilon he pi (run i m pi c es)).map (fun e=>es++[e])).toMeasure.map lastPrimitive=_
  rw [PMF.toMeasure_map _ _ (measurable_of_countable _),PMF.map_comp]
  have hf : (lastPrimitive∘(fun e=>es++[e]))=Prod.snd :=by
    funext e
    simp [lastPrimitive]
  rw [hf,event_primitive_law]

theorem measurable_native_primitives :
    Measurable (fun (z : ℕ→List Event) t=>(eventAt z t).2) :=by
  apply measurable_pi_lambda
  intro t
  exact (measurable_of_countable lastPrimitive).comp (measurable_pi_apply (t+1))

/-- Native growing-word paths have the actual IID primitive innovation law. -/
theorem native_primitive_law {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1)
    (pi : CausalPolicy.{0,0,0} (State n) (fun _=>Action)) (c : Config pi) :
    (wordPathLaw i noise m epsilon he pi c).map (fun z t=>(eventAt z t).2)=
      RegisterInstructionHomeostasis.iidSource noise epsilon he :=by
  let mu:=(primitiveLaw noise epsilon he).toMeasure
  let Q:=Kernel.const Primitive mu
  have hl : StrongLumpability (wordKernel i noise m epsilon he pi c) Q lastPrimitive (measurable_of_countable _) :=by
    apply (strongLumpability_iff_apply _ _ _ _).mpr
    intro es
    exact word_primitive_row i noise m epsilon he pi c es
  have h:=homTrajMeasure_path_naturality (Measure.dirac ([] : List Event))
    (wordKernel i noise m epsilon he pi c) Q lastPrimitive (measurable_of_countable _) hl
  rw [Measure.map_dirac' (measurable_of_countable _)] at h
  have hs:=UEOT.V3.RecoveryHittingRestart.homTrajMeasure_shift (Measure.dirac (lastPrimitive [])) Q
  have heq : Q ∘ₘ Measure.dirac (lastPrimitive [])=mu :=by
    simp [Q]
  rw [heq,constant_canonical_iid] at hs
  change (wordPathLaw i noise m epsilon he pi c).map (mapPath lastPrimitive)=_ at h
  change (wordPathLaw i noise m epsilon he pi c).map
    (UEOT.V3.RecoveryHittingFirstStep.pathShift∘mapPath lastPrimitive)=_
  rw [←Measure.map_map UEOT.V3.RecoveryHittingFirstStep.measurable_pathShift
    (measurable_mapPath _ (measurable_of_countable _)),h,hs]
  rfl

private theorem run_ast_memory {n : ℕ} (i : Fin n) (m : Mechanism) (p : Instruction n)
    (c : Config (astPolicy p)) (hc : c.2.1=c.2.2.physical) (es : List Event) :
    (run i m (astPolicy p) c es).2.1=(run i m (astPolicy p) c es).2.2.physical :=by
  induction es generalizing c with
  | nil=>exact hc
  | cons e es ih=>
    apply ih
    rfl

private theorem event_ast_action {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (p : Instruction n)
    (c : Config (astPolicy p)) (hc : c.2.1=c.2.2.physical) (es : List Event) :
    ∀ᵐ e ∂(eventLaw noise epsilon he (astPolicy p) (run i m (astPolicy p) c es)).toMeasure,
      e.1=interpret p (run i m (astPolicy p) c es).2.2.physical :=by
  rw [ae_iff,PMF.toMeasure_apply_eq_zero_iff _ ((Set.toFinite _).measurableSet)]
  apply Set.disjoint_left.mpr
  intro e hs hbad
  apply (PMF.mem_support_iff _ _).mp hs
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) ENNReal.zero_ne_top).mp
  rw [eventLaw_toReal]
  simp only [ENNReal.toReal_zero]
  have hprob : (astPolicy p).actionProb (run i m (astPolicy p) c es).2.1 e.1=
      (if e.1=interpret p (run i m (astPolicy p) c es).2.1 then (1 : ℝ) else 0) :=by
    simp [astPolicy,selectorPolicy]
  rw [eventWeight,hprob,run_ast_memory i m p c hc es,if_neg hbad]
  simp

private theorem wordKernel_ast_append {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (p : Instruction n)
    (c : Config (astPolicy p)) (hc : c.2.1=c.2.2.physical) (es : List Event) :
    ∀ᵐ ys ∂wordKernel i noise m epsilon he (astPolicy p) c es,
      ∃e : Event,ys=es++[e] ∧ e.1=interpret p (run i m (astPolicy p) c es).2.2.physical :=by
  change ∀ᵐ ys ∂(wordRow i noise m epsilon he (astPolicy p) c es).toMeasure,_
  rw [wordRow,←PMF.toMeasure_map _ _ (measurable_of_finite _)]
  apply (ae_map_iff (measurable_of_finite _).aemeasurable ((Set.to_countable _).measurableSet)).2
  filter_upwards [event_ast_action i noise m epsilon he p c hc es] with e ha
  exact ⟨e,rfl,ha⟩

private theorem wordPath_ast_append {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (p : Instruction n) (o : Organism n) (k : ℕ) :
    ∀ᵐ z ∂wordPathLaw i noise m epsilon he (astPolicy p) ⟨0,o.physical,o⟩,
      ∃e : Event,z (k+1)=z k++[e] ∧
        e.1=interpret p (run i m (astPolicy p) ⟨0,o.physical,o⟩ (z k)).2.2.physical :=by
  let Q:=wordKernel i noise m epsilon he (astPolicy p) ⟨0,o.physical,o⟩
  let mu:=wordPathLaw i noise m epsilon he (astPolicy p) ⟨0,o.physical,o⟩
  let : ∀j,IsMarkovKernel (homHistoryKernel Q j):=fun j=>isMarkovKernel_homHistoryKernel Q j
  have hstep : (mu.map (Preorder.frestrictLe k)) ⊗ₘ homHistoryKernel Q k=
      mu.map (fun z=>(Preorder.frestrictLe k z,z (k+1))) :=by
    simpa only [mu,wordPathLaw,Q,homTrajMeasure] using
      (Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
        (X:=fun _ : ℕ=>List Event) (μ₀:=Measure.dirac [])
        (κ:=homHistoryKernel Q) (a:=k))
  have hg : ∀ᵐ x ∂((mu.map (Preorder.frestrictLe k)) ⊗ₘ homHistoryKernel Q k),
      ∃e : Event,x.2=x.1 (lastHistoryIndex k)++[e] ∧
        e.1=interpret p (run i m (astPolicy p) ⟨0,o.physical,o⟩ (x.1 (lastHistoryIndex k))).2.2.physical :=by
    apply Measure.ae_compProd_of_ae_ae ((Set.to_countable _).measurableSet)
    apply ae_of_all
    intro h
    exact wordKernel_ast_append i noise m epsilon he p ⟨0,o.physical,o⟩ rfl _
  rw [hstep] at hg
  have hh:=ae_of_ae_map (by fun_prop : Measurable
    (fun z : ℕ→List Event=>(Preorder.frestrictLe k z,z (k+1)))).aemeasurable hg
  simpa only [Preorder.frestrictLe_apply,lastHistoryIndex] using hh

private theorem run_parent_snoc {n : ℕ} (i : Fin n) (m : Mechanism) (p : Instruction n)
    (c : Config (astPolicy p)) (es : List Event) (e : Event) :
    (run i m (astPolicy p) c (es++[e])).2.2=
      (modeRecordStep i m (run i m (astPolicy p) c es).2.2 e.1 e.2.1 e.2.2).transaction.parentAfter :=by
  unfold run
  rw [List.foldl_append]
  rfl

private theorem actual_word_ast_records {n : ℕ} (i : Fin n) (m : Mechanism) (p : Instruction n)
    (o : Organism n) (z : ℕ→List Event) (hz : z 0=[])
    (hlegal : ∀k,∃e : Event,z (k+1)=z k++[e] ∧
      e.1=interpret p (run i m (astPolicy p) ⟨0,o.physical,o⟩ (z k)).2.2.physical) :
    (fun k=>RegisterFaultInfiniteRecord.recordAt i m (astPolicy p) ⟨0,o.physical,o⟩ z k)=
      RegisterSemanticInstructionInfinite.recordAt i m p o (fun k=>(eventAt z k).2) :=by
  have hparents (k : ℕ) :
      (run i m (astPolicy p) ⟨0,o.physical,o⟩ (z k)).2.2=
        RegisterSemanticInstructionInfinite.parentAt i m p o (fun k=>(eventAt z k).2) k :=by
    induction k with
    | zero=>rw [hz];rfl
    | succ k ih=>
      obtain ⟨e,hy,ha⟩:=hlegal k
      have hevent : eventAt z k=e :=by simp [eventAt,hy]
      rw [hy,run_parent_snoc,RegisterSemanticInstructionInfinite.parentAt,hevent,←ih,ha]
  funext k
  obtain ⟨e,hy,ha⟩:=hlegal k
  have hevent : eventAt z k=e :=by simp [eventAt,hy]
  simp only [RegisterFaultInfiniteRecord.recordAt,RegisterSemanticInstructionInfinite.recordAt,hevent]
  rw [←hparents k,ha]

/-- COMPLETE native record law of THIS AST equals its actual primitive-IID
interpreter law, including every failed birth, fee, program and parent field. -/
theorem native_record_law {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (p : Instruction n) (o : Organism n) :
    RegisterFaultInfiniteRecord.recordPathLaw i noise m epsilon he (astPolicy p) ⟨0,o.physical,o⟩=
      RegisterSemanticInstructionInfinite.recordPathLaw i m p o
        (RegisterInstructionHomeostasis.iidSource noise epsilon he) :=by
  unfold RegisterFaultInfiniteRecord.recordPathLaw RegisterSemanticInstructionInfinite.recordPathLaw
  rw [←native_primitive_law i noise m epsilon he (astPolicy p) ⟨0,o.physical,o⟩,
    Measure.map_map (RegisterSemanticInstructionInfinite.measurable_recordPath i m p o) measurable_native_primitives]
  apply Measure.map_congr
  have hall : ∀ᵐ z ∂wordPathLaw i noise m epsilon he (astPolicy p) ⟨0,o.physical,o⟩,
      ∀k,∃e : Event,z (k+1)=z k++[e] ∧
        e.1=interpret p (run i m (astPolicy p) ⟨0,o.physical,o⟩ (z k)).2.2.physical :=by
    rw [ae_all_iff]
    exact wordPath_ast_append i noise m epsilon he p o
  filter_upwards [wordPathLaw_ae_coherent i noise m epsilon he (astPolicy p) ⟨0,o.physical,o⟩,hall] with z hz hlegal
  exact actual_word_ast_records i m p o z hz.1 hlegal

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterInstructionNativeSource
