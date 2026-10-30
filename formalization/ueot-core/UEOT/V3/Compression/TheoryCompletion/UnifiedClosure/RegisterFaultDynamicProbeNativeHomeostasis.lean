import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterInstructionNativeSource
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicProbeLifecycle

/-!
Original promise: the SAME data-returned program's long-run maintenance belongs to the actual training/deployment joint source.
Existing proof: exact AST native/primitive COMPLETE record-law identity, original strong law and real probe-parent/resource identity.
Premise reduced: transfer actual marginals/frequency/returns to native recordPathLaw and actual deploymentKernel, then ONE joint full-measure event.
Family: unchanged full Batch, actual postProbeParent, accepted repair p and actual synthesised q; idle and total fault are distinct boundaries.
Consumer: actual native jointLaw and its projected q records; no resampling, replacement initial parent, clock or free funding.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicProbeNativeHomeostasis
open MeasureTheory ProbabilityTheory Set Filter
open UEOT.V3.FiniteDiscountedControl UEOT.V3.Compression.TheoryCompletion
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultJointRecord
open RegisterFaultControlModel RegisterFaultInfiniteRecord RegisterInstructionScaleSource RegisterInstructionPurposeScale
open RegisterActuatorScaleSource RegisterSemanticInstructionScale RegisterInstructionRecoveryScale
open RegisterFaultFinitePurposeProbe RegisterFaultFinitePurposeInfinite RegisterFaultDynamicProbe RegisterFaultDynamicProbeInfinite
open RegisterFaultDynamicProbeLifecycle RegisterInstructionNativeSource
open scoped ENNReal Topology
noncomputable section
local instance {n : ℕ} : MeasurableSpace (ModeRecord n):=⊤
local instance {n : ℕ} : MeasurableSingletonClass (ModeRecord n):=⟨fun _=>trivial⟩
local instance {n : ℕ} (i : Fin n) (o : Organism n) : Decidable (Legitimate i o):=
  inferInstanceAs (Decidable (o.physical i=o.program))

def health {n : ℕ} (i : Fin n) (rs : ℕ→ModeRecord n) (t : ℕ) : ℝ:=
  if Legitimate i (rs t).transaction.parentAfter then 1 else 0

def frequency {n : ℕ} (i : Fin n) (epsilon : NNReal) : Set (ℕ→ModeRecord n):=
  {rs | Tendsto (fun N : ℕ=>(∑t∈Finset.range N,health i rs t)/(N : ℝ)) atTop (𝓝 (1-(epsilon : ℝ)))}

theorem measurable_frequency {n : ℕ} (i : Fin n) (epsilon : NNReal) : MeasurableSet (frequency i epsilon) :=by
  apply measurableSet_tendsto
  intro N
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro t ht
  exact (show Measurable (fun r : ModeRecord n=>if Legitimate i r.transaction.parentAfter then (1 : ℝ) else 0) from fun _ _=>trivial).comp (measurable_pi_apply t)

/-- This native AST law itself, rather than an independent replacement law. -/
theorem native_frequency {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (p : Instruction n)
    (hc : restorationCheck i m.goal p=true) (o : Organism n) (ho : o.program=m.goal) :
    ∀ᵐ rs ∂recordPathLaw i noise m epsilon he (astPolicy p) ⟨0,o.physical,o⟩,
      rs∈frequency i epsilon :=by
  rw [native_record_law]
  apply (ae_map_iff (RegisterSemanticInstructionInfinite.measurable_recordPath i m p o).aemeasurable
    (measurable_frequency i epsilon)).2
  exact RegisterInstructionHomeostasis.actual_maintenance_frequency i m.goal m.writeCost p hc o ho noise epsilon he

/-- Actual per-transaction marginal, including epsilon0/1 and zero fees. -/
theorem native_health_mass {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (p : Instruction n)
    (hc : restorationCheck i m.goal p=true) (o : Organism n) (ho : o.program=m.goal) (t : ℕ) :
    recordPathLaw i noise m epsilon he (astPolicy p) ⟨0,o.physical,o⟩
      {rs | Legitimate i (rs t).transaction.parentAfter}=ENNReal.ofReal (1-(epsilon : ℝ)) :=by
  have hS : MeasurableSet {rs : ℕ→ModeRecord n | Legitimate i (rs t).transaction.parentAfter}:=
    (show MeasurableSet {r : ModeRecord n | Legitimate i r.transaction.parentAfter} from trivial).preimage (measurable_pi_apply t)
  rw [native_record_law,RegisterSemanticInstructionInfinite.recordPathLaw,
    Measure.map_apply (RegisterSemanticInstructionInfinite.measurable_recordPath i m p o) hS]
  exact RegisterInstructionHomeostasis.actual_maintained_probability i m.goal m.writeCost p hc o ho noise epsilon he t

private theorem average_eventually (f : ℕ→ℝ) (a : ℝ) (h : ∀ᶠt in atTop,f t=a) :
    Tendsto (fun N : ℕ=>(∑t∈Finset.range N,f t)/(N : ℝ)) atTop (𝓝 a) :=by
  have hf : Tendsto f atTop (𝓝 a):=(tendsto_congr' h).mpr tendsto_const_nhds
  simpa only [div_eq_mul_inv,mul_comm] using hf.cesaro

theorem frequency_returns {n : ℕ} (i : Fin n) (epsilon : NNReal) (he : epsilon<1)
    (rs : ℕ→ModeRecord n) (hf : rs∈frequency i epsilon) :
    ∀N : ℕ,∃t≥N,Legitimate i (rs t).transaction.parentAfter :=by
  intro N
  by_contra hn
  have hz : ∀ᶠt in atTop,health i rs t=0 :=by
    filter_upwards [Ici_mem_atTop N] with t ht
    exact if_neg (fun h=>hn ⟨t,ht,h⟩)
  have h:=tendsto_nhds_unique hf (average_eventually _ 0 hz)
  have heR : (epsilon : ℝ)<1:=by exact_mod_cast he
  linarith

theorem frequency_no_permanence {n : ℕ} (i : Fin n) (epsilon : NNReal) (he : 0<epsilon)
    (rs : ℕ→ModeRecord n) (hf : rs∈frequency i epsilon) :
    ¬∃N : ℕ,∀t≥N,Legitimate i (rs t).transaction.parentAfter :=by
  rintro ⟨N,hN⟩
  have hz : ∀ᶠt in atTop,health i rs t=1 :=by
    filter_upwards [Ici_mem_atTop N] with t ht
    exact if_pos (hN t ht)
  have h:=tendsto_nhds_unique hf (average_eventually _ 1 hz)
  have heR : 0<(epsilon : ℝ):=by exact_mod_cast he
  linarith

/-- Both native laws are the original actual p and its computed q, and the
fine law transports to THIS q law with complete records. -/
theorem accepted_repair_native_pair {n N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (ho : o.program=m.goal)
    (b : Bool) (hs : classify price width d u (sourceData m width omega)=.repair b) :
    let parent:=postProbeParent i m omega o
    let p:=returnedAST i (classify price width d u (sourceData m width omega))
    let q:=returnedProgram i p
    (recordPathLaw i noise m epsilon he (astPolicy p) ⟨0,parent.physical,parent⟩).map
        (RegisterSemanticInstructionInfinite.projectPath i)=
      recordPathLaw (0 : Fin 1) noise m epsilon he (astPolicy q)
        ⟨0,(projectOrganism i parent).physical,projectOrganism i parent⟩ ∧
    (∀ᵐ rs ∂recordPathLaw i noise m epsilon he (astPolicy p) ⟨0,parent.physical,parent⟩,
      rs∈frequency i epsilon) ∧
    (∀ᵐ rs ∂recordPathLaw (0 : Fin 1) noise m epsilon he (astPolicy q)
      ⟨0,(projectOrganism i parent).physical,projectOrganism i parent⟩,
      rs∈frequency 0 epsilon) :=by
  let parent:=postProbeParent i m omega o
  let p:=returnedAST i (classify price width d u (sourceData m width omega))
  let q:=returnedProgram i p
  have hc:=accepted_repair_restores i m price width d u omega b hs
  have hsyn:=returned_synthesis i (classify price width d u (sourceData m width omega))
  have hp:=(postProbeParent_program i m omega o).trans ho
  refine ⟨?_,native_frequency i noise m epsilon he p hc parent hp,?_⟩
  · exact actual_recordPathLaw i noise m epsilon he p q hsyn ⟨0,parent.physical,parent⟩
  · exact native_frequency 0 noise m epsilon he q
      ((returned_restoration_iff i m.goal p q hsyn).mp hc) (projectOrganism i parent) hp

private theorem measurable_joint_frequency {n N : ℕ} (i : Fin n) (m : Mechanism)
    (epsilon : NNReal) (price width d u : ℚ) :
    MeasurableSet {z : (Coordinate N→Bool×Bool)×(ℕ→ModeRecord n) |
      ∀b : Bool,classify price width d u (sourceData m width z.1)=.repair b→z.2∈frequency i epsilon} :=by
  have heq : {z : (Coordinate N→Bool×Bool)×(ℕ→ModeRecord n) |
      ∀b : Bool,classify price width d u (sourceData m width z.1)=.repair b→z.2∈frequency i epsilon}=
      ⋂b : Bool,({z | classify price width d u (sourceData m width z.1)≠.repair b} ∪
        {z | z.2∈frequency i epsilon}) :=by ext z;simp only [Set.mem_ofPred_eq,Set.mem_iInter,Set.mem_union];simp only [imp_iff_not_or]
  rw [heq]
  apply MeasurableSet.iInter
  intro b
  exact (((Set.toFinite {omega : Coordinate N→Bool×Bool |
    classify price width d u (sourceData m width omega)≠.repair b}).measurableSet).preimage measurable_fst).union
    ((measurable_frequency i epsilon).preimage measurable_snd)

/-- ONE full-measure event of the original training×native-deployment law.
Acceptance is not conditioned on or selected by an after-the-fact redraw. -/
theorem actual_joint_repair_frequency {n N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (price width d u : ℚ) (o : Organism n) (ho : o.program=m.goal) :
    ∀ᵐ z ∂jointLaw (N:=N) i noise m epsilon he price width d u o,
      ∀b : Bool,classify price width d u (sourceData m width z.1)=.repair b→z.2∈frequency i epsilon :=by
  apply Measure.ae_compProd_of_ae_ae (measurable_joint_frequency i m epsilon price width d u)
  apply ae_of_all
  intro omega
  rw [ae_all_iff]
  intro b
  by_cases hs : classify price width d u (sourceData m width omega)=.repair b
  · filter_upwards [(accepted_repair_native_pair i noise m epsilon he price width d u omega o ho b hs).2.1] with rs hf
    exact fun _=>hf
  · exact ae_of_all _ (fun _ h=>False.elim (hs h))

theorem projected_frequency {n : ℕ} (i : Fin n) (epsilon : NNReal) (rs : ℕ→ModeRecord n) :
    RegisterSemanticInstructionInfinite.projectPath i rs∈frequency 0 epsilon↔rs∈frequency i epsilon :=Iff.rfl

/-- Same actual fine future and the records of the actual computed q share
frequency/returns/nonpermanence; all are native-deployment conclusions. -/
theorem actual_joint_repair_long_run {n N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (price width d u : ℚ) (o : Organism n) (ho : o.program=m.goal) :
    ∀ᵐ z ∂jointLaw (N:=N) i noise m epsilon he price width d u o,
      ∀b : Bool,classify price width d u (sourceData m width z.1)=.repair b→
        z.2∈frequency i epsilon ∧
        RegisterSemanticInstructionInfinite.projectPath i z.2∈frequency 0 epsilon ∧
        (epsilon<1→∀N : ℕ,∃t≥N,Legitimate i (z.2 t).transaction.parentAfter) ∧
        (0<epsilon→¬∃N : ℕ,∀t≥N,Legitimate i (z.2 t).transaction.parentAfter) :=by
  filter_upwards [actual_joint_repair_frequency (N:=N) i noise m epsilon he price width d u o ho] with z hz
  intro b hb
  have hf:=hz b hb
  exact ⟨hf,(projected_frequency i epsilon z.2).mpr hf,fun h=>frequency_returns i epsilon h z.2 hf,
    fun h=>frequency_no_permanence i epsilon h z.2 hf⟩

/-- Frequency zero is not used as a substitute for this stronger dead-source
statement: every actual post-transaction has zero healthy marginal. -/
theorem native_total_fault_never_healthy {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (p : Instruction n) (hc : restorationCheck i m.goal p=true) (o : Organism n) (ho : o.program=m.goal) :
    ∀ᵐ rs ∂recordPathLaw i noise m 1 (by norm_num) (astPolicy p) ⟨0,o.physical,o⟩,
      ∀t : ℕ,¬Legitimate i (rs t).transaction.parentAfter :=by
  rw [ae_all_iff]
  intro t
  have hz:=native_health_mass i noise m 1 (by norm_num) p hc o ho t
  norm_num at hz
  apply ae_iff.mpr
  simpa only [not_not] using hz

private theorem idle_stays_bad {n : ℕ} (i : Fin n) (m : Mechanism) (o : Organism n)
    (hb : o.physical i≠m.goal) (w : RegisterSemanticInstructionInfinite.Stream) (t : ℕ) :
    (RegisterSemanticInstructionInfinite.parentAt i m (.emit none) o w t).physical i≠m.goal :=by
  induction t with
  | zero=>exact hb
  | succ t ih=>
    change (modeRecordStep i m _ none (w t).1 (w t).2).transaction.parentAfter.physical i≠m.goal
    cases hm:(w t).1
    · simp [modeRecordStep]
    · simpa only [modeRecordStep,hm,if_true,RegisterJointRecord.recordStep,update] using ih

/-- Idle from actual damage cannot be called a restoring long-run controller,
even if it happens to be GOD under the registered economic evaluation. -/
theorem native_idle_bad {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (o : Organism n)
    (hb : o.physical i≠m.goal) (ho : o.program=m.goal) :
    ∀ᵐ rs ∂recordPathLaw i noise m epsilon he (astPolicy (.emit none)) ⟨0,o.physical,o⟩,
      ∀t : ℕ,¬Legitimate i (rs t).transaction.parentAfter :=by
  rw [native_record_law]
  have hS : MeasurableSet {rs : ℕ→ModeRecord n | ∀t : ℕ,¬Legitimate i (rs t).transaction.parentAfter} :=by
    have hE : {rs : ℕ→ModeRecord n | ∀t : ℕ,¬Legitimate i (rs t).transaction.parentAfter}=
        ⋂t : ℕ,{rs | ¬Legitimate i (rs t).transaction.parentAfter} :=by ext rs;simp
    rw [hE]
    exact MeasurableSet.iInter fun t=>(show MeasurableSet {r : ModeRecord n | ¬Legitimate i r.transaction.parentAfter} from trivial).preimage (measurable_pi_apply t)
  apply (ae_map_iff (RegisterSemanticInstructionInfinite.measurable_recordPath i m (.emit none) o).aemeasurable hS).2
  apply ae_of_all
  intro w t
  have hp:=RegisterSemanticInstructionInfinite.actual_protected_program i m (.emit none) o w (t+1)
  change ¬Legitimate i (RegisterSemanticInstructionInfinite.parentAt i m (.emit none) o w (t+1))
  rw [Legitimate,hp,ho]
  exact idle_stays_bad i m o hb w (t+1)

/-- Existing original all-prefix/prepay and retained-parent consumers now
share ONE actual joint event with the source-derived native life conclusion. -/
theorem funded_joint_repair_long_run {n N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (price width d u : ℚ) (o : Organism n) (ho : o.program=m.goal)
    (cap g initial : ℝ) (hcap : (m.writeCost : ℝ)≤cap) (hg : cap≤g) (hi : 0 ≤ initial) :
    ∀ᵐ z ∂jointLaw (N:=N) i noise m epsilon he price width d u o,
      RegisterFaultDynamicProbeResource.wholeRecords i m o z∈SameParentTrace o.history ∧
      UEOT.V3.Compression.Objecthood.ResourceClosure.ResourceViable initial (fun _=>g)
        (fun t=>(RegisterFaultDynamicProbeResource.wholeRecords i m o z t).transaction.expenditure) ∧
      (∀t,(RegisterFaultDynamicProbeResource.wholeRecords i m o z t).transaction.expenditure≤
        RegisterFaultDynamicProbeResource.balance i m o initial g z t+g) ∧
      ∀b : Bool,classify price width d u (sourceData m width z.1)=.repair b→
        z.2∈frequency i epsilon ∧
        RegisterSemanticInstructionInfinite.projectPath i z.2∈frequency 0 epsilon ∧
        (epsilon<1→∀N : ℕ,∃t≥N,Legitimate i (z.2 t).transaction.parentAfter) ∧
        (0<epsilon→¬∃N : ℕ,∀t≥N,Legitimate i (z.2 t).transaction.parentAfter) :=by
  filter_upwards [funded_joint_same_parent (N:=N) i noise m epsilon he price width d u o cap g initial hcap hg hi,
    actual_joint_repair_long_run (N:=N) i noise m epsilon he price width d u o ho] with z hfund hlife
  exact ⟨hfund.1,hfund.2.1,hfund.2.2,hlife⟩

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicProbeNativeHomeostasis
