import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterOwnProgramJournalLearning

/-!
Original commitment: mixed-program actual execution and parent learning must share a COMPLETE source law.
Existing premise: the registered journal learner's bound is pointwise in an already executed population episode.
Premise reduced: consume ALL original four-draw population outcomes times the SAME full fixed-N read product.
Models: original NEW own-program-fault population, epsilon=1/4/uniform labels, plus declared independent marked-journal reads eta=1/4.
Consumers: joint actual-parent risk, vanishing risk, and the SAME selected actual born child's own P5, with failures retained.

No conditioning on witnessRaw, a successful birth, or an accepted result occurs.
The fourth request is computed from the real first-three-step store for EVERY
raw outcome. The registered read law retains all N flags/confuser draws. The
selector is exactly existing select on decoded data, actual ID registry and
fixed fallback; truth, latent flags, means and either hazard are not selector
inputs. Joint sampling independence is an explicit new read-experiment source
condition. Read costs and a whole population bank/optimum are not asserted.
P5 is claimed only on derived Good AND an actual born target; failed births,
including positive-mass all-fault episodes, remain in the complete measure.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterOwnProgramJointJournal
open Set MeasureTheory ProbabilityTheory Filter Topology
open RegisterRepairSource RegisterRepairHistory
open RegisterPopulationJournalLearning
noncomputable section

abbrev PopulationRaw := Fin 4 → Bool × Bool
abbrev Event := Fin 4
abbrev Reads (N : ℕ) := Raw Event N
abbrev JointSample (N : ℕ) := PopulationRaw × Reads N

/-- Every original raw execution has exactly four actual ticks, even on
failure. The existing episode interface is definitionally Fin 4. -/
@[simp] theorem episode_length (omega : PopulationRaw) :
    (RegisterOwnProgramPopulation.fourStepRequests omega).length = 4 := by
  simp [RegisterOwnProgramPopulation.fourStepRequests]

def key (omega : PopulationRaw) : Event → Observation :=
  RegisterOwnProgramPopulation.observedChildID (0 : Fin 1) 1
    RegisterOwnProgramPopulation.witnessInitial (RegisterOwnProgramPopulation.fourStepRequests omega)

def parent (omega : PopulationRaw) : Event → Observation :=
  RegisterOwnProgramPopulation.actualParent (0 : Fin 1) 1
    RegisterOwnProgramPopulation.witnessInitial (RegisterOwnProgramPopulation.fourStepRequests omega)

def actualChild (omega : PopulationRaw) (j : Event) : Option (RegisterTimestampedBirthSource.ClockedOrganism 1) :=
  RegisterOwnProgramPopulation.childAt (0 : Fin 1) 1
    RegisterOwnProgramPopulation.witnessInitial (RegisterOwnProgramPopulation.fourStepRequests omega) j

/-- Source/actual journal are not direct selector inputs: this is the existing
executable data-only decoder with its explicit finite key table and fallback. -/
def estimate {N : ℕ} (keyTable : Event → Observation) (fallback : Event) (data : Data N) : Event :=
  select (List.finRange 4) keyTable fallback data

/-- SAME actual channel readout followed by SAME existing decoder. -/
def returnedEvent {N : ℕ} (truth fallback : Event) (z : JointSample N) : Event :=
  estimate (key z.1) fallback (readout (key z.1) truth z.2)

private theorem quarter_le_one : (1/4 : NNReal) ≤ 1 := by
  exact_mod_cast (by norm_num : (1/4 : ℝ) ≤ 1)

/-- Literal complete population source TIMES literal complete registered read
source; no success restriction, retry, selected law or external confidence field. -/
def jointLaw (confuser : PMF Event) (N : ℕ) : Measure (JointSample N) :=
  RegisterOwnProgramPopulation.fourDrawLaw.prod (rawLaw (1/4) quarter_le_one confuser N)

instance jointLaw_probability (confuser : PMF Event) (N : ℕ) : IsProbabilityMeasure (jointLaw confuser N) := by
  unfold jointLaw
  infer_instance

/-- The full joint source keeps the original population marginal unchanged. -/
theorem jointLaw_population_marginal (confuser : PMF Event) (N : ℕ) :
    (jointLaw confuser N).map Prod.fst = RegisterOwnProgramPopulation.fourDrawLaw := by
  simp [jointLaw]

/-- Exact read-noise marginal of the joint experiment, without conditioning on
any episode or successful birth. -/
theorem joint_bad_good_probability (confuser : PMF Event) (N : ℕ) :
    (jointLaw confuser N).real {z | z.2 ∉ Good (J:=Event) N} =
      (rawLaw (1/4) quarter_le_one confuser N).real (Good (J:=Event) N)ᶜ := by
  have hset : {z : JointSample N | z.2 ∉ Good (J:=Event) N} =
      Set.univ ×ˢ (Good (J:=Event) N)ᶜ := by ext z; simp
  rw [Measure.real,jointLaw,hset,Measure.prod_prod,measure_univ,one_mul]
  rfl

/-- Uniform source-derived Good correctness even though the actual key and
parent change with the entire population raw draw. Failed events stay None. -/
theorem good_returned_parent {N : ℕ} (truth fallback : Event) (z : JointSample N)
    (hg : z.2 ∈ Good (J:=Event) N) : parent z.1 (returnedEvent truth fallback z) = parent z.1 truth := by
  exact RegisterOwnProgramPopulation.parent_eq_of_childID (0 : Fin 1) 1
    RegisterOwnProgramPopulation.witnessInitial (RegisterOwnProgramPopulation.fourStepRequests z.1) _ truth
    (good_selected_class (List.finRange 4) (key z.1) fallback truth (List.mem_finRange truth) z.2 hg)

/-- ACTUAL joint wrong-parent probability over ALL population executions and
all N registered reads. No successful-episode conditional law is substituted. -/
theorem joint_parent_risk_le (confuser : PMF Event) (truth fallback : Event) (N : ℕ) :
    (jointLaw confuser N).real {z | parent z.1 (returnedEvent truth fallback z) ≠ parent z.1 truth} ≤
      Real.exp (-(N : ℝ)/8) := by
  calc
    _ ≤ (jointLaw confuser N).real {z | z.2 ∉ Good (J:=Event) N} := by
      apply measureReal_mono
      · intro z herr hgood
        exact herr (good_returned_parent truth fallback z hgood)
      · exact measure_ne_top _ _
    _ = (rawLaw (1/4) quarter_le_one confuser N).real (Good (J:=Event) N)ᶜ := joint_bad_good_probability confuser N
    _ ≤ Real.exp (-2 * (N : ℝ) * gap (1/4) ^ 2) :=
      bad_good_probability_le (1/4) quarter_le_one (by norm_num) confuser N
    _ = _ := by congr 1; norm_num [gap]; ring

/-- Joint wrong-parent risk tends to zero, retaining the random actual target
parent(None on failed birth). This is not an unconditional birth assertion. -/
theorem joint_parent_risk_tendsto_zero (confuser : PMF Event) (truth fallback : Event) :
    Tendsto (fun N => (jointLaw confuser N).real
      {z | parent z.1 (returnedEvent truth fallback z) ≠ parent z.1 truth}) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => measureReal_nonneg) (joint_parent_risk_le confuser truth fallback)
  have h := (learningSchedule (1/4) (by norm_num)).failure_tendsto_zero
  convert h using 1
  ext N
  change Real.exp (-(N : ℝ)/8) = Real.exp (-2 * (N : ℝ) * gap (1/4) ^ 2)
  congr 1
  norm_num [gap]
  ring

/-- On Good AND an actual born target, the returned event is the SAME actual
birth. No desired child/parent association is supplied to the selector. -/
theorem good_returned_actual_child {N : ℕ} (truth fallback : Event) (z : JointSample N)
    (d : RegisterTimestampedBirthSource.ClockedOrganism 1) (hd : actualChild z.1 truth = some d)
    (hg : z.2 ∈ Good (J:=Event) N) :
    returnedEvent truth fallback z = truth ∧ actualChild z.1 (returnedEvent truth fallback z) = some d := by
  have h := RegisterOwnProgramJournalLearning.good_selected_birth_event (0 : Fin 1) 1
    RegisterOwnProgramPopulation.witnessInitial (RegisterOwnProgramPopulation.fourStepRequests z.1)
    (List.finRange 4) fallback truth (List.mem_finRange truth) d hd z.2 hg
  change returnedEvent truth fallback z = truth at h
  exact ⟨h,by rw [h]; exact hd⟩

section Maintenance
open UEOT.V3.Compression.Objecthood
open UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
open UEOT.V3.Compression.Objecthood.JointHomeostasis
open UEOT.V3.Compression.Objecthood.OntogeneticConstruction
open UEOT.V3.ViabilityKernel
open RegisterFaultSource
variable [MeasurableSpace (State 1)] [MeasurableSingletonClass (State 1)]

/-- COMMON complete-source consumer: on the derived Good event and actual
birth, the returned SAME actual child enters its own ORIGINAL P5. Hazards for
the real population birth and subsequent maintenance are both 1/4. -/
theorem selected_actual_child_own_p5 {N : ℕ} (truth fallback : Event) (z : JointSample N)
    (d : RegisterTimestampedBirthSource.ClockedOrganism 1) (hd : actualChild z.1 truth = some d)
    (hg : z.2 ∈ Good (J:=Event) N) :
    let b := d.organism.program
    let seed : OntogeneticSeed (State 1) Bool := ⟨d.organism.physical,b⟩
    let S := finiteJointRecurrentHomeostasisSystem
      (physical (0 : Fin 1)) (target 0 b) (target_fixed 0 b) (certificate 0 b)
      (substrate 0) codec b (compiled_dynamics_implements 0 b)
      (fault 0) (1/4) quarter_le_one (actual_fault_envelope 0 b)
    returnedEvent truth fallback z = truth ∧
    StaysIn (PMF.pure (assembleRepairOrganization (substrate 0) codec seed)) S.carrier :=
  RegisterOwnProgramJournalLearning.selected_actual_child_own_p5 (0 : Fin 1) 1
    RegisterOwnProgramPopulation.witnessInitial (RegisterOwnProgramPopulation.fourStepRequests z.1)
    (List.finRange 4) fallback truth (List.mem_finRange truth) d hd z.2 hg (1/4) quarter_le_one
end Maintenance

/-- Complete law also contains all-fault population histories, with no births. -/
def allFaultRaw : PopulationRaw := fun _ => (false,true)

theorem all_fault_target_not_born (truth : Event) : actualChild allFaultRaw truth = none := by
  fin_cases truth <;>
    norm_num [actualChild,allFaultRaw,RegisterOwnProgramPopulation.fourStepRequests,List.ofFn_succ,
      RegisterOwnProgramPopulation.childAt,RegisterOwnProgramPopulation.storeBefore,
      RegisterOwnProgramPopulation.run,RegisterOwnProgramPopulation.next,RegisterOwnProgramPopulation.child,
      RegisterOwnProgramPopulation.mechanism,RegisterOwnProgramPopulation.compiledRequest,
      RegisterPopulationHistorySource.next,RegisterPopulationHistorySource.child,
      RegisterPopulationHistorySource.transaction,RegisterPopulationHistorySource.lookup,RegisterPopulationHistorySource.requestAt,
      RegisterTimestampedBirthSource.step,RegisterFaultJointRecord.modeRecordStep]

theorem all_fault_positive_mass : RegisterOwnProgramPopulation.fourDrawLaw.real {allFaultRaw} = 1/4096 := by
  rw [Measure.real,RegisterOwnProgramPopulation.fourDrawLaw,Measure.pi_singleton,ENNReal.toReal_prod]
  simp_rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  norm_num [Fin.prod_univ_succ,allFaultRaw,RegisterFaultFinitePurposeProbe.primitiveLaw_apply,ENNReal.toReal_mul,
    RegisterFaultControlModel.modeLaw,UEOT.V3.FiniteDiscountedControl.FiniteProbabilityRow.ofRealRow_apply_toReal,
    RegisterFaultControlModel.modeProbability,RegisterFaultControlModel.repairChance,PMF.uniformOfFintype_apply]

/-- Original nondegenerate positive witness remains in the joint population
marginal with exactly its registered mass; no conditioning promoted it to law. -/
theorem joint_original_witness_mass (confuser : PMF Event) (N : ℕ) :
    ((jointLaw confuser N).map Prod.fst).real {RegisterOwnProgramPopulation.witnessRaw} = 27/4096 := by
  rw [jointLaw_population_marginal]
  exact RegisterOwnProgramPopulation.witness_source_mass

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterOwnProgramJointJournal
