import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterOwnProgramPopulation
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterPopulationJournalLearning

/-!
Original commitment: actual mixed-program copying/maintenance/Price and P12 parent learning must use one compatible source.
Existing premise: own-program population supplies actual ID/parent functionality; noisy-read P12 was bound to the old fixed-goal run.
Premise reduced: derive original P12 and finite risk for the SAME own-program execution using the existing product/majority learner.
Models: NEW own-program-fault environment and separately declared noisy marked-journal read permission; old sources/data stay unchanged.
Consumers: original P12, same three-founder/two-type/paid-repair episode, inherited own P5/Price and optional local child funding.

Every lookup still computes the own protected target, with no new organism
operation/reset/install. The extra READ channel is exactly the previous finite
noisy-journal experiment: eta<1/2, arbitrary unknown confuser on this episode's
finite event registry, fixed complete N reads. select sees only the registry,
key/readouts and fixed fallback; truth/eta/Good never enter its inputs. Failed
births (None) remain one observation class; their parent=None does not identify
the attempted actor. This is ancestry from a marked journal, not bare physics.
No new sampler, thresholds, actual data, global optimum or population funding
claim is introduced. Original local P5/Price/resource conditions are retained.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterOwnProgramJournalLearning
open MeasureTheory ProbabilityTheory Filter Topology
open UEOT.V3.Compression.TheoryCompletion
open UEOT.V3.Compression.TheoryCompletion.InverseObjecthood
open RegisterRepairSource RegisterRepairHistory
open RegisterPopulationHistorySource (Store Request)
open RegisterPopulationJournalLearning
noncomputable section

/-- Actual own-program journal classes, with failure None retained. -/
def childJournalClass {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (es : List Request) : Setoid (Fin es.length) :=
  Setoid.ker (RegisterOwnProgramPopulation.observedChildID i c s es)

/-- Functionality comes from the actual serialized allocator, not an added
parent/unique-ID field or an independent genealogy function. -/
theorem child_journal_parent_bridge {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (es : List Request) :
    ObjectClassParentBridge (childJournalClass i c s es) (RegisterOwnProgramPopulation.actualParent i c s es) where
  parent_eq_of_class := by
    intro a b hab
    exact RegisterOwnProgramPopulation.parent_eq_of_childID i c s es a b hab

/-- SAME own-program population, SAME executable selected event, and SAME
actual product source. All correct-flag concentration facts are reused. -/
theorem actual_parent_risk_le {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (es : List Request)
    (registry : List (Fin es.length)) (fallback truth : Fin es.length) (ht : truth ∈ registry)
    (eta : NNReal) (he : eta ≤ 1) (heta : (eta : ℝ) < 1/2) (confuser : PMF (Fin es.length)) (N : ℕ) :
    (rawLaw eta he confuser N).real {omega |
      RegisterOwnProgramPopulation.actualParent i c s es
        (select registry (RegisterOwnProgramPopulation.observedChildID i c s es) fallback
          (readout (RegisterOwnProgramPopulation.observedChildID i c s es) truth omega)) ≠
      RegisterOwnProgramPopulation.actualParent i c s es truth} ≤ Real.exp (-2 * (N : ℝ) * gap eta ^ 2) := by
  apply (measureReal_mono ?_).trans (bad_good_probability_le eta he heta confuser N)
  intro omega herr hgood
  apply herr
  exact RegisterOwnProgramPopulation.parent_eq_of_childID i c s es _ truth
    (good_selected_class registry _ fallback truth ht omega hgood)

/-- Original P12 actually consumes the actual own-program parent bridge and
existing source-derived eventContract. There is NO external hgood premise. -/
theorem actual_journal_discovery_consumes_p12 {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (es : List Request)
    (registry : List (Fin es.length)) (fallback truth : Fin es.length) (ht : truth ∈ registry)
    (eta : NNReal) (he : eta ≤ 1) (heta : (eta : ℝ) < 1/2) (confuser : PMF (Fin es.length)) :
    Tendsto (fun N => (rawLaw eta he confuser N).real {omega |
      RegisterOwnProgramPopulation.actualParent i c s es
        (select registry (RegisterOwnProgramPopulation.observedChildID i c s es) fallback
          (readout (RegisterOwnProgramPopulation.observedChildID i c s es) truth omega)) ≠
      RegisterOwnProgramPopulation.actualParent i c s es truth}) atTop (𝓝 0) := by
  let C := eventContract eta he heta confuser
  let key := RegisterOwnProgramPopulation.observedChildID i c s es
  let estimate := fun N (omega : Raw (Fin es.length) N) => select registry key fallback (readout key truth omega)
  have hgood : ∀ N omega, omega ∈ C.good N → childJournalClass i c s es (estimate N omega) truth :=
    fun N omega hg => good_selected_class registry key fallback truth ht omega hg
  let D := objectClassDiscoveryContract_of_goodEvent C (fun _ => True)
    (childJournalClass i c s es) truth estimate trivial (fun _ _ => trivial) hgood
  exact p12_discovered_parent_tendsto_lifecycleParent D (RegisterOwnProgramPopulation.actualParent i c s es)
    (child_journal_parent_bridge i c s es) (RegisterOwnProgramPopulation.actualParent i c s es truth) rfl

/-- Successful global child IDs identify the ACTUAL event, not merely its
parent. Failure classes deliberately have no such injectivity assertion. -/
theorem good_selected_birth_event {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (es : List Request)
    (registry : List (Fin es.length)) (fallback truth : Fin es.length) (ht : truth ∈ registry)
    (d : RegisterTimestampedBirthSource.ClockedOrganism n)
    (hd : RegisterOwnProgramPopulation.childAt i c s es truth = some d)
    {N : ℕ} (omega : Raw (Fin es.length) N) (hg : omega ∈ Good (J:=Fin es.length) N) :
    select registry (RegisterOwnProgramPopulation.observedChildID i c s es) fallback
      (readout (RegisterOwnProgramPopulation.observedChildID i c s es) truth omega) = truth := by
  let chosen := select registry (RegisterOwnProgramPopulation.observedChildID i c s es) fallback
    (readout (RegisterOwnProgramPopulation.observedChildID i c s es) truth omega)
  have hclass := good_selected_class registry (RegisterOwnProgramPopulation.observedChildID i c s es)
    fallback truth ht omega hg
  change RegisterOwnProgramPopulation.observedChildID i c s es chosen = _ at hclass
  cases hc : RegisterOwnProgramPopulation.childAt i c s es chosen with
  | none => simp [RegisterOwnProgramPopulation.observedChildID,hc,hd] at hclass
  | some o =>
    simp only [RegisterOwnProgramPopulation.observedChildID,hc,hd,Option.map_some,Option.some.injEq] at hclass
    exact Fin.ext (by omega)

section SelectedMaintenance
open UEOT.V3.Compression.Objecthood
open UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
open UEOT.V3.Compression.Objecthood.JointHomeostasis
open UEOT.V3.Compression.Objecthood.OntogeneticConstruction
open UEOT.V3.ViabilityKernel
open RegisterFaultSource
variable {n : ℕ} [MeasurableSpace (State n)] [MeasurableSingletonClass (State n)]

/-- Common learner/P5 consumer: on derived Good the returned actual event is
this actual born child, and the SAME child enters its own original maintenance
system. The failure-parent convention is not mistaken for an actual child. -/
theorem selected_actual_child_own_p5 (i : Fin n) (c : NNReal) (s : Store n) (es : List Request)
    (registry : List (Fin es.length)) (fallback truth : Fin es.length) (ht : truth ∈ registry)
    (d : RegisterTimestampedBirthSource.ClockedOrganism n)
    (hd : RegisterOwnProgramPopulation.childAt i c s es truth = some d)
    {N : ℕ} (omega : Raw (Fin es.length) N) (hg : omega ∈ Good (J:=Fin es.length) N)
    (epsilon : NNReal) (he : epsilon ≤ 1) :
    let b := d.organism.program
    let seed : OntogeneticSeed (State n) Bool := ⟨d.organism.physical,b⟩
    let S := finiteJointRecurrentHomeostasisSystem
      (physical i) (target i b) (target_fixed i b) (certificate i b)
      (substrate i) codec b (compiled_dynamics_implements i b)
      (fault i) epsilon he (actual_fault_envelope i b)
    select registry (RegisterOwnProgramPopulation.observedChildID i c s es) fallback
      (readout (RegisterOwnProgramPopulation.observedChildID i c s es) truth omega) = truth ∧
    StaysIn (PMF.pure (assembleRepairOrganization (substrate i) codec seed)) S.carrier :=
  ⟨good_selected_birth_event i c s es registry fallback truth ht d hd omega hg,
   RegisterOwnProgramPopulation.actual_child_enters_own_maintenance i c
     (RegisterOwnProgramPopulation.storeBefore i c s es truth) (RegisterPopulationHistorySource.requestAt es truth)
     d hd epsilon he⟩
end SelectedMaintenance

/-- Literal SAME three-founder cohort followed by its actual paid repair. -/
def witnessEpisode : List Request :=
  RegisterOwnProgramPopulation.witnessEpisode ++ [RegisterOwnProgramPopulation.witnessRepair]
@[simp] theorem witnessEpisode_length : witnessEpisode.length = 4 := by
  simp [witnessEpisode,RegisterOwnProgramPopulation.witnessEpisode,RegisterPopulationTypePrice.cohortRequests,
    RegisterOwnProgramPopulation.witnessInitial,RegisterOwnProgramPopulation.witnessFounders,
    RegisterPopulationHistorySource.founders]
instance : NeZero witnessEpisode.length := ⟨by rw [witnessEpisode_length]; decide⟩
abbrev WitnessEvent := Fin witnessEpisode.length

def witnessKey : WitnessEvent → Observation :=
  RegisterOwnProgramPopulation.observedChildID (0 : Fin 1) 1 RegisterOwnProgramPopulation.witnessInitial witnessEpisode

def witnessParent : WitnessEvent → Observation :=
  RegisterOwnProgramPopulation.actualParent (0 : Fin 1) 1 RegisterOwnProgramPopulation.witnessInitial witnessEpisode

/-- Actual children from both protected types share one learning registry;
failed tick 1 remains None and the later paid-repair child is retained. -/
theorem two_type_key_parent_witness :
    witnessKey 0 = some 3 ∧ witnessKey 1 = none ∧ witnessKey 2 = some 5 ∧ witnessKey 3 = some 6 ∧
    witnessParent 0 = some 0 ∧ witnessParent 1 = none ∧ witnessParent 2 = some 2 ∧ witnessParent 3 = some 1 := by
  norm_num [witnessKey,witnessParent,witnessEpisode,
    RegisterOwnProgramPopulation.observedChildID,RegisterOwnProgramPopulation.actualParent,
    RegisterOwnProgramPopulation.childAt,RegisterOwnProgramPopulation.storeBefore,RegisterOwnProgramPopulation.run,
    RegisterOwnProgramPopulation.next,RegisterOwnProgramPopulation.child,RegisterOwnProgramPopulation.mechanism,
    RegisterOwnProgramPopulation.witnessInitial,RegisterOwnProgramPopulation.witnessFounders,
    RegisterOwnProgramPopulation.witnessEpisode,RegisterOwnProgramPopulation.witnessAfterCohort,
    RegisterOwnProgramPopulation.witnessRepair,RegisterOwnProgramPopulation.witnessActions,
    RegisterOwnProgramPopulation.witnessModes,RegisterOwnProgramPopulation.compiledRequest,
    RegisterPopulationTypePrice.cohortRequests,RegisterPopulationTypePrice.request,
    RegisterPopulationHistorySource.founders,RegisterPopulationHistorySource.requestAt,
    RegisterPopulationHistorySource.next,RegisterPopulationHistorySource.transaction,
    RegisterPopulationHistorySource.lookup,RegisterPopulationHistorySource.child,
    RegisterTimestampedBirthSource.step,RegisterFaultJointRecord.modeRecordStep,RegisterJointRecord.recordStep,
    birthEvent,repairEvent,RegisterRepairSource.execute_compiled,RegisterRepairSource.update,List.range_succ]

private theorem quarter_le_one : (1/4 : NNReal) ≤ 1 := by
  exact_mod_cast (by norm_num : (1/4 : ℝ) ≤ 1)

/-- Uniform over arbitrary unknown confusers for this SAME episode. N=0 gives
the honest bound 1; no repeated sampling or omitted failed read is used. -/
theorem two_type_parent_risk_le (confuser : PMF WitnessEvent) (truth fallback : WitnessEvent) (N : ℕ) :
    (rawLaw (1/4) quarter_le_one confuser N).real {omega |
      witnessParent (select (List.finRange witnessEpisode.length) witnessKey fallback (readout witnessKey truth omega)) ≠
        witnessParent truth} ≤ Real.exp (-(N : ℝ)/8) := by
  have h := actual_parent_risk_le (0 : Fin 1) 1 RegisterOwnProgramPopulation.witnessInitial witnessEpisode
    (List.finRange witnessEpisode.length) fallback truth (List.mem_finRange truth)
    (1/4) quarter_le_one (by norm_num) confuser N
  calc
    _ ≤ Real.exp (-2 * (N : ℝ) * gap (1/4) ^ 2) := h
    _ = _ := by congr 1; norm_num [gap]; ring

theorem two_type_p12_consumer (confuser : PMF WitnessEvent) (truth fallback : WitnessEvent) :
    Tendsto (fun N => (rawLaw (1/4) quarter_le_one confuser N).real {omega |
      witnessParent (select (List.finRange witnessEpisode.length) witnessKey fallback (readout witnessKey truth omega)) ≠
        witnessParent truth}) atTop (𝓝 0) :=
  actual_journal_discovery_consumes_p12 (0 : Fin 1) 1 RegisterOwnProgramPopulation.witnessInitial witnessEpisode
    (List.finRange witnessEpisode.length) fallback truth (List.mem_finRange truth)
    (1/4) quarter_le_one (by norm_num) confuser

/-- The existing information boundary transfers to the SAME own-program
journal. A fixed-budget readout-only deterministic estimator cannot distinguish
these two actual parents at half noise with the allowed swapped confusers. -/
theorem two_type_half_noise_obstruction (N : ℕ) (estimate : Data N → Observation) :
    observedLaw (1/2) (by norm_num) (PMF.pure (2 : WitnessEvent)) witnessKey 0 N =
      observedLaw (1/2) (by norm_num) (PMF.pure (0 : WitnessEvent)) witnessKey 2 N ∧
    witnessParent 0 ≠ witnessParent 2 ∧
    ((1/2 : ℝ) ≤ (observedLaw (1/2) (by norm_num) (PMF.pure (2 : WitnessEvent)) witnessKey 0 N).real
        {data | estimate data ≠ witnessParent 0} ∨
      (1/2 : ℝ) ≤ (observedLaw (1/2) (by norm_num) (PMF.pure (0 : WitnessEvent)) witnessKey 2 N).real
        {data | estimate data ≠ witnessParent 2}) := by
  have hp : witnessParent 0 ≠ witnessParent 2 := by
    rw [two_type_key_parent_witness.2.2.2.2.1,two_type_key_parent_witness.2.2.2.2.2.2.1]
    decide
  refine ⟨half_noise_observed_swap witnessKey 0 2 N,hp,?_⟩
  have h := half_noise_parent_risk_sum witnessKey 0 2 (witnessParent 0) (witnessParent 2) hp N estimate
  by_cases ha : (1/2 : ℝ) ≤ (observedLaw (1/2) (by norm_num) (PMF.pure (2 : WitnessEvent)) witnessKey 0 N).real
      {data | estimate data ≠ witnessParent 0}
  · exact Or.inl ha
  · right; linarith

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterOwnProgramJournalLearning
