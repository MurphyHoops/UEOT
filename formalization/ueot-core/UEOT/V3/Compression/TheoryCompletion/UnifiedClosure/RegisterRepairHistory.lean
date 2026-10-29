import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterRepairSource
import UEOT.V3.Compression.TheoryCompletion.AutopoiesisClosure

/-! # Actual repair/birth histories and the finite-individual obstruction
The history channel records actual birth instructions. Repair and damage do
not append births. Journal observation is an additional declared information
channel, not something inferred from unlabelled physical dynamics.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterRepairHistory
open Set MeasureTheory Filter Topology
open UEOT.V3.Compression.TheoryCompletion
open UEOT.V3.Compression.TheoryCompletion.InverseObjecthood
open RegisterRepairSource

/-- Finite permanent individual lists cannot support a normalized reproductive
channel whose every positive edge strictly advances true generation. This is
an additional-history boundary, not a contradiction in the old P8 interface. -/
theorem no_finite_normalized_strict_birth
    {O : Type*} [Fintype O] [Nonempty O]
    (generation : O → ℕ) (K : O → O → ℝ)
    (hg : ∀ p c, 0 < K p c → generation p < generation c)
    (hrow : ∀ p, ∑ c, K p c = 1) : False := by
  classical
  obtain ⟨p, _, hmax⟩ := Finset.exists_max_image Finset.univ generation Finset.univ_nonempty
  have hn : ∀ c, K p c ≤ 0 := by
    intro c
    by_contra h
    exact (not_lt_of_ge (hmax c (Finset.mem_univ c))) (hg p c (lt_of_not_ge h))
  have hs : ∑ c, K p c ≤ 0 := Finset.sum_nonpos fun c _ => hn c
  rw [hrow] at hs
  norm_num at hs

structure Organism (n : ℕ) where
  history : List Bool
  physical : State n
  program : Bool

/-- Repair runs the already-verified instruction interpreter. -/
def repairEvent {n : ℕ} (i : Fin n) (o : Organism n) : Organism n :=
  { o with physical := update i o.physical ((substrate i).execute o.program o.physical) }

/-- A birth appends its actual event label and literally copies the source
program. This is one lineage, not a population frequency equation. -/
def birthEvent {n : ℕ} (i : Fin n) (label : Bool) (o : Organism n) : Organism n :=
  { repairEvent i o with history := o.history ++ [label] }

def lineage {n : ℕ} (i : Fin n) : LineageSemantics (Organism n) (List Bool) where
  identity := Organism.history
  parentOf := fun p c => ∃ label, c = birthEvent i label p

@[simp] theorem repair_same_object {n : ℕ} (i : Fin n) (o : Organism n) :
    (lineage i).SameObject (repairEvent i o) o := rfl

@[simp] theorem birth_copies_program {n : ℕ} (i : Fin n) (label : Bool) (o : Organism n) :
    (birthEvent i label o).program = o.program := rfl

theorem birth_is_distinct_offspring {n : ℕ} (i : Fin n) (label : Bool) (o : Organism n) :
    (lineage i).OffspringOf o (birthEvent i label o) := by
  refine ⟨⟨label, rfl⟩, ?_⟩
  intro h
  have hl := congrArg List.length h
  simp [lineage, birthEvent] at hl

noncomputable def birthLaw {n : ℕ} (i : Fin n) (noise : PMF Bool)
    (o : Organism n) : PMF (Organism n) := noise.map (fun label => birthEvent i label o)

theorem birthLaw_supported_offspring {n : ℕ} (i : Fin n) (noise : PMF Bool)
    (o c : Organism n) (hc : c ∈ (birthLaw i noise o).support) :
    (lineage i).OffspringOf o c ∧ c.program = o.program := by
  obtain ⟨label, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hc
  exact ⟨birth_is_distinct_offspring i label o, rfl⟩

/-- History generation is the literal number of executed birth events. -/
theorem actual_birth_increases_generation {n : ℕ} (i : Fin n) (noise : PMF Bool)
    (o c : Organism n) (hc : c ∈ (birthLaw i noise o).support) :
    o.history.length < c.history.length := by
  obtain ⟨label, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hc
  simp [birthEvent]

/-- An actual repair reaches its program's target even after arbitrary damage. -/
theorem repair_reaches_target {n : ℕ} (i : Fin n) (o : Organism n) :
    (repairEvent i o).physical ∈ target i o.program := by
  simp only [repairEvent, execute_compiled]
  by_cases h : o.physical i = o.program <;> simp [h, update, target]

/-- If the physical state is already legitimate, a birth and its parent have
identical unlabelled physical/program records but different histories. The
previous information no-go is reused on these actual source outputs. -/
theorem unlabelled_record_cannot_recover_history {n : ℕ} (i : Fin n)
    (o : Organism n) (label : Bool) (hx : o.physical ∈ target i o.program) :
    ¬ ∃ decode : State n × Bool → List Bool,
      decode (o.physical, o.program) = o.history ∧
      decode ((birthEvent i label o).physical, (birthEvent i label o).program) =
        (birthEvent i label o).history := by
  have hp : (birthEvent i label o).physical = o.physical := by
    change o.physical i = o.program at hx
    simp [birthEvent, repairEvent, execute_compiled, hx, update]
  have hn : o.history ≠ (birthEvent i label o).history := by
    intro h
    have hl := congrArg List.length h
    simp [birthEvent] at hl
  simpa only [hp, birth_copies_program, PhysicalOnlyProgramSynthesizer] using
    (no_physicalOnly_synthesizer_for_distinct_sources (o.physical, o.program) hn)

inductive Event (n : ℕ) where
  | repair
  | damage : State n → Event n
  | birth : Bool → Event n

def step {n : ℕ} (i : Fin n) : Event n → Organism n → Organism n
  | .repair, o => repairEvent i o
  | .damage x, o => { o with physical := x }
  | .birth label, o => birthEvent i label o

def replay {n : ℕ} (i : Fin n) (o : Organism n) (log : List (Event n)) : Organism n :=
  log.foldl (fun s e => step i e s) o

def birthLabels {n : ℕ} (log : List (Event n)) : List Bool :=
  log.filterMap (fun e => match e with | .birth b => some b | _ => none)

/-- Provenance is derived by executing the history, not attached by an
independent same-parent certificate. -/
theorem replay_history {n : ℕ} (i : Fin n) (o : Organism n) (log : List (Event n)) :
    (replay i o log).history = o.history ++ birthLabels log := by
  induction log generalizing o with
  | nil => simp [replay, birthLabels]
  | cons e log ih =>
      change (replay i (step i e o) log).history = _
      rw [ih]
      cases e <;> simp [step, repairEvent, birthEvent, birthLabels, List.append_assoc]

/-- Observation classes retain the actual birth journal, while allowing
arbitrary repair/damage episodes and physical differences between candidates. -/
def journalClass (n : ℕ) : Setoid (List (Event n)) := Setoid.ker birthLabels

def actualParent {n : ℕ} (i : Fin n) (o : Organism n) (log : List (Event n)) : List Bool :=
  (replay i o log).history

/-- The old independent parent bridge now follows from interpreter semantics
and the declared journal observations. -/
theorem journal_parent_bridge {n : ℕ} (i : Fin n) (o : Organism n) :
    ObjectClassParentBridge (journalClass n) (actualParent i o) where
  parent_eq_of_class := by
    intro a b hab
    change birthLabels a = birthLabels b at hab
    simp [actualParent, replay_history, hab]

/-- Actual P12 discovery consumer. Statistical recovery of the declared raw
journal class is still a contract; the parent interpretation bridge is proved.
This assumes observation access to births, not discovery from unlabelled P. -/
theorem journal_discovery_consumes_p12
    {n : ℕ} (i : Fin n) (o : Organism n)
    {Omega : ℕ → Type*} [∀ k, MeasurableSpace (Omega k)]
    (C : UEOT.V3.Compression.TheoryCompletion.StatisticalConsistency.ChangingSampleEventContract Omega)
    (truth : List (Event n)) (estimate : ∀ k, Omega k → List (Event n))
    (hgood : ∀ k w, w ∈ C.good k → birthLabels (estimate k w) = birthLabels truth) :
    let D := objectClassDiscoveryContract_of_goodEvent C (fun _ => True)
      (journalClass n) truth estimate trivial (fun _ _ => trivial) hgood
    Tendsto (fun k => (D.mu k).real
      {w | actualParent i o (D.estimate k w) ≠ actualParent i o truth}) atTop (𝓝 0) := by
  dsimp only
  exact p12_discovered_parent_tendsto_lifecycleParent
    (objectClassDiscoveryContract_of_goodEvent C (fun _ => True)
      (journalClass n) truth estimate trivial (fun _ _ => trivial) hgood)
    (actualParent i o) (journal_parent_bridge i o) (actualParent i o truth) rfl

/-- Corrected population interface: finite parent TYPES and offspring event
labels index a one-generation channel. The individual history objects themselves
are not forced into a finite permanently reproductive set. Fertility intensities
remain an explicit input here, not inferred from journal access. -/
theorem actual_birth_price_bridge {I : Type*} [Fintype I]
    {n : ℕ} (i : Fin n) (parents : I → Organism n) (noise : I → PMF Bool)
    (p fertility z : I → ℝ) (z' : Bool → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j = 1)
    (hb : ∀ j, 0 ≤ fertility j)
    (hbar : 0 < UEOT.V3.EvolutionPrice.weightedMean p fertility) :
    let K := fun j label => (noise j label).toReal
    UEOT.V3.EvolutionPrice.offspringTraitMean
        (UEOT.V3.EvolutionPrice.nextFrequency p fertility K) z' -
        UEOT.V3.EvolutionPrice.weightedMean p z =
      UEOT.V3.EvolutionPrice.weightedCov p fertility z /
          UEOT.V3.EvolutionPrice.weightedMean p fertility +
        UEOT.V3.EvolutionPrice.weightedMean p
          (fun j => fertility j * (UEOT.V3.EvolutionPrice.transmittedTrait K z' j - z j)) /
          UEOT.V3.EvolutionPrice.weightedMean p fertility
    ∧ (∀ j label, 0 < K j label →
      birthEvent i label (parents j) ∈ (birthLaw i (noise j) (parents j)).support ∧
      (lineage i).OffspringOf (parents j) (birthEvent i label (parents j)) ∧
      (birthEvent i label (parents j)).program = (parents j).program) := by
  dsimp only
  constructor
  · apply UEOT.V3.EvolutionPrice.p_evo_01 p fertility z
      (fun j label => (noise j label).toReal) z' hp hpsum hb
      (fun _ _ => ENNReal.toReal_nonneg) _ hbar
    intro j
    have h := congrArg ENNReal.toReal (PMF.tsum_coe (noise j))
    rw [tsum_fintype, ENNReal.toReal_sum (fun label _ => PMF.apply_ne_top _ label)] at h
    simpa using h
  · intro j label hpos
    refine ⟨?_, birth_is_distinct_offspring i label (parents j), rfl⟩
    apply (PMF.mem_support_map_iff _ _ _).mpr
    refine ⟨label, ?_, rfl⟩
    exact (PMF.mem_support_iff _ _).mpr (by
      intro hz
      simp [hz] at hpos)

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterRepairHistory
