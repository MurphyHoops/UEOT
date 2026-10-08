import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCRegisteredCausalCandidates
import Mathlib.Tactic

/-!
# N3 finite registered causal resolver executable Lean counterchecks

Three finite *fully specified, calibrated* models demonstrate all output
branches: unique, unresolved competing candidate, and model uncovered.
The source kernel is a real normalized controlled Markov process, not a
placeholder Oracle. The examples are toy software truth certificates,
NOT measurements or claims of physical identity.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

open UEOT.V3.Compression.TheoryCompletion.ScientificClosure

/-- One-state world and one action. Response after transition is always zero. -/
def candidateToyKernel : FiniteControlledStochasticKernel PUnit.{1} PUnit.{1} where
  mass := fun _ _ _ => 1
  nonneg := by intro _ _ _; norm_num
  normalized := by intro _ _; simp

/-- A perfectly precise registered C2 interval for a model score. -/
def exactToyInterval (v : ℝ) : IntervalCertificate where
  estimate := v
  statisticalRadius := 0
  driftRadius := 0
  statisticalRadius_nonneg := by norm_num
  driftRadius_nonneg := by norm_num

/-- A single false-token candidate has predicted response 0;
the true-token alternative has 3, exceeding tolerance 1. -/
def uniquelyIdentifiableToy :
    RegisteredCausalCandidateProtocol PUnit.{1} PUnit.{1} Bool PUnit.{1} where
  kernel := candidateToyKernel
  source := PUnit.unit
  action := PUnit.unit
  read := fun _ _ => 0
  prediction := fun c _ => if c then 3 else 0
  registered := Finset.univ
  causal := fun _ => True
  tolerance := 1
  interval := fun c => exactToyInterval (if c then 3 else 0)
  observed_nonempty := ⟨PUnit.unit⟩

/-- The false-token candidate is certified while the true-token alternative
is *not rejected* because its interval spans the threshold. It would be
scientifically invalid to select false despite the single certified token. -/
def unresolvedCompetingToy :
    RegisteredCausalCandidateProtocol PUnit.{1} PUnit.{1} Bool PUnit.{1} where
  kernel := candidateToyKernel
  source := PUnit.unit
  action := PUnit.unit
  read := fun _ _ => 0
  prediction := fun c _ => if c then 3 else 0
  registered := Finset.univ
  causal := fun _ => True
  tolerance := 1
  interval := fun c => if c then {
    estimate := 3
    statisticalRadius := 3
    driftRadius := 0
    statisticalRadius_nonneg := by norm_num
    driftRadius_nonneg := by norm_num
  } else exactToyInterval 0
  observed_nonempty := ⟨PUnit.unit⟩

/-- Every registered candidate mismatches the K-derived response by 3 and
is correctly rejected relative to tolerance 1. 'Uncovered' is not death. -/
def uncoveredToy :
    RegisteredCausalCandidateProtocol PUnit.{1} PUnit.{1} Bool PUnit.{1} where
  kernel := candidateToyKernel
  source := PUnit.unit
  action := PUnit.unit
  read := fun _ _ => 0
  prediction := fun _ _ => 3
  registered := Finset.univ
  causal := fun _ => True
  tolerance := 1
  interval := fun _ => exactToyInterval 3
  observed_nonempty := ⟨PUnit.unit⟩

theorem toy_unique_calibrated : uniquelyIdentifiableToy.Calibrated := by
  intro c _
  cases c <;>
    norm_num [uniquelyIdentifiableToy,
      RegisteredCausalCandidateProtocol.Calibrated,
      registeredCandidateRisk, candidateToyKernel, exactToyInterval,
      IntervalCertificate.totalRadius]

theorem toy_competing_calibrated : unresolvedCompetingToy.Calibrated := by
  intro c _
  cases c <;>
    norm_num [unresolvedCompetingToy,
      RegisteredCausalCandidateProtocol.Calibrated,
      registeredCandidateRisk, candidateToyKernel, exactToyInterval,
      IntervalCertificate.totalRadius]

theorem toy_uncovered_calibrated : uncoveredToy.Calibrated := by
  intro c _
  cases c <;>
    norm_num [uncoveredToy,
      RegisteredCausalCandidateProtocol.Calibrated,
      registeredCandidateRisk, candidateToyKernel, exactToyInterval,
      IntervalCertificate.totalRadius]

/-- A genuinely finite registered positive certification exists. -/
theorem toy_unique_result_is_exact :
    ∃ c : Bool, resolveRegisteredCandidates uniquelyIdentifiableToy = .unique c ∧
      c = false := by
  classical
  have hpossible : registeredPossible uniquelyIdentifiableToy = {false} := by
    ext c
    cases c <;>
      norm_num [registeredPossible, uniquelyIdentifiableToy, decideAt,
        exactToyInterval, IntervalCertificate.upper,
        IntervalCertificate.lower, IntervalCertificate.totalRadius] <;> decide
  have hcert : decideAt (uniquelyIdentifiableToy.interval false)
      uniquelyIdentifiableToy.tolerance = .certified := by
    norm_num [uniquelyIdentifiableToy, decideAt, exactToyInterval,
      IntervalCertificate.upper, IntervalCertificate.totalRadius]
  have hsome : ∃ c : Bool,
      registeredPossible uniquelyIdentifiableToy = {c} ∧
      decideAt (uniquelyIdentifiableToy.interval c)
        uniquelyIdentifiableToy.tolerance = .certified :=
    ⟨false, hpossible, hcert⟩
  unfold resolveRegisteredCandidates
  simp only [dif_pos hsome]
  let c := Classical.choose hsome
  refine ⟨c, rfl, ?_⟩
  have hc := (Classical.choose_spec hsome).1
  have hm : false ∈ registeredPossible uniquelyIdentifiableToy :=
    (Finset.subset_of_eq hpossible.symm) (Finset.mem_singleton_self _)
  have hh : false ∈ ({c} : Finset Bool) :=
    (Finset.subset_of_eq hc) hm
  exact (Finset.mem_singleton.mp hh).symm

theorem toy_competing_must_abstain :
    resolveRegisteredCandidates unresolvedCompetingToy = .ambiguous := by
  classical
  have hfalse : false ∈ registeredPossible unresolvedCompetingToy := by
    norm_num [registeredPossible, unresolvedCompetingToy, decideAt,
      exactToyInterval, IntervalCertificate.upper,
      IntervalCertificate.lower, IntervalCertificate.totalRadius] <;> decide
  have htrue : true ∈ registeredPossible unresolvedCompetingToy := by
    norm_num [registeredPossible, unresolvedCompetingToy, decideAt,
      exactToyInterval, IntervalCertificate.upper,
      IntervalCertificate.lower, IntervalCertificate.totalRadius] <;> decide
  exact two_possible_candidates_force_ambiguity unresolvedCompetingToy
    hfalse htrue Bool.false_ne_true

theorem toy_all_rejected_means_uncovered :
    resolveRegisteredCandidates uncoveredToy = .uncovered := by
  classical
  have hempty : registeredPossible uncoveredToy = ∅ := by
    ext c
    cases c <;>
      norm_num [registeredPossible, uncoveredToy, decideAt,
        exactToyInterval, IntervalCertificate.upper,
        IntervalCertificate.lower, IntervalCertificate.totalRadius]
  have hnone : ¬ ∃ c : Bool,
      registeredPossible uncoveredToy = {c} ∧
      decideAt (uncoveredToy.interval c) uncoveredToy.tolerance = .certified := by
    rintro ⟨c, hc, _⟩
    have hmem : c ∈ registeredPossible uncoveredToy :=
      (Finset.subset_of_eq hc.symm) (Finset.mem_singleton_self _)
    rw [hempty] at hmem
    simpa [hempty] using hmem
  simp [resolveRegisteredCandidates, hnone, hempty]

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
