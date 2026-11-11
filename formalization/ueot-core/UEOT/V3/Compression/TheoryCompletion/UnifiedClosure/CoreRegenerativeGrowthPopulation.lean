import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthClassification
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeControlPopulation
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeRepair

/-!
# Exact growth classification on the existing observed-history population law

The state, request kernel, physical generation, public history, resource ledger,
and hereditary program are the existing ones. Only the positive weighting used
in their proof is generalized. An arbitrary `Policy` still permits joint real
request randomization and all permitted public history.

`HasExpectedGrowth` means two-sided constant multiples of an exponential for
all census times. It does not assert population optimality at every finite
deadline or almost-sure lineage survival.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthPopulation

noncomputable section
open scoped BigOperators
open CoreRegenerativeSource CoreRegenerativePopulation CoreRegenerativeQuotient
open CoreRegenerativeControlPopulation CoreRegenerativeGrowthClassification
open SourceCohortFeedback FiniteSourceGrowthControl
open UEOT.V3.EvolutionPerronGrowth (rowDot rowMass natRow)

def weightedPotential (r : Kind → ℝ) (xs : List Member) : ℝ :=
  rowDot (natRow (censusCount xs)) r

@[simp] theorem weightedPotential_nil (r : Kind → ℝ) : weightedPotential r [] = 0 := by
  simp [weightedPotential, rowDot, natRow, censusCount]

theorem weightedPotential_cons (r : Kind → ℝ) (m : Member) (xs : List Member) :
    weightedPotential r (m :: xs) = r (diagnostic m.body) + weightedPotential r xs := by
  simp [weightedPotential, rowDot, natRow, censusCount, add_mul,
    Finset.sum_add_distrib, ite_mul]

theorem weightedPotential_append (r : Kind → ℝ) (xs ys : List Member) :
    weightedPotential r (xs ++ ys) = weightedPotential r xs + weightedPotential r ys := by
  induction xs with
  | nil => simp
  | cons m xs ih => simp only [List.cons_append, weightedPotential_cons, ih, add_assoc]

theorem weightedPotential_actualStep (r : Kind → ℝ) (t : ℕ) (old : Member)
    (a : Action) (z : Noise) :
    weightedPotential r (actualStep t old a z) =
      ∑ j, (resultCount (step old.body a z) j : ℝ) * r j := by
  simp only [weightedPotential, actualStep, rowDot, natRow, liftResult_count]

theorem weighted_member_expected (p : Parameters) (r : Kind → ℝ) (t : ℕ)
    (old : Member) (a : Action) (hc : Canonical old.body) :
    expect (noiseWeight p) (fun z => weightedPotential r (actualStep t old a z)) =
      ∑ j, realizedRow p (diagnostic old.body) a j * r j := by
  obtain ⟨theta, i, tag, hx⟩ := hc
  simp only [expect, weightedPotential_actualStep, hx, diagnostic_programBody]
  rw [record_value_eq_row_value]
  change (∑ j, realizedMean p theta i tag a j * r j) = _
  simp_rw [realizedMean_eq]

/-- Public stationary requests are a special case of the unchanged full policy class. -/
def stationaryRequests (a : Kind → Action) : (xs : List Member) → RequestWord xs.length
  | [] => PUnit.unit
  | m :: xs => (a (diagnostic m.body), stationaryRequests a xs)

def stationaryObservedRequests (a : Kind → Action) :
    (n : ℕ) → ObservationWord n → RequestWord n
  | 0, _ => PUnit.unit
  | n + 1, o => (a (diagnostic (observedBody o.1)), stationaryObservedRequests a n o.2)

theorem stationaryObservedRequests_observations (a : Kind → Action) (xs : List Member) :
    stationaryObservedRequests a xs.length (observations xs) = stationaryRequests a xs := by
  induction xs with
  | nil => rfl
  | cons old xs ih =>
    simp [observations, stationaryObservedRequests, stationaryRequests, ih]
    rfl

def stationaryPolicy (a : Kind → Action) : Policy := by
  classical
  refine ⟨fun n _ obs w => if w = stationaryObservedRequests a n obs then 1 else 0, ?_, ?_⟩
  · intro n hist obs w
    split_ifs <;> norm_num
  · intro n hist obs
    simp

theorem probability_branchWeight_nonneg (p : Parameters) (hp : ProbabilityValid p)
    (K : Policy) (t : ℕ) (s : State) (w : Branch s) :
    0 ≤ branchWeight p K t s w :=
  mul_nonneg (K.nonneg _ _ _ _)
    (iidWeight_nonneg (noiseWeight p)
      (fun z => (CoreRegenerativeGrowthClassification.noiseWeight_pos p hp z).le) _ _)

theorem weighted_generation_bound (p : Parameters) (r : Kind → ℝ) (rho : ℝ)
    (hb : ∀ i a, (∑ j, realizedRow p i a j * r j) ≤ rho * r i)
    (t : ℕ) (xs : List Member) (hg : GoodPopulation xs) (a : RequestWord xs.length) :
    expect (iidWeight (noiseWeight p) xs.length)
      (fun z => weightedPotential r (generation t xs a z)) ≤ rho * weightedPotential r xs := by
  induction xs with
  | nil => simp [expect, generation]
  | cons old xs ih =>
    have hh : Canonical old.body := hg old (by simp)
    have ht : GoodPopulation xs := fun m hm => hg m (by simp [hm])
    change Action × Samples Action xs.length at a
    change expect (productWeight (noiseWeight p) (iidWeight (noiseWeight p) xs.length))
      (fun z => weightedPotential r (actualStep t old a.1 z.1 ++
        generation t xs a.2 z.2)) ≤ _
    simp_rw [weightedPotential_append]
    rw [product_expect_add (noiseWeight p) (iidWeight (noiseWeight p) xs.length)
      (fun z : Noise => weightedPotential r (actualStep t old a.1 z))
      (fun z : Samples Noise xs.length => weightedPotential r (generation t xs a.2 z)),
      iidWeight_total (noiseWeight p) (noiseWeight_sum p),
      noiseWeight_sum, mul_one, one_mul, weightedPotential_cons,
      weighted_member_expected p r t old a.1 hh]
    have hhead := hb (diagnostic old.body) a.1
    have htail := ih ht a.2
    nlinarith

theorem weighted_generation_eq (p : Parameters) (r : Kind → ℝ) (rho : ℝ)
    (a : Kind → Action)
    (he : ∀ i, (∑ j, realizedRow p i (a i) j * r j) = rho * r i)
    (t : ℕ) (xs : List Member) (hg : GoodPopulation xs) :
    expect (iidWeight (noiseWeight p) xs.length)
      (fun z => weightedPotential r (generation t xs (stationaryRequests a xs) z)) =
        rho * weightedPotential r xs := by
  induction xs with
  | nil => simp [expect, generation]
  | cons old xs ih =>
    have hh : Canonical old.body := hg old (by simp)
    have ht : GoodPopulation xs := fun m hm => hg m (by simp [hm])
    change expect (productWeight (noiseWeight p) (iidWeight (noiseWeight p) xs.length))
      (fun z => weightedPotential r (actualStep t old (a (diagnostic old.body)) z.1 ++
        generation t xs (stationaryRequests a xs) z.2)) = _
    simp_rw [weightedPotential_append]
    rw [product_expect_add (noiseWeight p) (iidWeight (noiseWeight p) xs.length)
      (fun z : Noise => weightedPotential r (actualStep t old (a (diagnostic old.body)) z))
      (fun z : Samples Noise xs.length => weightedPotential r
        (generation t xs (stationaryRequests a xs) z)),
      iidWeight_total (noiseWeight p) (noiseWeight_sum p), noiseWeight_sum,
      mul_one, one_mul, weighted_member_expected p r t old _ hh, he,
      ih ht, weightedPotential_cons]
    ring

theorem weighted_next_bound (p : Parameters) (r : Kind → ℝ) (rho : ℝ)
    (hb : ∀ i a, (∑ j, realizedRow p i a j * r j) ≤ rho * r i)
    (K : Policy) (t : ℕ) (s : State) :
    (∑ w, branchWeight p K t s w * weightedPotential r (next t s w).population) ≤
      rho * weightedPotential r s.population := by
  rw [branch_expect_split]
  calc
    _ ≤ ∑ a, K.kernel s.population.length s.publicHistory (observations s.population) a *
        (rho * weightedPotential r s.population) := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left
        (weighted_generation_bound p r rho hb t s.population s.good a) (K.nonneg _ _ _ a)
    _ = _ := by rw [← Finset.sum_mul, K.total, one_mul]

theorem weighted_next_eq (p : Parameters) (r : Kind → ℝ) (rho : ℝ)
    (a : Kind → Action)
    (he : ∀ i, (∑ j, realizedRow p i (a i) j * r j) = rho * r i)
    (t : ℕ) (s : State) :
    (∑ w, branchWeight p (stationaryPolicy a) t s w *
      weightedPotential r (next t s w).population) = rho * weightedPotential r s.population := by
  classical
  rw [branch_expect_split]
  simpa [stationaryPolicy, stationaryObservedRequests_observations, expect, next] using
    weighted_generation_eq p r rho a he t s.population s.good

def weightMin (r : Kind → ℝ) : ℝ := min (r false) (r true)
def weightMax (r : Kind → ℝ) : ℝ := max (r false) (r true)

theorem weightMin_pos (r : Kind → ℝ) (hr : ∀ i, 0 < r i) : 0 < weightMin r :=
  lt_min (hr false) (hr true)

theorem weightMax_pos (r : Kind → ℝ) (hr : ∀ i, 0 < r i) : 0 < weightMax r :=
  lt_of_lt_of_le (hr false) (le_max_left _ _)

theorem weight_bounds (r : Kind → ℝ) (i : Kind) : weightMin r ≤ r i ∧ r i ≤ weightMax r := by
  cases i
  · exact ⟨min_le_left _ _, le_max_left _ _⟩
  · exact ⟨min_le_right _ _, le_max_right _ _⟩

theorem weightedPotential_nonneg (r : Kind → ℝ) (hr : ∀ i, 0 < r i) (xs : List Member) :
    0 ≤ weightedPotential r xs := by
  unfold weightedPotential rowDot natRow
  exact Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hr i).le

theorem weightedPotential_pos (r : Kind → ℝ) (hr : ∀ i, 0 < r i) (xs : List Member)
    (hn : xs ≠ []) : 0 < weightedPotential r xs := by
  cases xs with
  | nil => exact False.elim (hn rfl)
  | cons old xs =>
    rw [weightedPotential_cons]
    exact add_pos_of_pos_of_nonneg (hr _) (weightedPotential_nonneg r hr xs)

theorem weighted_population_upper (p : Parameters) (hp : ProbabilityValid p)
    (r : Kind → ℝ) (hr : ∀ i, 0 < r i) (rho : ℝ) (hrho : 0 ≤ rho)
    (hb : ∀ i a, (∑ j, realizedRow p i a j * r j) ≤ rho * r i)
    (K : Policy) (initial : State) (n : ℕ) :
    populationExpectation p K initial n (fun s => (s.population.length : ℝ)) ≤
      (rho ^ n * weightedPotential r initial.population) / weightMin r := by
  have h := history_population_upper initial next (branchWeight p K)
    (probability_branchWeight_nonneg p hp K) rho hrho r (weightMin r) (weightMin_pos r hr)
    (fun i => (weight_bounds r i).1) (fun _ s => censusCount s.population)
    (weighted_next_bound p r rho hb K) n
  simpa only [populationExpectation, census_mass, weightedPotential] using h

theorem weighted_population_bounds (p : Parameters) (hp : ProbabilityValid p)
    (r : Kind → ℝ) (hr : ∀ i, 0 < r i) (rho : ℝ) (hrho : 0 ≤ rho)
    (a : Kind → Action)
    (he : ∀ i, (∑ j, realizedRow p i (a i) j * r j) = rho * r i)
    (initial : State) (n : ℕ) :
    (rho ^ n * weightedPotential r initial.population) / weightMax r ≤
      populationExpectation p (stationaryPolicy a) initial n
        (fun s => (s.population.length : ℝ)) ∧
    populationExpectation p (stationaryPolicy a) initial n
        (fun s => (s.population.length : ℝ)) ≤
      (rho ^ n * weightedPotential r initial.population) / weightMin r := by
  have h := history_population_bounds initial next (branchWeight p (stationaryPolicy a))
    (probability_branchWeight_nonneg p hp (stationaryPolicy a)) rho hrho r
    (weightMin r) (weightMax r) (weightMin_pos r hr) (weightMax_pos r hr)
    (fun i => (weight_bounds r i).1) (fun i => (weight_bounds r i).2)
    (fun _ s => censusCount s.population) (weighted_next_eq p r rho a he) n
  simpa only [populationExpectation, census_mass, weightedPotential] using h

/-- Positive two-sided exponential constants, not finite-deadline population optimality. -/
def HasExpectedGrowth (p : Parameters) (K : Policy) (initial : State) (rho : ℝ) : Prop :=
  ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧ ∀ n,
    lo * rho ^ n ≤ populationExpectation p K initial n (fun s => (s.population.length : ℝ)) ∧
    populationExpectation p K initial n (fun s => (s.population.length : ℝ)) ≤ hi * rho ^ n

theorem weighted_hasExpectedGrowth (p : Parameters) (hp : ProbabilityValid p)
    (r : Kind → ℝ) (hr : ∀ i, 0 < r i) (rho : ℝ) (hrho : 0 ≤ rho)
    (a : Kind → Action)
    (he : ∀ i, (∑ j, realizedRow p i (a i) j * r j) = rho * r i)
    (initial : State) (hn : initial.population ≠ []) :
    HasExpectedGrowth p (stationaryPolicy a) initial rho := by
  have hv := weightedPotential_pos r hr initial.population hn
  refine ⟨weightedPotential r initial.population / weightMax r,
    weightedPotential r initial.population / weightMin r,
    div_pos hv (weightMax_pos r hr), div_pos hv (weightMin_pos r hr), ?_⟩
  intro n
  simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
    weighted_population_bounds p hp r hr rho hrho a he initial n

def optimalPolicy (p : Parameters) : Policy := stationaryPolicy (optimalAction p)

/-- One common finite-time upper bound covers every original public-history policy. -/
theorem optimal_population_upper (p : Parameters) (hp : ProbabilityValid p)
    (K : Policy) (initial : State) (n : ℕ) :
    populationExpectation p K initial n (fun s => (s.population.length : ℝ)) ≤
      (optimalRate p ^ n * weightedPotential (optimalValue p) initial.population) /
        valueMin p := by
  exact weighted_population_upper p hp (optimalValue p) (optimalValue_pos p hp)
    (optimalRate p) (optimalRate_pos p).le
    (CoreRegenerativeGrowthClassification.actual_row_bound p hp) K initial n

theorem optimal_population_bounds (p : Parameters) (hp : ProbabilityValid p)
    (initial : State) (n : ℕ) :
    (optimalRate p ^ n * weightedPotential (optimalValue p) initial.population) /
        valueMax p ≤
      populationExpectation p (optimalPolicy p) initial n (fun s => (s.population.length : ℝ)) ∧
    populationExpectation p (optimalPolicy p) initial n (fun s => (s.population.length : ℝ)) ≤
      (optimalRate p ^ n * weightedPotential (optimalValue p) initial.population) /
        valueMin p := by
  exact weighted_population_bounds p hp (optimalValue p) (optimalValue_pos p hp)
    (optimalRate p) (optimalRate_pos p).le (optimalAction p) (selected_row_eq p hp) initial n

theorem optimal_hasExpectedGrowth (p : Parameters) (hp : ProbabilityValid p)
    (initial : State) (hn : initial.population ≠ []) :
    HasExpectedGrowth p (optimalPolicy p) initial (optimalRate p) :=
  weighted_hasExpectedGrowth p hp (optimalValue p) (optimalValue_pos p hp)
    (optimalRate p) (optimalRate_pos p).le (optimalAction p) (selected_row_eq p hp) initial hn

/-- The same physical public policy is used for either hereditary internal program. -/
def programPolicy (theta : Bool) : Policy := stationaryPolicy (programAction theta)

theorem program_row_equality (p : Parameters) (theta i : Bool) :
    (∑ j, realizedRow p i (programAction theta i) j * programValue p theta j) =
      growthRate p theta * programValue p theta i := by
  simp_rw [realizedRow_program]
  change (∑ j, row p (programAction theta i) j * programValue p theta j) = _
  rw [row_programValue]
  exact mul_comm _ _

theorem program_hasExpectedGrowth (p : Parameters) (hp : ProbabilityValid p)
    (theta : Bool) (initial : State) (hn : initial.population ≠ []) :
    HasExpectedGrowth p (programPolicy theta) initial (growthRate p theta) :=
  weighted_hasExpectedGrowth p hp (programValue p theta) (programValue_pos p hp theta)
    (growthRate p theta) (programRate_pos p hp theta).le (programAction theta)
    (program_row_equality p theta) initial hn

theorem program_request (theta : Bool) (old : Member) (hc : CarriesProgram theta old.body) :
    requestOf old.body = programAction theta (diagnostic old.body) := by
  obtain ⟨i, tag, hx⟩ := hc
  simp [hx]

theorem program_step_is_internal (theta : Bool) (t : ℕ) (old : Member) (z : Noise)
    (hc : CarriesProgram theta old.body) :
    actualStep t old (programAction theta (diagnostic old.body)) z =
      liftResult t old (programStep old.body z) := by
  rw [actualStep, ← program_request theta old hc, ← programStep_eq_step]

theorem program_generation_is_internal (theta : Bool) (t : ℕ) (xs : List Member)
    (hg : ProgramPopulation theta xs) (z : NoiseWord xs.length) :
    generation t xs (stationaryRequests (programAction theta) xs) z =
      internalGeneration t xs z := by
  induction xs with
  | nil => rfl
  | cons old xs ih =>
    have hh : CarriesProgram theta old.body := hg old (by simp)
    have ht : ProgramPopulation theta xs := fun m hm => hg m (by simp [hm])
    change actualStep t old (programAction theta (diagnostic old.body)) z.1 ++
      generation t xs (stationaryRequests (programAction theta) xs) z.2 = _
    rw [program_step_is_internal theta t old z.1 hh, ih ht]
    rfl

/-- Positive actual branches execute the inherited program, including paid repair.
The existing `reachable_program` theorem preserves the premise on every later census. -/
theorem programPolicy_positive_branch_is_internal (p : Parameters) (theta : Bool)
    (t : ℕ) (s : State) (w : Branch s) (hg : ProgramPopulation theta s.population)
    (hw : 0 < branchWeight p (programPolicy theta) t s w) :
    (next t s w).population = internalGeneration t s.population w.2 := by
  classical
  have ha : w.1 = stationaryRequests (programAction theta) s.population := by
    by_contra hne
    have hz : branchWeight p (programPolicy theta) t s w = 0 := by
      simp [branchWeight, productWeight, programPolicy, stationaryPolicy,
        stationaryObservedRequests_observations, hne]
    rw [hz] at hw
    exact (lt_irrefl 0) hw
  change generation t s.population w.1 w.2 = _
  rw [ha]
  exact program_generation_is_internal theta t s.population hg w.2

def founderState (index : ℕ) (theta i tag : Bool) : State := by
  refine ⟨[founder index theta i tag], [], ?_⟩
  intro m hm
  simp only [List.mem_singleton] at hm
  subst m
  exact canonical_programBody theta i tag

theorem founder_program (index : ℕ) (theta i tag : Bool) :
    ProgramPopulation theta (founderState index theta i tag).population := by
  intro m hm
  simp only [founderState, List.mem_singleton] at hm
  subst m
  exact carries_programBody theta i tag

theorem damaged_founder_hasExpectedGrowth (p : Parameters) (hp : ProbabilityValid p)
    (index : ℕ) (theta tag : Bool) :
    HasExpectedGrowth p (programPolicy theta) (founderState index theta true tag)
      (growthRate p theta) :=
  program_hasExpectedGrowth p hp theta (founderState index theta true tag)
    (by simp [founderState])

/-- Each program uses its own actual damaged code body with the original six units. -/
theorem damaged_founder_paid_repair (index : ℕ) (theta tag : Bool) (z : Noise) :
    (programStep (founder index theta true tag).body z).repairPaid = 3 ∧
    (programStep (founder index theta true tag).body z).operationPaid = 1 ∧
    (programStep (founder index theta true tag).body z).status = .executed := by
  simp [founder, program_step_executes, executedResult, programAction, operationCost]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthPopulation
