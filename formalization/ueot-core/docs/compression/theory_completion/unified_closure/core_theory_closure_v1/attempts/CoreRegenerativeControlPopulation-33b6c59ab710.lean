import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteSourceGrowthControl
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativePopulation
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeQuotient

/-!
# Full observed-history control of the actual regenerative population

This module runs `CoreRegenerativePopulation.actualStep` once for each old
member.  Its output list, with original identities, parent pointers, ages and
ancestry, becomes the next census.  Requests are an arbitrary joint real kernel
on the whole finite current population.  Current world atoms are sampled only
after requests; the controller interface receives the existing tag-free physical
observation and its public receipt history, never the audit state.

The weighted conditional expectation is derived from actual `step` records.
No conditional mean, fitness, success, or optimality premise is a source field.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeControlPopulation

noncomputable section
open scoped BigOperators
open CoreRegenerativeSource CoreRegenerativePopulation CoreRegenerativeQuotient
open SourceCohortFeedback FiniteSourceGrowthControl FiniteSourceGrowthControl.SourceConsumer
open UEOT.V3.EvolutionPerronGrowth (rowDot rowMass natRow)

def Canonical (x : Body) : Prop := ∃ theta i tag, x = programBody theta i tag

@[simp] theorem canonical_programBody (theta i tag : Bool) :
    Canonical (programBody theta i tag) := ⟨theta, i, tag, rfl⟩

def GoodPopulation (xs : List Member) : Prop := ∀ m ∈ xs, Canonical m.body

theorem step_outputs_canonical (theta i tag : Bool) (a : Action) (z : Noise) :
    (∀ b ∈ (step (programBody theta i tag) a z).retained.toList, Canonical b) ∧
    (∀ b ∈ (step (programBody theta i tag) a z).newborn.toList, Canonical b) := by
  by_cases hs : a = .stop
  · subst a
    simp [step]
  · by_cases he : canExecute (programBody theta i tag) a = true
    · cases hr : retains a z <;> cases hb : births a z <;>
        simp [step, hs, he, executedResult, hr, hb, copied_code_faithful]
    · have hf : canExecute (programBody theta i tag) a = false := Bool.eq_false_iff.mpr he
      simp [step, hs, hf]

theorem liftResult_good (t : ℕ) (old : Member) (r : LocalResult)
    (hr : ∀ b ∈ r.retained.toList, Canonical b)
    (hb : ∀ b ∈ r.newborn.toList, Canonical b) : GoodPopulation (liftResult t old r) := by
  intro m hm
  simp only [liftResult, List.mem_append, List.mem_map] at hm
  rcases hm with ⟨b, hmem, rfl⟩ | ⟨b, hmem, rfl⟩
  · exact hr b hmem
  · exact hb b hmem

theorem actualStep_good (t : ℕ) (old : Member) (a : Action) (z : Noise)
    (hc : Canonical old.body) : GoodPopulation (actualStep t old a z) := by
  obtain ⟨theta, i, tag, hx⟩ := hc
  apply liftResult_good
  · simpa [hx] using (step_outputs_canonical theta i tag a z).1
  · simpa [hx] using (step_outputs_canonical theta i tag a z).2

/-- Reuses the exact nested finite-product atoms already used for cohorts. -/
abbrev RequestWord (n : ℕ) := Samples Action n
abbrev NoiseWord (n : ℕ) := Samples Noise n
abbrev ObservationWord (n : ℕ) := Samples Observation n

/-- Every old member runs exactly once; output members wait for the next census. -/
def generation (t : ℕ) : (xs : List Member) →
    RequestWord xs.length → NoiseWord xs.length → List Member
  | [], _, _ => []
  | old :: xs, a, z => actualStep t old a.1 z.1 ++ generation t xs a.2 z.2

theorem generation_good (t : ℕ) (xs : List Member) (hg : GoodPopulation xs)
    (a : RequestWord xs.length) (z : NoiseWord xs.length) :
    GoodPopulation (generation t xs a z) := by
  induction xs with
  | nil => simp [generation, GoodPopulation]
  | cons old xs ih =>
    have hh : Canonical old.body := hg old (by simp)
    have ht : GoodPopulation xs := fun m hm => hg m (by simp [hm])
    intro m hm
    simp only [generation, List.mem_append] at hm
    rcases hm with hm | hm
    · exact actualStep_good t old a.1 z.1 hh m hm
    · exact ih ht a.2 z.2 m hm

def censusCount : List Member → Kind → ℕ
  | [], _ => 0
  | m :: xs, j => (if diagnostic m.body = j then 1 else 0) + censusCount xs j

def potential (p : Parameters) (xs : List Member) : ℝ :=
  rowDot (natRow (censusCount xs)) (sourceValue p)

@[simp] theorem potential_nil (p : Parameters) : potential p [] = 0 := by
  simp [potential, rowDot, natRow, censusCount]

theorem potential_cons (p : Parameters) (m : Member) (xs : List Member) :
    potential p (m :: xs) = sourceValue p (diagnostic m.body) + potential p xs := by
  simp [potential, rowDot, natRow, censusCount, add_mul, Finset.sum_add_distrib, ite_mul]

theorem potential_append (p : Parameters) (xs ys : List Member) :
    potential p (xs ++ ys) = potential p xs + potential p ys := by
  induction xs with
  | nil => simp
  | cons m xs ih => simp only [List.cons_append, potential_cons, ih, add_assoc]

theorem census_mass (xs : List Member) :
    rowMass (natRow (censusCount xs)) = (xs.length : ℝ) := by
  induction xs with
  | nil => simp [rowMass, natRow, censusCount]
  | cons m xs ih =>
    cases hd : diagnostic m.body <;>
      simp [rowMass, natRow, censusCount, hd] at * <;> linarith

theorem liftResult_count (t : ℕ) (old : Member) (r : LocalResult) (j : Kind) :
    censusCount (liftResult t old r) j = resultCount r j := by
  cases hr : r.retained <;> cases hb : r.newborn <;>
    simp [liftResult, hr, hb, censusCount, resultCount, bodyCount,
      retainedMember, newbornMember]

theorem potential_actualStep (p : Parameters) (t : ℕ) (old : Member)
    (a : Action) (z : Noise) :
    potential p (actualStep t old a z) =
      ∑ j, (resultCount (step old.body a z) j : ℝ) * sourceValue p j := by
  simp only [potential, actualStep, rowDot, natRow, liftResult_count]

theorem member_expected_bound (p : Parameters) (hp : Valid p) (t : ℕ)
    (old : Member) (a : Action) (hc : Canonical old.body) :
    expect (noiseWeight p) (fun z => potential p (actualStep t old a z)) ≤
      growthRate p true * sourceValue p (diagnostic old.body) := by
  obtain ⟨theta, i, tag, hx⟩ := hc
  simp only [expect, potential_actualStep, hx, diagnostic_programBody]
  exact actual_one_step_value_le p hp theta i tag a

theorem member_expected_eq (p : Parameters) (t : ℕ)
    (old : Member) (hc : Canonical old.body) :
    expect (noiseWeight p)
      (fun z => potential p (actualStep t old (programAction true (diagnostic old.body)) z)) =
      growthRate p true * sourceValue p (diagnostic old.body) := by
  obtain ⟨theta, i, tag, hx⟩ := hc
  simp only [expect, potential_actualStep, hx, diagnostic_programBody]
  exact actual_best_request_one_step_value_eq p theta i tag

def bestRequests : (xs : List Member) → RequestWord xs.length
  | [] => PUnit.unit
  | m :: xs => (programAction true (diagnostic m.body), bestRequests xs)

/-- The joint source noise law is explicit.  This local calculation is then
mixed over arbitrary correlated requests for the whole population. -/
theorem generation_expected_bound (p : Parameters) (hp : Valid p) (t : ℕ)
    (xs : List Member) (hg : GoodPopulation xs) (a : RequestWord xs.length) :
    expect (iidWeight (noiseWeight p) xs.length) (fun z => potential p (generation t xs a z)) ≤
      growthRate p true * potential p xs := by
  induction xs with
  | nil => simp [expect, generation]
  | cons old xs ih =>
    have hh : Canonical old.body := hg old (by simp)
    have ht : GoodPopulation xs := fun m hm => hg m (by simp [hm])
    change expect (productWeight (noiseWeight p) (iidWeight (noiseWeight p) xs.length))
      (fun z => potential p (actualStep t old a.1 z.1 ++ generation t xs a.2 z.2)) ≤ _
    simp_rw [potential_append]
    rw [product_expect_add, iidWeight_total (noiseWeight p) (noiseWeight_sum p),
      noiseWeight_sum, mul_one, one_mul, potential_cons]
    have hhead := member_expected_bound p hp t old a.1 hh
    have htail := ih ht a.2
    nlinarith

/-- Equality uses the same requests executed by the physical true program. -/
theorem generation_expected_eq (p : Parameters) (t : ℕ)
    (xs : List Member) (hg : GoodPopulation xs) :
    expect (iidWeight (noiseWeight p) xs.length)
      (fun z => potential p (generation t xs (bestRequests xs) z)) =
      growthRate p true * potential p xs := by
  induction xs with
  | nil => simp [expect, generation]
  | cons old xs ih =>
    have hh : Canonical old.body := hg old (by simp)
    have ht : GoodPopulation xs := fun m hm => hg m (by simp [hm])
    change expect (productWeight (noiseWeight p) (iidWeight (noiseWeight p) xs.length))
      (fun z => potential p (actualStep t old (programAction true (diagnostic old.body)) z.1 ++
        generation t xs (bestRequests xs) z.2)) = _
    simp_rw [potential_append]
    rw [product_expect_add, iidWeight_total (noiseWeight p) (noiseWeight_sum p),
      noiseWeight_sum, mul_one, one_mul, member_expected_eq p t old hh, ih ht, potential_cons]
    ring

/-! ## An observed-history policy interface and the actual controlled law -/

structure PublicReceipt where
  before : Observation
  request : Action
  status : Status
  repairPaid : ℕ
  operationPaid : ℕ
  refund : ℕ
  retained : Option Observation
  newborn : Option Observation

def publicReceipt (old : Member) (a : Action) (z : Noise) : PublicReceipt :=
  let r := step old.body a z
  ⟨observe old.body, a, r.status, r.repairPaid, r.operationPaid, r.refund,
    r.retained.map observe, r.newborn.map observe⟩

def receipts : (xs : List Member) → RequestWord xs.length → NoiseWord xs.length →
    List PublicReceipt
  | [], _, _ => []
  | old :: xs, a, z => publicReceipt old a.1 z.1 :: receipts xs a.2 z.2

def observations : (xs : List Member) → ObservationWord xs.length
  | [] => PUnit.unit
  | old :: xs => (observe old.body, observations xs)

def observedBody (o : Observation) : Body :=
  ⟨o.1, o.2.1, o.2.2.1, o.2.2.2, false⟩

@[simp] theorem diagnostic_observedBody (x : Body) :
    diagnostic (observedBody (observe x)) = diagnostic x := rfl

def bestObservedRequests : (n : ℕ) → ObservationWord n → RequestWord n
  | 0, _ => PUnit.unit
  | n + 1, o => (programAction true (diagnostic (observedBody o.1)),
      bestObservedRequests n o.2)

theorem bestObservedRequests_observations (xs : List Member) :
    bestObservedRequests xs.length (observations xs) = bestRequests xs := by
  induction xs with
  | nil => rfl
  | cons old xs ih => simp [observations, bestObservedRequests, bestRequests, ih]

/-- A full permitted-history behavioral law.  The joint request distribution
can coordinate all current members and use arbitrary real private probabilities.
No audit identity, hidden physical tag, or raw world atom is an argument. -/
structure Policy where
  kernel : ∀ n, List (List PublicReceipt) → ObservationWord n → RequestWord n → ℝ
  nonneg : ∀ n hist obs a, 0 ≤ kernel n hist obs a
  total : ∀ n hist obs, ∑ a, kernel n hist obs a = 1

def bestPolicy : Policy := by
  classical
  refine ⟨fun n _ obs a => if a = bestObservedRequests n obs then 1 else 0, ?_, ?_⟩
  · intro n hist obs a
    split_ifs <;> norm_num
  · intro n hist obs
    simp

/-- The proof field records a source invariant; policies cannot inspect it or
the audit population.  Their sole data come from `observations` and publicHistory. -/
structure State where
  population : List Member
  publicHistory : List (List PublicReceipt)
  good : GoodPopulation population

abbrev Branch (s : State) := RequestWord s.population.length × NoiseWord s.population.length

instance (s : State) : Fintype (Branch s) := by
  unfold Branch RequestWord NoiseWord
  infer_instance

def next (t : ℕ) (s : State) (w : Branch s) : State :=
  ⟨generation t s.population w.1 w.2,
    s.publicHistory ++ [receipts s.population w.1 w.2],
    generation_good t s.population s.good w.1 w.2⟩

def branchWeight (p : Parameters) (K : Policy) (_t : ℕ) (s : State) : Branch s → ℝ :=
  productWeight
    (K.kernel s.population.length s.publicHistory (observations s.population))
    (iidWeight (noiseWeight p) s.population.length)

theorem branchWeight_nonneg (p : Parameters) (hp : Valid p) (K : Policy)
    (t : ℕ) (s : State) (w : Branch s) : 0 ≤ branchWeight p K t s w :=
  mul_nonneg (K.nonneg _ _ _ _)
    (iidWeight_nonneg (noiseWeight p) (fun z => (noiseWeight_pos p hp z).le) _ _)

theorem branchWeight_total (p : Parameters) (K : Policy) (t : ℕ) (s : State) :
    (∑ w, branchWeight p K t s w) = 1 := by
  rw [branchWeight, productWeight_total, K.total,
    iidWeight_total (noiseWeight p) (noiseWeight_sum p), one_mul]

theorem branch_expect_split (p : Parameters) (K : Policy) (t : ℕ) (s : State)
    (F : Branch s → ℝ) :
    (∑ w, branchWeight p K t s w * F w) =
      ∑ a, K.kernel s.population.length s.publicHistory (observations s.population) a *
        (∑ z, iidWeight (noiseWeight p) s.population.length z * F (a, z)) := by
  simp only [branchWeight, productWeight, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

/-- The actual source discharges the one-step premise of the general finite
history theorem for every permitted history kernel. -/
theorem next_expected_bound (p : Parameters) (hp : Valid p) (K : Policy)
    (t : ℕ) (s : State) :
    (∑ w, branchWeight p K t s w * potential p (next t s w).population) ≤
      growthRate p true * potential p s.population := by
  rw [branch_expect_split]
  calc
    _ ≤ ∑ a, K.kernel s.population.length s.publicHistory (observations s.population) a *
        (growthRate p true * potential p s.population) := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left
        (generation_expected_bound p hp t s.population s.good a) (K.nonneg _ _ _ a)
    _ = _ := by rw [← Finset.sum_mul, K.total, one_mul]

theorem next_expected_eq (p : Parameters) (t : ℕ) (s : State) :
    (∑ w, branchWeight p bestPolicy t s w * potential p (next t s w).population) =
      growthRate p true * potential p s.population := by
  classical
  rw [branch_expect_split]
  simpa [bestPolicy, bestObservedRequests_observations, expect, next] using
    generation_expected_eq p t s.population s.good

def populationExpectation (p : Parameters) (K : Policy) (initial : State)
    (n : ℕ) (F : State → ℝ) : ℝ :=
  historyExpectation (H := fun _ => State) (O := fun _ s => Branch s)
    initial next (branchWeight p K) n F

def W (p : Parameters) (n : ℕ) (s : State) : ℝ :=
  normalizedValue (growthRate p true) (fun _ s => potential p s.population) n s

theorem potential_nonneg (p : Parameters) (hp : Valid p) (xs : List Member) :
    0 ≤ potential p xs := by
  unfold potential rowDot natRow
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (Nat.cast_nonneg _) (sourceValue_pos p hp i).le

theorem potential_pos_of_nonempty (p : Parameters) (hp : Valid p) (xs : List Member)
    (hn : xs ≠ []) : 0 < potential p xs := by
  cases xs with
  | nil => exact False.elim (hn rfl)
  | cons old xs =>
    rw [potential_cons]
    exact add_pos_of_pos_of_nonneg (sourceValue_pos p hp _) (potential_nonneg p hp xs)

/-- Finite-law nonnegative supermartingale, at every actual full-history node. -/
theorem actual_supermartingale (p : Parameters) (hp : Valid p) (K : Policy)
    (n : ℕ) (s : State) :
    0 ≤ W p n s ∧
    (∑ w, branchWeight p K n s w * W p (n + 1) (next n s w)) ≤ W p n s := by
  have hr : 0 < growthRate p true := lt_trans zero_lt_one (sourceRate_gt_one p hp)
  constructor
  · exact mul_nonneg (inv_nonneg.mpr (pow_pos hr _).le)
      (potential_nonneg p hp s.population)
  · exact historyConditional_normalized_le next (branchWeight p K) (growthRate p true) hr
      (fun _ s => potential p s.population) n s (next_expected_bound p hp K n s)

/-- The actual observation-coded attaining program gives conditional equality. -/
theorem actual_martingale (p : Parameters) (hp : Valid p) (n : ℕ) (s : State) :
    (∑ w, branchWeight p bestPolicy n s w * W p (n + 1) (next n s w)) = W p n s := by
  exact historyConditional_normalized_eq next (branchWeight p bestPolicy) (growthRate p true)
    (lt_trans zero_lt_one (sourceRate_gt_one p hp))
    (fun _ s => potential p s.population) n s (next_expected_eq p n s)

theorem actual_expected_potential_upper (p : Parameters) (hp : Valid p) (K : Policy)
    (initial : State) (n : ℕ) :
    populationExpectation p K initial n (fun s => potential p s.population) ≤
      growthRate p true ^ n * potential p initial.population := by
  exact historyExpectation_iterate_le initial next (branchWeight p K)
    (branchWeight_nonneg p hp K) (growthRate p true)
    (le_of_lt (lt_trans zero_lt_one (sourceRate_gt_one p hp)))
    (fun _ s => potential p s.population) (next_expected_bound p hp K) n

theorem actual_expected_potential_eq (p : Parameters) (initial : State) (n : ℕ) :
    populationExpectation p bestPolicy initial n (fun s => potential p s.population) =
      growthRate p true ^ n * potential p initial.population := by
  exact historyExpectation_iterate_eq initial next (branchWeight p bestPolicy) (growthRate p true)
    (fun _ s => potential p s.population) (next_expected_eq p) n

theorem actual_population_upper (p : Parameters) (hp : Valid p) (K : Policy)
    (initial : State) (n : ℕ) :
    populationExpectation p K initial n (fun s => (s.population.length : ℝ)) ≤
      (growthRate p true ^ n * potential p initial.population) / countRate p .care := by
  have h := history_population_upper initial next (branchWeight p K) (branchWeight_nonneg p hp K)
    (growthRate p true) (le_of_lt (lt_trans zero_lt_one (sourceRate_gt_one p hp)))
    (sourceValue p) (countRate p .care) (careRate_pos p hp)
    (fun i => (sourceValue_bounds p hp i).1)
    (fun _ s => censusCount s.population) (next_expected_bound p hp K) n
  simpa only [populationExpectation, census_mass, potential] using h

theorem actual_population_bounds (p : Parameters) (hp : Valid p)
    (initial : State) (n : ℕ) :
    (growthRate p true ^ n * potential p initial.population) / countRate p .bloom ≤
      populationExpectation p bestPolicy initial n (fun s => (s.population.length : ℝ)) ∧
    populationExpectation p bestPolicy initial n (fun s => (s.population.length : ℝ)) ≤
      (growthRate p true ^ n * potential p initial.population) / countRate p .care := by
  have h := history_population_bounds initial next (branchWeight p bestPolicy)
    (branchWeight_nonneg p hp bestPolicy) (growthRate p true)
    (le_of_lt (lt_trans zero_lt_one (sourceRate_gt_one p hp)))
    (sourceValue p) (countRate p .care) (countRate p .bloom) (careRate_pos p hp)
    (lt_of_lt_of_le (careRate_pos p hp) (careRate_le_bloomRate p hp))
    (fun i => (sourceValue_bounds p hp i).1) (fun i => (sourceValue_bounds p hp i).2)
    (fun _ s => censusCount s.population) (next_expected_eq p) n
  simpa only [populationExpectation, census_mass, potential] using h

/-- Positive constants require the declared nonempty initial population.
The conclusion concerns expected population; extinction remains possible. -/
theorem actual_growth_constants (p : Parameters) (hp : Valid p) (initial : State)
    (hn : initial.population ≠ []) :
    ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧ ∀ n,
      lo * growthRate p true ^ n ≤
        populationExpectation p bestPolicy initial n (fun s => (s.population.length : ℝ)) ∧
      populationExpectation p bestPolicy initial n (fun s => (s.population.length : ℝ)) ≤
        hi * growthRate p true ^ n := by
  have hv := potential_pos_of_nonempty p hp initial.population hn
  refine ⟨potential p initial.population / countRate p .bloom,
    potential p initial.population / countRate p .care,
    div_pos hv (lt_of_lt_of_le (careRate_pos p hp) (careRate_le_bloomRate p hp)),
    div_pos hv (careRate_pos p hp), ?_⟩
  intro n
  simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
    actual_population_bounds p hp initial n

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeControlPopulation
