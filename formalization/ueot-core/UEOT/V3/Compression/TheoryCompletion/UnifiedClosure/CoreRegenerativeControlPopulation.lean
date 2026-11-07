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

@[simp] theorem canonical_damage_encode (theta d tag : Bool) :
    Canonical (damageBody (encode theta false tag) d) := ⟨theta, d, tag, rfl⟩

def GoodPopulation (xs : List Member) : Prop := ∀ m ∈ xs, Canonical m.body

theorem step_outputs_canonical (theta i tag : Bool) (a : Action) (z : Noise) :
    (∀ b ∈ (step (programBody theta i tag) a z).retained.toList, Canonical b) ∧
    (∀ b ∈ (step (programBody theta i tag) a z).newborn.toList, Canonical b) := by
  by_cases hs : a = .stop
  · subst a
    simp [step]
  · by_cases he : canExecute (programBody theta i tag) a = true
    · cases hr : retains a z <;> cases hb : births a z <;>
        simp [step, hs, he, executedResult, hr, hb]
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
    change Action × Samples Action xs.length at a
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
    change Action × Samples Action xs.length at a
    change expect (productWeight (noiseWeight p) (iidWeight (noiseWeight p) xs.length))
      (fun z => potential p (actualStep t old a.1 z.1 ++ generation t xs a.2 z.2)) ≤ _
    simp_rw [potential_append]
    rw [product_expect_add (noiseWeight p) (iidWeight (noiseWeight p) xs.length)
      (fun z : Noise => potential p (actualStep t old a.1 z))
      (fun z : Samples Noise xs.length => potential p (generation t xs a.2 z)),
      iidWeight_total (noiseWeight p) (noiseWeight_sum p),
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
    rw [product_expect_add (noiseWeight p) (iidWeight (noiseWeight p) xs.length)
      (fun z : Noise => potential p
        (actualStep t old (programAction true (diagnostic old.body)) z))
      (fun z : Samples Noise xs.length => potential p (generation t xs (bestRequests xs) z)),
      iidWeight_total (noiseWeight p) (noiseWeight_sum p),
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
  | cons old xs ih =>
    simp [observations, bestObservedRequests, bestRequests, ih]
    rfl

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
  normalizedValue (growthRate p true)
    (fun (_ : ℕ) (s : State) => potential p s.population) n s

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

/-! ## The same resources and the same physically inherited true program -/

def receiptCash (r : PublicReceipt) : ℕ := r.repairPaid + r.operationPaid + r.refund

/-- Every census pays from exactly one retained unit plus five explicit
environmental units per old member.  Each output holds the one actually paid
unit.  Stop refunds six and rejection refunds five, exactly as in `step`. -/
theorem generation_budget (t : ℕ) (xs : List Member)
    (a : RequestWord xs.length) (z : NoiseWord xs.length) :
    ((receipts xs a z).map receiptCash).sum + (generation t xs a z).length =
      6 * xs.length := by
  induction xs with
  | nil => simp [receipts, generation]
  | cons old xs ih =>
    change Action × Samples Action xs.length at a
    change Noise × Samples Noise xs.length at z
    have hh := actualStep_budget t old a.1 z.1
    have ht := ih a.2 z.2
    simp only [capital] at hh
    simp only [receipts, generation, List.map_cons, List.sum_cons, List.length_append,
      List.length_cons, receiptCash, publicReceipt]
    omega

def CarriesProgram (theta : Bool) (x : Body) : Prop :=
  ∃ i tag, x = programBody theta i tag

@[simp] theorem carries_programBody (theta i tag : Bool) :
    CarriesProgram theta (programBody theta i tag) := ⟨i, tag, rfl⟩

@[simp] theorem carries_damage_encode (theta d tag : Bool) :
    CarriesProgram theta (damageBody (encode theta false tag) d) := ⟨d, tag, rfl⟩

def ProgramPopulation (theta : Bool) (xs : List Member) : Prop :=
  ∀ m ∈ xs, CarriesProgram theta m.body

theorem step_outputs_program (theta i tag : Bool) (a : Action) (z : Noise) :
    (∀ b ∈ (step (programBody theta i tag) a z).retained.toList, CarriesProgram theta b) ∧
    (∀ b ∈ (step (programBody theta i tag) a z).newborn.toList, CarriesProgram theta b) := by
  by_cases hs : a = .stop
  · subst a
    simp [step]
  · by_cases he : canExecute (programBody theta i tag) a = true
    · cases hr : retains a z <;> cases hb : births a z <;>
        simp [step, hs, he, executedResult, hr, hb]
    · have hf : canExecute (programBody theta i tag) a = false := Bool.eq_false_iff.mpr he
      simp [step, hs, hf]

theorem actualStep_program (theta : Bool) (t : ℕ) (old : Member)
    (a : Action) (z : Noise) (hc : CarriesProgram theta old.body) :
    ProgramPopulation theta (actualStep t old a z) := by
  obtain ⟨i, tag, hx⟩ := hc
  have ho := step_outputs_program theta i tag a z
  intro m hm
  simp only [actualStep, liftResult, List.mem_append, List.mem_map] at hm
  rcases hm with ⟨b, hmem, rfl⟩ | ⟨b, hmem, rfl⟩
  · exact ho.1 b (by simpa [hx] using hmem)
  · exact ho.2 b (by simpa [hx] using hmem)

/-- Public override requests never replace inherited code by an optimized label. -/
theorem generation_program (theta : Bool) (t : ℕ) (xs : List Member)
    (hg : ProgramPopulation theta xs) (a : RequestWord xs.length) (z : NoiseWord xs.length) :
    ProgramPopulation theta (generation t xs a z) := by
  induction xs with
  | nil => simp [generation, ProgramPopulation]
  | cons old xs ih =>
    have hh : CarriesProgram theta old.body := hg old (by simp)
    have ht : ProgramPopulation theta xs := fun m hm => hg m (by simp [hm])
    intro m hm
    simp only [generation, List.mem_append] at hm
    rcases hm with hm | hm
    · exact actualStep_program theta t old a.1 z.1 hh m hm
    · exact ih ht a.2 z.2 m hm

theorem true_program_request (old : Member) (hc : CarriesProgram true old.body) :
    requestOf old.body = programAction true (diagnostic old.body) := by
  obtain ⟨i, tag, hx⟩ := hc
  simp [hx]

/-- A physical true-program member executes exactly the attaining request,
including the charged repair and actual active-cell interpretation. -/
theorem best_step_is_programStep (t : ℕ) (old : Member) (z : Noise)
    (hc : CarriesProgram true old.body) :
    actualStep t old (programAction true (diagnostic old.body)) z =
      liftResult t old (programStep old.body z) := by
  rw [actualStep, ← true_program_request old hc, ← programStep_eq_step]

def internalGeneration (t : ℕ) : (xs : List Member) → NoiseWord xs.length → List Member
  | [], _ => []
  | old :: xs, z => liftResult t old (programStep old.body z.1) ++ internalGeneration t xs z.2

theorem attaining_generation_is_internal (t : ℕ) (xs : List Member)
    (hg : ProgramPopulation true xs) (z : NoiseWord xs.length) :
    generation t xs (bestRequests xs) z = internalGeneration t xs z := by
  induction xs with
  | nil => rfl
  | cons old xs ih =>
    have hh : CarriesProgram true old.body := hg old (by simp)
    have ht : ProgramPopulation true xs := fun m hm => hg m (by simp [hm])
    change actualStep t old (programAction true (diagnostic old.body)) z.1 ++
      generation t xs (bestRequests xs) z.2 = _
    rw [best_step_is_programStep t old z.1 hh, ih ht]
    rfl

inductive Reachable (initial : State) : ℕ → State → Prop where
  | start : Reachable initial 0 initial
  | advance {t : ℕ} {s : State} : Reachable initial t s →
      (w : Branch s) → Reachable initial (t + 1) (next t s w)

theorem reachable_program (theta : Bool) (initial : State)
    (hg : ProgramPopulation theta initial.population) {t : ℕ} {s : State}
    (h : Reachable initial t s) : ProgramPopulation theta s.population := by
  induction h with
  | start => exact hg
  | @advance t s h w ih => exact generation_program theta t s.population ih w.1 w.2

def trueFounderState (index : ℕ) (i tag : Bool) : State := by
  refine ⟨[founder index true i tag], [], ?_⟩
  intro m hm
  simp only [List.mem_singleton] at hm
  subst m
  exact canonical_programBody true i tag

theorem trueFounder_program (index : ℕ) (i tag : Bool) :
    ProgramPopulation true (trueFounderState index i tag).population := by
  intro m hm
  simp only [trueFounderState, List.mem_singleton] at hm
  subst m
  exact carries_programBody true i tag

/-- A single initially damaged true-program founder is a nonempty common
execution witness.  The same source program repairs itself and attains growth;
no switch to a second controller or free resource state is made. -/
theorem damaged_true_founder_growth (p : Parameters) (hp : Valid p) (index : ℕ) (tag : Bool) :
    ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧ ∀ n,
      lo * growthRate p true ^ n ≤ populationExpectation p bestPolicy
        (trueFounderState index true tag) n (fun s => (s.population.length : ℝ)) ∧
      populationExpectation p bestPolicy (trueFounderState index true tag) n
        (fun s => (s.population.length : ℝ)) ≤ hi * growthRate p true ^ n := by
  exact actual_growth_constants p hp (trueFounderState index true tag) (by simp [trueFounderState])

theorem bestPolicy_positive_branch_is_internal (p : Parameters) (t : ℕ) (s : State)
    (w : Branch s) (hg : ProgramPopulation true s.population)
    (hw : 0 < branchWeight p bestPolicy t s w) :
    (next t s w).population = internalGeneration t s.population w.2 := by
  classical
  have ha : w.1 = bestRequests s.population := by
    by_contra hne
    have hz : branchWeight p bestPolicy t s w = 0 := by
      simp [branchWeight, productWeight, bestPolicy, bestObservedRequests_observations, hne]
    rw [hz] at hw
    exact (lt_irrefl 0) hw
  change generation t s.population w.1 w.2 = _
  rw [ha]
  exact attaining_generation_is_internal t s.population hg w.2

/-! ## The same public record under the lawful hidden-tag quotient -/

def eraseMember (m : Member) : Member := { m with body := eraseTag m.body }

theorem eraseMember_keeps_identity (m : Member) :
    (eraseMember m).identity = m.identity ∧ (eraseMember m).parent = m.parent ∧
      (eraseMember m).bornAt = m.bornAt ∧ (eraseMember m).age = m.age ∧
      (eraseMember m).ancestry = m.ancestry := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- This is the actual complete policy receipt, including both marked slots
and every payment field, not only a matrix or diagnostic equality. -/
theorem publicReceipt_eraseMember (old : Member) (a : Action) (z : Noise) :
    publicReceipt (eraseMember old) a z = publicReceipt old a z := by
  have hf : observe ∘ eraseTag = observe := rfl
  simp [publicReceipt, eraseMember, step_joint_record_commutes, eraseResult, Option.map_map, hf]

theorem population_observations_eraseMember (xs : List Member) :
    (xs.map eraseMember).map (fun m => observe m.body) =
      xs.map (fun m => observe m.body) := by
  simp [List.map_map, eraseMember]

/-! ## Complete finite-history transport of the same actual state and law

The only transport below is the length equality of a mapped finite population.
It keeps every request and every source atom.  The permitted `Policy` itself is
unchanged in both directions because its complete public inputs are unchanged.
-/

def transportSamples {α : Type*} {n m : ℕ} (h : n = m) (w : Samples α n) : Samples α m :=
  h ▸ w

theorem transportSamples_succ {α : Type*} {n m : ℕ} (h : n + 1 = m + 1)
    (a : α) (w : Samples α n) :
    transportSamples h (a, w) = (a, transportSamples (Nat.succ.inj h) w) := by
  obtain rfl := Nat.succ.inj h
  rfl

theorem erasedLength (xs : List Member) : xs.length = (xs.map eraseMember).length :=
  by simp

def eraseWord {α : Type*} (xs : List Member) (w : Samples α xs.length) :
    Samples α (xs.map eraseMember).length := transportSamples (erasedLength xs) w

theorem eraseWord_cons {α : Type*} (old : Member) (xs : List Member)
    (a : α) (w : Samples α xs.length) :
    eraseWord (old :: xs) (a, w) = (a, eraseWord xs w) := by
  unfold eraseWord
  exact transportSamples_succ _ a w

theorem eraseMember_retained (t : ℕ) (old : Member) (status : Status) (body : Body) :
    retainedMember t (eraseMember old) status (eraseTag body) =
      eraseMember (retainedMember t old status body) := rfl

theorem eraseMember_newborn (t : ℕ) (old : Member) (body : Body) :
    newbornMember t (eraseMember old) (eraseTag body) =
      eraseMember (newbornMember t old body) := rfl

theorem liftResult_eraseMember (t : ℕ) (old : Member) (r : LocalResult) :
    liftResult t (eraseMember old) (eraseResult r) = (liftResult t old r).map eraseMember := by
  cases hr : r.retained <;> cases hb : r.newborn <;>
    simp [liftResult, eraseResult, hr, hb, eraseMember_retained, eraseMember_newborn]

/-- This commuting square preserves actual identity and marked ancestry, in
addition to the physical transaction and its costs. -/
theorem actualStep_eraseMember (t : ℕ) (old : Member) (a : Action) (z : Noise) :
    actualStep t (eraseMember old) a z = (actualStep t old a z).map eraseMember := by
  change liftResult t (eraseMember old) (step (eraseTag old.body) a z) = _
  rw [step_joint_record_commutes]
  exact liftResult_eraseMember t old (step old.body a z)

theorem generation_eraseMember (t : ℕ) (xs : List Member)
    (a : RequestWord xs.length) (z : NoiseWord xs.length) :
    generation t (xs.map eraseMember) (eraseWord xs a) (eraseWord xs z) =
      (generation t xs a z).map eraseMember := by
  induction xs with
  | nil => rfl
  | cons old xs ih =>
    change Action × Samples Action xs.length at a
    change Noise × Samples Noise xs.length at z
    rcases a with ⟨a, tailA⟩
    rcases z with ⟨z, tailZ⟩
    simp only [eraseWord_cons]
    change actualStep t (eraseMember old) a z ++
        generation t (xs.map eraseMember) (eraseWord xs tailA) (eraseWord xs tailZ) =
      (actualStep t old a z ++ generation t xs tailA tailZ).map eraseMember
    rw [actualStep_eraseMember, ih, List.map_append]

theorem receipts_eraseMember (xs : List Member)
    (a : RequestWord xs.length) (z : NoiseWord xs.length) :
    receipts (xs.map eraseMember) (eraseWord xs a) (eraseWord xs z) = receipts xs a z := by
  induction xs with
  | nil => rfl
  | cons old xs ih =>
    change Action × Samples Action xs.length at a
    change Noise × Samples Noise xs.length at z
    rcases a with ⟨a, tailA⟩
    rcases z with ⟨z, tailZ⟩
    simp only [eraseWord_cons]
    change publicReceipt (eraseMember old) a z ::
        receipts (xs.map eraseMember) (eraseWord xs tailA) (eraseWord xs tailZ) =
      publicReceipt old a z :: receipts xs tailA tailZ
    rw [publicReceipt_eraseMember, ih]

theorem observations_eraseMember (xs : List Member) :
    observations (xs.map eraseMember) = eraseWord xs (observations xs) := by
  induction xs with
  | nil => rfl
  | cons old xs ih =>
    change observations (eraseMember old :: xs.map eraseMember) =
      eraseWord (old :: xs) (observe old.body, observations xs)
    rw [eraseWord_cons]
    change (observe (eraseMember old).body, observations (xs.map eraseMember)) =
      (observe old.body, eraseWord xs (observations xs))
    rw [ih]
    rfl

theorem policy_kernel_transport (K : Policy) {n m : ℕ} (h : n = m)
    (hist : List (List PublicReceipt)) (obs : ObservationWord n) (a : RequestWord n) :
    K.kernel m hist (transportSamples h obs) (transportSamples h a) = K.kernel n hist obs a := by
  cases h
  rfl

/-- Every allowed kernel is its own transport and lift.  Only unchanged public
history and unchanged physical readouts reach the controller. -/
theorem policy_kernel_eraseMember (K : Policy) (xs : List Member)
    (hist : List (List PublicReceipt)) (a : RequestWord xs.length) :
    K.kernel (xs.map eraseMember).length hist (observations (xs.map eraseMember)) (eraseWord xs a) =
      K.kernel xs.length hist (observations xs) a := by
  rw [observations_eraseMember]
  exact policy_kernel_transport K (erasedLength xs) hist (observations xs) a

theorem iidWeight_transport {α : Type*} (q : α → ℝ) {n m : ℕ} (h : n = m)
    (w : Samples α n) : iidWeight q m (transportSamples h w) = iidWeight q n w := by
  cases h
  rfl

theorem eraseTag_programBody (theta i tag : Bool) :
    eraseTag (programBody theta i tag) = programBody theta i false := by
  cases i <;> rfl

theorem goodPopulation_eraseMember (xs : List Member) (hg : GoodPopulation xs) :
    GoodPopulation (xs.map eraseMember) := by
  intro m hm
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
  obtain ⟨theta, i, tag, hx⟩ := hg old hold
  refine ⟨theta, i, false, ?_⟩
  change eraseTag old.body = _
  rw [hx, eraseTag_programBody]

def eraseState (s : State) : State :=
  ⟨s.population.map eraseMember, s.publicHistory, goodPopulation_eraseMember s.population s.good⟩

theorem state_ext {s u : State} (hp : s.population = u.population)
    (hh : s.publicHistory = u.publicHistory) : s = u := by
  cases s
  cases u
  cases hp
  cases hh
  rfl

@[simp] theorem eraseMember_idempotent (m : Member) : eraseMember (eraseMember m) = eraseMember m := rfl

theorem eraseState_idempotent (s : State) : eraseState (eraseState s) = eraseState s := by
  apply state_ext
  · simp [eraseState, List.map_map, Function.comp_def]
  · rfl

def transportSamplesEquiv {α : Type*} {n m : ℕ} (h : n = m) : Samples α n ≃ Samples α m where
  toFun := transportSamples h
  invFun := transportSamples h.symm
  left_inv := by intro w; cases h; rfl
  right_inv := by intro w; cases h; rfl

/-- The branch equivalence changes neither selected requests nor raw noise. -/
def eraseBranchEquiv (s : State) : Branch s ≃ Branch (eraseState s) :=
  (transportSamplesEquiv (α := Action) (erasedLength s.population)).prodCongr
    (transportSamplesEquiv (α := Noise) (erasedLength s.population))

theorem eraseBranchEquiv_apply (s : State) (w : Branch s) :
    eraseBranchEquiv s w = (eraseWord s.population w.1, eraseWord s.population w.2) := rfl

theorem branchWeight_eraseState (p : Parameters) (K : Policy) (t : ℕ) (s : State) (w : Branch s) :
    branchWeight p K t (eraseState s) (eraseBranchEquiv s w) = branchWeight p K t s w := by
  change K.kernel (s.population.map eraseMember).length s.publicHistory
      (observations (s.population.map eraseMember)) (eraseWord s.population w.1) *
      iidWeight (noiseWeight p) (s.population.map eraseMember).length (eraseWord s.population w.2) =
    K.kernel s.population.length s.publicHistory (observations s.population) w.1 *
      iidWeight (noiseWeight p) s.population.length w.2
  rw [policy_kernel_eraseMember]
  rw [show iidWeight (noiseWeight p) (s.population.map eraseMember).length
      (eraseWord s.population w.2) = iidWeight (noiseWeight p) s.population.length w.2 from
        iidWeight_transport (noiseWeight p) (erasedLength s.population) w.2]

theorem next_eraseState (t : ℕ) (s : State) (w : Branch s) :
    next t (eraseState s) (eraseBranchEquiv s w) = eraseState (next t s w) := by
  apply state_ext
  · exact generation_eraseMember t s.population w.1 w.2
  · change s.publicHistory ++
        [receipts (s.population.map eraseMember) (eraseWord s.population w.1) (eraseWord s.population w.2)] =
      s.publicHistory ++ [receipts s.population w.1 w.2]
    rw [receipts_eraseMember]

/-- Exact change of finite variables in the actual controlled transition law. -/
theorem next_expectation_eraseState (p : Parameters) (K : Policy) (t : ℕ) (s : State)
    (F : State → ℝ) :
    (∑ w, branchWeight p K t (eraseState s) w * F (next t (eraseState s) w)) =
      ∑ w, branchWeight p K t s w * F (eraseState (next t s w)) := by
  symm
  apply Fintype.sum_equiv (eraseBranchEquiv s)
  intro w
  rw [branchWeight_eraseState, next_eraseState]

/-- All finite horizons of the actual controlled law commute with the quotient.
`F` may inspect the complete terminal audit state, including its accumulated
public history and protected identity/ancestry fields. -/
theorem populationExpectation_eraseState (p : Parameters) (K : Policy) (initial : State)
    (n : ℕ) (F : State → ℝ) :
    populationExpectation p K (eraseState initial) n F =
      populationExpectation p K initial n (fun s => F (eraseState s)) := by
  induction n generalizing F with
  | zero => rfl
  | succ n ih =>
    change populationExpectation p K (eraseState initial) n
        (fun s => ∑ w, branchWeight p K n s w * F (next n s w)) =
      populationExpectation p K initial n
        (fun s => ∑ w, branchWeight p K n s w * F (eraseState (next n s w)))
    rw [ih]
    apply congrArg (populationExpectation p K initial n)
    funext s
    exact next_expectation_eraseState p K n s F

theorem protected_test_expectation_eq (p : Parameters) (K : Policy) (initial : State)
    (n : ℕ) (F : State → ℝ) (hF : ∀ s, F (eraseState s) = F s) :
    populationExpectation p K (eraseState initial) n F = populationExpectation p K initial n F := by
  rw [populationExpectation_eraseState]
  exact congrArg (populationExpectation p K initial n) (funext hF)

/-- Since the same full permitted policy set is available in both directions,
the attainable protected test values agree, not merely one selected controller. -/
theorem attainable_test_values_eraseState (p : Parameters) (initial : State) (n : ℕ)
    (F : State → ℝ) (hF : ∀ s, F (eraseState s) = F s) :
    Set.range (fun K : Policy => populationExpectation p K (eraseState initial) n F) =
      Set.range (fun K : Policy => populationExpectation p K initial n F) := by
  congr 1
  funext K
  exact protected_test_expectation_eq p K initial n F hF

theorem censusCount_eraseMember (xs : List Member) (i : Kind) :
    censusCount (xs.map eraseMember) i = censusCount xs i := by
  induction xs with
  | nil => rfl
  | cons old xs ih =>
    simp [List.map_cons, censusCount, eraseMember, ih]
    rfl

/-- Counts, including extinction events and arbitrary tests of type counts,
are transported under the complete actual finite-history law. -/
theorem census_test_expectation_eq (p : Parameters) (K : Policy) (initial : State) (n : ℕ)
    (F : (Kind → ℕ) → ℝ) :
    populationExpectation p K (eraseState initial) n (fun s => F (censusCount s.population)) =
      populationExpectation p K initial n (fun s => F (censusCount s.population)) := by
  apply protected_test_expectation_eq
  intro s
  congr 1
  funext i
  exact censusCount_eraseMember s.population i

theorem population_size_expectation_eq (p : Parameters) (K : Policy) (initial : State) (n : ℕ) :
    populationExpectation p K (eraseState initial) n (fun s => (s.population.length : ℝ)) =
      populationExpectation p K initial n (fun s => (s.population.length : ℝ)) := by
  apply protected_test_expectation_eq
  intro s
  simp [eraseState]

/-- This includes every finite-history test of actual repair/operation payments,
refunds, requested actions, and both marked observed output slots. -/
theorem public_history_test_expectation_eq (p : Parameters) (K : Policy) (initial : State)
    (n : ℕ) (F : List (List PublicReceipt) → ℝ) :
    populationExpectation p K (eraseState initial) n (fun s => F s.publicHistory) =
      populationExpectation p K initial n (fun s => F s.publicHistory) := by
  exact protected_test_expectation_eq p K initial n (fun s => F s.publicHistory) (fun _ => rfl)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeControlPopulation
