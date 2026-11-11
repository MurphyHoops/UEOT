import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthPopulation

/-!
# Exact optimal exponential factor and the two inherited programs

Uniform upper bounds quantify over the unchanged full observed-history `Policy`.
The positive exponential scale is unique. The two existing internal programs
attain that scale exactly in the stated parameter regions. Their execution and
paid repair refer to their own actual damaged founder, not a replacement code.
No finite-deadline population maximization or almost-sure survival is asserted.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthAttainment

noncomputable section
open CoreRegenerativeSource CoreRegenerativePopulation CoreRegenerativeControlPopulation
open CoreRegenerativeGrowthClassification CoreRegenerativeGrowthPopulation

/-- Uniform constant-multiple bounds order positive exponential factors. -/
theorem rate_le_of_bounds {a b lo hi : ℝ} (hb : 0 < b)
    (hlo : 0 < lo) (h : ∀ n : ℕ, lo * a ^ n ≤ hi * b ^ n) : a ≤ b := by
  by_contra hab
  have hba : b < a := lt_of_not_ge hab
  have hratio : 1 < a / b := (one_lt_div hb).mpr hba
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (hi / lo) hratio
  have hbad : hi * b ^ n < a ^ n * lo :=
    (div_lt_div_iff₀ hlo (pow_pos hb n)).mp (by simpa only [div_pow] using hn)
  have hbound := h n
  nlinarith

theorem expected_growth_unique (p : Parameters) (K : Policy) (initial : State)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hga : HasExpectedGrowth p K initial a) (hgb : HasExpectedGrowth p K initial b) :
    a = b := by
  obtain ⟨la, ua, hla, _, hga⟩ := hga
  obtain ⟨lb, ub, hlb, _, hgb⟩ := hgb
  apply le_antisymm
  · exact rate_le_of_bounds hb hla (fun n => le_trans (hga n).1 (hgb n).2)
  · exact rate_le_of_bounds ha hlb (fun n => le_trans (hgb n).1 (hga n).2)

/-- The constant is shared by all permitted history kernels and all census times. -/
def UniformExpectedUpper (p : Parameters) (initial : State) (rho : ℝ) : Prop :=
  0 < rho ∧ ∃ C : ℝ, ∀ (K : Policy) (n : ℕ),
    populationExpectation p K initial n (fun s => (s.population.length : ℝ)) ≤ C * rho ^ n

theorem optimalRate_uniform_upper (p : Parameters) (hp : ProbabilityValid p)
    (initial : State) : UniformExpectedUpper p initial (optimalRate p) := by
  refine ⟨optimalRate_pos p,
    weightedPotential (optimalValue p) initial.population / valueMin p, ?_⟩
  intro K n
  simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
    optimal_population_upper p hp K initial n

/-- Exactness is a least uniform exponential bound, without assuming every
history policy has an exponential limit or a two-sided exponential scale. -/
theorem optimalRate_isLeast_uniform_upper (p : Parameters) (hp : ProbabilityValid p)
    (initial : State) (hn : initial.population ≠ []) :
    IsLeast {rho : ℝ | UniformExpectedUpper p initial rho} (optimalRate p) := by
  refine ⟨optimalRate_uniform_upper p hp initial, ?_⟩
  intro rho h
  obtain ⟨hrho, C, hC⟩ := h
  obtain ⟨lo, hi, hlo, _, hg⟩ := optimal_hasExpectedGrowth p hp initial hn
  exact rate_le_of_bounds hrho hlo
    (fun n => le_trans (hg n).1 (hC (optimalPolicy p) n))

theorem any_expected_growth_le_optimal (p : Parameters) (hp : ProbabilityValid p)
    (K : Policy) (initial : State) {rho : ℝ}
    (hg : HasExpectedGrowth p K initial rho) : rho ≤ optimalRate p := by
  obtain ⟨lo, hi, hlo, _, h⟩ := hg
  obtain ⟨_, C, hC⟩ := optimalRate_uniform_upper p hp initial
  exact rate_le_of_bounds (optimalRate_pos p) hlo (fun n => le_trans (h n).1 (hC K n))

theorem program_attains_iff_rate (p : Parameters) (hp : ProbabilityValid p)
    (theta : Bool) (initial : State) (hn : initial.population ≠ []) :
    HasExpectedGrowth p (programPolicy theta) initial (optimalRate p) ↔
      growthRate p theta = optimalRate p := by
  constructor
  · intro h
    exact expected_growth_unique p (programPolicy theta) initial
      (programRate_pos p hp theta) (optimalRate_pos p)
      (program_hasExpectedGrowth p hp theta initial hn) h
  · intro h
    rw [← h]
    exact program_hasExpectedGrowth p hp theta initial hn

theorem false_program_attains_iff (p : Parameters) (hp : ProbabilityValid p)
    (initial : State) (hn : initial.population ≠ []) :
    HasExpectedGrowth p (programPolicy false) initial (optimalRate p) ↔
      p.bloomOnly ≤ p.careOnly ∧ 1 ≤ kc p :=
  (program_attains_iff_rate p hp false initial hn).trans (false_rate_optimal_iff p hp)

theorem true_program_attains_iff (p : Parameters) (hp : ProbabilityValid p)
    (initial : State) (hn : initial.population ≠ []) :
    HasExpectedGrowth p (programPolicy true) initial (optimalRate p) ↔
      p.careOnly ≤ p.bloomOnly ∧ 1 ≤ growthRate p true :=
  (program_attains_iff_rate p hp true initial hn).trans (true_rate_optimal_iff p hp)

def programRegion (p : Parameters) (theta : Bool) : Prop :=
  if theta then p.careOnly ≤ p.bloomOnly ∧ 1 ≤ growthRate p true
  else p.bloomOnly ≤ p.careOnly ∧ 1 ≤ kc p

theorem damaged_program_attains_iff (p : Parameters) (hp : ProbabilityValid p)
    (index : ℕ) (theta tag : Bool) :
    HasExpectedGrowth p (programPolicy theta) (founderState index theta true tag)
      (optimalRate p) ↔ programRegion p theta := by
  cases theta
  · exact false_program_attains_iff p hp _ (by simp [founderState])
  · exact true_program_attains_iff p hp _ (by simp [founderState])

theorem founder_is_same_repair_body (index : ℕ) (theta tag : Bool) :
    (founder index theta true tag).body = (startState theta true tag).body := rfl

/-- The repair cost and growth assertion belong to the same damaged program
and the same six-unit transaction. Repair itself holds throughout the domain. -/
theorem same_damaged_program_repairs_and_attains_iff (p : Parameters)
    (hp : ProbabilityValid p) (index : ℕ) (theta tag : Bool) :
    ((paidRepair (startState theta true tag)).body = encode theta false tag ∧
      (paidRepair (startState theta true tag)).balance.val = 3 ∧
      (∀ z : Noise, (programStep (founder index theta true tag).body z).repairPaid = 3) ∧
      HasExpectedGrowth p (programPolicy theta) (founderState index theta true tag)
        (optimalRate p)) ↔ programRegion p theta := by
  constructor
  · rintro ⟨_, _, _, hg⟩
    exact (damaged_program_attains_iff p hp index theta tag).mp hg
  · intro h
    have hr := paidRepair_damaged_costs_three theta tag
    exact ⟨hr.1, hr.2.1, fun z => (damaged_founder_paid_repair index theta tag z).1,
      (damaged_program_attains_iff p hp index theta tag).mpr h⟩

theorem subcritical_existing_programs_do_not_attain (p : Parameters)
    (hp : ProbabilityValid p) (hc : kc p < 1) (hb : growthRate p true < 1)
    (initial : State) (hn : initial.population ≠ []) :
    (¬ HasExpectedGrowth p (programPolicy false) initial (optimalRate p)) ∧
    (¬ HasExpectedGrowth p (programPolicy true) initial (optimalRate p)) := by
  constructor
  · intro h
    exact (not_le_of_gt hc) ((false_program_attains_iff p hp initial hn).mp h).2
  · intro h
    exact (not_le_of_gt hb) ((true_program_attains_iff p hp initial hn).mp h).2

theorem old_valid_damaged_program_attains (p : Parameters) (hp : Valid p)
    (index : ℕ) (tag : Bool) :
    HasExpectedGrowth p (programPolicy true) (founderState index true true tag)
      (optimalRate p) := by
  rw [← old_valid_rate p hp]
  exact damaged_founder_hasExpectedGrowth p (valid_probabilityValid p hp) index true tag

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthAttainment
