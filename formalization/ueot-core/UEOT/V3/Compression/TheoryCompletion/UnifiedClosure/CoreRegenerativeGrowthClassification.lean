import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteSourceGrowthControl

/-!
# Exact growth classification on the unchanged regenerative source

Only the parameter domain is enlarged.  `step`, the two internal programs,
observations, six-unit transactions, stop and damaged-bloom refusal are exactly
the existing definitions.  The two positive potentials below certify the whole
request menu, including the refused identity row, without a reducible Perron
construction.  The old `Valid` contract is retained as a sufficient special case.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthClassification

noncomputable section
open scoped BigOperators
open CoreRegenerativeSource FiniteSourceGrowthControl

/-- Primitive probabilities only: no action advantage or growth premise. -/
structure ProbabilityValid (p : Parameters) : Prop where
  careOnly_pos : 0 < p.careOnly
  careOnly_lt_survival : p.careOnly < p.survival
  survival_lt_one : p.survival < 1
  commonBirth_pos : 0 < p.commonBirth
  bloomOnly_pos : 0 < p.bloomOnly
  birth_sum_lt_one : p.commonBirth + p.bloomOnly < 1
  damage_pos : 0 < p.damage
  damage_lt_one : p.damage < 1

theorem valid_probabilityValid (p : Parameters) (hp : Valid p) : ProbabilityValid p :=
  ⟨hp.careOnly_pos, hp.careOnly_lt_survival, hp.survival_lt_one,
    hp.commonBirth_pos, lt_trans hp.careOnly_pos hp.advantage,
    hp.birth_sum_lt_one, hp.damage_pos, hp.damage_lt_one⟩

/-- All original 36 atoms remain strictly positive in the enlarged domain. -/
theorem noiseWeight_pos (p : Parameters) (hp : ProbabilityValid p) (z : Noise) :
    0 < noiseWeight p z := by
  have hs : 0 < survivalWeight p z.1.1 := by
    unfold survivalWeight
    split_ifs <;> linarith [hp.survival_lt_one, hp.careOnly_pos, hp.careOnly_lt_survival]
  have hb : 0 < birthWeight p z.1.2 := by
    unfold birthWeight
    split_ifs <;> linarith [hp.birth_sum_lt_one, hp.bloomOnly_pos, hp.commonBirth_pos]
  have hd : ∀ j, 0 < damageWeight p j := by
    intro j
    cases j <;> simp [damageWeight] <;> linarith [hp.damage_pos, hp.damage_lt_one]
  exact mul_pos (mul_pos (mul_pos hs hb) (hd _)) (hd _)

def kc (p : Parameters) : ℝ := countRate p .care
def kb (p : Parameters) : ℝ := countRate p .bloom
def kStar (p : Parameters) : ℝ := max (kc p) (kb p)
def mu (p : Parameters) : ℝ := (1 - p.damage) * kStar p + p.damage * kc p
def optimalRate (p : Parameters) : ℝ := max 1 (mu p)

theorem kc_eq (p : Parameters) : kc p = p.survival + p.commonBirth := rfl

theorem kb_eq (p : Parameters) :
    kb p = p.survival - p.careOnly + (p.commonBirth + p.bloomOnly) := rfl

/-- Exactly the two extra responsibilities of the older sufficient class. -/
theorem valid_iff_probability_advantage_supercritical (p : Parameters) :
    Valid p ↔ ProbabilityValid p ∧ p.careOnly < p.bloomOnly ∧ 1 < kc p := by
  constructor
  · intro hp
    exact ⟨valid_probabilityValid p hp, hp.advantage, hp.supercritical⟩
  · rintro ⟨hp, ha, hs⟩
    exact ⟨hp.careOnly_pos, hp.careOnly_lt_survival, hp.survival_lt_one,
      hp.commonBirth_pos, hp.birth_sum_lt_one, ha,
      hp.damage_pos, hp.damage_lt_one, hs⟩

theorem kc_pos (p : Parameters) (hp : ProbabilityValid p) : 0 < kc p := by
  rw [kc_eq]
  linarith [hp.careOnly_pos, hp.careOnly_lt_survival, hp.commonBirth_pos]

theorem kb_pos (p : Parameters) (hp : ProbabilityValid p) : 0 < kb p := by
  rw [kb_eq]
  linarith [hp.careOnly_lt_survival, hp.commonBirth_pos, hp.bloomOnly_pos]

theorem kc_le_kStar (p : Parameters) : kc p ≤ kStar p := le_max_left _ _
theorem kb_le_kStar (p : Parameters) : kb p ≤ kStar p := le_max_right _ _

theorem kStar_pos (p : Parameters) (hp : ProbabilityValid p) : 0 < kStar p :=
  lt_of_lt_of_le (kc_pos p hp) (kc_le_kStar p)

theorem mu_pos (p : Parameters) (hp : ProbabilityValid p) : 0 < mu p :=
  add_pos (mul_pos (sub_pos.mpr hp.damage_lt_one) (kStar_pos p hp))
    (mul_pos hp.damage_pos (kc_pos p hp))

theorem one_le_optimalRate (p : Parameters) : 1 ≤ optimalRate p := le_max_left _ _

theorem optimalRate_pos (p : Parameters) : 0 < optimalRate p :=
  lt_of_lt_of_le zero_lt_one (one_le_optimalRate p)

theorem growthRate_false (p : Parameters) : growthRate p false = kc p := by
  simp [growthRate, programAction, kc]
  ring

theorem growthRate_true (p : Parameters) :
    growthRate p true = (1 - p.damage) * kb p + p.damage * kc p := by
  simp [growthRate, programAction, kc, kb]

theorem growthRate_difference (p : Parameters) :
    growthRate p true - growthRate p false =
      (1 - p.damage) * (p.bloomOnly - p.careOnly) := by
  simp [growthRate, programAction, countRate, survivalRate, birthRate]
  ring

theorem mu_eq_max (p : Parameters) (hp : ProbabilityValid p) :
    mu p = max (growthRate p false) (growthRate p true) := by
  rw [growthRate_false, growthRate_true]
  have hq : 0 ≤ 1 - p.damage := (sub_pos.mpr hp.damage_lt_one).le
  by_cases h : kb p ≤ kc p
  · have hl : (1 - p.damage) * kb p + p.damage * kc p ≤ kc p := by
      nlinarith [mul_le_mul_of_nonneg_left h hq]
    rw [max_eq_left hl]
    simp only [mu, kStar, max_eq_left h]
    ring
  · have hk : kc p ≤ kb p := le_of_not_ge h
    have hl : kc p ≤ (1 - p.damage) * kb p + p.damage * kc p := by
      nlinarith [mul_le_mul_of_nonneg_left hk hq]
    rw [max_eq_right hl]
    simp only [mu, kStar, max_eq_right hk]

theorem optimalRate_formula (p : Parameters) (hp : ProbabilityValid p) :
    optimalRate p = max 1 (max (growthRate p false) (growthRate p true)) := by
  rw [optimalRate, mu_eq_max p hp]

def healthyAction (p : Parameters) : Action := if kb p ≤ kc p then .care else .bloom

/-- The D/bloom case is the original refused transaction, not a new action. -/
def optimalAction (p : Parameters) (i : Kind) : Action :=
  if i then (if 1 ≤ mu p then .care else .bloom) else healthyAction p

theorem healthyAction_rate (p : Parameters) : countRate p (healthyAction p) = kStar p := by
  unfold healthyAction
  split_ifs with h
  · change kc p = kStar p
    exact (max_eq_left h).symm
  · change kb p = kStar p
    exact (max_eq_right (le_of_not_ge h)).symm

/-- Positive right potential, including the genuinely subcritical region. -/
def optimalValue (p : Parameters) (i : Kind) : ℝ :=
  if 1 ≤ mu p then (if i then kc p else kStar p)
  else (if i then 1 else kStar p * p.damage / (1 - kStar p * (1 - p.damage)))

def valueMin (p : Parameters) : ℝ := min (optimalValue p false) (optimalValue p true)
def valueMax (p : Parameters) : ℝ := max (optimalValue p false) (optimalValue p true)

theorem subcritical_denominator_pos (p : Parameters) (hp : ProbabilityValid p)
    (h : ¬ 1 ≤ mu p) : 0 < 1 - kStar p * (1 - p.damage) := by
  have hm : mu p < 1 := lt_of_not_ge h
  have hc := mul_pos hp.damage_pos (kc_pos p hp)
  unfold mu at hm
  nlinarith

theorem optimalValue_pos (p : Parameters) (hp : ProbabilityValid p) (i : Kind) :
    0 < optimalValue p i := by
  by_cases h : 1 ≤ mu p
  · cases i <;> simp only [optimalValue, h, Bool.false_eq_true, ↓reduceIte]
    · exact kStar_pos p hp
    · exact kc_pos p hp
  · cases i <;> simp only [optimalValue, h, Bool.false_eq_true, ↓reduceIte]
    · exact div_pos (mul_pos (kStar_pos p hp) hp.damage_pos)
        (subcritical_denominator_pos p hp h)
    · exact zero_lt_one

theorem valueMin_pos (p : Parameters) (hp : ProbabilityValid p) : 0 < valueMin p :=
  lt_min (optimalValue_pos p hp false) (optimalValue_pos p hp true)

theorem valueMax_pos (p : Parameters) (hp : ProbabilityValid p) : 0 < valueMax p :=
  lt_of_lt_of_le (optimalValue_pos p hp false) (le_max_left _ _)

theorem optimalValue_bounds (p : Parameters) (i : Kind) :
    valueMin p ≤ optimalValue p i ∧ optimalValue p i ≤ valueMax p := by
  cases i
  · exact ⟨min_le_left _ _, le_max_left _ _⟩
  · exact ⟨min_le_right _ _, le_max_right _ _⟩

def valueAverage (p : Parameters) (r : Kind → ℝ) : ℝ :=
  (1 - p.damage) * r false + p.damage * r true

theorem row_value (p : Parameters) (a : Action) (r : Kind → ℝ) :
    (∑ j, row p a j * r j) = countRate p a * valueAverage p r := by
  simp [row, damageWeight, valueAverage]
  ring

theorem valueAverage_pos (p : Parameters) (hp : ProbabilityValid p) :
    0 < valueAverage p (optimalValue p) :=
  add_pos (mul_pos (sub_pos.mpr hp.damage_lt_one) (optimalValue_pos p hp false))
    (mul_pos hp.damage_pos (optimalValue_pos p hp true))

theorem optimal_healthy_eq (p : Parameters) (hp : ProbabilityValid p) :
    kStar p * valueAverage p (optimalValue p) =
      optimalRate p * optimalValue p false := by
  by_cases h : 1 ≤ mu p
  · simp only [valueAverage, optimalValue, h, Bool.false_eq_true, ↓reduceIte,
      optimalRate, max_eq_right h]
    unfold mu
    ring
  · have hd := subcritical_denominator_pos p hp h
    have hdiv := div_mul_cancel₀ (kStar p * p.damage) (ne_of_gt hd)
    simp only [valueAverage, optimalValue, h, Bool.false_eq_true, ↓reduceIte,
      optimalRate, max_eq_left (le_of_not_ge h)]
    nlinarith

theorem optimal_damaged_care_bound (p : Parameters) (hp : ProbabilityValid p) :
    kc p * valueAverage p (optimalValue p) ≤ optimalRate p * optimalValue p true := by
  by_cases h : 1 ≤ mu p
  · simp only [valueAverage, optimalValue, h, Bool.false_eq_true, ↓reduceIte,
      optimalRate, max_eq_right h]
    unfold mu
    nlinarith
  · have hd := subcritical_denominator_pos p hp h
    have hdiv := div_mul_cancel₀ (kStar p * p.damage) (ne_of_gt hd)
    have hm : mu p < 1 := lt_of_not_ge h
    have hh : (1 - p.damage) *
        (kStar p * p.damage / (1 - kStar p * (1 - p.damage))) + p.damage =
        p.damage / (1 - kStar p * (1 - p.damage)) := by
      apply (eq_div_iff (ne_of_gt hd)).2
      rw [add_mul, mul_assoc, hdiv]
      ring
    simp only [valueAverage, optimalValue, h, Bool.false_eq_true, ↓reduceIte,
      optimalRate, max_eq_left (le_of_not_ge h), mul_one]
    rw [hh]
    rw [← mul_div_assoc, div_le_iff₀ hd]
    unfold mu at hm
    nlinarith

theorem actual_row_bound (p : Parameters) (hp : ProbabilityValid p)
    (i : Kind) (a : Action) :
    (∑ j, realizedRow p i a j * optimalValue p j) ≤
      optimalRate p * optimalValue p i := by
  have hav := (valueAverage_pos p hp).le
  cases i with
  | false =>
    cases a with
    | care =>
      have he : (∑ j, realizedRow p false .care j * optimalValue p j) =
          kc p * valueAverage p (optimalValue p) := by
        simpa [realizedRow, kc] using row_value p .care (optimalValue p)
      rw [he, ← optimal_healthy_eq p hp]
      exact mul_le_mul_of_nonneg_right (kc_le_kStar p) hav
    | bloom =>
      have he : (∑ j, realizedRow p false .bloom j * optimalValue p j) =
          kb p * valueAverage p (optimalValue p) := by
        simpa [realizedRow, kb] using row_value p .bloom (optimalValue p)
      rw [he, ← optimal_healthy_eq p hp]
      exact mul_le_mul_of_nonneg_right (kb_le_kStar p) hav
    | stop =>
      have he : (∑ j, realizedRow p false .stop j * optimalValue p j) = 0 := by
        simp [realizedRow, row, countRate, survivalRate, birthRate]
      rw [he]
      exact mul_nonneg (optimalRate_pos p).le (optimalValue_pos p hp false).le
  | true =>
    cases a with
    | care =>
      have he : (∑ j, realizedRow p true .care j * optimalValue p j) =
          kc p * valueAverage p (optimalValue p) := by
        simpa [realizedRow, kc] using row_value p .care (optimalValue p)
      rw [he]
      exact optimal_damaged_care_bound p hp
    | bloom =>
      have he : (∑ j, realizedRow p true .bloom j * optimalValue p j) =
          optimalValue p true := by simp [realizedRow]
      rw [he]
      simpa using mul_le_mul_of_nonneg_right (one_le_optimalRate p)
        (optimalValue_pos p hp true).le
    | stop =>
      have he : (∑ j, realizedRow p true .stop j * optimalValue p j) = 0 := by
        simp [realizedRow, row, countRate, survivalRate, birthRate]
      rw [he]
      exact mul_nonneg (optimalRate_pos p).le (optimalValue_pos p hp true).le

theorem selected_row_eq (p : Parameters) (hp : ProbabilityValid p) (i : Kind) :
    (∑ j, realizedRow p i (optimalAction p i) j * optimalValue p j) =
      optimalRate p * optimalValue p i := by
  cases i with
  | false =>
    have he : (∑ j, realizedRow p false (optimalAction p false) j * optimalValue p j) =
        countRate p (healthyAction p) * valueAverage p (optimalValue p) := by
      simpa [optimalAction, realizedRow] using row_value p (healthyAction p) (optimalValue p)
    rw [he, healthyAction_rate]
    exact optimal_healthy_eq p hp
  | true =>
    by_cases h : 1 ≤ mu p
    · have he : (∑ j, realizedRow p true (optimalAction p true) j * optimalValue p j) =
          kc p * valueAverage p (optimalValue p) := by
        simpa [optimalAction, h, realizedRow, kc] using row_value p .care (optimalValue p)
      rw [he]
      simp only [valueAverage, optimalValue, h, Bool.false_eq_true, ↓reduceIte,
        optimalRate, max_eq_right h]
      unfold mu
      ring
    · simp [optimalAction, h, realizedRow, optimalRate, max_eq_left (le_of_not_ge h)]

/-- The certificate is discharged by the original physical output records. -/
theorem actual_one_step_value_le (p : Parameters) (hp : ProbabilityValid p)
    (theta i tag : Bool) (a : Action) :
    (∑ z : Noise, noiseWeight p z *
      (∑ j, (resultCount (step (programBody theta i tag) a z) j : ℝ) * optimalValue p j)) ≤
        optimalRate p * optimalValue p i := by
  calc
    _ = ∑ j, realizedMean p theta i tag a j * optimalValue p j :=
      record_value_eq_row_value (noiseWeight p)
        (fun z j => resultCount (step (programBody theta i tag) a z) j) (optimalValue p)
    _ = ∑ j, realizedRow p i a j * optimalValue p j := by simp_rw [realizedMean_eq]
    _ ≤ _ := actual_row_bound p hp i a

theorem actual_selected_one_step_value_eq (p : Parameters) (hp : ProbabilityValid p)
    (theta i tag : Bool) :
    (∑ z : Noise, noiseWeight p z *
      (∑ j, (resultCount (step (programBody theta i tag) (optimalAction p i) z) j : ℝ) *
        optimalValue p j)) = optimalRate p * optimalValue p i := by
  calc
    _ = ∑ j, realizedMean p theta i tag (optimalAction p i) j * optimalValue p j :=
      record_value_eq_row_value (noiseWeight p)
        (fun z j => resultCount (step (programBody theta i tag) (optimalAction p i) z) j)
        (optimalValue p)
    _ = ∑ j, realizedRow p i (optimalAction p i) j * optimalValue p j := by
      simp_rw [realizedMean_eq]
    _ = _ := selected_row_eq p hp i

def programValue (p : Parameters) (theta i : Bool) : ℝ := countRate p (programAction theta i)

theorem programValue_pos (p : Parameters) (hp : ProbabilityValid p) (theta i : Bool) :
    0 < programValue p theta i := by
  cases theta <;> cases i
  · exact kc_pos p hp
  · exact kc_pos p hp
  · exact kb_pos p hp
  · exact kc_pos p hp

theorem programRate_pos (p : Parameters) (hp : ProbabilityValid p) (theta : Bool) :
    0 < growthRate p theta :=
  add_pos (mul_pos (sub_pos.mpr hp.damage_lt_one) (programValue_pos p hp theta false))
    (mul_pos hp.damage_pos (programValue_pos p hp theta true))

theorem row_programValue (p : Parameters) (theta : Bool) (a : Action) :
    (∑ j, row p a j * programValue p theta j) = countRate p a * growthRate p theta := by
  simp [row, programValue, growthRate, damageWeight]
  ring

/-- A fixed original program has its own exact positive first-moment ray. -/
theorem actual_program_one_step_value_eq (p : Parameters) (theta program i tag : Bool) :
    (∑ z : Noise, noiseWeight p z *
      (∑ j, (resultCount (step (programBody program i tag) (programAction theta i) z) j : ℝ) *
        programValue p theta j)) = growthRate p theta * programValue p theta i := by
  calc
    _ = ∑ j, realizedMean p program i tag (programAction theta i) j * programValue p theta j :=
      record_value_eq_row_value (noiseWeight p)
        (fun z j => resultCount (step (programBody program i tag) (programAction theta i) z) j)
        (programValue p theta)
    _ = ∑ j, row p (programAction theta i) j * programValue p theta j := by
      simp_rw [realizedMean_eq, realizedRow_program, programRow]
    _ = _ := by rw [row_programValue]; exact mul_comm _ _

theorem trueRate_le_falseRate_iff (p : Parameters) (hp : ProbabilityValid p) :
    growthRate p true ≤ growthRate p false ↔ p.bloomOnly ≤ p.careOnly := by
  have hq := sub_pos.mpr hp.damage_lt_one
  constructor
  · intro h
    by_contra hn
    have hprod := mul_pos hq (sub_pos.mpr (lt_of_not_ge hn))
    nlinarith [growthRate_difference p]
  · intro h
    have hprod := mul_nonpos_of_nonneg_of_nonpos hq.le (sub_nonpos.mpr h)
    nlinarith [growthRate_difference p]

theorem falseRate_le_trueRate_iff (p : Parameters) (hp : ProbabilityValid p) :
    growthRate p false ≤ growthRate p true ↔ p.careOnly ≤ p.bloomOnly := by
  have hq := sub_pos.mpr hp.damage_lt_one
  constructor
  · intro h
    by_contra hn
    have hprod := mul_pos hq (sub_pos.mpr (lt_of_not_ge hn))
    nlinarith [growthRate_difference p]
  · intro h
    have hprod := mul_nonneg hq.le (sub_nonneg.mpr h)
    nlinarith [growthRate_difference p]

theorem false_rate_optimal_iff (p : Parameters) (hp : ProbabilityValid p) :
    growthRate p false = optimalRate p ↔ p.bloomOnly ≤ p.careOnly ∧ 1 ≤ kc p := by
  rw [optimalRate_formula p hp]
  constructor
  · intro h
    have hone : 1 ≤ growthRate p false := by rw [h]; exact le_max_left _ _
    have hother : growthRate p true ≤ growthRate p false := by
      rw [h]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    exact ⟨(trueRate_le_falseRate_iff p hp).mp hother, by simpa [growthRate_false] using hone⟩
  · rintro ⟨hadv, hone⟩
    have hother := (trueRate_le_falseRate_iff p hp).mpr hadv
    rw [max_eq_left hother, max_eq_right (by simpa [growthRate_false] using hone)]

theorem true_rate_optimal_iff (p : Parameters) (hp : ProbabilityValid p) :
    growthRate p true = optimalRate p ↔
      p.careOnly ≤ p.bloomOnly ∧ 1 ≤ growthRate p true := by
  rw [optimalRate_formula p hp]
  constructor
  · intro h
    have hone : 1 ≤ growthRate p true := by rw [h]; exact le_max_left _ _
    have hother : growthRate p false ≤ growthRate p true := by
      rw [h]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    exact ⟨(falseRate_le_trueRate_iff p hp).mp hother, hone⟩
  · rintro ⟨hadv, hone⟩
    have hother := (falseRate_le_trueRate_iff p hp).mpr hadv
    rw [max_eq_right hother, max_eq_right hone]

/-- Old positive class and its attaining internal program are a special case. -/
theorem old_valid_rate (p : Parameters) (hp : Valid p) :
    growthRate p true = optimalRate p :=
  (true_rate_optimal_iff p (valid_probabilityValid p hp)).mpr
    ⟨hp.advantage.le, (FiniteSourceGrowthControl.SourceConsumer.sourceRate_gt_one p hp).le⟩

end

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthClassification
