import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeSource
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SourceCohortFeedback

/-!
# Finite actual-source cohort feedback

The only one-individual transition called here is `CoreRegenerativeSource.programStep`.
Its retained/newborn options determine the two recursive slots.  Unoccupied slots
carry unused independent noise and contribute zero; a newborn first acts in the
next recursive round.  The population wrapper attaches actual identities and
parent pointers to these same slots and proves the resulting census length.

All mean formulas below are derived from this execution and the primitive source
weights.  In particular, the final cohort estimate has no assumed `hmean`, success,
fitness, or supplied-optimality field.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeFeedback

open scoped BigOperators Topology
open Filter
open CoreRegenerativeSource
open SourceCohortFeedback

def optionValue {α : Type*} [Zero α] (f : Body → α) : Option Body → α
  | none => 0
  | some x => f x

def NoiseTree : ℕ → Type
  | 0 => PUnit.{1}
  | T + 1 => Noise × (NoiseTree T × NoiseTree T)

instance noiseTreeFintype (T : ℕ) : Fintype (NoiseTree T) := by
  induction T with
  | zero => exact inferInstanceAs (Fintype PUnit.{1})
  | succ T ih =>
    letI := ih
    change Fintype (Noise × (NoiseTree T × NoiseTree T))
    infer_instance

def treeWeight (p : Parameters) : (T : ℕ) → NoiseTree T → ℝ
  | 0, _ => 1
  | T + 1, w => noiseWeight p w.1 *
      (treeWeight p T w.2.1 * treeWeight p T w.2.2)

def treeCount : (T : ℕ) → Body → NoiseTree T → ℕ
  | 0, _, _ => 1
  | T + 1, x, w =>
      let r := programStep x w.1
      optionValue (fun y => treeCount T y w.2.1) r.retained +
        optionValue (fun y => treeCount T y w.2.2) r.newborn

/-- Number of actually processed old individuals, hence five times this is the
actual environmental inflow before the terminal census. -/
def treeWork : (T : ℕ) → Body → NoiseTree T → ℕ
  | 0, _, _ => 0
  | T + 1, x, w =>
      let r := programStep x w.1
      1 + optionValue (fun y => treeWork T y w.2.1) r.retained +
        optionValue (fun y => treeWork T y w.2.2) r.newborn

theorem treeWeight_pos (p : Parameters) (hp : Valid p) (T : ℕ) :
    ∀ w, 0 < treeWeight p T w := by
  induction T with
  | zero => intro w; exact zero_lt_one
  | succ T ih =>
    intro w
    exact mul_pos (noiseWeight_pos p hp w.1) (mul_pos (ih w.2.1) (ih w.2.2))

theorem treeWeight_total (p : Parameters) (T : ℕ) :
    (∑ w, treeWeight p T w) = 1 := by
  induction T with
  | zero =>
    change (∑ _ : PUnit.{1}, (1 : ℝ)) = 1
    simp
  | succ T ih =>
    change (∑ w : Noise × (NoiseTree T × NoiseTree T),
      productWeight (noiseWeight p) (productWeight (treeWeight p T) (treeWeight p T)) w) = 1
    rw [productWeight_total, productWeight_total, noiseWeight_sum, ih]
    ring

theorem treeCount_le (T : ℕ) : ∀ x w, treeCount T x w ≤ 2 ^ T := by
  induction T with
  | zero => intro x w; rfl
  | succ T ih =>
    intro x w
    have ho : ∀ (o : Option Body) (v : NoiseTree T),
        optionValue (fun y => treeCount T y v) o ≤ 2 ^ T := by
      intro o v
      cases o with
      | none => exact Nat.zero_le _
      | some y => exact ih y v
    have hr := ho (programStep x w.1).retained w.2.1
    have hb := ho (programStep x w.1).newborn w.2.2
    simp only [treeCount, pow_succ]
    omega

theorem treeWork_le (T : ℕ) : ∀ x w, treeWork T x w ≤ 2 ^ T - 1 := by
  induction T with
  | zero => intro x w; rfl
  | succ T ih =>
    intro x w
    have ho : ∀ (o : Option Body) (v : NoiseTree T),
        optionValue (fun y => treeWork T y v) o ≤ 2 ^ T - 1 := by
      intro o v
      cases o with
      | none => exact Nat.zero_le _
      | some y => exact ih y v
    have hr := ho (programStep x w.1).retained w.2.1
    have hb := ho (programStep x w.1).newborn w.2.2
    have hpow : 0 < (2 : ℕ) ^ T := by positivity
    simp only [treeWork, pow_succ]
    omega

def treeMean (p : Parameters) (T : ℕ) (x : Body) : ℝ :=
  expect (treeWeight p T) (fun w => (treeCount T x w : ℝ))

theorem expect_optionCount (p : Parameters) (T : ℕ) (o : Option Body) :
    expect (treeWeight p T)
      (fun w => ((optionValue (fun y => treeCount T y w) o : ℕ) : ℝ)) =
      optionValue (treeMean p T) o := by
  cases o <;> simp [optionValue, treeMean, expect]

@[simp] theorem treeMean_zero (p : Parameters) (x : Body) : treeMean p 0 x = 1 := by
  simp [treeMean, expect, treeWeight, treeCount, NoiseTree, noiseTreeFintype]

theorem treeMean_succ (p : Parameters) (T : ℕ) (x : Body) :
    treeMean p (T + 1) x = ∑ z : Noise, noiseWeight p z *
      (optionValue (treeMean p T) (programStep x z).retained +
        optionValue (treeMean p T) (programStep x z).newborn) := by
  calc
    treeMean p (T + 1) x = ∑ z : Noise, noiseWeight p z *
        expect (productWeight (treeWeight p T) (treeWeight p T))
          (fun v =>
            ((optionValue (fun y => treeCount T y v.1) (programStep x z).retained : ℕ) : ℝ) +
            ((optionValue (fun y => treeCount T y v.2) (programStep x z).newborn : ℕ) : ℝ)) := by
      simp only [treeMean, expect, treeWeight, treeCount, Nat.cast_add,
        productWeight]
      change (∑ w : Noise × (NoiseTree T × NoiseTree T),
        noiseWeight p w.1 * (treeWeight p T w.2.1 * treeWeight p T w.2.2) *
          (((optionValue (fun y => treeCount T y w.2.1) (programStep x w.1).retained : ℕ) : ℝ) +
            ((optionValue (fun y => treeCount T y w.2.2) (programStep x w.1).newborn : ℕ) : ℝ))) = _
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z _
      congr 1
      have h := product_expect_add (treeWeight p T) (treeWeight p T)
        (fun v => ((optionValue (fun y => treeCount T y v) (programStep x z).retained : ℕ) : ℝ))
        (fun v => ((optionValue (fun y => treeCount T y v) (programStep x z).newborn : ℕ) : ℝ))
      simpa only [treeWeight_total, mul_one, one_mul, expect_optionCount] using h

theorem eventCount_test (a : Action) (z : Noise) (f : Kind → ℝ) :
    (∑ j : Kind, (eventCount a z j : ℝ) * f j) =
      (if retains a z then f z.2.1 else 0) +
        (if births a z then f z.2.2 else 0) := by
  cases hr : retains a z <;> cases hb : births a z <;>
    cases hdp : z.2.1 <;> cases hdc : z.2.2 <;>
    simp [eventCount, hr, hb, hdp, hdc] <;> ring

/-- A test-function form of the actual retained/newborn mean, derived from the
36 source atoms.  It is useful for both count feedback and weighted ancestry. -/
theorem noise_expected_children (p : Parameters) (a : Action) (f : Kind → ℝ) :
    (∑ z : Noise, noiseWeight p z *
      ((if retains a z then f z.2.1 else 0) +
        (if births a z then f z.2.2 else 0))) =
      ∑ j : Kind, row p a j * f j := by
  simp_rw [← eventCount_test a _ f, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  calc
    (∑ z : Noise, noiseWeight p z * ((eventCount a z j : ℝ) * f j)) =
        eventMean p a j * f j := by
      rw [eventMean, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = row p a j * f j := by rw [eventMean_eq_row]

theorem treeMean_program_recurrence (p : Parameters) (T : ℕ) (theta i tag : Bool) :
    treeMean p (T + 1) (programBody theta i tag) =
      ∑ j : Kind, programRow p theta i j * treeMean p T (programBody theta j tag) := by
  rw [treeMean_succ]
  have hlocal : ∀ z : Noise,
      optionValue (treeMean p T) (programStep (programBody theta i tag) z).retained +
        optionValue (treeMean p T) (programStep (programBody theta i tag) z).newborn =
      (if retains (programAction theta i) z then treeMean p T (programBody theta z.2.1 tag) else 0) +
        (if births (programAction theta i) z then treeMean p T (programBody theta z.2.2 tag) else 0) := by
    intro z
    rw [program_step_executes]
    cases hr : retains (programAction theta i) z <;>
      cases hb : births (programAction theta i) z <;>
      simp [executedResult, optionValue, hr, hb, copied_code_faithful] <;> rfl
  simp_rw [hlocal]
  exact noise_expected_children p (programAction theta i)
    (fun j => treeMean p T (programBody theta j tag))

/-- The rank-one source gives an explicit all-horizon mean, not an assumed
fitness recurrence.  The original body affects the first actual action. -/
theorem treeMean_program_succ (p : Parameters) (theta tag : Bool) (T : ℕ) :
    ∀ i, treeMean p (T + 1) (programBody theta i tag) =
      countRate p (programAction theta i) * growthRate p theta ^ T := by
  induction T with
  | zero =>
    intro i
    rw [treeMean_program_recurrence]
    simp [programRow, row, damageWeight]
    ring
  | succ T ih =>
    intro i
    rw [treeMean_program_recurrence]
    simp_rw [ih]
    simp [programRow, row, damageWeight, growthRate, pow_succ]
    ring

theorem program_countRate_pos (p : Parameters) (hp : Valid p) (theta i : Bool) :
    0 < countRate p (programAction theta i) := by
  cases theta <;> cases i <;>
    simp [programAction, countRate, survivalRate, birthRate] <;>
    linarith [hp.careOnly_pos, hp.careOnly_lt_survival, hp.commonBirth_pos, hp.advantage]

theorem program_growthRate_pos (p : Parameters) (hp : Valid p) (theta : Bool) :
    0 < growthRate p theta := by
  have h0 := program_countRate_pos p hp theta false
  have h1 := program_countRate_pos p hp theta true
  unfold growthRate
  exact add_pos (mul_pos (sub_pos.mpr hp.damage_lt_one) h0) (mul_pos hp.damage_pos h1)

theorem treeMean_program_pos (p : Parameters) (hp : Valid p)
    (theta i tag : Bool) (T : ℕ) :
    0 < treeMean p T (programBody theta i tag) := by
  cases T with
  | zero => simp
  | succ T =>
    rw [treeMean_program_succ]
    exact mul_pos (program_countRate_pos p hp theta i)
      (pow_pos (program_growthRate_pos p hp theta) _)

abbrev CohortAtoms (T : ℕ) := NoiseTree T × NoiseTree T

/-- One cohort contains a healthy founder of each faithfully inherited program.
Both founders and every descendant have their own literal source endowment. -/
def cohortWeight (p : Parameters) (T : ℕ) : CohortAtoms T → ℝ :=
  productWeight (treeWeight p T) (treeWeight p T)

def cohortLower (T : ℕ) (w : CohortAtoms T) : ℝ :=
  treeCount T (programBody false false false) w.1

def cohortTotal (T : ℕ) (w : CohortAtoms T) : ℝ :=
  (treeCount T (programBody false false false) w.1 : ℝ) +
    (treeCount T (programBody true false false) w.2 : ℝ)

def lowerMean (p : Parameters) (T : ℕ) : ℝ :=
  treeMean p T (programBody false false false)

def upperMean (p : Parameters) (T : ℕ) : ℝ :=
  treeMean p T (programBody true false false)

def totalMean (p : Parameters) (T : ℕ) : ℝ := lowerMean p T + upperMean p T

theorem cohortWeight_total (p : Parameters) (T : ℕ) :
    (∑ w, cohortWeight p T w) = 1 := by
  rw [cohortWeight, productWeight_total, treeWeight_total, one_mul]

theorem cohortWeight_nonneg (p : Parameters) (hp : Valid p) (T : ℕ) :
    ∀ w, 0 ≤ cohortWeight p T w := by
  intro w
  exact le_of_lt (mul_pos (treeWeight_pos p hp T w.1) (treeWeight_pos p hp T w.2))

theorem cohortLower_mean (p : Parameters) (T : ℕ) :
    expect (cohortWeight p T) (cohortLower T) = lowerMean p T := by
  have h := product_expect_add (treeWeight p T) (treeWeight p T)
    (fun w => (treeCount T (programBody false false false) w : ℝ)) (fun _ => 0)
  simpa [cohortWeight, cohortLower, lowerMean, treeMean, expect,
    treeWeight_total] using h

theorem cohortTotal_mean (p : Parameters) (T : ℕ) :
    expect (cohortWeight p T) (cohortTotal T) = totalMean p T := by
  have h := product_expect_add (treeWeight p T) (treeWeight p T)
    (fun w => (treeCount T (programBody false false false) w : ℝ))
    (fun w => (treeCount T (programBody true false false) w : ℝ))
  simpa only [cohortWeight, cohortTotal, totalMean, lowerMean, upperMean, treeMean,
    treeWeight_total, mul_one, one_mul] using h

theorem lowerMean_pos (p : Parameters) (hp : Valid p) (T : ℕ) : 0 < lowerMean p T :=
  treeMean_program_pos p hp false false false T

theorem upperMean_pos (p : Parameters) (hp : Valid p) (T : ℕ) : 0 < upperMean p T :=
  treeMean_program_pos p hp true false false T

theorem totalMean_pos (p : Parameters) (hp : Valid p) (T : ℕ) : 0 < totalMean p T :=
  add_pos (lowerMean_pos p hp T) (upperMean_pos p hp T)

/-- Actual count laws, actual source parameters, and independent entire cohort
copies instantiate the finite ratio theorem.  Zero population remains bad. -/
theorem actual_cohort_feedback (p : Parameters) (hp : Valid p) (T n : ℕ) (ε : ℝ)
    (hn : 0 < n) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    eventMass (iidWeight (cohortWeight p T) n) (fun w =>
      sampleSum (cohortTotal T) n w = 0 ∨
        (0 < sampleSum (cohortTotal T) n w ∧
          ε < |sampleSum (cohortLower T) n w / sampleSum (cohortTotal T) n w -
            lowerMean p T / totalMean p T|)) ≤
      9 * (centeredSecond (cohortWeight p T) (cohortLower T) (lowerMean p T) +
        centeredSecond (cohortWeight p T) (cohortTotal T) (totalMean p T)) /
        ((n : ℝ) * ε ^ 2 * totalMean p T ^ 2) := by
  apply iid_badRatio_mass_le _ _ _ _ _ _ _ (cohortWeight_nonneg p hp T)
    (cohortWeight_total p T) (cohortTotal_mean p T) (cohortLower_mean p T)
    (totalMean_pos p hp T) (le_of_lt (lowerMean_pos p hp T))
  · unfold totalMean
    linarith [upperMean_pos p hp T]
  · exact hε0
  · exact hε1
  · exact hn

theorem cohort_count_bounds (T : ℕ) (w : CohortAtoms T) :
    0 ≤ cohortLower T w ∧ cohortLower T w ≤ cohortTotal T w ∧
      0 ≤ cohortTotal T w ∧ cohortTotal T w ≤ 2 * (2 : ℝ) ^ T := by
  have hl : (treeCount T (programBody false false false) w.1 : ℝ) ≤ (2 : ℝ) ^ T := by
    exact_mod_cast treeCount_le T (programBody false false false) w.1
  have hu : (treeCount T (programBody true false false) w.2 : ℝ) ≤ (2 : ℝ) ^ T := by
    exact_mod_cast treeCount_le T (programBody true false false) w.2
  unfold cohortLower cohortTotal
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · positivity
  · linarith

theorem cohort_variances_bounded (p : Parameters) (hp : Valid p) (T : ℕ) :
    centeredSecond (cohortWeight p T) (cohortLower T) (lowerMean p T) ≤
        (2 * (2 : ℝ) ^ T) ^ 2 ∧
      centeredSecond (cohortWeight p T) (cohortTotal T) (totalMean p T) ≤
        (2 * (2 : ℝ) ^ T) ^ 2 := by
  constructor
  · apply centeredSecond_le_bound_sq _ _ _ _ (cohortWeight_nonneg p hp T)
      (cohortWeight_total p T) (cohortLower_mean p T) (by positivity)
    intro w
    have h := cohort_count_bounds T w
    exact ⟨h.1, le_trans h.2.1 h.2.2.2⟩
  · apply centeredSecond_le_bound_sq _ _ _ _ (cohortWeight_nonneg p hp T)
      (cohortWeight_total p T) (cohortTotal_mean p T) (by positivity)
    intro w
    have h := cohort_count_bounds T w
    exact ⟨h.2.2.1, h.2.2.2⟩

/-- A coarse explicit finite bound is enough to choose a finite replication
count.  It is derived from actual retained/newborn branching, not assumed moments. -/
theorem actual_cohort_feedback_bounded (p : Parameters) (hp : Valid p)
    (T n : ℕ) (ε : ℝ) (hn : 0 < n) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    eventMass (iidWeight (cohortWeight p T) n) (fun w =>
      sampleSum (cohortTotal T) n w = 0 ∨
        (0 < sampleSum (cohortTotal T) n w ∧
          ε < |sampleSum (cohortLower T) n w / sampleSum (cohortTotal T) n w -
            lowerMean p T / totalMean p T|)) ≤
      18 * (2 * (2 : ℝ) ^ T) ^ 2 / ((n : ℝ) * ε ^ 2 * totalMean p T ^ 2) := by
  refine le_trans (actual_cohort_feedback p hp T n ε hn hε0 hε1) ?_
  have hb := cohort_variances_bounded p hp T
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith [hb.1, hb.2]

theorem growthRate_order (p : Parameters) (hp : Valid p) :
    growthRate p false < growthRate p true := by
  have hpos : 0 < (1 - p.damage) * (p.bloomOnly - p.careOnly) :=
    mul_pos (sub_pos.mpr hp.damage_lt_one) (sub_pos.mpr hp.advantage)
  simp only [growthRate, programAction, Bool.false_eq_true, ↓reduceIte,
    countRate, survivalRate, birthRate]
  nlinarith

theorem lower_upper_ratio (p : Parameters) (hp : Valid p) (T : ℕ) :
    lowerMean p (T + 1) / upperMean p (T + 1) =
      (countRate p .care / countRate p .bloom) *
        (growthRate p false / growthRate p true) ^ T := by
  unfold lowerMean upperMean
  rw [treeMean_program_succ, treeMean_program_succ]
  simp only [programAction, Bool.false_eq_true, ↓reduceIte]
  rw [div_pow]
  field_simp
  <;> ring

theorem lower_total_ratio_le (p : Parameters) (hp : Valid p) (T : ℕ) :
    lowerMean p (T + 1) / totalMean p (T + 1) ≤
      (countRate p .care / countRate p .bloom) *
        (growthRate p false / growthRate p true) ^ T := by
  rw [← lower_upper_ratio p hp T]
  apply (div_le_div_iff₀ (totalMean_pos p hp _) (upperMean_pos p hp _)).2
  have hlo := le_of_lt (lowerMean_pos p hp (T + 1))
  have hden : upperMean p (T + 1) ≤ totalMean p (T + 1) := by
    unfold totalMean
    linarith
  exact mul_le_mul_of_nonneg_left hden hlo

/-- Selection of normalized expected counts follows from the same literal
source.  This limit is kept distinct from actual random population proportions. -/
theorem lower_mean_share_tendsto_zero (p : Parameters) (hp : Valid p) :
    Tendsto (fun T : ℕ => lowerMean p (T + 1) / totalMean p (T + 1)) atTop (𝓝 0) := by
  have hg0 := program_growthRate_pos p hp false
  have hg1 := program_growthRate_pos p hp true
  have hr0 : 0 ≤ growthRate p false / growthRate p true :=
    div_nonneg (le_of_lt hg0) (le_of_lt hg1)
  have hr1 : growthRate p false / growthRate p true < 1 :=
    (div_lt_one hg1).2 (growthRate_order p hp)
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  have hlimit : Tendsto
      (fun T : ℕ => (countRate p .care / countRate p .bloom) *
        (growthRate p false / growthRate p true) ^ T) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hpow
  exact squeeze_zero
    (fun T => div_nonneg (le_of_lt (lowerMean_pos p hp _))
      (le_of_lt (totalMean_pos p hp _)))
    (lower_total_ratio_le p hp) hlimit

/-- The horizon is chosen before the independent cohort count. -/
theorem exists_horizon_mean_share (p : Parameters) (hp : Valid p) (ε : ℝ)
    (hε : 0 < ε) : ∃ T : ℕ, 0 < T ∧ lowerMean p T / totalMean p T ≤ ε := by
  have hlim := lower_mean_share_tendsto_zero p hp
  have hev : ∀ᶠ T : ℕ in atTop, lowerMean p (T + 1) / totalMean p (T + 1) < ε :=
    (tendsto_order.1 hlim).2 ε hε
  obtain ⟨T, hT⟩ := hev.exists
  exact ⟨T + 1, Nat.succ_pos T, le_of_lt hT⟩

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeFeedback
