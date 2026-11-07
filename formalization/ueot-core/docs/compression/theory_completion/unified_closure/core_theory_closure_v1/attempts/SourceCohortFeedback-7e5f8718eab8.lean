import Mathlib

/-!
# Finite cohort feedback from actual count laws

This file supplies only finite algebra and finite probability calculations.
The source consumer must supply its actual finite noise atoms, count functions,
and independent cohort product law.  In particular, a source mean, variance,
fitness, or success event is not a field of a new source interface here.

Zero population is included explicitly in `BadRatio`.  The final estimate is
finite-horizon and finite-population; it makes no almost-sure eventual-selection
claim.  The cohort replication parameter is a real resource commitment in the
source consumer, not free replication of an experiment.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SourceCohortFeedback

open scoped BigOperators

section FiniteLaw

variable {Ω : Type*} [Fintype Ω]

def expect (p : Ω → ℝ) (X : Ω → ℝ) : ℝ :=
  ∑ ω, p ω * X ω

def centeredSecond (p : Ω → ℝ) (X : Ω → ℝ) (μ : ℝ) : ℝ :=
  ∑ ω, p ω * (X ω - μ) ^ 2

noncomputable def eventMass (p : Ω → ℝ) (E : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω, if E ω then p ω else 0

theorem centered_expect_zero (p : Ω → ℝ) (X : Ω → ℝ) (μ : ℝ)
    (hp : ∑ ω, p ω = 1) (hμ : expect p X = μ) :
    expect p (fun ω => X ω - μ) = 0 := by
  simp only [expect, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul] at *
  rw [hp, one_mul, hμ, sub_self]

theorem centeredSecond_nonneg (p : Ω → ℝ) (X : Ω → ℝ) (μ : ℝ)
    (hp : ∀ ω, 0 ≤ p ω) :
    0 ≤ centeredSecond p X μ := by
  exact Finset.sum_nonneg fun ω _ => mul_nonneg (hp ω) (sq_nonneg _)

theorem centeredSecond_eq_second_sub (p : Ω → ℝ) (X : Ω → ℝ) (μ : ℝ)
    (hp : ∑ ω, p ω = 1) (hμ : expect p X = μ) :
    centeredSecond p X μ = expect p (fun ω => X ω ^ 2) - μ ^ 2 := by
  have hexpand : centeredSecond p X μ =
      expect p (fun ω => X ω ^ 2) -
        (2 * μ) * expect p X + μ ^ 2 * (∑ ω, p ω) := by
    simp only [centeredSecond, expect, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    ring
  rw [hexpand, hp, hμ]
  ring

theorem centeredSecond_le_bound_sq (p : Ω → ℝ) (X : Ω → ℝ) (μ R : ℝ)
    (hp0 : ∀ ω, 0 ≤ p ω) (hp : ∑ ω, p ω = 1)
    (hμ : expect p X = μ) (hR : 0 ≤ R)
    (hX : ∀ ω, 0 ≤ X ω ∧ X ω ≤ R) :
    centeredSecond p X μ ≤ R ^ 2 := by
  have hsecond : expect p (fun ω => X ω ^ 2) ≤ R ^ 2 := by
    calc
      expect p (fun ω => X ω ^ 2) ≤ ∑ ω, p ω * R ^ 2 := by
        apply Finset.sum_le_sum
        intro ω _
        apply mul_le_mul_of_nonneg_left _ (hp0 ω)
        have hprod := mul_nonneg (sub_nonneg.mpr (hX ω).2)
          (add_nonneg hR (hX ω).1)
        nlinarith
      _ = R ^ 2 := by rw [← Finset.sum_mul, hp, one_mul]
  rw [centeredSecond_eq_second_sub p X μ hp hμ]
  nlinarith [sq_nonneg μ]

end FiniteLaw

/-- A deterministic ratio estimate.  `a` and `b` are total and selected
expected counts on the same scale; no division by zero is hidden. -/
theorem good_ratio {N Z a b ε : ℝ}
    (ha : 0 < a) (hb0 : 0 ≤ b) (hba : b ≤ a)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hN : |N - a| ≤ ε * a / 3)
    (hZ : |Z - b| ≤ ε * a / 3) :
    0 < N ∧ |Z / N - b / a| ≤ ε := by
  let δ : ℝ := ε * a / 3
  have hδ0 : 0 ≤ δ := by dsimp [δ]; positivity
  have ha0 : 0 ≤ a := le_of_lt ha
  have hεnonneg : 0 ≤ ε := le_of_lt hε0
  have hn : -δ ≤ N - a ∧ N - a ≤ δ := abs_le.mp hN
  have hz : -δ ≤ Z - b ∧ Z - b ≤ δ := abs_le.mp hZ
  have hNlower : 2 * a / 3 ≤ N := by
    have h := mul_le_mul_of_nonneg_right hε1 ha0
    dsimp [δ] at hn
    linarith
  have hNpos : 0 < N := lt_of_lt_of_le (by positivity) hNlower
  refine ⟨hNpos, ?_⟩
  have htarget : 2 * a * δ ≤ ε * (N * a) := by
    have h₁ := mul_le_mul_of_nonneg_left hNlower hεnonneg
    have h₂ := mul_le_mul_of_nonneg_right h₁ ha0
    dsimp [δ]
    nlinarith
  have hzlo := mul_le_mul_of_nonneg_left hz.1 ha0
  have hzhi := mul_le_mul_of_nonneg_left hz.2 ha0
  have hnlo := mul_le_mul_of_nonneg_left hn.1 hb0
  have hnhi := mul_le_mul_of_nonneg_left hn.2 hb0
  have hbδ := mul_le_mul_of_nonneg_right hba hδ0
  have hden : 0 < N * a := mul_pos hNpos ha
  have hid : Z / N - b / a = (a * Z - b * N) / (N * a) := by
    field_simp [ne_of_gt hNpos, ne_of_gt ha]
    <;> ring
  rw [hid, abs_div, abs_of_pos hden]
  apply (div_le_iff₀ hden).2
  apply abs_le.mpr
  constructor <;> nlinarith

/-- The extinction event is a failure event, not silently conditioned away. -/
def BadRatio (N Z a b ε : ℝ) : Prop :=
  N = 0 ∨ (0 < N ∧ ε < |Z / N - b / a|)

theorem badRatio_deviation {N Z a b ε : ℝ}
    (ha : 0 < a) (hb0 : 0 ≤ b) (hba : b ≤ a)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hbad : BadRatio N Z a b ε) :
    ε * a / 3 < |Z - b| ∨ ε * a / 3 < |N - a| := by
  by_cases hN : |N - a| ≤ ε * a / 3
  · by_cases hZ : |Z - b| ≤ ε * a / 3
    · have hg := good_ratio ha hb0 hba hε0 hε1 hN hZ
      rcases hbad with hz | ⟨_, herr⟩
      · exact False.elim (by linarith [hg.1])
      · exact False.elim ((not_lt_of_ge hg.2) herr)
    · exact Or.inl (lt_of_not_ge hZ)
  · exact Or.inr (lt_of_not_ge hN)

theorem badRatio_square_bound {N Z a b ε : ℝ}
    (ha : 0 < a) (hb0 : 0 ≤ b) (hba : b ≤ a)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hbad : BadRatio N Z a b ε) :
    (ε * a / 3) ^ 2 ≤ (Z - b) ^ 2 + (N - a) ^ 2 := by
  have hδ0 : 0 ≤ ε * a / 3 := by positivity
  have hsquare : ∀ x : ℝ, ε * a / 3 < |x| →
      (ε * a / 3) ^ 2 ≤ x ^ 2 := by
    intro x hx
    have hprod := mul_nonneg (sub_nonneg.mpr (le_of_lt hx))
      (add_nonneg (abs_nonneg x) hδ0)
    have hs : (ε * a / 3) ^ 2 ≤ |x| ^ 2 := by nlinarith
    simpa only [sq_abs] using hs
  rcases badRatio_deviation ha hb0 hba hε0 hε1 hbad with hz | hn
  · have h := hsquare (Z - b) hz
    nlinarith [sq_nonneg (N - a)]
  · have h := hsquare (N - a) hn
    nlinarith [sq_nonneg (Z - b)]

/-- A finite Chebyshev/union estimate, proved directly from atom weights.
It needs no count process, independence, or regular conditional probability API. -/
theorem badRatio_mass_le {Ω : Type*} [Fintype Ω]
    (p : Ω → ℝ) (N Z : Ω → ℝ) (a b ε : ℝ)
    (hp0 : ∀ ω, 0 ≤ p ω)
    (ha : 0 < a) (hb0 : 0 ≤ b) (hba : b ≤ a)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    eventMass p (fun ω => BadRatio (N ω) (Z ω) a b ε) ≤
      9 * (centeredSecond p Z b + centeredSecond p N a) / (ε ^ 2 * a ^ 2) := by
  classical
  let E : Ω → Prop := fun ω => BadRatio (N ω) (Z ω) a b ε
  have hterm : ∀ ω, (ε * a / 3) ^ 2 * (if E ω then p ω else 0) ≤
      p ω * ((Z ω - b) ^ 2 + (N ω - a) ^ 2) := by
    intro ω
    by_cases he : E ω
    · rw [if_pos he, mul_comm ((ε * a / 3) ^ 2)]
      exact mul_le_mul_of_nonneg_left
        (badRatio_square_bound ha hb0 hba hε0 hε1 he) (hp0 ω)
    · rw [if_neg he, mul_zero]
      exact mul_nonneg (hp0 ω) (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hsum := Finset.sum_le_sum (fun ω (_ : ω ∈ Finset.univ) => hterm ω)
  have hsplit : (∑ ω, p ω * ((Z ω - b) ^ 2 + (N ω - a) ^ 2)) =
      centeredSecond p Z b + centeredSecond p N a := by
    simp only [centeredSecond, mul_add, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, hsplit] at hsum
  have hδpos : 0 < (ε * a / 3) ^ 2 := by positivity
  have hbound : eventMass p E ≤
      (centeredSecond p Z b + centeredSecond p N a) / (ε * a / 3) ^ 2 := by
    apply (le_div_iff₀ hδpos).2
    simpa only [eventMass, mul_comm] using hsum
  calc
    eventMass p (fun ω => BadRatio (N ω) (Z ω) a b ε) ≤
        (centeredSecond p Z b + centeredSecond p N a) / (ε * a / 3) ^ 2 := hbound
    _ = 9 * (centeredSecond p Z b + centeredSecond p N a) /
        (ε ^ 2 * a ^ 2) := by
      field_simp [ne_of_gt hε0, ne_of_gt ha]
      <;> ring

section ProductLaw

variable {Ω Ψ : Type*} [Fintype Ω] [Fintype Ψ]

def productWeight (p : Ω → ℝ) (q : Ψ → ℝ) : Ω × Ψ → ℝ :=
  fun w => p w.1 * q w.2

theorem productWeight_total (p : Ω → ℝ) (q : Ψ → ℝ) :
    (∑ w, productWeight p q w) = (∑ ω, p ω) * (∑ ψ, q ψ) := by
  simp only [productWeight, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem product_expect_add (p : Ω → ℝ) (q : Ψ → ℝ)
    (X : Ω → ℝ) (Y : Ψ → ℝ) :
    expect (productWeight p q) (fun w => X w.1 + Y w.2) =
      expect p X * (∑ ψ, q ψ) + (∑ ω, p ω) * expect q Y := by
  simp only [expect, productWeight, Fintype.sum_prod_type,
    Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  apply Finset.sum_congr rfl
  intro ψ _
  ring

theorem product_centeredSecond (p : Ω → ℝ) (q : Ψ → ℝ)
    (X : Ω → ℝ) (Y : Ψ → ℝ) (μ ν : ℝ) :
    centeredSecond (productWeight p q) (fun w => X w.1 + Y w.2) (μ + ν) =
      centeredSecond p X μ * (∑ ψ, q ψ) +
      (∑ ω, p ω) * centeredSecond q Y ν +
      2 * expect p (fun ω => X ω - μ) * expect q (fun ψ => Y ψ - ν) := by
  simp only [centeredSecond, expect, productWeight, Fintype.sum_prod_type,
    Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  apply Finset.sum_congr rfl
  intro ψ _
  ring

theorem product_centeredSecond_of_means (p : Ω → ℝ) (q : Ψ → ℝ)
    (X : Ω → ℝ) (Y : Ψ → ℝ) (μ ν : ℝ)
    (hp : ∑ ω, p ω = 1) (hq : ∑ ψ, q ψ = 1)
    (hμ : expect p X = μ) (hν : expect q Y = ν) :
    centeredSecond (productWeight p q) (fun w => X w.1 + Y w.2) (μ + ν) =
      centeredSecond p X μ + centeredSecond q Y ν := by
  rw [product_centeredSecond, hp, hq,
    centered_expect_zero p X μ hp hμ, centered_expect_zero q Y ν hq hν]
  ring

end ProductLaw

/-! A recursively nested finite product gives explicit iid cohort atoms.
Each coordinate is one complete finite-horizon source cohort noise word. -/

def Samples (Ω : Type*) : ℕ → Type _
  | 0 => PUnit
  | n + 1 => Ω × Samples Ω n

instance samplesFintype (Ω : Type*) [Fintype Ω] (n : ℕ) : Fintype (Samples Ω n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih =>
    letI := ih
    change Fintype (Ω × Samples Ω n)
    infer_instance

def iidWeight {Ω : Type*} (p : Ω → ℝ) : (n : ℕ) → Samples Ω n → ℝ
  | 0, _ => 1
  | n + 1, w => p w.1 * iidWeight p n w.2

def sampleSum {Ω : Type*} (X : Ω → ℝ) : (n : ℕ) → Samples Ω n → ℝ
  | 0, _ => 0
  | n + 1, w => X w.1 + sampleSum X n w.2

theorem iidWeight_nonneg {Ω : Type*} (p : Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (n : ℕ) : ∀ w, 0 ≤ iidWeight p n w := by
  induction n with
  | zero => intro w; exact zero_le_one
  | succ n ih => intro w; exact mul_nonneg (hp w.1) (ih w.2)

theorem iidWeight_total {Ω : Type*} [Fintype Ω] (p : Ω → ℝ)
    (hp : ∑ ω, p ω = 1) (n : ℕ) :
    (∑ w, iidWeight p n w) = 1 := by
  induction n with
  | zero =>
    have hu : (Finset.univ : Finset (Samples Ω 0)) = {PUnit.unit} := by
      ext w
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      change w = (PUnit.unit : PUnit)
      cases w
      rfl
    rw [hu, Finset.sum_singleton]
    rfl
  | succ n ih =>
    change (∑ w : Ω × Samples Ω n, productWeight p (iidWeight p n) w) = 1
    rw [productWeight_total, hp, ih, one_mul]

theorem iid_expect_sum {Ω : Type*} [Fintype Ω] (p : Ω → ℝ)
    (X : Ω → ℝ) (μ : ℝ) (hp : ∑ ω, p ω = 1)
    (hμ : expect p X = μ) (n : ℕ) :
    expect (iidWeight p n) (sampleSum X n) = (n : ℝ) * μ := by
  induction n with
  | zero => simp [expect, iidWeight, sampleSum]
  | succ n ih =>
    change expect (productWeight p (iidWeight p n))
      (fun w => X w.1 + sampleSum X n w.2) = ((n + 1 : ℕ) : ℝ) * μ
    rw [product_expect_add, hμ, iidWeight_total p hp n, hp, ih]
    push_cast
    ring

theorem iid_centeredSecond_sum {Ω : Type*} [Fintype Ω] (p : Ω → ℝ)
    (X : Ω → ℝ) (μ : ℝ) (hp : ∑ ω, p ω = 1)
    (hμ : expect p X = μ) (n : ℕ) :
    centeredSecond (iidWeight p n) (sampleSum X n) ((n : ℝ) * μ) =
      (n : ℝ) * centeredSecond p X μ := by
  induction n with
  | zero => simp [centeredSecond, iidWeight, sampleSum]
  | succ n ih =>
    have hm : ((n + 1 : ℕ) : ℝ) * μ = μ + (n : ℝ) * μ := by push_cast; ring
    rw [hm]
    change centeredSecond (productWeight p (iidWeight p n))
      (fun w => X w.1 + sampleSum X n w.2) (μ + (n : ℝ) * μ) = _
    rw [product_centeredSecond_of_means p (iidWeight p n) X (sampleSum X n)
      μ ((n : ℝ) * μ) hp (iidWeight_total p hp n) hμ (iid_expect_sum p X μ hp hμ n), ih]
    push_cast
    ring

/-- The finite exact iid cohort bound, with zero-population outcomes retained.
All moments on the right are computed from the single actual cohort atom law. -/
theorem iid_badRatio_mass_le {Ω : Type*} [Fintype Ω]
    (p : Ω → ℝ) (N Z : Ω → ℝ) (μ ν ε : ℝ) (n : ℕ)
    (hp0 : ∀ ω, 0 ≤ p ω) (hp : ∑ ω, p ω = 1)
    (hμ : expect p N = μ) (hν : expect p Z = ν)
    (hμ0 : 0 < μ) (hν0 : 0 ≤ ν) (hνμ : ν ≤ μ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 0 < n) :
    eventMass (iidWeight p n) (fun w =>
      sampleSum N n w = 0 ∨
        (0 < sampleSum N n w ∧
          ε < |sampleSum Z n w / sampleSum N n w - ν / μ|)) ≤
      9 * (centeredSecond p Z ν + centeredSecond p N μ) /
        ((n : ℝ) * ε ^ 2 * μ ^ 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hratio : ((n : ℝ) * ν) / ((n : ℝ) * μ) = ν / μ := by
    field_simp [ne_of_gt hn0, ne_of_gt hμ0]
  have h := badRatio_mass_le (iidWeight p n) (sampleSum N n) (sampleSum Z n)
    ((n : ℝ) * μ) ((n : ℝ) * ν) ε (iidWeight_nonneg p hp0 n)
    (mul_pos hn0 hμ0) (mul_nonneg (le_of_lt hn0) hν0)
    (mul_le_mul_of_nonneg_left hνμ (le_of_lt hn0)) hε0 hε1
  rw [iid_centeredSecond_sum p Z ν hp hν n,
    iid_centeredSecond_sum p N μ hp hμ n] at h
  have hfrac :
      9 * ((n : ℝ) * centeredSecond p Z ν + (n : ℝ) * centeredSecond p N μ) /
          (ε ^ 2 * ((n : ℝ) * μ) ^ 2) =
        9 * (centeredSecond p Z ν + centeredSecond p N μ) /
          ((n : ℝ) * ε ^ 2 * μ ^ 2) := by
    field_simp [ne_of_gt hn0, ne_of_gt hε0, ne_of_gt hμ0]
    <;> ring
  simpa only [BadRatio, hratio, hfrac] using h

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SourceCohortFeedback
