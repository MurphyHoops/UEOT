import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Correlated Two-Mode Gaussian Bath Identifiability & Signed-Phase Inversion (`P-MICRO-10`)

Formalizes the mathematical core of Chapter 71 (`v31.15`):
1. Physical admissibility of the correlated two-mode Gaussian bath `(λ, n, c)` via
   nonnegative normal-mode occupancies `n - c ≥ 0` and `n + c ≥ 0`.
2. Exact free-Ramsey indistinguishability of the witness pair
   `(3/10, 1/2, 1/4)` and `(1/3, 31/100, 81/400)`: both lie strictly inside the
   physical interior `[1/5, 2/5] × {n ≥ |c| > 0}` yet generate identical Ramsey
   decay exponents `u = λ^2 (2n + 1) = 9/50` and `v = λ^2 c = 9/400`, hence identical
   free-Ramsey expectations `η * exp(-u A - v B)` for ALL durations and visibilities.
3. Exact global identifiability and quantitative Lipschitz stability when augmented
   by the bath-preserving signed Weyl commutator phase observable `w = λ^2`.
-/

namespace UEOTPhysicsUnification.CorrelatedBathIdentifiability

/-- Parameter tuple `(λ, n, c)` for the correlated two-mode Gaussian bath. -/
structure BathParams where
  lam : ℝ
  n : ℝ
  c : ℝ

/-- Physical normal-mode occupancy positivity (`n_+ = n + c ≥ 0`, `n_- = n - c ≥ 0`)
and positive coupling `λ > 0`. -/
def BathParams.Admissible (p : BathParams) : Prop :=
  0 < p.lam ∧ 0 ≤ p.n - p.c ∧ 0 ≤ p.n + p.c

theorem admissible_nonneg_n {p : BathParams} (hp : p.Admissible) : 0 ≤ p.n := by
  rcases hp with ⟨_, h1, h2⟩
  linarith

/-- The two combinations accessible to arbitrary-duration ordinary free-Ramsey fringes:
`u = λ^2 (2n + 1)` and `v = λ^2 c`. -/
def ramseyObservablePair (p : BathParams) : ℝ × ℝ :=
  (p.lam ^ 2 * (2 * p.n + 1), p.lam ^ 2 * p.c)

/-- Free-Ramsey X expectation `m(t) = η * exp(-u A(t) - v B(t))` for arbitrary mode
displacement weights `A, B` and shared visibility `η`. -/
noncomputable def freeRamseyMean (η : ℝ) (p : BathParams) (A B : ℝ) : ℝ :=
  let uv := ramseyObservablePair p
  η * Real.exp (-(uv.1 * A + uv.2 * B))

/-- First interior Chapter 71 witness `(3/10, 1/2, 1/4)`. -/
noncomputable def witnessOne : BathParams :=
  { lam := 3 / 10, n := 1 / 2, c := 1 / 4 }

/-- Second interior Chapter 71 witness `(1/3, 31/100, 81/400)`. -/
noncomputable def witnessTwo : BathParams :=
  { lam := 1 / 3, n := 31 / 100, c := 81 / 400 }

theorem witnessOne_admissible : witnessOne.Admissible := by
  unfold BathParams.Admissible witnessOne
  norm_num

theorem witnessTwo_admissible : witnessTwo.Admissible := by
  unfold BathParams.Admissible witnessTwo
  norm_num

theorem witnessOne_ne_witnessTwo : witnessOne ≠ witnessTwo := by
  intro h
  have hlam := congrArg BathParams.lam h
  norm_num [witnessOne, witnessTwo] at hlam

theorem witness_same_ramsey_pair :
    ramseyObservablePair witnessOne = (9 / 50, 9 / 400) ∧
      ramseyObservablePair witnessTwo = (9 / 50, 9 / 400) := by
  unfold ramseyObservablePair witnessOne witnessTwo
  norm_num

/-- **Exact Free-Ramsey Indistinguishability Theorem**:
Two distinct admissible interior bath parameter tuples yield identical free-Ramsey
curves across ALL visibilities `η` and ALL time-dependent kernel values `(A, B)`. -/
theorem exists_distinct_admissible_indistinguishable_ramsey :
    ∃ p₁ p₂ : BathParams,
      p₁.Admissible ∧ p₂.Admissible ∧ p₁ ≠ p₂ ∧
      ∀ η A B : ℝ, freeRamseyMean η p₁ A B = freeRamseyMean η p₂ A B := by
  refine ⟨witnessOne, witnessTwo, witnessOne_admissible, witnessTwo_admissible,
    witnessOne_ne_witnessTwo, ?_⟩
  intro η A B
  unfold freeRamseyMean
  rw [witness_same_ramsey_pair.1, witness_same_ramsey_pair.2]

/-- Extended observable triple `(u, v, w) = (λ^2 (2n + 1), λ^2 c, λ^2)` obtained by adding
the bath-preserving signed Weyl phase intervention `w = λ^2`. -/
def signedInterventionTriple (p : BathParams) : ℝ × ℝ × ℝ :=
  (p.lam ^ 2 * (2 * p.n + 1), p.lam ^ 2 * p.c, p.lam ^ 2)

/-- Explicit analytic inverse `(u, v, w) ↦ (√w, (u - w)/(2w), v/w)`. -/
noncomputable def invertSignedTriple (u v w : ℝ) : BathParams :=
  { lam := Real.sqrt w
    n := (u - w) / (2 * w)
    c := v / w }

/-- **Global Identifiability Theorem**: On `λ > 0`, `invertSignedTriple` recovers `(λ, n, c)`
uniquely and exactly from `(u, v, w)`. -/
theorem invert_signedInterventionTriple {p : BathParams} (hlam : 0 < p.lam) :
    invertSignedTriple
      (signedInterventionTriple p).1
      (signedInterventionTriple p).2.1
      (signedInterventionTriple p).2.2 = p := by
  cases p with
  | mk lam n c =>
    dsimp [BathParams.lam] at hlam
    have hw : lam ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hlam)
    unfold signedInterventionTriple invertSignedTriple
    congr 1
    · exact Real.sqrt_sq (le_of_lt hlam)
    · field_simp [hw]
      ring
    · field_simp [hw]

theorem signedInterventionTriple_injective {p₁ p₂ : BathParams}
    (h₁ : 0 < p₁.lam) (h₂ : 0 < p₂.lam)
    (heq : signedInterventionTriple p₁ = signedInterventionTriple p₂) :
    p₁ = p₂ := by
  rw [← invert_signedInterventionTriple h₁, ← invert_signedInterventionTriple h₂, heq]

/-- Signed phase observable `w = λ^2` strictly separates the two free-Ramsey-degenerate witnesses
by `1/9 - 9/100 = 19/900 > 0`. -/
theorem signed_phase_separates_witnesses :
    (signedInterventionTriple witnessTwo).2.2 -
      (signedInterventionTriple witnessOne).2.2 = 19 / 900 := by
  unfold signedInterventionTriple witnessOne witnessTwo
  norm_num

/-- **Quantitative Inverse Stability Bound for `c = v / w`**:
Whenever `w₁, w₂ ≥ w_min > 0` and `|v₂| ≤ w₂ * c_max`,
`|v₁/w₁ - v₂/w₂| ≤ |v₁ - v₂| / w_min + c_max * |w₁ - w₂| / w_min`. -/
theorem correlation_inverse_stability
    {v₁ v₂ w₁ w₂ wMin cMax : ℝ}
    (hwMin : 0 < wMin) (hw₁ : wMin ≤ w₁) (hw₂ : wMin ≤ w₂)
    (hc : |v₂| ≤ w₂ * cMax) :
    |v₁ / w₁ - v₂ / w₂| ≤ |v₁ - v₂| / wMin + cMax * |w₁ - w₂| / wMin := by
  have hw1_pos : 0 < w₁ := lt_of_lt_of_le hwMin hw₁
  have hw2_pos : 0 < w₂ := lt_of_lt_of_le hwMin hw₂
  have hdecomp : v₁ / w₁ - v₂ / w₂ = (v₁ - v₂) / w₁ + (v₂ / w₂) * ((w₂ - w₁) / w₁) := by
    field_simp [ne_of_gt hw1_pos, ne_of_gt hw2_pos]
    ring
  rw [hdecomp]
  have htri := abs_add_le ((v₁ - v₂) / w₁) ((v₂ / w₂) * ((w₂ - w₁) / w₁))
  have hterm1 : |(v₁ - v₂) / w₁| ≤ |v₁ - v₂| / wMin := by
    rw [abs_div, abs_of_pos hw1_pos]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hwMin hw₁
  have hv2w2 : |v₂ / w₂| ≤ cMax := by
    rw [abs_div, abs_of_pos hw2_pos, div_le_iff₀ hw2_pos]
    linarith [hc]
  have hcMax_nonneg : 0 ≤ cMax := le_trans (abs_nonneg _) hv2w2
  have hterm2 : |(v₂ / w₂) * ((w₂ - w₁) / w₁)| ≤ cMax * |w₁ - w₂| / wMin := by
    rw [abs_mul, abs_div (w₂ - w₁) w₁, abs_of_pos hw1_pos, abs_sub_comm w₂ w₁]
    calc
      |v₂ / w₂| * (|w₁ - w₂| / w₁) ≤ cMax * (|w₁ - w₂| / w₁) :=
        mul_le_mul_of_nonneg_right hv2w2 (div_nonneg (abs_nonneg _) (le_of_lt hw1_pos))
      _ = (cMax * |w₁ - w₂|) / w₁ := by ring
      _ ≤ (cMax * |w₁ - w₂|) / wMin :=
        div_le_div_of_nonneg_left (mul_nonneg hcMax_nonneg (abs_nonneg _)) hwMin hw₁
  linarith

end UEOTPhysicsUnification.CorrelatedBathIdentifiability
