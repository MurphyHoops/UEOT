import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

/-!
# P-QSD-02 — finite Perron / Doob representation

The source invokes Perron--Frobenius as K-PF-01 and then proves three
algebraic consequences for a killed finite kernel Q:

* a normalized positive left Perron vector q is quasi-stationary;
* the h-transform Q^up has row sums one;
* pi_i = q_i h_i is an invariant probability law.

This module formalizes exactly that finite algebraic layer.  Existence and
uniqueness of the Perron data remain the standard K-PF-01 input, not a new
UEOT axiom.
-/

namespace UEOT.V3.QSDPerron

noncomputable section

open scoped BigOperators

universe uS

variable {S : Type uS} [Fintype S]

local instance : DecidableEq S := Classical.decEq S

/-- Row-vector action q Q. -/
def rowApply (q : S → ℝ) (Q : Matrix S S ℝ) (j : S) : ℝ :=
  ∑ i : S, q i * Q i j

/-- Column-vector action Q h. -/
def colApply (Q : Matrix S S ℝ) (h : S → ℝ) (i : S) : ℝ :=
  ∑ j : S, Q i j * h j

/-- Doob h-transform attached to positive Perron data. -/
def doobTransform (Q : Matrix S S ℝ) (h : S → ℝ) (ρ : ℝ) :
    Matrix S S ℝ :=
  fun i j => Q i j * h j / (ρ * h i)

/-- Candidate invariant law of the Doob transform. -/
def doobInvariant (q h : S → ℝ) : S → ℝ :=
  fun i => q i * h i

/-- Left Perron eigenrelation propagates to every positive integer step. -/
theorem qsd_one_step
    (Q : Matrix S S ℝ) (q : S → ℝ) (ρ : ℝ)
    (hρ : 0 < ρ)
    (hq : ∀ j, rowApply q Q j = ρ * q j) :
    ∀ j, rowApply q Q j / ρ = q j := by
  intro j
  rw [hq j]
  field_simp [hρ.ne']

/-- The survival mass of the q-law after one killed step is ρ whenever q has
unit total mass. -/
theorem qsd_survival_mass
    (Q : Matrix S S ℝ) (q : S → ℝ) (ρ : ℝ)
    (hqsum : ∑ i : S, q i = 1)
    (hq : ∀ j, rowApply q Q j = ρ * q j) :
    ∑ j : S, rowApply q Q j = ρ := by
  simp_rw [hq]
  rw [← Finset.mul_sum]
  simp [hqsum]


/-- Associativity of the row-vector action, written in the source's component
notation rather than relying on an ambient module-action instance. -/
theorem rowApply_mul
    (q : S → ℝ) (A B : Matrix S S ℝ) :
    rowApply q (A * B) =
      rowApply (fun k => rowApply q A k) B := by
  funext j
  unfold rowApply
  simp only [Matrix.mul_apply]
  calc
    (∑ i : S, q i * ∑ k : S, A i k * B k j) =
        ∑ i : S, ∑ k : S, (q i * A i k) * B k j := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = ∑ k : S, ∑ i : S, (q i * A i k) * B k j := by
      rw [Finset.sum_comm]
    _ = ∑ k : S, (∑ i : S, q i * A i k) * B k j := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_mul]
    _ = ∑ k : S, rowApply q A k * B k j := by
      rfl

/-- The left Perron relation propagates to every discrete killed step:
`q Q^n = ρ^n q`.  This is the exact algebra used by the source to identify
`q` as a quasi-stationary distribution. -/
theorem leftPerron_pow
    (Q : Matrix S S ℝ) (q : S → ℝ) (ρ : ℝ)
    (hleft : ∀ j, rowApply q Q j = ρ * q j) :
    ∀ n j, rowApply q (Q ^ n) j = ρ ^ n * q j := by
  intro n
  induction n with
  | zero =>
      intro j
      classical
      simp [rowApply, Matrix.one_apply]
  | succ n ih =>
      intro j
      rw [pow_succ, rowApply_mul]
      have hfun :
          (fun k => rowApply q (Q ^ n) k) =
            fun k => ρ ^ n * q k := by
        funext k
        exact ih k
      rw [hfun]
      calc
        rowApply (fun k => ρ ^ n * q k) Q j =
            ρ ^ n * rowApply q Q j := by
              unfold rowApply
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k hk
              ring
        _ = ρ ^ n * (ρ * q j) := by rw [hleft j]
        _ = ρ ^ (n + 1) * q j := by
              rw [pow_succ]
              ring

/-- The survival mass from the Perron left eigenlaw is `ρ^n` at every
discrete time, under the normalization `q 1 = 1`. -/
theorem qsd_survival_mass_pow
    (Q : Matrix S S ℝ) (q : S → ℝ) (ρ : ℝ)
    (hqsum : ∑ i : S, q i = 1)
    (hleft : ∀ j, rowApply q Q j = ρ * q j) :
    ∀ n, ∑ j : S, rowApply q (Q ^ n) j = ρ ^ n := by
  intro n
  simp_rw [leftPerron_pow Q q ρ hleft n]
  rw [← Finset.mul_sum]
  simp [hqsum]

/-- Source QSD identity at every finite step: after conditioning the killed
law by its survival mass `ρ^n`, the distribution is again `q`. -/
theorem qsd_all_steps
    (Q : Matrix S S ℝ) (q : S → ℝ) (ρ : ℝ)
    (hρ : 0 < ρ)
    (hleft : ∀ j, rowApply q Q j = ρ * q j) :
    ∀ n j, rowApply q (Q ^ n) j / ρ ^ n = q j := by
  intro n j
  rw [leftPerron_pow Q q ρ hleft n j]
  have hn : ρ ^ n ≠ 0 := pow_ne_zero _ hρ.ne'
  field_simp [hn]

/-- The Doob transform is row-stochastic under the positive right Perron
relation Qh = ρh. -/
theorem doobTransform_row_sum
    (Q : Matrix S S ℝ) (h : S → ℝ) (ρ : ℝ)
    (hρ : 0 < ρ)
    (hh : ∀ i, 0 < h i)
    (heig : ∀ i, colApply Q h i = ρ * h i) :
    ∀ i, ∑ j : S, doobTransform Q h ρ i j = 1 := by
  intro i
  unfold doobTransform
  have hden : ρ * h i ≠ 0 := mul_ne_zero hρ.ne' (hh i).ne'
  calc
    (∑ j : S, Q i j * h j / (ρ * h i)) =
        (∑ j : S, Q i j * h j) / (ρ * h i) := by
          rw [Finset.sum_div]
    _ = colApply Q h i / (ρ * h i) := by rfl
    _ = (ρ * h i) / (ρ * h i) := by rw [heig i]
    _ = 1 := div_self hden

/-- The Perron normalization q h = 1 makes pi_i=q_i h_i a probability
weight vector. -/
theorem doobInvariant_sum
    (q h : S → ℝ)
    (hqh : ∑ i : S, q i * h i = 1) :
    ∑ i : S, doobInvariant q h i = 1 := by
  simpa [doobInvariant] using hqh

/-- pi_i=q_i h_i is invariant for the Doob transform. -/
theorem doobInvariant_stationary
    (Q : Matrix S S ℝ) (q h : S → ℝ) (ρ : ℝ)
    (hρ : 0 < ρ)
    (hh : ∀ i, 0 < h i)
    (hq : ∀ j, rowApply q Q j = ρ * q j) :
    ∀ j,
      rowApply (doobInvariant q h) (doobTransform Q h ρ) j =
        doobInvariant q h j := by
  intro j
  unfold rowApply doobInvariant doobTransform
  have hρ0 : ρ ≠ 0 := hρ.ne'
  calc
    (∑ i : S, (q i * h i) * (Q i j * h j / (ρ * h i))) =
        ∑ i : S, (q i * Q i j) * (h j / ρ) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hhi : h i ≠ 0 := (hh i).ne'
          field_simp [hρ0, hhi]
    _ = (∑ i : S, q i * Q i j) * (h j / ρ) := by
          rw [Finset.sum_mul]
    _ = rowApply q Q j * (h j / ρ) := by rfl
    _ = (ρ * q j) * (h j / ρ) := by rw [hq j]
    _ = q j * h j := by
          field_simp [hρ0]

/-- A nonnegative substochastic killed kernel has Perron survival factor at
most one whenever the normalized nonnegative left Perron vector is a
probability vector.  This recovers the probability semantic side condition
used in the source discussion before P-QSD-02. -/
theorem perron_root_le_one_of_substochastic
    (Q : Matrix S S ℝ) (q : S → ℝ) (ρ : ℝ)
    (hq0 : ∀ i, 0 ≤ q i)
    (hrows : ∀ i, ∑ j : S, Q i j ≤ 1)
    (hqsum : ∑ i : S, q i = 1)
    (hleft : ∀ j, rowApply q Q j = ρ * q j) :
    ρ ≤ 1 := by
  have hmass :
      (∑ j : S, rowApply q Q j) = ρ := by
    simp_rw [hleft]
    rw [← Finset.mul_sum, hqsum, mul_one]
  calc
    ρ = ∑ j : S, rowApply q Q j := hmass.symm
    _ = ∑ i : S, q i * (∑ j : S, Q i j) := by
      unfold rowApply
      calc
        (∑ j : S, ∑ i : S, q i * Q i j) =
            ∑ i : S, ∑ j : S, q i * Q i j := by
          rw [Finset.sum_comm]
        _ = ∑ i : S, q i * (∑ j : S, Q i j) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
    _ ≤ ∑ i : S, q i * 1 := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hrows i) (hq0 i)
    _ = 1 := by simp [hqsum]

/-- Source-facing P-QSD-02 algebraic bundle, conditional on the Perron data
supplied by K-PF-01.  Nonnegativity hypotheses record that q and Q are
probability/subprobability weights; positivity of h and ρ makes the Doob
transform well-defined. -/
theorem p_qsd_02
    (Q : Matrix S S ℝ) (q h : S → ℝ) (ρ : ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j)
    (hq0 : ∀ i, 0 ≤ q i)
    (hρ : 0 < ρ)
    (hh : ∀ i, 0 < h i)
    (hqsum : ∑ i : S, q i = 1)
    (hqh : ∑ i : S, q i * h i = 1)
    (hleft : ∀ j, rowApply q Q j = ρ * q j)
    (hright : ∀ i, colApply Q h i = ρ * h i) :
    (∀ n j, rowApply q (Q ^ n) j / ρ ^ n = q j) ∧
    (∀ n, ∑ j : S, rowApply q (Q ^ n) j = ρ ^ n) ∧
    (∀ i, ∑ j : S, doobTransform Q h ρ i j = 1) ∧
    (∀ i j, 0 ≤ doobTransform Q h ρ i j) ∧
    (∑ i : S, doobInvariant q h i = 1) ∧
    (∀ i, 0 ≤ doobInvariant q h i) ∧
    (∀ j,
      rowApply (doobInvariant q h) (doobTransform Q h ρ) j =
        doobInvariant q h j) := by
  refine ⟨qsd_all_steps Q q ρ hρ hleft,
    qsd_survival_mass_pow Q q ρ hqsum hleft,
    doobTransform_row_sum Q h ρ hρ hh hright, ?_, ?_, ?_, ?_⟩
  · intro i j
    exact div_nonneg
      (mul_nonneg (hQ i j) (le_of_lt (hh j)))
      (mul_nonneg (le_of_lt hρ) (le_of_lt (hh i)))
  · exact doobInvariant_sum q h hqh
  · intro i
    exact mul_nonneg (hq0 i) (le_of_lt (hh i))
  · exact doobInvariant_stationary Q q h ρ hρ hh hleft

/-- Literal killed-kernel wrapper for P-QSD-02.  The source context assumes
that Q is a finite killed substochastic kernel.  The Perron existence and
positivity data are supplied by the standard K-PF-01 input; this theorem
machine-checks the QSD/Doob consequences and also derives rho ≤ 1 from the
substochastic rows. -/
theorem p_qsd_02_killed
    (Q : Matrix S S ℝ) (q h : S → ℝ) (ρ : ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j)
    (hrows : ∀ i, ∑ j : S, Q i j ≤ 1)
    (hq0 : ∀ i, 0 ≤ q i)
    (hρ : 0 < ρ)
    (hh : ∀ i, 0 < h i)
    (hqsum : ∑ i : S, q i = 1)
    (hqh : ∑ i : S, q i * h i = 1)
    (hleft : ∀ j, rowApply q Q j = ρ * q j)
    (hright : ∀ i, colApply Q h i = ρ * h i) :
    ρ ≤ 1 ∧
    (∀ n j, rowApply q (Q ^ n) j / ρ ^ n = q j) ∧
    (∀ n, ∑ j : S, rowApply q (Q ^ n) j = ρ ^ n) ∧
    (∀ i, ∑ j : S, doobTransform Q h ρ i j = 1) ∧
    (∀ i j, 0 ≤ doobTransform Q h ρ i j) ∧
    (∑ i : S, doobInvariant q h i = 1) ∧
    (∀ i, 0 ≤ doobInvariant q h i) ∧
    (∀ j,
      rowApply (doobInvariant q h) (doobTransform Q h ρ) j =
        doobInvariant q h j) := by
  refine ⟨perron_root_le_one_of_substochastic Q q ρ hq0 hrows hqsum hleft, ?_⟩
  exact p_qsd_02 Q q h ρ hQ hq0 hρ hh hqsum hqh hleft hright


end

end UEOT.V3.QSDPerron
