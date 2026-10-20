import UEOTQM.Weighted
import UEOT.V3.QSDPerron
import Mathlib.Data.Matrix.Basis

/-!
# Actual quantum realization of a finite killed kernel

Distributions are row vectors: `(p Q) j = sum i, p i * Q i j`.
The matrix unit `|j><i|` measures source `i` and prepares destination `j`.
Success has weight `Q i j`; failure has the diagonal row deficit. Their
weighted completeness is proved before forming an ordinary Kraus instrument.

The Core Perron results are used with explicit eigenvector hypotheses.
No spectral existence, irreducibility, convergence or quantum/classical
intertwining equality is assumed as a structure field.
-/

namespace UEOTQM.Survival

open Matrix
open scoped BigOperators ComplexOrder

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Real weights embedded as the diagonal of a genuine complex operator. -/
def diagonalOperator (p : ι → ℝ) : Operator ι :=
  Matrix.diagonal (fun i => (p i : ℂ))

omit [Fintype ι] in
theorem diagonalOperator_posSemidef (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) :
    (diagonalOperator p).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  exact Complex.nonneg_iff.mpr ⟨hp i, rfl⟩

@[simp] theorem mass_diagonalOperator (p : ι → ℝ) :
    mass (diagonalOperator p) = ∑ i, p i := by
  simp [mass, diagonalOperator, Matrix.trace_diagonal, Complex.re_sum]

omit [Fintype ι] in
theorem diagonalOperator_injective :
    Function.Injective (diagonalOperator (ι := ι)) := by
  intro p q h
  funext i
  have hi := congrArg (fun X : Operator ι => (X i i).re) h
  simpa [diagonalOperator] using hi

omit [Fintype ι] in
theorem diagonalOperator_smul (r : ℝ) (p : ι → ℝ) :
    diagonalOperator (fun i => r * p i) = r • diagonalOperator p := by
  ext i j
  by_cases hij : i = j <;>
    simp [diagonalOperator, hij, Complex.real_smul]

/-- A normalized nonnegative classical law gives an actual density operator. -/
def diagonalDensity (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) : Density ι where
  matrix := diagonalOperator p
  positive := diagonalOperator_posSemidef p hp
  trace_one := by
    simp only [diagonalOperator, Matrix.trace_diagonal]
    exact_mod_cast hsum

@[simp] theorem diagonalDensity_matrix (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) :
    (diagonalDensity p hp hsum).matrix = diagonalOperator p := rfl

/-- `matrixUnit j i = |j><i|`: destination first, source second. -/
def matrixUnit (j i : ι) : Operator ι := Matrix.single j i 1

@[simp] theorem matrixUnit_gram (j i : ι) :
    (matrixUnit j i)ᴴ * matrixUnit j i = Matrix.single i i 1 := by
  simp [matrixUnit]

@[simp] theorem matrixUnit_sandwich (j i : ι) (X : Operator ι) :
    matrixUnit j i * X * (matrixUnit j i)ᴴ = Matrix.single j j (X i i) := by
  simp [matrixUnit]

/-- The actual weighted measure-prepare operation, before sign restrictions. -/
def measurePrepare (Q : Matrix ι ι ℝ) (X : Operator ι) : Operator ι :=
  weightedKrausMap (fun ij : ι × ι => Q ij.1 ij.2)
    (fun ij => matrixUnit ij.2 ij.1) X

theorem measurePrepare_apply (Q : Matrix ι ι ℝ) (X : Operator ι) :
    measurePrepare Q X =
      Matrix.diagonal (fun j => ∑ i, (Q i j : ℂ) * X i i) := by
  ext a b
  by_cases hab : a = b
  · subst b
    simp [measurePrepare, weightedKrausMap, Fintype.sum_prod_type,
      Matrix.sum_apply, Matrix.single_apply, Complex.real_smul]
  · have hnot (j : ι) : ¬(j = a ∧ j = b) := by
      rintro ⟨rfl, rfl⟩
      exact hab rfl
    simp [measurePrepare, weightedKrausMap, Matrix.sum_apply, hab, hnot]

theorem measurePrepare_diagonal (Q : Matrix ι ι ℝ) (p : ι → ℝ) :
    measurePrepare Q (diagonalOperator p) =
      diagonalOperator (UEOT.V3.QSDPerron.rowApply p Q) := by
  rw [measurePrepare_apply]
  congr 1
  funext j
  simp [diagonalOperator, UEOT.V3.QSDPerron.rowApply,
    Complex.ofReal_sum, Complex.ofReal_mul, mul_comm]

theorem measurePrepare_gram (Q : Matrix ι ι ℝ) :
    (∑ ij : ι × ι, Q ij.1 ij.2 •
      ((matrixUnit ij.2 ij.1)ᴴ * matrixUnit ij.2 ij.1)) =
      diagonalOperator (fun i => ∑ j, Q i j) := by
  simp only [matrixUnit_gram]
  ext a b
  by_cases hab : a = b
  · subst b
    simp [Fintype.sum_prod_type, Matrix.sum_apply,
      Matrix.single_apply, diagonalOperator,
      Complex.real_smul, Complex.ofReal_sum]
  · have hnot (i : ι) : ¬(i = a ∧ i = b) := by
      rintro ⟨rfl, rfl⟩
      exact hab rfl
    simp [Matrix.sum_apply, diagonalOperator, hab, hnot]

/-- Failure remains in the measured source state, with its missing row mass. -/
def failureKernel (Q : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal (fun i => 1 - ∑ j, Q i j)

theorem failureKernel_nonneg (Q : Matrix ι ι ℝ)
    (hrows : ∀ i, ∑ j, Q i j ≤ 1) : ∀ i j, 0 ≤ failureKernel Q i j := by
  intro i j
  by_cases hij : i = j
  · subst j
    simpa [failureKernel] using sub_nonneg.mpr (hrows i)
  · simp [failureKernel, hij]

/-- Only two outcomes are distinguished: `true` means survival. -/
def outcomeKernel (Q : Matrix ι ι ℝ) (o : Bool) : Matrix ι ι ℝ :=
  if o then Q else failureKernel Q

theorem outcomeKernel_complete (Q : Matrix ι ι ℝ) :
    (∑ o : Bool, ∑ ij : ι × ι, outcomeKernel Q o ij.1 ij.2 •
      ((matrixUnit ij.2 ij.1)ᴴ * matrixUnit ij.2 ij.1)) = 1 := by
  simp_rw [measurePrepare_gram]
  ext a b
  by_cases hab : a = b
  · subst b
    simp [outcomeKernel, failureKernel, diagonalOperator, Matrix.sum_apply,
      Matrix.diagonal_apply, apply_ite]
  · simp [outcomeKernel, failureKernel, diagonalOperator, Matrix.sum_apply, hab]

/-- Nonnegative substochastic data are converted to an ordinary instrument.
Completeness and the quantum/classical interpretation are proved, not fields. -/
def weightedInstrument (Q : Matrix ι ι ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hrows : ∀ i, ∑ j, Q i j ≤ 1) : WeightedInstrument ι Bool (ι × ι) where
  weight o ij := outcomeKernel Q o ij.1 ij.2
  kraus _ ij := matrixUnit ij.2 ij.1
  weight_nonneg := by
    intro o ij
    cases o
    · exact failureKernel_nonneg Q hrows ij.1 ij.2
    · exact hQ ij.1 ij.2
  complete := outcomeKernel_complete Q

def instrument (Q : Matrix ι ι ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hrows : ∀ i, ∑ j, Q i j ≤ 1) : Instrument ι Bool (ι × ι) :=
  (weightedInstrument Q hQ hrows).toInstrument

theorem instrument_branch (Q : Matrix ι ι ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hrows : ∀ i, ∑ j, Q i j ≤ 1) (o : Bool) (X : Operator ι) :
    (instrument Q hQ hrows).branch o X = measurePrepare (outcomeKernel Q o) X := by
  rw [instrument, WeightedInstrument.toInstrument_branch]
  rfl

@[simp] theorem success_branch (Q : Matrix ι ι ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hrows : ∀ i, ∑ j, Q i j ≤ 1) (p : ι → ℝ) :
    (instrument Q hQ hrows).branch true (diagonalOperator p) =
      diagonalOperator (UEOT.V3.QSDPerron.rowApply p Q) := by
  rw [instrument_branch]
  exact measurePrepare_diagonal Q p

omit [DecidableEq ι] in
theorem rowApply_nonneg (Q : Matrix ι ι ℝ) (p : ι → ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hp : ∀ i, 0 ≤ p i) :
    ∀ j, 0 ≤ UEOT.V3.QSDPerron.rowApply p Q j := by
  intro j
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hp i) (hQ i j))

/-- The ordinary Kraus probability is the classical surviving row mass. -/
theorem success_probability (Q : Matrix ι ι ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hrows : ∀ i, ∑ j, Q i j ≤ 1) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    (instrument Q hQ hrows).probability (diagonalDensity p hp hsum) true =
      ∑ j, UEOT.V3.QSDPerron.rowApply p Q j := by
  unfold Instrument.probability
  rw [diagonalDensity_matrix, success_branch, mass_diagonalOperator]

/-- Conditioning is performed only with a positive probability witness. -/
theorem success_posterior_matrix (Q : Matrix ι ι ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hrows : ∀ i, ∑ j, Q i j ≤ 1) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hpos : 0 < (instrument Q hQ hrows).probability
      (diagonalDensity p hp hsum) true) :
    ((instrument Q hQ hrows).posterior (diagonalDensity p hp hsum) true hpos).matrix =
      diagonalOperator (fun j => UEOT.V3.QSDPerron.rowApply p Q j /
        (∑ k, UEOT.V3.QSDPerron.rowApply p Q k)) := by
  rw [Instrument.posterior_matrix, diagonalDensity_matrix, success_branch,
    success_probability, ← diagonalOperator_smul]
  congr 1
  funext j
  exact mul_comm _ _

/-- Repeated success is an actual chronological instrument record. -/
def killedIterate (I : Instrument ι Bool (ι × ι)) (n : ℕ) (X : Operator ι) : Operator ι :=
  recordOperator (fun _ : Unit => I) (List.replicate n ((), true)) X

theorem killedIterate_posSemidef (I : Instrument ι Bool (ι × ι)) (n : ℕ)
    {X : Operator ι} (hX : X.PosSemidef) : (killedIterate I n X).PosSemidef :=
  recordOperator_posSemidef (fun _ : Unit => I) _ hX

/-- The whole repeated-success quantum operator equals `diag (p Q^n)`. -/
theorem killedIterate_diagonal (Q : Matrix ι ι ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hrows : ∀ i, ∑ j, Q i j ≤ 1) (p : ι → ℝ) (n : ℕ) :
    killedIterate (instrument Q hQ hrows) n (diagonalOperator p) =
      diagonalOperator (UEOT.V3.QSDPerron.rowApply p (Q ^ n)) := by
  induction n generalizing p with
  | zero =>
      simp only [killedIterate, List.replicate_zero, recordOperator, pow_zero]
      congr 1
      funext j
      simp [UEOT.V3.QSDPerron.rowApply, Matrix.one_apply]
  | succ n ih =>
      change recordOperator (fun _ : Unit => instrument Q hQ hrows)
        (((), true) :: List.replicate n ((), true)) (diagonalOperator p) = _
      simp only [recordOperator]
      rw [success_branch]
      change killedIterate (instrument Q hQ hrows) n
        (diagonalOperator (UEOT.V3.QSDPerron.rowApply p Q)) = _
      rw [ih, pow_succ', UEOT.V3.QSDPerron.rowApply_mul]

def survivalMass (I : Instrument ι Bool (ι × ι)) (ρ : Density ι) (n : ℕ) : ℝ :=
  mass (killedIterate I n ρ.matrix)

theorem survivalMass_eq_response (I : Instrument ι Bool (ι × ι))
    (ρ : Density ι) (n : ℕ) :
    survivalMass I ρ n = response (fun _ : Unit => I) ρ
      (List.replicate n ((), true)) := rfl

theorem survivalMass_diagonal (Q : Matrix ι ι ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hrows : ∀ i, ∑ j, Q i j ≤ 1) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (n : ℕ) :
    survivalMass (instrument Q hQ hrows) (diagonalDensity p hp hsum) n =
      ∑ j, UEOT.V3.QSDPerron.rowApply p (Q ^ n) j := by
  unfold survivalMass
  rw [diagonalDensity_matrix, killedIterate_diagonal, mass_diagonalOperator]

/-- The normalized state after the actual success word; never defined at zero mass. -/
def conditionalState (I : Instrument ι Bool (ι × ι)) (ρ : Density ι) (n : ℕ)
    (hpos : 0 < survivalMass I ρ n) : Density ι :=
  normalize (killedIterate I n ρ.matrix) (killedIterate_posSemidef I n ρ.positive) hpos

/-- Actual reuse of the frozen Core finite Perron power theorem. -/
theorem qsd_killedIterate (Q : Matrix ι ι ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hrows : ∀ i, ∑ j, Q i j ≤ 1) (q : ι → ℝ) (r : ℝ)
    (hleft : ∀ j, UEOT.V3.QSDPerron.rowApply q Q j = r * q j) (n : ℕ) :
    killedIterate (instrument Q hQ hrows) n (diagonalOperator q) =
      r ^ n • diagonalOperator q := by
  have hd : (inferInstance : DecidableEq ι) = Classical.decEq ι := Subsingleton.elim _ _
  cases hd
  classical
  rw [killedIterate_diagonal]
  have heq : UEOT.V3.QSDPerron.rowApply q (Q ^ n) = fun j => r ^ n * q j :=
    funext (UEOT.V3.QSDPerron.leftPerron_pow Q q r hleft n)
  rw [heq, diagonalOperator_smul]

/-- The probability of the genuine all-success record is `r^n`, not an input field. -/
theorem qsd_survival_pow (Q : Matrix ι ι ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hrows : ∀ i, ∑ j, Q i j ≤ 1) (q : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hqsum : ∑ i, q i = 1) (r : ℝ)
    (hleft : ∀ j, UEOT.V3.QSDPerron.rowApply q Q j = r * q j) (n : ℕ) :
    survivalMass (instrument Q hQ hrows) (diagonalDensity q hq hqsum) n = r ^ n := by
  have hd : (inferInstance : DecidableEq ι) = Classical.decEq ι := Subsingleton.elim _ _
  cases hd
  classical
  rw [survivalMass_diagonal]
  exact UEOT.V3.QSDPerron.qsd_survival_mass_pow Q q r hqsum hleft n

theorem qsd_survival_pos (Q : Matrix ι ι ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hrows : ∀ i, ∑ j, Q i j ≤ 1) (q : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hqsum : ∑ i, q i = 1) (r : ℝ) (hr : 0 < r)
    (hleft : ∀ j, UEOT.V3.QSDPerron.rowApply q Q j = r * q j) (n : ℕ) :
    0 < survivalMass (instrument Q hQ hrows) (diagonalDensity q hq hqsum) n := by
  rw [qsd_survival_pow Q hQ hrows q hq hqsum r hleft n]
  exact pow_pos hr n

/-- The actual conditioned quantum state is the original diagonal QSD.
Core `qsd_all_steps` is applied only after deriving the quantum/row identity. -/
theorem qsd_conditionalState (Q : Matrix ι ι ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hrows : ∀ i, ∑ j, Q i j ≤ 1) (q : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hqsum : ∑ i, q i = 1) (r : ℝ) (hr : 0 < r)
    (hleft : ∀ j, UEOT.V3.QSDPerron.rowApply q Q j = r * q j) (n : ℕ)
    (hpos : 0 < survivalMass (instrument Q hQ hrows) (diagonalDensity q hq hqsum) n) :
    conditionalState (instrument Q hQ hrows) (diagonalDensity q hq hqsum) n hpos =
      diagonalDensity q hq hqsum := by
  have hd : (inferInstance : DecidableEq ι) = Classical.decEq ι := Subsingleton.elim _ _
  cases hd
  classical
  apply Density.ext
  change (survivalMass (instrument Q hQ hrows) (diagonalDensity q hq hqsum) n)⁻¹ •
      killedIterate (instrument Q hQ hrows) n (diagonalOperator q) = diagonalOperator q
  rw [qsd_survival_pow Q hQ hrows q hq hqsum r hleft n,
    killedIterate_diagonal, ← diagonalOperator_smul]
  congr 1
  funext j
  have h := UEOT.V3.QSDPerron.qsd_all_steps Q q r hr hleft n j
  simpa only [div_eq_mul_inv, mul_comm] using h

omit [DecidableEq ι] in
/-- The probability meaning bounds the conditional survival factor by one. -/
theorem qsd_rate_le_one (Q : Matrix ι ι ℝ)
    (hrows : ∀ i, ∑ j, Q i j ≤ 1) (q : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hqsum : ∑ i, q i = 1) (r : ℝ)
    (hleft : ∀ j, UEOT.V3.QSDPerron.rowApply q Q j = r * q j) : r ≤ 1 :=
  UEOT.V3.QSDPerron.perron_root_le_one_of_substochastic Q q r hq hrows hqsum hleft

omit [Fintype ι] [DecidableEq ι] in
/-- Positivity makes the Core Doob transform a genuine nonnegative kernel. -/
theorem doobTransform_nonneg (Q : Matrix ι ι ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (h : ι → ℝ) (r : ℝ) (hr : 0 < r) (hh : ∀ i, 0 < h i) :
    ∀ i j, 0 ≤ UEOT.V3.QSDPerron.doobTransform Q h r i j := by
  intro i j
  exact div_nonneg (mul_nonneg (hQ i j) (hh j).le) (mul_pos hr (hh i)).le

/-- Actual ordinary Kraus realization of the Core Doob kernel. Its row
completeness follows from the stated right eigenrelation, not an extra field.
No infinite-horizon conditioning limit is asserted here. -/
def doobInstrument (Q : Matrix ι ι ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (h : ι → ℝ) (r : ℝ) (hr : 0 < r) (hh : ∀ i, 0 < h i)
    (hright : ∀ i, UEOT.V3.QSDPerron.colApply Q h i = r * h i) :
    Instrument ι Bool (ι × ι) :=
  instrument (UEOT.V3.QSDPerron.doobTransform Q h r)
    (doobTransform_nonneg Q hQ h r hr hh)
    (fun i => (UEOT.V3.QSDPerron.doobTransform_row_sum Q h r hr hh hright i).le)

/-- The Doob invariant density uses `pi_i = q_i * h_i`. It is generally
different from the original killed-kernel QSD `q`. -/
def doobDensity (q h : ι → ℝ) (hq : ∀ i, 0 ≤ q i) (hh : ∀ i, 0 < h i)
    (hqh : ∑ i, q i * h i = 1) : Density ι :=
  diagonalDensity (UEOT.V3.QSDPerron.doobInvariant q h)
    (fun i => mul_nonneg (hq i) (hh i).le)
    (UEOT.V3.QSDPerron.doobInvariant_sum q h hqh)

/-- Core stationarity is transported to the actual complex-matrix branch. -/
theorem doob_success_branch (Q : Matrix ι ι ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (q h : ι → ℝ) (r : ℝ) (hr : 0 < r) (hh : ∀ i, 0 < h i)
    (hleft : ∀ j, UEOT.V3.QSDPerron.rowApply q Q j = r * q j)
    (hright : ∀ i, UEOT.V3.QSDPerron.colApply Q h i = r * h i) :
    (doobInstrument Q hQ h r hr hh hright).branch true
      (diagonalOperator (UEOT.V3.QSDPerron.doobInvariant q h)) =
        diagonalOperator (UEOT.V3.QSDPerron.doobInvariant q h) := by
  rw [doobInstrument, success_branch]
  congr 1
  funext j
  exact UEOT.V3.QSDPerron.doobInvariant_stationary Q q h r hr hh hleft j

/-- Every normalized diagonal input survives the stochastic Doob step. -/
theorem doob_success_probability (Q : Matrix ι ι ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (h : ι → ℝ) (r : ℝ) (hr : 0 < r) (hh : ∀ i, 0 < h i)
    (hright : ∀ i, UEOT.V3.QSDPerron.colApply Q h i = r * h i)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    (doobInstrument Q hQ h r hr hh hright).probability
      (diagonalDensity p hp hsum) true = 1 := by
  rw [doobInstrument, success_probability]
  unfold UEOT.V3.QSDPerron.rowApply
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum,
    UEOT.V3.QSDPerron.doobTransform_row_sum Q h r hr hh hright, mul_one]
  exact hsum

/-- The genuine finite all-success record fixes the Doob invariant operator. -/
theorem doob_killedIterate (Q : Matrix ι ι ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (q h : ι → ℝ) (r : ℝ) (hr : 0 < r) (hh : ∀ i, 0 < h i)
    (hleft : ∀ j, UEOT.V3.QSDPerron.rowApply q Q j = r * q j)
    (hright : ∀ i, UEOT.V3.QSDPerron.colApply Q h i = r * h i) (n : ℕ) :
    killedIterate (doobInstrument Q hQ h r hr hh hright) n
      (diagonalOperator (UEOT.V3.QSDPerron.doobInvariant q h)) =
        diagonalOperator (UEOT.V3.QSDPerron.doobInvariant q h) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change recordOperator (fun _ : Unit => doobInstrument Q hQ h r hr hh hright)
        (((), true) :: List.replicate n ((), true))
        (diagonalOperator (UEOT.V3.QSDPerron.doobInvariant q h)) = _
      simp only [recordOperator, doob_success_branch Q hQ q h r hr hh hleft hright]
      exact ih

theorem doob_survivalMass (Q : Matrix ι ι ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (q h : ι → ℝ) (hq : ∀ i, 0 ≤ q i) (r : ℝ) (hr : 0 < r)
    (hh : ∀ i, 0 < h i) (hqh : ∑ i, q i * h i = 1)
    (hleft : ∀ j, UEOT.V3.QSDPerron.rowApply q Q j = r * q j)
    (hright : ∀ i, UEOT.V3.QSDPerron.colApply Q h i = r * h i) (n : ℕ) :
    survivalMass (doobInstrument Q hQ h r hr hh hright)
      (doobDensity q h hq hh hqh) n = 1 := by
  change mass (killedIterate (doobInstrument Q hQ h r hr hh hright) n
    (diagonalOperator (UEOT.V3.QSDPerron.doobInvariant q h))) = 1
  rw [doob_killedIterate Q hQ q h r hr hh hleft hright n, mass_diagonalOperator]
  exact UEOT.V3.QSDPerron.doobInvariant_sum q h hqh

/-- Finite positive-event conditioning of the realized Doob process fixes
`diag (q*h)`. This does not identify that state with `diag q`. -/
theorem doob_conditionalState (Q : Matrix ι ι ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (q h : ι → ℝ) (hq : ∀ i, 0 ≤ q i) (r : ℝ) (hr : 0 < r)
    (hh : ∀ i, 0 < h i) (hqh : ∑ i, q i * h i = 1)
    (hleft : ∀ j, UEOT.V3.QSDPerron.rowApply q Q j = r * q j)
    (hright : ∀ i, UEOT.V3.QSDPerron.colApply Q h i = r * h i) (n : ℕ)
    (hpos : 0 < survivalMass (doobInstrument Q hQ h r hr hh hright)
      (doobDensity q h hq hh hqh) n) :
    conditionalState (doobInstrument Q hQ h r hr hh hright)
      (doobDensity q h hq hh hqh) n hpos = doobDensity q h hq hh hqh := by
  apply Density.ext
  change (survivalMass (doobInstrument Q hQ h r hr hh hright)
      (doobDensity q h hq hh hqh) n)⁻¹ •
      killedIterate (doobInstrument Q hQ h r hr hh hright) n
        (diagonalOperator (UEOT.V3.QSDPerron.doobInvariant q h)) =
    diagonalOperator (UEOT.V3.QSDPerron.doobInvariant q h)
  rw [doob_survivalMass Q hQ q h hq r hr hh hqh hleft hright n,
    doob_killedIterate Q hQ q h r hr hh hleft hright n, inv_one, one_smul]

end

end UEOTQM.Survival
