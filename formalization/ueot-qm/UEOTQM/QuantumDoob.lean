import UEOTQM.Weighted
import UEOTQM.Effects

/-!
# Finite quantum survival and an explicit invertible-filter Doob transform

The source is an actual branch of a complete Kraus instrument. Right and left
eigenrelations are explicit hypotheses. A two-sided matrix inverse supplies the
filter; neither transformed completeness nor a stationary state is an input.
The construction proves finite record identities on all complex matrices.
No existence/dominance of spectral data or infinite conditioned limit is claimed.
-/

namespace UEOTQM.QuantumDoob

open Matrix
open scoped BigOperators ComplexOrder

noncomputable section

variable {ι κ O : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [Fintype O]

/-- The actual chronological record containing one selected outcome repeatedly. -/
def successOperator (I : Instrument ι O κ) (o : O) (n : ℕ)
    (X : Operator ι) : Operator ι :=
  recordOperator (fun _ : Unit => I) (List.replicate n ((), o)) X

@[simp] theorem successOperator_zero (I : Instrument ι O κ) (o : O)
    (X : Operator ι) : successOperator I o 0 X = X := rfl

theorem successOperator_succ (I : Instrument ι O κ) (o : O) (n : ℕ)
    (X : Operator ι) :
    successOperator I o (n + 1) X = successOperator I o n (I.branch o X) := rfl

theorem successOperator_smul (I : Instrument ι O κ) (o : O) (n : ℕ)
    (a : ℝ) (X : Operator ι) :
    successOperator I o n (a • X) = a • successOperator I o n X :=
  recordOperator_smul _ _ _ _

theorem successOperator_posSemidef (I : Instrument ι O κ) (o : O) (n : ℕ)
    {X : Operator ι} (hX : X.PosSemidef) :
    (successOperator I o n X).PosSemidef := recordOperator_posSemidef _ _ hX

/-- No diagonal or commutativity restriction on the right eigenoperator. -/
theorem eigen_successOperator (I : Instrument ι O κ) (o : O) (X : Operator ι)
    (r : ℝ) (hX : I.branch o X = r • X) (n : ℕ) :
    successOperator I o n X = r ^ n • X := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [successOperator_succ, hX, successOperator_smul, ih, smul_smul, pow_succ']

def successMass (I : Instrument ι O κ) (o : O) (ρ : Density ι) (n : ℕ) : ℝ :=
  mass (successOperator I o n ρ.matrix)

theorem successMass_eq_response (I : Instrument ι O κ) (o : O)
    (ρ : Density ι) (n : ℕ) :
    successMass I o ρ n = response (fun _ : Unit => I) ρ
      (List.replicate n ((), o)) := rfl

theorem eigen_successMass (I : Instrument ι O κ) (o : O) (ρ : Density ι)
    (r : ℝ) (hρ : I.branch o ρ.matrix = r • ρ.matrix) (n : ℕ) :
    successMass I o ρ n = r ^ n := by
  simp only [successMass, eigen_successOperator I o ρ.matrix r hρ n,
    mass_smul, ρ.mass_one, mul_one]

theorem eigen_successMass_pos (I : Instrument ι O κ) (o : O) (ρ : Density ι)
    (r : ℝ) (hr : 0 < r) (hρ : I.branch o ρ.matrix = r • ρ.matrix) (n : ℕ) :
    0 < successMass I o ρ n := by
  rw [eigen_successMass I o ρ r hρ n]
  exact pow_pos hr n

/-- Conditioning uses the actual record and requires positive record mass. -/
def conditionalState (I : Instrument ι O κ) (o : O) (ρ : Density ι) (n : ℕ)
    (hp : 0 < successMass I o ρ n) : Density ι :=
  normalize (successOperator I o n ρ.matrix)
    (successOperator_posSemidef I o n ρ.positive) hp

theorem eigen_conditionalState (I : Instrument ι O κ) (o : O) (ρ : Density ι)
    (r : ℝ) (hr : 0 < r) (hρ : I.branch o ρ.matrix = r • ρ.matrix) (n : ℕ)
    (hp : 0 < successMass I o ρ n) : conditionalState I o ρ n hp = ρ := by
  apply Density.ext
  change (successMass I o ρ n)⁻¹ • successOperator I o n ρ.matrix = ρ.matrix
  rw [eigen_successMass I o ρ r hρ n, eigen_successOperator I o ρ.matrix r hρ n,
    smul_smul, inv_mul_cancel₀ (pow_ne_zero n hr.ne'), one_smul]

theorem eigen_rate_nonneg (I : Instrument ι O κ) (o : O) (ρ : Density ι)
    (r : ℝ) (hρ : I.branch o ρ.matrix = r • ρ.matrix) : 0 ≤ r := by
  have h := I.probability_nonneg ρ o
  simpa only [Instrument.probability, hρ, mass_smul, ρ.mass_one, mul_one] using h

theorem eigen_rate_le_one (I : Instrument ι O κ) (o : O) (ρ : Density ι)
    (r : ℝ) (hρ : I.branch o ρ.matrix = r • ρ.matrix) : r ≤ 1 := by
  have h := I.probability_le_one ρ o
  simpa only [Instrument.probability, hρ, mass_smul, ρ.mass_one, mul_one] using h

/-- Only an actual matrix and its two-sided inverse are supplied. -/
structure InvertibleFilter (ι : Type*) [Fintype ι] [DecidableEq ι] where
  matrix : Operator ι
  inverse : Operator ι
  inverse_mul : inverse * matrix = 1
  mul_inverse : matrix * inverse = 1

namespace InvertibleFilter

def apply (F : InvertibleFilter ι) (X : Operator ι) : Operator ι :=
  F.matrix * X * F.matrixᴴ

def unapply (F : InvertibleFilter ι) (X : Operator ι) : Operator ι :=
  F.inverse * X * F.inverseᴴ

def metric (F : InvertibleFilter ι) : Operator ι := F.matrixᴴ * F.matrix

theorem apply_smul (F : InvertibleFilter ι) (a : ℝ) (X : Operator ι) :
    F.apply (a • X) = a • F.apply X := by
  simp only [apply, Matrix.mul_smul, Matrix.smul_mul]

theorem unapply_apply (F : InvertibleFilter ι) (X : Operator ι) :
    F.unapply (F.apply X) = X := by
  calc
    F.unapply (F.apply X) = (F.inverse * F.matrix) * X *
        (F.inverse * F.matrix)ᴴ := by
      simp only [unapply, apply, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = X := by rw [F.inverse_mul]; simp

theorem apply_unapply (F : InvertibleFilter ι) (X : Operator ι) :
    F.apply (F.unapply X) = X := by
  calc
    F.apply (F.unapply X) = (F.matrix * F.inverse) * X *
        (F.matrix * F.inverse)ᴴ := by
      simp only [unapply, apply, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = X := by rw [F.mul_inverse]; simp

theorem apply_posSemidef (F : InvertibleFilter ι) {X : Operator ι}
    (hX : X.PosSemidef) : (F.apply X).PosSemidef :=
  hX.mul_mul_conjTranspose_same F.matrix

/-- Invertibility proves strictly positive filtered mass for every density. -/
theorem mass_apply_pos (F : InvertibleFilter ι) (ρ : Density ι) :
    0 < mass (F.apply ρ.matrix) := by
  have hn := mass_nonneg (F.apply_posSemidef ρ.positive)
  by_contra hp
  have hz : mass (F.apply ρ.matrix) = 0 := le_antisymm (le_of_not_gt hp) hn
  have hx := (mass_eq_zero_iff (F.apply_posSemidef ρ.positive)).mp hz
  have hρ : ρ.matrix = 0 := by
    calc
      ρ.matrix = F.unapply (F.apply ρ.matrix) := (F.unapply_apply _).symm
      _ = 0 := by rw [hx]; simp [unapply]
  have hm := ρ.mass_one
  rw [hρ] at hm
  simp [mass] at hm

def state (F : InvertibleFilter ι) (ρ : Density ι) : Density ι :=
  normalize (F.apply ρ.matrix) (F.apply_posSemidef ρ.positive) (F.mass_apply_pos ρ)

@[simp] theorem state_matrix (F : InvertibleFilter ι) (ρ : Density ι) :
    (F.state ρ).matrix = (mass (F.apply ρ.matrix))⁻¹ • F.apply ρ.matrix := rfl

theorem mass_apply_eq_pairing (F : InvertibleFilter ι) (X : Operator ι) :
    mass (F.apply X) = pairing F.metric X := by
  exact congrArg Complex.re (Matrix.trace_mul_cycle F.matrix X F.matrixᴴ)

theorem metric_conjugate (F : InvertibleFilter ι) :
    F.inverseᴴ * F.metric * F.inverse = 1 := by
  calc
    F.inverseᴴ * F.metric * F.inverse =
        (F.matrix * F.inverse)ᴴ * (F.matrix * F.inverse) := by
      simp only [metric, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [F.mul_inverse]; simp

end InvertibleFilter

omit [DecidableEq ι] in
theorem transformed_gram (K : κ → Operator ι) (S T : Operator ι) :
    (∑ k, (S * K k * T)ᴴ * (S * K k * T)) =
      Tᴴ * heisenberg K (Sᴴ * S) * T := by
  simp only [heisenberg, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    Matrix.mul_sum, Matrix.sum_mul]

omit [DecidableEq ι] in
theorem transformed_map (K : κ → Operator ι) (S T X : Operator ι) :
    krausMap (fun k => S * K k * T) X =
      S * krausMap K (T * X * Tᴴ) * Sᴴ := by
  simp only [krausMap, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    Matrix.mul_sum, Matrix.sum_mul]

/-- The actual left eigenrelation implies transformed weighted completeness. -/
theorem doob_complete (F : InvertibleFilter ι) (K : κ → Operator ι)
    (r : ℝ) (hr : 0 < r)
    (hleft : heisenberg K F.metric = r • F.metric) :
    (∑ k, r⁻¹ • ((F.matrix * K k * F.inverse)ᴴ *
      (F.matrix * K k * F.inverse))) = 1 := by
  rw [← Finset.smul_sum, transformed_gram]
  change r⁻¹ • (F.inverseᴴ * heisenberg K F.metric * F.inverse) = 1
  rw [hleft, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
    inv_mul_cancel₀ hr.ne', one_smul, F.metric_conjugate]

/-- The weighted representation isolates the real square-root scaling. -/
def doobWeighted (F : InvertibleFilter ι) (I : Instrument ι O κ) (o : O)
    (r : ℝ) (hr : 0 < r)
    (hleft : heisenberg (I.kraus o) F.metric = r • F.metric) :
    WeightedInstrument ι Unit κ where
  weight _ _ := r⁻¹
  kraus _ k := F.matrix * I.kraus o k * F.inverse
  weight_nonneg _ _ := inv_nonneg.mpr hr.le
  complete := by simpa using doob_complete F (I.kraus o) r hr hleft

/-- The ordinary Kraus family is sqrt(r⁻¹) times the explicitly filtered family. -/
def doobInstrument (F : InvertibleFilter ι) (I : Instrument ι O κ) (o : O)
    (r : ℝ) (hr : 0 < r)
    (hleft : heisenberg (I.kraus o) F.metric = r • F.metric) :
    Instrument ι Unit κ := (doobWeighted F I o r hr hleft).toInstrument

theorem doob_branch (F : InvertibleFilter ι) (I : Instrument ι O κ) (o : O)
    (r : ℝ) (hr : 0 < r)
    (hleft : heisenberg (I.kraus o) F.metric = r • F.metric) (X : Operator ι) :
    (doobInstrument F I o r hr hleft).branch () X =
      r⁻¹ • F.apply (I.branch o (F.unapply X)) := by
  rw [doobInstrument, WeightedInstrument.toInstrument_branch]
  change (∑ k, r⁻¹ • ((F.matrix * I.kraus o k * F.inverse) * X *
    (F.matrix * I.kraus o k * F.inverse)ᴴ)) = _
  rw [← Finset.smul_sum]
  congr 1
  exact transformed_map (I.kraus o) F.matrix F.inverse X

theorem doob_branch_apply (F : InvertibleFilter ι) (I : Instrument ι O κ) (o : O)
    (r : ℝ) (hr : 0 < r)
    (hleft : heisenberg (I.kraus o) F.metric = r • F.metric) (X : Operator ι) :
    (doobInstrument F I o r hr hleft).branch () (F.apply X) =
      r⁻¹ • F.apply (I.branch o X) := by
  rw [doob_branch, F.unapply_apply]

theorem doob_branch_state (F : InvertibleFilter ι) (I : Instrument ι O κ) (o : O)
    (r : ℝ) (hr : 0 < r)
    (hleft : heisenberg (I.kraus o) F.metric = r • F.metric) (ρ : Density ι)
    (hright : I.branch o ρ.matrix = r • ρ.matrix) :
    (doobInstrument F I o r hr hleft).branch () (F.state ρ).matrix =
      (F.state ρ).matrix := by
  have h : (doobInstrument F I o r hr hleft).branch () (F.apply ρ.matrix) =
      F.apply ρ.matrix := by
    rw [doob_branch_apply, hright, F.apply_smul, smul_smul,
      inv_mul_cancel₀ hr.ne', one_smul]
  rw [F.state_matrix, Instrument.branch_smul, h]

theorem doob_channelState (F : InvertibleFilter ι) (I : Instrument ι O κ) (o : O)
    (r : ℝ) (hr : 0 < r)
    (hleft : heisenberg (I.kraus o) F.metric = r • F.metric) (ρ : Density ι)
    (hright : I.branch o ρ.matrix = r • ρ.matrix) :
    (doobInstrument F I o r hr hleft).channelState (F.state ρ) = F.state ρ := by
  apply Density.ext
  simpa only [Instrument.channelState_matrix, Instrument.channel, Fintype.sum_unique]
    using doob_branch_state F I o r hr hleft ρ hright

/-- Finite iteration intertwining holds on all operators, before positivity. -/
theorem doob_successOperator_apply (F : InvertibleFilter ι)
    (I : Instrument ι O κ) (o : O) (r : ℝ) (hr : 0 < r)
    (hleft : heisenberg (I.kraus o) F.metric = r • F.metric)
    (n : ℕ) (X : Operator ι) :
    successOperator (doobInstrument F I o r hr hleft) () n (F.apply X) =
      (r⁻¹) ^ n • F.apply (successOperator I o n X) := by
  induction n generalizing X with
  | zero => simp
  | succ n ih =>
    rw [successOperator_succ, doob_branch_apply, successOperator_smul, ih,
      smul_smul, pow_succ', successOperator_succ]

/-- The left eigenmetric controls filtered record mass for every operator. -/
theorem eigenmetric_successMass (F : InvertibleFilter ι)
    (I : Instrument ι O κ) (o : O) (r : ℝ)
    (hleft : heisenberg (I.kraus o) F.metric = r • F.metric)
    (n : ℕ) (X : Operator ι) :
    mass (F.apply (successOperator I o n X)) = r ^ n * mass (F.apply X) := by
  have hstep (Y : Operator ι) : mass (F.apply (I.branch o Y)) =
      r * mass (F.apply Y) := by
    rw [F.mass_apply_eq_pairing]
    change pairing F.metric (krausMap (I.kraus o) Y) = _
    rw [pairing_heisenberg, hleft, pairing_smul_left, ← F.mass_apply_eq_pairing]
  induction n generalizing X with
  | zero => simp
  | succ n ih =>
    rw [successOperator_succ, ih, hstep, pow_succ]
    ring

/-- A strictly positive eigenmetric and positive rate rule out finite zero survival,
even for initial densities which are not right eigenstates. -/
theorem eigenmetric_successMass_pos (F : InvertibleFilter ι)
    (I : Instrument ι O κ) (o : O) (r : ℝ) (hr : 0 < r)
    (hleft : heisenberg (I.kraus o) F.metric = r • F.metric)
    (ρ : Density ι) (n : ℕ) : 0 < successMass I o ρ n := by
  have hn := mass_nonneg (successOperator_posSemidef I o n ρ.positive)
  change 0 ≤ successMass I o ρ n at hn
  by_contra hp
  have hz : successMass I o ρ n = 0 := le_antisymm (le_of_not_gt hp) hn
  have hx := (mass_eq_zero_iff (successOperator_posSemidef I o n ρ.positive)).mp hz
  have hpos : 0 < mass (F.apply (successOperator I o n ρ.matrix)) := by
    rw [eigenmetric_successMass F I o r hleft n]
    exact mul_pos (pow_pos hr n) (F.mass_apply_pos ρ)
  rw [hx] at hpos
  simp [InvertibleFilter.apply, mass] at hpos

/-- Finite conditioning conjugates exactly to the actual Doob dynamics for every
initial density. This is a finite identity, not an infinite-horizon limit. -/
theorem doob_finite_conditioning (F : InvertibleFilter ι)
    (I : Instrument ι O κ) (o : O) (r : ℝ) (hr : 0 < r)
    (hleft : heisenberg (I.kraus o) F.metric = r • F.metric)
    (ρ : Density ι) (n : ℕ) (hp : 0 < successMass I o ρ n) :
    (F.state (conditionalState I o ρ n hp)).matrix =
      successOperator (doobInstrument F I o r hr hleft) () n (F.state ρ).matrix := by
  rw [F.state_matrix, F.state_matrix, successOperator_smul,
    doob_successOperator_apply]
  change (mass (F.apply ((successMass I o ρ n)⁻¹ •
    successOperator I o n ρ.matrix)))⁻¹ •
    F.apply ((successMass I o ρ n)⁻¹ • successOperator I o n ρ.matrix) = _
  rw [F.apply_smul, mass_smul, smul_smul, _root_.mul_inv_rev, inv_inv]
  rw [mul_assoc, mul_inv_cancel₀ hp.ne', mul_one,
    eigenmetric_successMass F I o r hleft n, _root_.mul_inv_rev, ← inv_pow, smul_smul]

theorem doob_successOperator_state (F : InvertibleFilter ι)
    (I : Instrument ι O κ) (o : O) (r : ℝ) (hr : 0 < r)
    (hleft : heisenberg (I.kraus o) F.metric = r • F.metric)
    (ρ : Density ι) (hright : I.branch o ρ.matrix = r • ρ.matrix) (n : ℕ) :
    successOperator (doobInstrument F I o r hr hleft) () n (F.state ρ).matrix =
      (F.state ρ).matrix := by
  simpa only [one_pow, one_smul] using eigen_successOperator
    (doobInstrument F I o r hr hleft) () (F.state ρ).matrix 1
    (by simpa using doob_branch_state F I o r hr hleft ρ hright) n

theorem doob_successMass_state (F : InvertibleFilter ι)
    (I : Instrument ι O κ) (o : O) (r : ℝ) (hr : 0 < r)
    (hleft : heisenberg (I.kraus o) F.metric = r • F.metric)
    (ρ : Density ι) (hright : I.branch o ρ.matrix = r • ρ.matrix) (n : ℕ) :
    successMass (doobInstrument F I o r hr hleft) () (F.state ρ) n = 1 := by
  rw [successMass, doob_successOperator_state F I o r hr hleft ρ hright n,
    Density.mass_one]

end

end UEOTQM.QuantumDoob
