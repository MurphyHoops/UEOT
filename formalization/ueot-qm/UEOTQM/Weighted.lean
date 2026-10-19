import UEOTQM.Observables
import Mathlib.Analysis.Real.Sqrt

/-!
# Nonnegative weighted Kraus data and ordinary quantum instruments

Rational runtime data may describe a Kraus term by a matrix and an independent
nonnegative weight. The corresponding ordinary Kraus matrix is `sqrt w • K`;
its entries need not remain rational. This file proves the exact branch,
Heisenberg and completeness identities, so certificate proofs can work with
the original weighted data without expanding square roots.

Only the weights, their nonnegativity, the matrices and weighted completeness
are inputs to `WeightedInstrument`. No state-map equivalence is a structure
field. Zero weights are allowed, including zero padding of a finite table.
-/

namespace UEOTQM

open Matrix
open scoped BigOperators ComplexOrder

noncomputable section

variable {ι κ O : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [Fintype O]

/-- A finite weighted Schrödinger map, defined before any sign condition. -/
def weightedKrausMap (w : κ → ℝ) (K : κ → Operator ι) (X : Operator ι) : Operator ι :=
  ∑ k, w k • (K k * X * (K k)ᴴ)

/-- The corresponding finite weighted Heisenberg pullback. -/
def weightedHeisenberg (w : κ → ℝ) (K : κ → Operator ι) (E : Operator ι) : Operator ι :=
  ∑ k, w k • ((K k)ᴴ * E * K k)

/-- Ordinary Kraus matrices associated with nonnegative weighted data. -/
def sqrtWeightedKraus (w : κ → ℝ) (K : κ → Operator ι) : κ → Operator ι :=
  fun k => Real.sqrt (w k) • K k

omit [DecidableEq ι] in
theorem sqrt_smul_gram (w : ℝ) (K : Operator ι) (hw : 0 ≤ w) :
    (Real.sqrt w • K)ᴴ * (Real.sqrt w • K) = w • (Kᴴ * K) := by
  simp only [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, Real.mul_self_sqrt hw]

omit [DecidableEq ι] in
theorem sqrt_smul_krausTerm (w : ℝ) (K X : Operator ι) (hw : 0 ≤ w) :
    (Real.sqrt w • K) * X * (Real.sqrt w • K)ᴴ = w • (K * X * Kᴴ) := by
  simp only [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, Real.mul_self_sqrt hw]

omit [DecidableEq ι] in
theorem sqrt_smul_heisenbergTerm (w : ℝ) (K E : Operator ι) (hw : 0 ≤ w) :
    (Real.sqrt w • K)ᴴ * E * (Real.sqrt w • K) = w • (Kᴴ * E * K) := by
  simp only [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, Real.mul_self_sqrt hw]

omit [DecidableEq ι] in
/-- Exact equality of the ordinary and weighted Schrödinger formulas. -/
theorem krausMap_sqrtWeightedKraus (w : κ → ℝ) (K : κ → Operator ι)
    (hw : ∀ k, 0 ≤ w k) (X : Operator ι) :
    krausMap (sqrtWeightedKraus w K) X = weightedKrausMap w K X := by
  apply Finset.sum_congr rfl
  intro k _
  exact sqrt_smul_krausTerm (w k) (K k) X (hw k)

omit [DecidableEq ι] in
/-- Exact equality of the ordinary and weighted Heisenberg formulas. -/
theorem heisenberg_sqrtWeightedKraus (w : κ → ℝ) (K : κ → Operator ι)
    (hw : ∀ k, 0 ≤ w k) (E : Operator ι) :
    heisenberg (sqrtWeightedKraus w K) E = weightedHeisenberg w K E := by
  apply Finset.sum_congr rfl
  intro k _
  exact sqrt_smul_heisenbergTerm (w k) (K k) E (hw k)

theorem weightedKrausMap_posSemidef (w : κ → ℝ) (K : κ → Operator ι)
    (hw : ∀ k, 0 ≤ w k) {X : Operator ι} (hX : X.PosSemidef) :
    (weightedKrausMap w K X).PosSemidef := by
  rw [← krausMap_sqrtWeightedKraus w K hw]
  exact krausMap_posSemidef (sqrtWeightedKraus w K) hX

theorem weightedHeisenberg_posSemidef (w : κ → ℝ) (K : κ → Operator ι)
    (hw : ∀ k, 0 ≤ w k) {E : Operator ι} (hE : E.PosSemidef) :
    (weightedHeisenberg w K E).PosSemidef := by
  rw [← heisenberg_sqrtWeightedKraus w K hw]
  exact heisenberg_posSemidef (sqrtWeightedKraus w K) hE

theorem pairing_weightedKrausMap (w : κ → ℝ) (K : κ → Operator ι)
    (hw : ∀ k, 0 ≤ w k) (E X : Operator ι) :
    pairing E (weightedKrausMap w K X) = pairing (weightedHeisenberg w K E) X := by
  rw [← krausMap_sqrtWeightedKraus w K hw, pairing_heisenberg,
    heisenberg_sqrtWeightedKraus w K hw]

/-- Finite weighted quantum data with the actual weighted completeness law. -/
structure WeightedInstrument (ι O κ : Type*) [Fintype ι] [DecidableEq ι]
    [Fintype O] [Fintype κ] where
  weight : O → κ → ℝ
  kraus : O → κ → Operator ι
  weight_nonneg : ∀ o k, 0 ≤ weight o k
  complete : (∑ o, ∑ k, weight o k • ((kraus o k)ᴴ * kraus o k)) = 1

namespace WeightedInstrument

def branch (W : WeightedInstrument ι O κ) (o : O) (X : Operator ι) : Operator ι :=
  weightedKrausMap (W.weight o) (W.kraus o) X

/-- Weighted completeness becomes ordinary Kraus completeness by the proved
square-root scaling identity; it is not assumed for the converted family. -/
def toInstrument (W : WeightedInstrument ι O κ) : Instrument ι O κ where
  kraus o := sqrtWeightedKraus (W.weight o) (W.kraus o)
  complete := by
    calc
      (∑ o, ∑ k,
        (sqrtWeightedKraus (W.weight o) (W.kraus o) k)ᴴ *
          sqrtWeightedKraus (W.weight o) (W.kraus o) k) =
          ∑ o, ∑ k, W.weight o k • ((W.kraus o k)ᴴ * W.kraus o k) := by
        apply Finset.sum_congr rfl
        intro o _
        apply Finset.sum_congr rfl
        intro k _
        exact sqrt_smul_gram (W.weight o k) (W.kraus o k) (W.weight_nonneg o k)
      _ = 1 := W.complete

@[simp] theorem toInstrument_kraus (W : WeightedInstrument ι O κ) (o : O) (k : κ) :
    W.toInstrument.kraus o k = Real.sqrt (W.weight o k) • W.kraus o k := rfl

@[simp] theorem toInstrument_branch (W : WeightedInstrument ι O κ) (o : O) (X : Operator ι) :
    W.toInstrument.branch o X = W.branch o X :=
  krausMap_sqrtWeightedKraus (W.weight o) (W.kraus o) (W.weight_nonneg o) X

/-- This is the certificate-facing rewrite: ordinary pullbacks are computed
by the original exact weighted sum, with no remaining square roots. -/
@[simp] theorem toInstrument_heisenberg (W : WeightedInstrument ι O κ) (o : O)
    (E : Operator ι) :
    heisenberg (W.toInstrument.kraus o) E = weightedHeisenberg (W.weight o) (W.kraus o) E :=
  heisenberg_sqrtWeightedKraus (W.weight o) (W.kraus o) (W.weight_nonneg o) E

theorem toInstrument_complete (W : WeightedInstrument ι O κ) :
    (∑ o, ∑ k, (W.toInstrument.kraus o k)ᴴ * W.toInstrument.kraus o k) = 1 :=
  W.toInstrument.complete

theorem branch_posSemidef (W : WeightedInstrument ι O κ) (o : O)
    {X : Operator ι} (hX : X.PosSemidef) : (W.branch o X).PosSemidef :=
  weightedKrausMap_posSemidef (W.weight o) (W.kraus o) (W.weight_nonneg o) hX

@[simp] theorem toInstrument_probability (W : WeightedInstrument ι O κ)
    (ρ : Density ι) (o : O) : W.toInstrument.probability ρ o = mass (W.branch o ρ.matrix) := by
  unfold Instrument.probability
  rw [W.toInstrument_branch]

theorem sum_mass_branch (W : WeightedInstrument ι O κ) (X : Operator ι) :
    (∑ o, mass (W.branch o X)) = mass X := by
  simpa only [W.toInstrument_branch] using W.toInstrument.sum_mass_branch X

theorem toInstrument_posterior_matrix (W : WeightedInstrument ι O κ)
    (ρ : Density ι) (o : O) (hp : 0 < W.toInstrument.probability ρ o) :
    (W.toInstrument.posterior ρ o hp).matrix =
      (mass (W.branch o ρ.matrix))⁻¹ • W.branch o ρ.matrix := by
  rw [Instrument.posterior_matrix, W.toInstrument_probability, W.toInstrument_branch]

end WeightedInstrument

end

end UEOTQM
