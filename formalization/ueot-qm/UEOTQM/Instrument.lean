import UEOTQM.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Finite Kraus instruments

Only the Kraus operators and their algebraic completeness relation are input.
PSD preservation, trace probabilities, their normalization, and positive-branch
posteriors are proved. An arbitrary finite identity-ancilla extension is also
constructed and proved positive on every joint PSD input.
-/

namespace UEOTQM

open Matrix
open scoped BigOperators ComplexOrder Kronecker

noncomputable section

variable {ι κ O : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [Fintype O]

/-- A Kraus sum, before any outcome conditioning or trace normalization. -/
def krausMap (K : κ → Operator ι) (A : Operator ι) : Operator ι :=
  ∑ k, K k * A * (K k)ᴴ

theorem krausMap_posSemidef (K : κ → Operator ι) {A : Operator ι}
    (hA : A.PosSemidef) : (krausMap K A).PosSemidef := by
  exact Matrix.posSemidef_sum Finset.univ
    (fun k _ => hA.mul_mul_conjTranspose_same (K k))

theorem krausMap_smul (K : κ → Operator ι) (r : ℝ) (A : Operator ι) :
    krausMap K (r • A) = r • krausMap K A := by
  simp only [krausMap, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

theorem trace_krausMap (K : κ → Operator ι) (A : Operator ι) :
    (krausMap K A).trace = ((∑ k, (K k)ᴴ * K k) * A).trace := by
  rw [krausMap, Matrix.trace_sum, Matrix.sum_mul, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact Matrix.trace_mul_cycle (K k) A (K k)ᴴ

/-- The declared quantum operation is an instrument because its complete
Kraus family satisfies the trace-preserving algebraic identity. -/
structure Instrument (ι O κ : Type*) [Fintype ι] [DecidableEq ι]
    [Fintype O] [Fintype κ] where
  kraus : O → κ → Operator ι
  complete : (∑ o, ∑ k, (kraus o k)ᴴ * kraus o k) = 1

namespace Instrument

def branch (I : Instrument ι O κ) (o : O) (A : Operator ι) : Operator ι :=
  krausMap (I.kraus o) A

theorem branch_posSemidef (I : Instrument ι O κ) (o : O) {A : Operator ι}
    (hA : A.PosSemidef) : (I.branch o A).PosSemidef :=
  krausMap_posSemidef (I.kraus o) hA

theorem branch_smul (I : Instrument ι O κ) (o : O) (r : ℝ) (A : Operator ι) :
    I.branch o (r • A) = r • I.branch o A :=
  krausMap_smul (I.kraus o) r A

theorem sum_trace_branch (I : Instrument ι O κ) (A : Operator ι) :
    (∑ o, (I.branch o A).trace) = A.trace := by
  simp_rw [branch, trace_krausMap]
  rw [← Matrix.trace_sum, ← Matrix.sum_mul, I.complete, one_mul]

theorem sum_mass_branch (I : Instrument ι O κ) (A : Operator ι) :
    (∑ o, mass (I.branch o A)) = mass A := by
  unfold mass
  rw [← Complex.re_sum, I.sum_trace_branch]

def probability (I : Instrument ι O κ) (ρ : Density ι) (o : O) : ℝ :=
  mass (I.branch o ρ.matrix)

theorem probability_nonneg (I : Instrument ι O κ) (ρ : Density ι) (o : O) :
    0 ≤ I.probability ρ o :=
  mass_nonneg (I.branch_posSemidef o ρ.positive)

theorem sum_probability (I : Instrument ι O κ) (ρ : Density ι) :
    (∑ o, I.probability ρ o) = 1 := by
  unfold probability
  rw [I.sum_mass_branch, ρ.mass_one]

theorem probability_le_one (I : Instrument ι O κ) (ρ : Density ι) (o : O) :
    I.probability ρ o ≤ 1 := by
  calc
    I.probability ρ o ≤ ∑ y, I.probability ρ y :=
      Finset.single_le_sum (fun y _ => I.probability_nonneg ρ y) (Finset.mem_univ o)
    _ = 1 := I.sum_probability ρ

def posterior (I : Instrument ι O κ) (ρ : Density ι) (o : O)
    (hp : 0 < I.probability ρ o) : Density ι :=
  normalize (I.branch o ρ.matrix) (I.branch_posSemidef o ρ.positive) hp

@[simp] theorem posterior_matrix (I : Instrument ι O κ) (ρ : Density ι) (o : O)
    (hp : 0 < I.probability ρ o) :
    (I.posterior ρ o hp).matrix = (I.probability ρ o)⁻¹ • I.branch o ρ.matrix := rfl

theorem zero_probability_iff_zero_branch (I : Instrument ι O κ)
    (ρ : Density ι) (o : O) :
    I.probability ρ o = 0 ↔ I.branch o ρ.matrix = 0 :=
  mass_eq_zero_iff (I.branch_posSemidef o ρ.positive)

end Instrument

section Ancilla

variable {ν : Type*} [Fintype ν] [DecidableEq ν]

/-- The explicit identity-ancilla extension uses K_k tensor I. -/
def ancillaKrausMap (K : κ → Operator ι) (X : Operator (ι × ν)) : Operator (ι × ν) :=
  krausMap (fun k => K k ⊗ₖ (1 : Operator ν)) X

/-- Positivity holds for arbitrary joint PSD inputs, including entangled inputs;
it is not restricted to product states or single-system positivity. -/
theorem ancillaKrausMap_posSemidef (K : κ → Operator ι)
    {X : Operator (ι × ν)} (hX : X.PosSemidef) :
    (ancillaKrausMap K X).PosSemidef :=
  krausMap_posSemidef (fun k => K k ⊗ₖ (1 : Operator ν)) hX

/-- Entrywise agreement with applying the original map to each ancilla block:
this identifies the positive joint map with its genuine identity amplification. -/
theorem ancillaKrausMap_entry (K : κ → Operator ι) (X : Operator (ι × ν))
    (i j : ι) (u v : ν) :
    ancillaKrausMap K X (i, u) (j, v) =
      krausMap K (Matrix.of fun x y => X (x, u) (y, v)) i j := by
  classical
  simp [ancillaKrausMap, krausMap, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.kronecker_apply, Fintype.sum_prod_type, Matrix.one_apply, mul_assoc]

end Ancilla

end

end UEOTQM
