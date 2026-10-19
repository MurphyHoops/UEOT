import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic

/-!
# Finite complex density operators

The quantum sector is explicit: finite complex matrices, the existing Mathlib
positive-semidefinite cone, and the trace pairing. No reconstruction of that
sector from the classical UEOT Core is claimed here.
-/

namespace UEOTQM

open Matrix
open scoped BigOperators ComplexOrder

noncomputable section

abbrev Operator (ι : Type*) := Matrix ι ι ℂ

variable {ι : Type*} [Fintype ι]

/-- The real trace of an operator. It is nonnegative on the PSD cone. -/
def mass (A : Operator ι) : ℝ := A.trace.re

/-- All finite complex PSD trace-one operators, with no Gram-only restriction. -/
structure Density (ι : Type*) [Fintype ι] where
  matrix : Operator ι
  positive : matrix.PosSemidef
  trace_one : matrix.trace = 1

@[ext] theorem Density.ext {ρ σ : Density ι} (h : ρ.matrix = σ.matrix) : ρ = σ := by
  cases ρ
  cases σ
  cases h
  rfl

theorem mass_nonneg {A : Operator ι} (hA : A.PosSemidef) : 0 ≤ mass A := by
  exact (Complex.nonneg_iff.mp hA.trace_nonneg).1

theorem trace_im_eq_zero {A : Operator ι} (hA : A.PosSemidef) : A.trace.im = 0 := by
  exact (Complex.nonneg_iff.mp hA.trace_nonneg).2.symm

@[simp] theorem mass_smul (r : ℝ) (A : Operator ι) :
    mass (r • A) = r * mass A := by
  simp [mass, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]

@[simp] theorem Density.mass_one (ρ : Density ι) : mass ρ.matrix = 1 := by
  simp [mass, ρ.trace_one]

theorem mass_eq_zero_iff {A : Operator ι} (hA : A.PosSemidef) : mass A = 0 ↔ A = 0 := by
  constructor
  · intro h
    apply hA.trace_eq_zero_iff.mp
    apply Complex.ext
    · exact h
    · exact trace_im_eq_zero hA
  · rintro rfl
    simp [mass]

/-- Normalization is defined only with a strictly positive mass witness. -/
def normalize (A : Operator ι) (hA : A.PosSemidef) (hp : 0 < mass A) : Density ι where
  matrix := (mass A)⁻¹ • A
  positive := hA.smul (inv_nonneg.mpr hp.le)
  trace_one := by
    rw [Matrix.trace_smul]
    apply Complex.ext
    · change (mass A)⁻¹ * mass A = 1
      exact inv_mul_cancel₀ hp.ne'
    · change (mass A)⁻¹ * A.trace.im = 0
      rw [trace_im_eq_zero hA, mul_zero]

@[simp] theorem normalize_matrix (A : Operator ι) (hA : A.PosSemidef)
    (hp : 0 < mass A) :
    (normalize A hA hp).matrix = (mass A)⁻¹ • A := rfl

end

end UEOTQM
