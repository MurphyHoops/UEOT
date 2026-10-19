import UEOTQM.Observables
import Mathlib.Analysis.Matrix.Order

/-!
# Actual quantum effects and complete Kraus pullbacks

An effect is a finite complex matrix E with E and I-E positive semidefinite.
The Born bounds below are proved for every existing Density, not only for
inputs supplied with a chosen Gram factor. MatrixOrder is used locally to
derive a factor from the existing positive-semidefinite predicate.

Pulling a possibly different continuation effect through every outcome of a
complete instrument again gives an effect. This proves both complete-channel
and selective-branch bounds, and upgrades every existing recordEffect to an
actual effect. No empirical interpretation or reconstruction is added.
-/

namespace UEOTQM

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

variable {ι κ O A : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [Fintype O]

omit [DecidableEq ι] in
theorem pairing_sub_left (E F X : Operator ι) :
    pairing (E - F) X = pairing E X - pairing F X := by
  simp [pairing, mass, Matrix.sub_mul]

omit [DecidableEq ι] in
theorem pairing_add_right (E X Y : Operator ι) :
    pairing E (X + Y) = pairing E X + pairing E Y := by
  simp [pairing, mass, Matrix.mul_add]

omit [DecidableEq ι] in
theorem pairing_sum_right {β : Type*} (s : Finset β) (E : Operator ι)
    (X : β → Operator ι) :
    pairing E (∑ j ∈ s, X j) = ∑ j ∈ s, pairing E (X j) := by
  simp [pairing, mass, Matrix.mul_sum]

/-- PSD trace pairing is nonnegative, derived from the full PSD cone. -/
theorem pairing_nonneg {E X : Operator ι}
    (hE : E.PosSemidef) (hX : X.PosSemidef) : 0 ≤ pairing E X := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hE.nonneg
  rw [hB]
  change 0 ≤ ((Bᴴ * B * X).trace).re
  rw [← Matrix.trace_mul_cycle B X Bᴴ]
  exact mass_nonneg (hX.mul_mul_conjTranspose_same B)

/-- Every matrix in the quantum order interval [0,I]. -/
structure Effect (ι : Type*) [Fintype ι] [DecidableEq ι] where
  matrix : Operator ι
  positive : matrix.PosSemidef
  complement_positive : (1 - matrix).PosSemidef

namespace Effect

@[ext] theorem ext {E F : Effect ι} (h : E.matrix = F.matrix) : E = F := by
  cases E
  cases F
  cases h
  rfl

def zero : Effect ι where
  matrix := 0
  positive := Matrix.PosSemidef.zero
  complement_positive := by simpa using (Matrix.PosSemidef.one :
    (1 : Operator ι).PosSemidef)

def one : Effect ι where
  matrix := 1
  positive := Matrix.PosSemidef.one
  complement_positive := by simp only [sub_self]; exact Matrix.PosSemidef.zero

def complement (E : Effect ι) : Effect ι where
  matrix := 1 - E.matrix
  positive := E.complement_positive
  complement_positive := by simpa using E.positive

@[simp] theorem zero_matrix : (zero : Effect ι).matrix = 0 := rfl
@[simp] theorem one_matrix : (one : Effect ι).matrix = 1 := rfl
@[simp] theorem complement_matrix (E : Effect ι) :
    E.complement.matrix = 1 - E.matrix := rfl

theorem pairing_nonneg (E : Effect ι) {X : Operator ι} (hX : X.PosSemidef) :
    0 ≤ pairing E.matrix X := UEOTQM.pairing_nonneg E.positive hX

theorem pairing_le_mass (E : Effect ι) {X : Operator ι} (hX : X.PosSemidef) :
    pairing E.matrix X ≤ mass X := by
  have h := UEOTQM.pairing_nonneg E.complement_positive hX
  rw [pairing_sub_left, pairing_one] at h
  linarith

/-- The actual Born effect probability on a density matrix. -/
def probability (E : Effect ι) (ρ : Density ι) : ℝ := pairing E.matrix ρ.matrix

theorem probability_nonneg (E : Effect ι) (ρ : Density ι) :
    0 ≤ E.probability ρ := E.pairing_nonneg ρ.positive

theorem probability_le_one (E : Effect ι) (ρ : Density ι) :
    E.probability ρ ≤ 1 := by
  simpa only [probability, ρ.mass_one] using E.pairing_le_mass ρ.positive

@[simp] theorem probability_zero (ρ : Density ι) :
    (zero : Effect ι).probability ρ = 0 := by simp [probability]

@[simp] theorem probability_one (ρ : Density ι) :
    (one : Effect ι).probability ρ = 1 := by simp [probability]

theorem probability_complement (E : Effect ι) (ρ : Density ι) :
    E.complement.probability ρ = 1 - E.probability ρ := by
  simp [probability, pairing_sub_left]

end Effect

namespace Instrument

/-- The complete, outcome-forgetting Kraus channel on all operators. -/
def channel (I : Instrument ι O κ) (X : Operator ι) : Operator ι :=
  ∑ o, I.branch o X

theorem channel_posSemidef (I : Instrument ι O κ) {X : Operator ι}
    (hX : X.PosSemidef) : (I.channel X).PosSemidef :=
  Matrix.posSemidef_sum Finset.univ (fun o _ => I.branch_posSemidef o hX)

theorem trace_channel (I : Instrument ι O κ) (X : Operator ι) :
    (I.channel X).trace = X.trace := by
  rw [channel, Matrix.trace_sum, I.sum_trace_branch]

def channelState (I : Instrument ι O κ) (ρ : Density ι) : Density ι where
  matrix := I.channel ρ.matrix
  positive := I.channel_posSemidef ρ.positive
  trace_one := by rw [I.trace_channel, ρ.trace_one]

@[simp] theorem channelState_matrix (I : Instrument ι O κ) (ρ : Density ι) :
    (I.channelState ρ).matrix = I.channel ρ.matrix := rfl

/-- A continuation effect may depend on the observed instrument outcome.
Completeness, not an assumed final bound, proves the complement is PSD. -/
def pullbackEffects (I : Instrument ι O κ) (E : O → Effect ι) : Effect ι where
  matrix := ∑ o, heisenberg (I.kraus o) (E o).matrix
  positive := Matrix.posSemidef_sum Finset.univ
    (fun o _ => heisenberg_posSemidef _ (E o).positive)
  complement_positive := by
    have h := Matrix.posSemidef_sum Finset.univ
      (fun o _ => heisenberg_posSemidef (I.kraus o) (E o).complement_positive)
    simpa only [heisenberg, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Finset.sum_sub_distrib, I.complete] using h

@[simp] theorem pullbackEffects_matrix (I : Instrument ι O κ) (E : O → Effect ι) :
    (I.pullbackEffects E).matrix = ∑ o, heisenberg (I.kraus o) (E o).matrix := rfl

theorem pairing_pullbackEffects (I : Instrument ι O κ) (E : O → Effect ι)
    (X : Operator ι) :
    pairing (I.pullbackEffects E).matrix X = ∑ o, pairing (E o).matrix (I.branch o X) := by
  rw [pullbackEffects_matrix, pairing_sum_left]
  apply Finset.sum_congr rfl
  intro o _
  exact (pairing_heisenberg (I.kraus o) (E o).matrix X).symm

def pullbackEffect (I : Instrument ι O κ) (E : Effect ι) : Effect ι :=
  I.pullbackEffects (fun _ => E)

theorem pairing_pullbackEffect (I : Instrument ι O κ) (E : Effect ι)
    (X : Operator ι) : pairing (I.pullbackEffect E).matrix X = pairing E.matrix (I.channel X) := by
  rw [pullbackEffect, I.pairing_pullbackEffects, channel, pairing_sum_right]

theorem probability_channelState (I : Instrument ι O κ) (E : Effect ι) (ρ : Density ι) :
    E.probability (I.channelState ρ) = (I.pullbackEffect E).probability ρ := by
  exact (I.pairing_pullbackEffect E ρ.matrix).symm

/-- Select one outcome, assigning the zero continuation to all other outcomes. -/
def branchEffect (I : Instrument ι O κ) (o : O) (E : Effect ι) : Effect ι := by
  classical
  exact I.pullbackEffects (fun y => if y = o then E else Effect.zero)

@[simp] theorem branchEffect_matrix (I : Instrument ι O κ) (o : O) (E : Effect ι) :
    (I.branchEffect o E).matrix = heisenberg (I.kraus o) E.matrix := by
  classical
  unfold branchEffect
  rw [pullbackEffects_matrix, Finset.sum_eq_single o]
  · simp
  · intro y _ hy
    simp [hy]
  · simp

theorem pairing_branchEffect (I : Instrument ι O κ) (o : O) (E : Effect ι)
    (X : Operator ι) : pairing (I.branchEffect o E).matrix X = pairing E.matrix (I.branch o X) := by
  rw [branchEffect_matrix]
  exact (pairing_heisenberg (I.kraus o) E.matrix X).symm

theorem probability_branchEffect_one (I : Instrument ι O κ) (o : O) (ρ : Density ι) :
    (I.branchEffect o Effect.one).probability ρ = I.probability ρ o := by
  rw [Effect.probability, I.pairing_branchEffect]
  exact pairing_one (I.branch o ρ.matrix)

theorem probability_posterior (I : Instrument ι O κ) (o : O) (E : Effect ι)
    (ρ : Density ι) (hp : 0 < I.probability ρ o) :
    E.probability (I.posterior ρ o hp) =
      (I.branchEffect o E).probability ρ / I.probability ρ o := by
  rw [Effect.probability, posterior_matrix, pairing_smul_right,
    Effect.probability, I.pairing_branchEffect]
  simp only [div_eq_mul_inv, mul_comm]

end Instrument

/-- The existing word effect, bundled with its newly proved upper bound. -/
def recordTest (I : A → Instrument ι O κ) : List (A × O) → Effect ι
  | [] => Effect.one
  | e :: w => (I e.1).branchEffect e.2 (recordTest I w)

@[simp] theorem recordTest_matrix (I : A → Instrument ι O κ) (w : List (A × O)) :
    (recordTest I w).matrix = recordEffect I w := by
  induction w with
  | nil => rfl
  | cons e w ih => simp only [recordTest, Instrument.branchEffect_matrix, recordEffect, ih]

theorem recordEffect_complement_posSemidef (I : A → Instrument ι O κ)
    (w : List (A × O)) : (1 - recordEffect I w).PosSemidef := by
  simpa only [recordTest_matrix] using (recordTest I w).complement_positive

theorem response_eq_effect_probability (I : A → Instrument ι O κ) (ρ : Density ι)
    (w : List (A × O)) : response I ρ w = (recordTest I w).probability ρ := by
  simp only [response_eq_pairing, Effect.probability, recordTest_matrix]

theorem response_le_one (I : A → Instrument ι O κ) (ρ : Density ι)
    (w : List (A × O)) : response I ρ w ≤ 1 := by
  rw [response_eq_effect_probability]
  exact (recordTest I w).probability_le_one ρ

end

end UEOTQM
