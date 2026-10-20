import UEOTQM.OperationalSystems

/-!
# Exact finite controls for the full-state purification interface

The Bell vector uses the rational complex amplitude `(1+i)/2`, which differs
from the usual positive `1/sqrt 2` amplitude only by a global phase. Its density
matrix is the usual Bell projector. All purity claims use the full density
space. The singleton-restricted classical predicate below is deliberately
separate and demonstrates why restricting the allowed state space is unsound
for the main purification claim.
-/

namespace UEOTQM.QuantumPurificationExamples

open Matrix QuantumPurification OperationalSystems
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

def bellAmplitude : ℂ := (1 + Complex.I) / 2

theorem bellAmplitude_norm : bellAmplitude * star bellAmplitude = 1 / 2 := by
  apply Complex.ext <;> norm_num [bellAmplitude, Complex.mul_re, Complex.mul_im]

def bellVector (p : Fin 2 × Fin 2) : ℂ :=
  if p.1 = p.2 then bellAmplitude else 0

theorem bell_outer_entry (p q : Fin 2 × Fin 2) :
    outer bellVector p q = if p.1 = p.2 ∧ q.1 = q.2 then (1 / 2 : ℂ) else 0 := by
  by_cases hp : p.1 = p.2
  · by_cases hq : q.1 = q.2
    · simp only [outer_apply, bellVector, if_pos hp, if_pos hq, if_pos (And.intro hp hq)]
      exact bellAmplitude_norm
    · simp [outer_apply, bellVector, hp, hq]
  · simp [outer_apply, bellVector, hp]

theorem bell_normalized : (outer bellVector).trace = 1 := by
  change (∑ p : Fin 2 × Fin 2, outer bellVector p p) = 1
  simp only [Fintype.sum_prod_type, Fin.sum_univ_succ, bell_outer_entry]
  norm_num

def bell : Density (Fin 2 × Fin 2) := vectorState bellVector bell_normalized

theorem bell_isPure : QuantumPurification.IsPure bell :=
  vectorState_isPure bellVector bell_normalized

def mixed : Density (Fin 2) where
  matrix := (1 / 2 : ℝ) • 1
  positive := (Matrix.PosSemidef.one : (1 : Operator (Fin 2)).PosSemidef).smul (by norm_num)
  trace_one := by norm_num [Matrix.trace, Fin.sum_univ_succ]

theorem bell_marginal :
    (RectangularChannel.discardRight (Fin 2) (Fin 2)).state bell = mixed := by
  apply Density.ext
  ext i j
  change (RectangularChannel.discardRight (Fin 2) (Fin 2)).operator
    (outer bellVector) i j = ((1 / 2 : ℝ) • (1 : Operator (Fin 2))) i j
  rw [RectangularChannel.discardRight_operator_apply]
  simp only [bell_outer_entry]
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.sum_univ_succ, Matrix.one_apply]

def qubitSystem : FiniteSystem := FiniteSystem.of (Fin 2)

theorem bell_purifies_in_complex_interface :
    Purifies complexModel (A := qubitSystem) (B := qubitSystem) bell mixed := by
  exact ⟨(complex_pure_iff (A := qubitSystem.product qubitSystem) bell).mpr bell_isPure,
    bell_marginal⟩

/-- The universal theorem also applies to the displayed mixed state directly. -/
theorem mixed_has_generic_purification :
    ∃ Ψ : Density (Fin 2 × Fin 2), QuantumPurification.IsPure Ψ ∧
      (RectangularChannel.discardRight (Fin 2) (Fin 2)).state Ψ = mixed :=
  exists_purification mixed

def classicalMixed : Classical.State (Fin 2) :=
  Classical.halfMix (Classical.dirac 0) (Classical.dirac 1)

theorem classicalMixed_not_pure : ¬ Classical.IsPure classicalMixed :=
  Classical.halfMix_not_pure (by decide)

theorem ordinary_classical_extension_exists :
    ∃ p : Classical.State (Fin 2 × Unit), Classical.marginalLeft p = classicalMixed :=
  ⟨Classical.attach classicalMixed (), Classical.marginalLeft_attach classicalMixed ()⟩

theorem pure_classical_extension_impossible (B : Type*) [Fintype B] :
    ¬ ∃ p : Classical.State (Fin 2 × B), Classical.IsPure p ∧
      Classical.marginalLeft p = classicalMixed :=
  Classical.no_pure_extension_halfMix (by decide)

/-- A restricted predicate, used only to expose a bad change of state space. -/
def RestrictedPure (S : Set (Classical.State (Fin 2))) (p : Classical.State (Fin 2)) : Prop :=
  ∀ q ∈ S, ∀ r ∈ S, ∀ (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1),
    p = Classical.mix t ht0.le ht1.le q r → q = p ∧ r = p

theorem singleton_fake_pure : RestrictedPure {classicalMixed} classicalMixed := by
  intro q hq r hr _ _ _ _
  exact ⟨Set.mem_singleton_iff.mp hq, Set.mem_singleton_iff.mp hr⟩

theorem singleton_full_state_negative_control :
    RestrictedPure {classicalMixed} classicalMixed ∧ ¬ Classical.IsPure classicalMixed :=
  ⟨singleton_fake_pure, classicalMixed_not_pure⟩

/-- Removing the real local-effect restriction restores a concrete product
distinction for the existing two-rebit counterexample, within this same API. -/
theorem complex_local_effects_distinguish_real_pair :
    complexModel.probability (A := qubitSystem.product qubitSystem)
      (complexModel.productEffect (A := qubitSystem) (B := qubitSystem)
        RealLocalTomography.complexLocalTest RealLocalTomography.complexLocalTest)
      RealLocalTomography.rhoPlus ≠
    complexModel.probability (A := qubitSystem.product qubitSystem)
      (complexModel.productEffect (A := qubitSystem) (B := qubitSystem)
        RealLocalTomography.complexLocalTest RealLocalTomography.complexLocalTest)
      RealLocalTomography.rhoMinus :=
  RealLocalTomography.complex_product_distinguishes

end
end UEOTQM.QuantumPurificationExamples

#print axioms UEOTQM.QuantumPurificationExamples.bellAmplitude
#print axioms UEOTQM.QuantumPurificationExamples.bellAmplitude_norm
#print axioms UEOTQM.QuantumPurificationExamples.bellVector
#print axioms UEOTQM.QuantumPurificationExamples.bell_outer_entry
#print axioms UEOTQM.QuantumPurificationExamples.bell_normalized
#print axioms UEOTQM.QuantumPurificationExamples.bell
#print axioms UEOTQM.QuantumPurificationExamples.bell_isPure
#print axioms UEOTQM.QuantumPurificationExamples.mixed
#print axioms UEOTQM.QuantumPurificationExamples.bell_marginal
#print axioms UEOTQM.QuantumPurificationExamples.qubitSystem
#print axioms UEOTQM.QuantumPurificationExamples.bell_purifies_in_complex_interface
#print axioms UEOTQM.QuantumPurificationExamples.mixed_has_generic_purification
#print axioms UEOTQM.QuantumPurificationExamples.classicalMixed
#print axioms UEOTQM.QuantumPurificationExamples.classicalMixed_not_pure
#print axioms UEOTQM.QuantumPurificationExamples.ordinary_classical_extension_exists
#print axioms UEOTQM.QuantumPurificationExamples.pure_classical_extension_impossible
#print axioms UEOTQM.QuantumPurificationExamples.RestrictedPure
#print axioms UEOTQM.QuantumPurificationExamples.singleton_fake_pure
#print axioms UEOTQM.QuantumPurificationExamples.singleton_full_state_negative_control
#print axioms UEOTQM.QuantumPurificationExamples.complex_local_effects_distinguish_real_pair
