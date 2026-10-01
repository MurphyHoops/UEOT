import UEOT.V3.FiniteRecurrentDecompositionStability
import UEOT.V3.Compression.TopologyChangingGoaInvariantUniquenessIsolation

/-!
# Recurrent-class uniqueness and invariant probability semantics

This Track-S module works with an already certified finite recurrent
decomposition and identifies the remaining structural obstruction to unique
invariant probability semantics: multiplicity of recurrent classes.

It does not assume a generic recurrent-decomposition existence theorem. Instead
it proves, for every provided `FiniteRecurrentDecomposition`, that invariant
probability vectors are unique exactly when the recurrent-class index type is
subsingleton. The proof uses the already formalized class invariant laws,
strict class positivity, transient-mass extinction, and the stationary class
formula.

This is post-FINAL, uncounted Track-S research.
-/

namespace UEOT.V3.Compression.TopologyChangingGoaRecurrentClassUniqueness

open UEOT.V3
open UEOT.V3.FiniteDobrushin
open UEOT.V3.FiniteRecurrentDecompositionStability
open UEOT.V3.Compression.InvariantSetGaugeInvariance
open UEOT.V3.Compression.TopologyChangingGoaL1ResidualConorm
open UEOT.V3.Compression.TopologyChangingGoaInvariantUniquenessIsolation

universe uT uR uC
noncomputable section

variable {T : Type uT} {R : Type uR} {C : Type uC}
  [Fintype T] [DecidableEq T] [Fintype R] [DecidableEq R]
  [Fintype C] [DecidableEq C]
  {K : RecurrentPartition R C}

def InvariantProbabilityVectorUnique
    (M : FiniteRecurrentDecomposition (T := T) K) : Prop :=
  ∀ mu nu : stdSimplex ℝ (FullState T R),
    Matrix.vecMul mu.1 M.P = mu.1 →
    Matrix.vecMul nu.1 M.P = nu.1 →
    mu = nu

theorem classLaw_ne_of_ne
    (M : FiniteRecurrentDecomposition (T := T) K)
    {c d : C} (hcd : c ≠ d) :
    M.classLaw c ≠ M.classLaw d := by
  obtain ⟨r, hrc⟩ := K.class_nonempty c
  have hpos := M.classLaw_positive c r hrc
  have hrd : K.classOf r ≠ d := by
    intro h
    apply hcd
    exact hrc.symm.trans h
  have hzero := M.classLaw_other_zero d r hrd
  intro heq
  have hcoord := congrArg
    (fun mu : stdSimplex ℝ (FullState T R) => mu.1 (Sum.inr r)) heq
  rw [hzero] at hcoord
  linarith

theorem invariantProbabilityVectorUnique_implies_class_subsingleton
    (M : FiniteRecurrentDecomposition (T := T) K)
    (huniq : InvariantProbabilityVectorUnique M) :
    Subsingleton C := by
  refine ⟨?_⟩
  intro c d
  by_contra hcd
  exact classLaw_ne_of_ne M hcd
    (huniq (M.classLaw c) (M.classLaw d)
      (M.classLaw_invariant c) (M.classLaw_invariant d))

private theorem recurrentClassMass_eq_one_of_subsingleton
    (M : FiniteRecurrentDecomposition (T := T) K)
    [Subsingleton C]
    (mu : stdSimplex ℝ (FullState T R))
    (hinv : Matrix.vecMul mu.1 M.P = mu.1)
    (c : C) :
    recurrentClassMass K mu c = 1 := by
  have htrans := M.invariant_transient_zero mu hinv
  unfold recurrentClassMass
  have hall : ∀ r : R, K.classOf r = c := fun r => Subsingleton.elim _ _
  simp_rw [if_pos (hall _)]
  have hsum0 := stdSimplex.sum_eq_one mu
  change (∑ x : FullState T R, mu.1 x) = 1 at hsum0
  rw [Fintype.sum_sum_type] at hsum0
  have hsum :
      (∑ i : T, mu.1 (Sum.inl i)) +
        ∑ r : R, mu.1 (Sum.inr r) = 1 := hsum0
  have htranssum : (∑ i : T, mu.1 (Sum.inl i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact htrans i
  rw [htranssum, zero_add] at hsum
  exact hsum

theorem invariantProbabilityVectorUnique_of_class_subsingleton
    (M : FiniteRecurrentDecomposition (T := T) K)
    [Subsingleton C] :
    InvariantProbabilityVectorUnique M := by
  intro mu nu hmu hnu
  have hmuTrans := M.invariant_transient_zero mu hmu
  have hnuTrans := M.invariant_transient_zero nu hnu
  apply Subtype.ext
  funext x
  cases x with
  | inl i =>
      rw [hmuTrans i, hnuTrans i]
  | inr r =>
      have hmuFormula := M.stationary_class_formula mu hmu hmuTrans r
      have hnuFormula := M.stationary_class_formula nu hnu hnuTrans r
      have hmuMass :=
        recurrentClassMass_eq_one_of_subsingleton M mu hmu (K.classOf r)
      have hnuMass :=
        recurrentClassMass_eq_one_of_subsingleton M nu hnu (K.classOf r)
      rw [hmuMass, one_mul] at hmuFormula
      rw [hnuMass, one_mul] at hnuFormula
      exact hmuFormula.trans hnuFormula.symm

theorem invariantProbabilityVectorUnique_iff_class_subsingleton
    (M : FiniteRecurrentDecomposition (T := T) K) :
    InvariantProbabilityVectorUnique M ↔ Subsingleton C := by
  constructor
  · exact invariantProbabilityVectorUnique_implies_class_subsingleton M
  · intro h
    letI : Subsingleton C := h
    exact invariantProbabilityVectorUnique_of_class_subsingleton M

/-- A certified recurrent decomposition on a nontrivial finite full state space
must contain at least one recurrent class.  This makes the later
`Subsingleton C` characterization literally equivalent to "exactly one
recurrent class", rather than merely "at most one". -/
theorem recurrentClass_nonempty_of_nontrivial_full_state
    (M : FiniteRecurrentDecomposition (T := T) K)
    (hcard : 1 < Fintype.card (FullState T R)) :
    Nonempty C := by
  classical
  rcases isEmpty_or_nonempty R with hRempty | hRnonempty
  · let _ : IsEmpty R := hRempty
    have hfull : Nonempty (FullState T R) :=
      Fintype.card_pos_iff.mp (lt_trans Nat.zero_lt_one hcard)
    let x : FullState T R := Classical.choice hfull
    cases x with
    | inl i =>
        rcases isEmpty_or_nonempty C with hCempty | hCnonempty
        · let _ : IsEmpty C := hCempty
          have hrow := M.block.H_row_sum i
          simp at hrow
        · exact hCnonempty
    | inr r =>
        exact isEmptyElim r
  · exact ⟨K.classOf (Classical.choice hRnonempty)⟩

private theorem recurrentClass_card_eq_one_iff_subsingleton
    (M : FiniteRecurrentDecomposition (T := T) K)
    (hcard : 1 < Fintype.card (FullState T R)) :
    Fintype.card C = 1 ↔ Subsingleton C := by
  have hCpos : 0 < Fintype.card C :=
    Fintype.card_pos_iff.mpr
      (recurrentClass_nonempty_of_nontrivial_full_state M hcard)
  constructor
  · intro hcardC
    exact Fintype.card_le_one_iff_subsingleton.mp (by omega)
  · intro hsub
    have hCle : Fintype.card C ≤ 1 :=
      Fintype.card_le_one_iff_subsingleton.mpr hsub
    omega

/-- On a nontrivial certified finite recurrent decomposition, uniqueness of
invariant probability vectors is equivalent to having exactly one recurrent
class. -/
theorem invariantProbabilityVectorUnique_iff_recurrentClass_card_eq_one
    (M : FiniteRecurrentDecomposition (T := T) K)
    (hcard : 1 < Fintype.card (FullState T R)) :
    InvariantProbabilityVectorUnique M ↔ Fintype.card C = 1 := by
  rw [invariantProbabilityVectorUnique_iff_class_subsingleton M]
  exact (recurrentClass_card_eq_one_iff_subsingleton M hcard).symm

private theorem classicalStochastic
    (M : FiniteRecurrentDecomposition (T := T) K) :
    letI : DecidableEq (FullState T R) := Classical.decEq _
    M.P ∈ Matrix.rowStochastic ℝ (FullState T R) := by
  let oldDec : DecidableEq (FullState T R) := inferInstance
  have hs :
      (∀ i j : FullState T R, 0 ≤ M.P i j) ∧
      ∀ i : FullState T R, ∑ j, M.P i j = 1 := by
    exact (@Matrix.mem_rowStochastic_iff_sum
      ℝ (FullState T R) _ oldDec _ _ _ M.P).1 M.stochastic
  letI : DecidableEq (FullState T R) := Classical.decEq _
  exact (Matrix.mem_rowStochastic_iff_sum).2 hs

private theorem invariantSetSubsingleton_iff_probabilityVectorUnique
    [Nonempty (FullState T R)]
    (M : FiniteRecurrentDecomposition (T := T) K) :
    (invariantLawSet M.P (classicalStochastic M)).Subsingleton ↔
      InvariantProbabilityVectorUnique M := by
  constructor
  · intro hsub mu nu hmu hnu
    apply hsub
    · rw [mem_invariantLawSet]
      apply Subtype.ext
      exact hmu
    · rw [mem_invariantLawSet]
      apply Subtype.ext
      exact hnu
  · intro hraw mu hmu nu hnu
    rw [mem_invariantLawSet] at hmu hnu
    have hmu' := congrArg Subtype.val hmu
    have hnu' := congrArg Subtype.val hnu
    change Matrix.vecMul mu.1 M.P = mu.1 at hmu'
    change Matrix.vecMul nu.1 M.P = nu.1 at hnu'
    exact hraw mu nu hmu' hnu'

private theorem invariantSetSubsingleton_iff_classSubsingleton
    [Nonempty (FullState T R)]
    (M : FiniteRecurrentDecomposition (T := T) K) :
    (invariantLawSet M.P (classicalStochastic M)).Subsingleton ↔
      Subsingleton C := by
  rw [invariantSetSubsingleton_iff_probabilityVectorUnique M]
  exact invariantProbabilityVectorUnique_iff_class_subsingleton M

/-- For any certified finite recurrent decomposition on a nontrivial full
state space, the canonical direct-L1 residual conorm is positive exactly when
the recurrent-class index has at most one element. -/
theorem l1ResidualConorm_pos_iff_recurrentClass_subsingleton
    (M : FiniteRecurrentDecomposition (T := T) K)
    (hcard : 1 < Fintype.card (FullState T R)) :
    0 < l1ResidualConorm M.P ↔ Subsingleton C := by
  letI : Nonempty (FullState T R) :=
    Fintype.card_pos_iff.mp (lt_trans Nat.zero_lt_one hcard)
  rw [l1ResidualConorm_pos_iff_invariantLawSet_subsingleton
    M.P (classicalStochastic M) hcard]
  exact invariantSetSubsingleton_iff_classSubsingleton M

/-- Exact recurrent-topology form of the Track-S certificate: on a nontrivial
certified finite recurrent decomposition, the canonical direct-L1 residual
conorm is positive exactly when there is one recurrent class. -/
theorem l1ResidualConorm_pos_iff_recurrentClass_card_eq_one
    (M : FiniteRecurrentDecomposition (T := T) K)
    (hcard : 1 < Fintype.card (FullState T R)) :
    0 < l1ResidualConorm M.P ↔ Fintype.card C = 1 := by
  rw [l1ResidualConorm_pos_iff_recurrentClass_subsingleton M hcard]
  exact (recurrentClass_card_eq_one_iff_subsingleton M hcard).symm

end
end UEOT.V3.Compression.TopologyChangingGoaRecurrentClassUniqueness
