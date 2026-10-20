import UEOTQM.ClassicalQuantumMemory

/-!
# Reading a finite classical history with quantum memory

The Kraus matrices below explicitly read and dephase the history register. The
input may be any joint density matrix, but this is not a coherent controller.
The action error is compared on one shared input. Its principal-block masses
are common weights, and a zero-mass PSD block is zero rather than an assigned
posterior. Both the controlled channel and the legal restricted output effects
are actual matrices.
-/

namespace UEOTQM.HistoryChannels

open Matrix
open scoped BigOperators ComplexOrder

noncomputable section

variable {H ι ν κ η : Type*} [Fintype H] [DecidableEq H]
  [Fintype ι] [DecidableEq ι] [Fintype ν] [DecidableEq ν]
  [Fintype κ] [Fintype η]

/-- The principal quantum block at one classical history. -/
def principal (X : Operator (H × ι)) (h : H) : Operator ι :=
  X.submatrix (fun i => (h, i)) (fun i => (h, i))

@[simp] theorem principal_apply (X : Operator (H × ι)) (h : H) (i j : ι) :
    principal X h i j = X (h, i) (h, j) := rfl

theorem principal_posSemidef {X : Operator (H × ι)} (hX : X.PosSemidef) (h : H) :
    (principal X h).PosSemidef :=
  hX.submatrix (fun i => (h, i))

theorem sum_mass_principal (X : Operator (H × ι)) :
    (∑ h, mass (principal X h)) = mass X := by
  simp [mass, principal, Matrix.trace, Fintype.sum_prod_type]

def weight (ρ : Density (H × ι)) (h : H) : ℝ := mass (principal ρ.matrix h)

theorem weight_nonneg (ρ : Density (H × ι)) (h : H) : 0 ≤ weight ρ h :=
  mass_nonneg (principal_posSemidef ρ.positive h)

@[simp] theorem sum_weight (ρ : Density (H × ι)) : (∑ h, weight ρ h) = 1 := by
  simpa only [weight, sum_mass_principal] using ρ.mass_one

theorem zero_weight_iff_zero_principal (ρ : Density (H × ι)) (h : H) :
    weight ρ h = 0 ↔ principal ρ.matrix h = 0 :=
  mass_eq_zero_iff (principal_posSemidef ρ.positive h)

/-- A principal restriction of a legal joint effect is a legal quantum effect. -/
def restrictEffect (E : Effect (H × ι)) (h : H) : Effect ι where
  matrix := principal E.matrix h
  positive := principal_posSemidef E.positive h
  complement_positive := by
    have hx := E.complement_positive.submatrix (fun i => (h, i))
    have hi : Function.Injective (fun i : ι => (h, i)) := by
      intro i j hij
      exact congrArg Prod.snd hij
    simpa [principal, Matrix.submatrix_sub, Matrix.submatrix_one _ hi] using hx

@[simp] theorem restrictEffect_matrix (E : Effect (H × ι)) (h : H) :
    (restrictEffect E h).matrix = principal E.matrix h := rfl

/-- The trace pairing with a genuine block matrix is the sum of block pairings. -/
theorem pairing_block (E : Operator (H × ι)) (B : H → Operator ι) :
    pairing E (ClassicalQuantumMemory.block B) = ∑ h, pairing (principal E h) (B h) := by
  simp [pairing, mass, Matrix.trace, Matrix.mul_apply, ClassicalQuantumMemory.block,
    principal, Fintype.sum_prod_type]

/-- Read one input history and write the same output history. -/
def readKraus (h : H) (K : Matrix ν ι ℂ) : Matrix (H × ν) (H × ι) ℂ :=
  fun p q => if p.1 = h then if q.1 = h then K p.2 q.2 else 0 else 0

theorem readKraus_gram (h g g' : H) (K : Matrix ν ι ℂ) (i j : ι) :
    ((readKraus h K)ᴴ * readKraus h K) (g, i) (g', j) =
      if g = h then if g' = h then (Kᴴ * K) i j else 0 else 0 := by
  classical
  by_cases hg : g = h <;> by_cases hg' : g' = h <;>
    simp [readKraus, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, hg, hg']

theorem readKraus_conjugation (h g g' : H) (K : Matrix ν ι ℂ)
    (X : Operator (H × ι)) (i j : ν) :
    (readKraus h K * X * (readKraus h K)ᴴ) (g, i) (g', j) =
      if g = h then if g' = h then (K * principal X h * Kᴴ) i j else 0 else 0 := by
  classical
  by_cases hg : g = h <;> by_cases hg' : g' = h <;>
    simp [readKraus, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, principal, hg, hg', apply_ite, mul_ite]

/-- A genuine history-reading CPTP channel from the actual selected channels. -/
def controlled (C : H → RectangularChannel ι ν κ) :
    RectangularChannel (H × ι) (H × ν) (H × κ) where
  kraus q := readKraus q.1 ((C q.1).kraus q.2)
  complete := by
    classical
    ext ⟨g, i⟩ ⟨g', j⟩
    simp only [Fintype.sum_prod_type, Matrix.sum_apply, readKraus_gram]
    rw [Finset.sum_eq_single g]
    · by_cases hg : g = g'
      · subst g'
        simpa [Matrix.sum_apply, Matrix.one_apply, Prod.mk.injEq] using
          congrFun (congrFun (C g).complete i) j
      · simp [hg, Ne.symm hg, Matrix.one_apply, Prod.mk.injEq]
    · intro a _ hag
      simp [Ne.symm hag]
    · simp

theorem controlled_operator_apply (C : H → RectangularChannel ι ν κ)
    (X : Operator (H × ι)) (g g' : H) (i j : ν) :
    (controlled C).operator X (g, i) (g', j) =
      if g = g' then (C g).operator (principal X g) i j else 0 := by
  classical
  simp only [RectangularChannel.operator, controlled, Fintype.sum_prod_type,
    Matrix.sum_apply, readKraus_conjugation]
  rw [Finset.sum_eq_single g]
  · by_cases hg : g = g'
    · subst g'
      simp
    · simp [hg, Ne.symm hg]
  · intro a _ hag
    simp [Ne.symm hag]
  · simp

theorem controlled_operator_eq_block (C : H → RectangularChannel ι ν κ)
    (X : Operator (H × ι)) :
    (controlled C).operator X =
      ClassicalQuantumMemory.block (fun h => (C h).operator (principal X h)) := by
  ext ⟨h, i⟩ ⟨g, j⟩
  exact controlled_operator_apply C X h g i j

/-- The subnormalized block estimate uses normalization only at positive mass. -/
theorem pairing_operator_difference_le_mass_mul_defect
    (C : RectangularChannel ι ν κ) (D : RectangularChannel ι ν η)
    {X : Operator ι} (hX : X.PosSemidef) (E : Effect ν) :
    |pairing E.matrix (C.operator X) - pairing E.matrix (D.operator X)| ≤
      mass X * C.defect D := by
  by_cases hz : mass X = 0
  · have hx : X = 0 := (mass_eq_zero_iff hX).mp hz
    simp [hx, RectangularChannel.operator_zero, pairing, mass]
  · have hp : 0 < mass X := lt_of_le_of_ne (mass_nonneg hX) (Ne.symm hz)
    let ρ := normalize X hX hp
    have hx : X = mass X • ρ.matrix := by
      simp [ρ, smul_smul, hp.ne']
    have gap := E.probability_sub_le_effectDistance (C.state ρ) (D.state ρ)
    have bound := (C.state_distance_le_defect D ρ)
    calc
      |pairing E.matrix (C.operator X) - pairing E.matrix (D.operator X)| =
          mass X * |E.probability (C.state ρ) - E.probability (D.state ρ)| := by
        conv_lhs => rw [hx]
        rw [C.operator_real_smul, D.operator_real_smul, pairing_smul_right,
          pairing_smul_right, ← mul_sub, abs_mul, abs_of_pos hp]
        rfl
      _ ≤ mass X * C.defect D := mul_le_mul_of_nonneg_left (gap.trans bound) hp.le

/-- The actual controlled outputs share the principal-block weights of one input. -/
theorem controlled_state_distance_le_weighted_defect
    (C : H → RectangularChannel ι ν κ) (D : H → RectangularChannel ι ν η)
    (ρ : Density (H × ι)) :
    effectDistance ((controlled C).state ρ) ((controlled D).state ρ) ≤
      ∑ h, weight ρ h * (C h).defect (D h) := by
  apply (effectDistance_le_iff _ _ _).mpr
  intro E
  change |pairing E.matrix ((controlled C).operator ρ.matrix) -
    pairing E.matrix ((controlled D).operator ρ.matrix)| ≤ _
  rw [controlled_operator_eq_block, controlled_operator_eq_block, pairing_block,
    pairing_block, ← Finset.sum_sub_distrib]
  calc
    |∑ h, (pairing (principal E.matrix h) ((C h).operator (principal ρ.matrix h)) -
        pairing (principal E.matrix h) ((D h).operator (principal ρ.matrix h)))| ≤
        ∑ h, |pairing (principal E.matrix h) ((C h).operator (principal ρ.matrix h)) -
          pairing (principal E.matrix h) ((D h).operator (principal ρ.matrix h))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ h, weight ρ h * (C h).defect (D h) := by
      apply Finset.sum_le_sum
      intro h _
      exact pairing_operator_difference_le_mass_mul_defect (C h) (D h)
        (principal_posSemidef ρ.positive h) (restrictEffect E h)

theorem controlled_state_distance_le_uniform
    (C : H → RectangularChannel ι ν κ) (D : H → RectangularChannel ι ν η)
    (ρ : Density (H × ι)) (ε : ℝ) (hε : ∀ h, (C h).defect (D h) ≤ ε) :
    effectDistance ((controlled C).state ρ) ((controlled D).state ρ) ≤ ε := by
  calc
    effectDistance ((controlled C).state ρ) ((controlled D).state ρ) ≤
        ∑ h, weight ρ h * (C h).defect (D h) :=
      controlled_state_distance_le_weighted_defect C D ρ
    _ ≤ ∑ h, weight ρ h * ε := Finset.sum_le_sum (fun h _ =>
      mul_le_mul_of_nonneg_left (hε h) (weight_nonneg ρ h))
    _ = ε := by rw [← Finset.sum_mul, sum_weight, one_mul]

/-- Zero is explicitly included in the defect, including empty input carriers. -/
theorem controlled_defect_le_uniform
    (C : H → RectangularChannel ι ν κ) (D : H → RectangularChannel ι ν η)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ∀ h, (C h).defect (D h) ≤ ε) :
    (controlled C).defect (controlled D) ≤ ε := by
  apply csSup_le (Set.insert_nonempty 0 _)
  rintro x (rfl | ⟨ρ, rfl⟩)
  · exact hε0
  · exact controlled_state_distance_le_uniform C D ρ ε hε


/-- The actual law of the full classical register, even on a non-block-diagonal input. -/
def weights (ρ : Density (H × ι)) : Mixture.Weights H where
  weight := weight ρ
  nonneg := weight_nonneg ρ
  sum_one := sum_weight ρ

@[simp] theorem weights_weight (ρ : Density (H × ι)) (h : H) :
    (weights ρ).weight h = weight ρ h := rfl

theorem event_probability (ρ : Density (H × ι)) (s : Finset H) :
    (ClassicalQuantumMemory.eventEffect ι s).probability ρ =
      RecordProbability.eventProbability (weights ρ) s := by
  classical
  simp [ClassicalQuantumMemory.eventEffect, Effect.probability, pairing, mass,
    Matrix.trace, Matrix.diagonal_mul, Fintype.sum_prod_type,
    RecordProbability.eventProbability, weights, weight, principal, apply_ite]

/-- Every finite-record event is a legal joint effect. -/
theorem record_tv_le_joint_distance (ρ σ : Density (H × ι)) :
    Mixture.tv (weights ρ) (weights σ) ≤ effectDistance ρ σ := by
  apply (RecordProbability.tv_le_iff_events _ _ _).mpr
  intro s
  rw [← event_probability, ← event_probability]
  exact (ClassicalQuantumMemory.eventEffect ι s).probability_sub_le_effectDistance ρ σ

/-- A bijection is implemented by an explicit rectangular permutation Kraus matrix. -/
def relabelKraus (e : ι ≃ ν) : Matrix ν ι ℂ :=
  fun y x => if e.symm y = x then 1 else 0

theorem relabelKraus_gram (e : ι ≃ ν) :
    (relabelKraus e)ᴴ * relabelKraus e = 1 := by
  classical
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [← Equiv.sum_comp e]
  simp [relabelKraus, Matrix.one_apply, eq_comm]

/-- Relabelling preserves the whole state by an actual CPTP map. -/
def relabel (e : ι ≃ ν) : RectangularChannel ι ν Unit where
  kraus _ := relabelKraus e
  complete := by simpa using relabelKraus_gram e

theorem relabel_operator_apply (e : ι ≃ ν) (X : Operator ι) (y z : ν) :
    (relabel e).operator X y z = X (e.symm y) (e.symm z) := by
  classical
  simp [RectangularChannel.operator, relabel, relabelKraus, Matrix.mul_apply,
    Matrix.conjTranspose_apply, apply_ite, mul_ite]

@[simp] theorem relabel_state_matrix (e : ι ≃ ν) (ρ : Density ι) (y z : ν) :
    ((relabel e).state ρ).matrix y z = ρ.matrix (e.symm y) (e.symm z) :=
  relabel_operator_apply e ρ.matrix y z

/-- Inverse relabelling gives equality of the operational distances. -/
theorem relabel_state_distance (e : ι ≃ ν) (ρ σ : Density ι) :
    effectDistance ((relabel e).state ρ) ((relabel e).state σ) = effectDistance ρ σ := by
  apply le_antisymm ((relabel e).state_effectDistance_le ρ σ)
  have hρ : (relabel e.symm).state ((relabel e).state ρ) = ρ := by
    apply Density.ext
    ext i j
    simp
  have hσ : (relabel e.symm).state ((relabel e).state σ) = σ := by
    apply Density.ext
    ext i j
    simp
  simpa only [hρ, hσ] using
    (relabel e.symm).state_effectDistance_le ((relabel e).state ρ) ((relabel e).state σ)

end

end UEOTQM.HistoryChannels
