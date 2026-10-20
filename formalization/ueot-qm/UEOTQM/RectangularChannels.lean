import UEOTQM.Stability

/-!
# Finite rectangular Kraus channels

The input and output carriers are distinct. Only the actual Kraus matrices and
input-space completeness are assumed. Positivity, complex trace preservation,
all finite identity amplifications, effect pullback and all-effect contraction
are derived. In particular the positivity theorem for an amplification ranges
over every joint PSD input, not merely product inputs.
-/

namespace UEOTQM

open Matrix
open scoped BigOperators ComplexOrder Kronecker

noncomputable section

/-- A finite Kraus channel with explicitly typed input and output. -/
structure RectangularChannel (input output κ : Type*)
    [Fintype input] [DecidableEq input] [Fintype output] [DecidableEq output]
    [Fintype κ] where
  kraus : κ → Matrix output input ℂ
  complete : (∑ k, (kraus k)ᴴ * kraus k) = 1

namespace RectangularChannel

variable {ι ο κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype ο] [DecidableEq ο] [Fintype κ]

/-- The actual operator map on every complex matrix. -/
def operator (C : RectangularChannel ι ο κ) (X : Operator ι) : Operator ο :=
  ∑ k, C.kraus k * X * (C.kraus k)ᴴ

theorem operator_posSemidef (C : RectangularChannel ι ο κ) {X : Operator ι}
    (hX : X.PosSemidef) : (C.operator X).PosSemidef :=
  Matrix.posSemidef_sum Finset.univ
    (fun k _ => hX.mul_mul_conjTranspose_same (C.kraus k))

@[simp] theorem operator_zero (C : RectangularChannel ι ο κ) : C.operator 0 = 0 := by
  simp [operator]

theorem operator_add (C : RectangularChannel ι ο κ) (X Y : Operator ι) :
    C.operator (X + Y) = C.operator X + C.operator Y := by
  simp only [operator, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]

theorem operator_smul (C : RectangularChannel ι ο κ) (c : ℂ) (X : Operator ι) :
    C.operator (c • X) = c • C.operator X := by
  simp only [operator, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

theorem operator_real_smul (C : RectangularChannel ι ο κ) (r : ℝ) (X : Operator ι) :
    C.operator (r • X) = r • C.operator X := by
  simp only [operator, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

def operatorLinear (C : RectangularChannel ι ο κ) : Operator ι →ₗ[ℂ] Operator ο where
  toFun := C.operator
  map_add' := C.operator_add
  map_smul' c X := C.operator_smul c X

theorem operator_sum {β : Type*} [Fintype β] (C : RectangularChannel ι ο κ)
    (X : β → Operator ι) : C.operator (∑ b, X b) = ∑ b, C.operator (X b) :=
  map_sum C.operatorLinear X Finset.univ

/-- Complex trace preservation is proved before restricting to density states. -/
@[simp] theorem trace_operator (C : RectangularChannel ι ο κ) (X : Operator ι) :
    (C.operator X).trace = X.trace := by
  calc
    (C.operator X).trace = ((∑ k, (C.kraus k)ᴴ * C.kraus k) * X).trace := by
      rw [operator, Matrix.trace_sum, Matrix.sum_mul, Matrix.trace_sum]
      apply Finset.sum_congr rfl
      intro k _
      exact Matrix.trace_mul_cycle (C.kraus k) X (C.kraus k)ᴴ
    _ = X.trace := by rw [C.complete, one_mul]

@[simp] theorem mass_operator (C : RectangularChannel ι ο κ) (X : Operator ι) :
    mass (C.operator X) = mass X := by simp [mass]

def state (C : RectangularChannel ι ο κ) (ρ : Density ι) : Density ο where
  matrix := C.operator ρ.matrix
  positive := C.operator_posSemidef ρ.positive
  trace_one := by rw [C.trace_operator, ρ.trace_one]

@[simp] theorem state_matrix (C : RectangularChannel ι ο κ) (ρ : Density ι) :
    (C.state ρ).matrix = C.operator ρ.matrix := rfl

/-- Concrete Heisenberg adjoint between the two correctly typed carriers. -/
def adjoint (C : RectangularChannel ι ο κ) (E : Operator ο) : Operator ι :=
  ∑ k, (C.kraus k)ᴴ * E * C.kraus k

theorem adjoint_posSemidef (C : RectangularChannel ι ο κ) {E : Operator ο}
    (hE : E.PosSemidef) : (C.adjoint E).PosSemidef :=
  Matrix.posSemidef_sum Finset.univ
    (fun k _ => hE.conjTranspose_mul_mul_same (C.kraus k))

@[simp] theorem adjoint_one (C : RectangularChannel ι ο κ) : C.adjoint 1 = 1 := by
  simpa [adjoint] using C.complete

theorem adjoint_sub (C : RectangularChannel ι ο κ) (E F : Operator ο) :
    C.adjoint (E - F) = C.adjoint E - C.adjoint F := by
  simp only [adjoint, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]

theorem trace_adjoint (C : RectangularChannel ι ο κ) (E : Operator ο) (X : Operator ι) :
    (E * C.operator X).trace = (C.adjoint E * X).trace := by
  simp only [operator, adjoint, Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro k _
  calc
    (E * (C.kraus k * X * (C.kraus k)ᴴ)).trace =
        ((E * C.kraus k) * X * (C.kraus k)ᴴ).trace := by simp only [Matrix.mul_assoc]
    _ = ((C.kraus k)ᴴ * (E * C.kraus k) * X).trace :=
      Matrix.trace_mul_cycle (E * C.kraus k) X (C.kraus k)ᴴ
    _ = ((C.kraus k)ᴴ * E * C.kraus k * X).trace := by simp only [Matrix.mul_assoc]

def pullbackEffect (C : RectangularChannel ι ο κ) (E : Effect ο) : Effect ι where
  matrix := C.adjoint E.matrix
  positive := C.adjoint_posSemidef E.positive
  complement_positive := by
    have h := C.adjoint_posSemidef E.complement_positive
    simpa only [C.adjoint_sub, C.adjoint_one] using h

@[simp] theorem pullbackEffect_matrix (C : RectangularChannel ι ο κ) (E : Effect ο) :
    (C.pullbackEffect E).matrix = C.adjoint E.matrix := rfl

theorem probability_state (C : RectangularChannel ι ο κ) (E : Effect ο) (ρ : Density ι) :
    E.probability (C.state ρ) = (C.pullbackEffect E).probability ρ :=
  congrArg Complex.re (C.trace_adjoint E.matrix ρ.matrix)

theorem state_effectDistance_le (C : RectangularChannel ι ο κ) (ρ σ : Density ι) :
    effectDistance (C.state ρ) (C.state σ) ≤ effectDistance ρ σ := by
  apply (effectDistance_le_iff _ _ _).mpr
  intro E
  rw [C.probability_state E ρ, C.probability_state E σ]
  exact (C.pullbackEffect E).probability_sub_le_effectDistance ρ σ

section Composition

variable {μ η : Type*} [Fintype μ] [DecidableEq μ] [Fintype η]

/-- The identity channel has one genuine identity Kraus matrix. -/
def identity (ι : Type*) [Fintype ι] [DecidableEq ι] : RectangularChannel ι ι Unit where
  kraus _ := 1
  complete := by simp

@[simp] theorem identity_operator (X : Operator ι) : (identity ι).operator X = X := by
  simp [identity, operator]

@[simp] theorem identity_state (ρ : Density ι) : (identity ι).state ρ = ρ := by
  apply Density.ext
  simp

/-- Temporal composition: C first, then D. The path index is (D,C). -/
def comp (D : RectangularChannel ο μ η) (C : RectangularChannel ι ο κ) :
    RectangularChannel ι μ (η × κ) where
  kraus q := D.kraus q.1 * C.kraus q.2
  complete := by
    simp only [Fintype.sum_prod_type, Matrix.conjTranspose_mul]
    rw [Finset.sum_comm]
    calc
      (∑ k, ∑ l, (C.kraus k)ᴴ * (D.kraus l)ᴴ * (D.kraus l * C.kraus k)) =
          ∑ k, (C.kraus k)ᴴ * (∑ l, (D.kraus l)ᴴ * D.kraus l) * C.kraus k := by
        simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
      _ = 1 := by simp only [D.complete, Matrix.mul_one, C.complete]

theorem comp_operator (D : RectangularChannel ο μ η) (C : RectangularChannel ι ο κ)
    (X : Operator ι) : (D.comp C).operator X = D.operator (C.operator X) := by
  simp only [operator, comp, Fintype.sum_prod_type, Matrix.conjTranspose_mul,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]

theorem comp_state (D : RectangularChannel ο μ η) (C : RectangularChannel ι ο κ)
    (ρ : Density ι) : (D.comp C).state ρ = D.state (C.state ρ) := by
  apply Density.ext
  exact D.comp_operator C ρ.matrix

end Composition

section Amplification

variable (ν : Type*) [Fintype ν] [DecidableEq ν]

/-- K tensor I on an arbitrary finite auxiliary carrier. -/
def amplify (C : RectangularChannel ι ο κ) :
    RectangularChannel (ι × ν) (ο × ν) κ where
  kraus k := C.kraus k ⊗ₖ (1 : Operator ν)
  complete := by
    simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul]
    calc
      (∑ k, ((C.kraus k)ᴴ * C.kraus k) ⊗ₖ (1 : Operator ν)) =
          (∑ k, (C.kraus k)ᴴ * C.kraus k) ⊗ₖ (1 : Operator ν) := by
        ext ⟨i, a⟩ ⟨j, b⟩
        simp [Matrix.sum_apply, Matrix.kronecker_apply, Finset.sum_mul]
      _ = 1 := by rw [C.complete, Matrix.one_kronecker_one]

/-- Complete positivity is quantified over every joint PSD input. -/
theorem amplify_posSemidef (C : RectangularChannel ι ο κ)
    {X : Operator (ι × ν)} (hX : X.PosSemidef) :
    ((C.amplify ν).operator X).PosSemidef :=
  (C.amplify ν).operator_posSemidef hX

/-- This identifies the Kraus extension with the actual identity amplification,
entry by entry on arbitrary complex joint inputs. -/
theorem amplify_operator_apply (C : RectangularChannel ι ο κ) (X : Operator (ι × ν))
    (i j : ο) (a b : ν) :
    (C.amplify ν).operator X (i, a) (j, b) =
      C.operator (fun x y => X (x, a) (y, b)) i j := by
  classical
  simp only [operator, amplify, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kronecker_apply,
    Fintype.sum_prod_type, Matrix.one_apply, mul_assoc]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single b]
  · simp [Matrix.mul_apply]
    left
    rfl
  · intro y _ hy
    simp [Ne.symm hy]
  · simp

end Amplification

section Discard

variable (ι ν : Type*) [Fintype ι] [DecidableEq ι] [Fintype ν] [DecidableEq ν]

/-- The a-th basis bra on the right auxiliary factor. -/
def discardRightKraus (a : ν) : Matrix ι (ι × ν) ℂ :=
  fun i p => if p = (i, a) then 1 else 0

def discardRight : RectangularChannel (ι × ν) ι ν where
  kraus := discardRightKraus ι ν
  complete := by
    classical
    ext ⟨i, a⟩ ⟨j, b⟩
    simp only [Matrix.sum_apply]
    rw [Finset.sum_eq_single a]
    · simp only [Matrix.mul_apply]
      rw [Finset.sum_eq_single i]
      · by_cases hab : a = b <;> by_cases hij : i = j <;>
          simp_all [discardRightKraus, Matrix.conjTranspose_apply,
            Matrix.one_apply, Prod.mk.injEq, eq_comm]
      · intro x _ hxi
        simp [discardRightKraus, Matrix.conjTranspose_apply,
          Prod.mk.injEq, Ne.symm hxi]
      · simp
    · intro c _ hca
      simp [discardRightKraus, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Prod.mk.injEq, Ne.symm hca]
    · simp

theorem discardRight_operator_apply (X : Operator (ι × ν)) (i j : ι) :
    (discardRight ι ν).operator X i j = ∑ a, X (i, a) (j, a) := by
  classical
  simp only [operator, discardRight, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  simp [discardRightKraus, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- The a-th basis bra on the left factor; this forgets a classical label. -/
def discardLeftKraus (a : ν) : Matrix ι (ν × ι) ℂ :=
  fun i p => if p = (a, i) then 1 else 0

def discardLeft : RectangularChannel (ν × ι) ι ν where
  kraus := discardLeftKraus ι ν
  complete := by
    classical
    ext ⟨a, i⟩ ⟨b, j⟩
    simp only [Matrix.sum_apply]
    rw [Finset.sum_eq_single a]
    · simp only [Matrix.mul_apply]
      rw [Finset.sum_eq_single i]
      · by_cases hab : a = b <;> by_cases hij : i = j <;>
          simp_all [discardLeftKraus, Matrix.conjTranspose_apply,
            Matrix.one_apply, Prod.mk.injEq, eq_comm]
      · intro x _ hxi
        simp [discardLeftKraus, Matrix.conjTranspose_apply,
          Prod.mk.injEq, Ne.symm hxi]
      · simp
    · intro c _ hca
      simp [discardLeftKraus, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Prod.mk.injEq, Ne.symm hca]
    · simp

theorem discardLeft_operator_apply (X : Operator (ν × ι)) (i j : ι) :
    (discardLeft ι ν).operator X i j = ∑ a, X (a, i) (a, j) := by
  classical
  simp only [operator, discardLeft, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  simp [discardLeftKraus, Matrix.mul_apply, Matrix.conjTranspose_apply]

end Discard

section Defect

variable {η : Type*} [Fintype η]

/-- Actual worst-case output effect distance for channels with possibly
rectangular input/output carriers; no error bound is accepted as input. -/
def defect (C : RectangularChannel ι ο κ) (D : RectangularChannel ι ο η) : ℝ :=
  sSup (Set.insert 0 (Set.range (fun ρ => effectDistance (C.state ρ) (D.state ρ))))

theorem defect_bddAbove (C : RectangularChannel ι ο κ) (D : RectangularChannel ι ο η) :
    BddAbove (Set.insert 0 (Set.range (fun ρ => effectDistance (C.state ρ) (D.state ρ)))) := by
  refine ⟨1, ?_⟩
  rintro x (rfl | ⟨ρ, rfl⟩)
  · norm_num
  · exact effectDistance_le_one _ _

theorem defect_nonneg (C : RectangularChannel ι ο κ) (D : RectangularChannel ι ο η) :
    0 ≤ C.defect D := le_csSup (C.defect_bddAbove D) (Set.mem_insert 0 _)

theorem defect_le_one (C : RectangularChannel ι ο κ) (D : RectangularChannel ι ο η) :
    C.defect D ≤ 1 := by
  apply csSup_le (Set.insert_nonempty 0 _)
  rintro x (rfl | ⟨ρ, rfl⟩)
  · norm_num
  · exact effectDistance_le_one _ _

theorem state_distance_le_defect (C : RectangularChannel ι ο κ)
    (D : RectangularChannel ι ο η) (ρ : Density ι) :
    effectDistance (C.state ρ) (D.state ρ) ≤ C.defect D :=
  le_csSup (C.defect_bddAbove D) (Set.mem_insert_of_mem 0 ⟨ρ, rfl⟩)

theorem perturbation_bound (C : RectangularChannel ι ο κ)
    (D : RectangularChannel ι ο η) (ρ σ : Density ι) :
    effectDistance (C.state ρ) (D.state σ) ≤ effectDistance ρ σ + C.defect D :=
  (effectDistance_triangle (C.state ρ) (C.state σ) (D.state σ)).trans
    (add_le_add (C.state_effectDistance_le ρ σ) (C.state_distance_le_defect D σ))

end Defect

end RectangularChannel

end

end UEOTQM
