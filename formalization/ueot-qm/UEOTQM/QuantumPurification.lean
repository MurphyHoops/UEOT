import UEOTQM.RectangularChannels

/-!
# Convex-extreme pure states and finite quantum purification

Purity quantifies over the entire existing `Density` type. Rank-one form is
used to prove convex extremality, never as its definition. Gram factors are
obtained from the existing positive-semidefinite predicate.
-/

namespace UEOTQM.QuantumPurification

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker

noncomputable section

universe u v
variable {ι : Type u} {α : Type v} [Fintype ι] [DecidableEq ι]
  [Fintype α] [DecidableEq α]

/-- The actual binary convex mixture in the full density state space. -/
def mix (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ρ σ : Density ι) : Density ι where
  matrix := t • ρ.matrix + (1 - t) • σ.matrix
  positive := (ρ.positive.smul ht0).add (σ.positive.smul (sub_nonneg.mpr ht1))
  trace_one := by
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, ρ.trace_one, σ.trace_one]
    simp

omit [DecidableEq ι] in
@[simp] theorem mix_matrix (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ρ σ : Density ι) :
    (mix t ht0 ht1 ρ σ).matrix = t • ρ.matrix + (1 - t) • σ.matrix := rfl

/-- Convex extremality relative to every positive trace-one matrix. -/
def IsPure (ρ : Density ι) : Prop :=
  ∀ (σ τ : Density ι) (t : ℝ), 0 < t → t < 1 →
    ρ.matrix = t • σ.matrix + (1 - t) • τ.matrix → σ = ρ ∧ τ = ρ

def outer (v : ι → ℂ) : Operator ι := Matrix.vecMulVec v (star v)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem outer_apply (v : ι → ℂ) (i j : ι) :
    outer v i j = v i * star (v j) := rfl

omit [DecidableEq ι] in
theorem outer_positive (v : ι → ℂ) : (outer v).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star v

omit [DecidableEq ι] in
theorem outer_hermitian (v : ι → ℂ) : (outer v)ᴴ = outer v :=
  (outer_positive v).isHermitian.eq

omit [DecidableEq ι] in
theorem outer_trace (v : ι → ℂ) : (outer v).trace = star v ⬝ᵥ v := by
  rw [outer, Matrix.trace_vecMulVec, dotProduct_comm]

omit [DecidableEq ι] in
theorem outer_square (v : ι → ℂ) (hv : (outer v).trace = 1) :
    outer v * outer v = outer v := by
  rw [outer_trace] at hv
  simp only [outer, Matrix.vecMulVec_mul_vecMulVec, hv, one_smul]

omit [DecidableEq ι] in
theorem outer_sandwich (v : ι → ℂ) (X : Operator ι) :
    outer v * X * outer v = (X * outer v).trace • outer v := by
  change Matrix.vecMulVec v (star v) * X * Matrix.vecMulVec v (star v) =
    (X * Matrix.vecMulVec v (star v)).trace • Matrix.vecMulVec v (star v)
  rw [Matrix.vecMulVec_mul v (star v) X, Matrix.vecMulVec_mul_vecMulVec,
    Matrix.vecMulVec_smul, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec,
    ← dotProduct_mulVec, dotProduct_comm (star v) (X *ᵥ v)]

/-- A normalized vector defines a member of the whole density space. -/
def vectorState (v : ι → ℂ) (hv : (outer v).trace = 1) : Density ι where
  matrix := outer v
  positive := outer_positive v
  trace_one := hv

omit [DecidableEq ι] in
@[simp] theorem vectorState_matrix (v : ι → ℂ) (hv : (outer v).trace = 1) :
    (vectorState v hv).matrix = outer v := rfl

/-- The factor is derived from PSD, not supplied by a state caller. -/
theorem exists_gram (ρ : Density ι) : ∃ A : Operator ι, ρ.matrix = A * Aᴴ := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ρ.positive.nonneg
  refine ⟨Bᴴ, ?_⟩
  simpa only [star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] using hB

/-- Vanishing positive compression forces its whole supported column block to
vanish. The proof obtains a Gram factor from the full PSD cone. -/
theorem positive_compression_zero {X Q : Operator ι} (hX : X.PosSemidef)
    (hQ : Qᴴ = Q) (hz : Q * X * Q = 0) : X * Q = 0 := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hX.nonneg
  change X = Bᴴ * B at hB
  have hBQ : B * Q = 0 := by
    apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
    calc
      ((B * Q)ᴴ * (B * Q)).trace = (Q * (Bᴴ * B) * Q).trace := by
        simp only [Matrix.conjTranspose_mul, hQ, Matrix.mul_assoc]
      _ = 0 := by
        rw [← hB, hz, Matrix.trace_zero]
  rw [hB, Matrix.mul_assoc, hBQ, Matrix.mul_zero]

theorem density_eq_vector_of_compression_zero (v : ι → ℂ)
    (ρ : Density ι) (hz : (1 - outer v) * ρ.matrix * (1 - outer v) = 0) :
    ρ.matrix = outer v := by
  have hQ : (1 - outer v)ᴴ = 1 - outer v := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, outer_hermitian]
  have hr := positive_compression_zero ρ.positive hQ hz
  rw [Matrix.mul_sub, Matrix.mul_one] at hr
  have hright : ρ.matrix * outer v = ρ.matrix := (sub_eq_zero.mp hr).symm
  have hleft : outer v * ρ.matrix = ρ.matrix := by
    have h := congrArg Matrix.conjTranspose hright
    simpa only [Matrix.conjTranspose_mul, outer_hermitian,
      ρ.positive.isHermitian.eq] using h
  have h := outer_sandwich v ρ.matrix
  rw [hleft, hright, ρ.trace_one, one_smul] at h
  exact h

/-- Rank-one normalized states are proved extreme against all density inputs. -/
theorem vectorState_isPure (v : ι → ℂ) (hv : (outer v).trace = 1) :
    IsPure (vectorState v hv) := by
  intro σ τ t ht0 ht1 heq
  let Q : Operator ι := 1 - outer v
  have hQ : Qᴴ = Q := by
    simp only [Q, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, outer_hermitian]
  have hQP : Q * outer v = 0 := by
    simp only [Q, Matrix.sub_mul, Matrix.one_mul, outer_square v hv, sub_self]
  have hs : (Q * σ.matrix * Q).PosSemidef := by
    simpa only [hQ] using σ.positive.mul_mul_conjTranspose_same Q
  have ht : (Q * τ.matrix * Q).PosSemidef := by
    simpa only [hQ] using τ.positive.mul_mul_conjTranspose_same Q
  have hzero : t • (Q * σ.matrix * Q) + (1 - t) • (Q * τ.matrix * Q) = 0 := by
    calc
      _ = Q * (t • σ.matrix + (1 - t) • τ.matrix) * Q := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
      _ = Q * outer v * Q := by rw [← heq]; rfl
      _ = 0 := by rw [hQP, Matrix.zero_mul]
  have hparts := (add_eq_zero_iff_of_nonneg
    (hs.smul ht0.le).nonneg (ht.smul (sub_nonneg.mpr ht1.le)).nonneg).mp hzero
  have hs0 : Q * σ.matrix * Q = 0 :=
    (smul_eq_zero.mp hparts.1).resolve_left ht0.ne'
  have ht0' : Q * τ.matrix * Q = 0 :=
    (smul_eq_zero.mp hparts.2).resolve_left (sub_pos.mpr ht1).ne'
  exact ⟨Density.ext (density_eq_vector_of_compression_zero v σ hs0),
    Density.ext (density_eq_vector_of_compression_zero v τ ht0')⟩

/-- A matrix is regarded as a vector on the actual product carrier. -/
def vectorize (A : Matrix ι α ℂ) : ι × α → ℂ := fun p => A p.1 p.2

omit [DecidableEq ι] [DecidableEq α] in
theorem vectorize_outer_trace (A : Matrix ι α ℂ) :
    (outer (vectorize A)).trace = (A * Aᴴ).trace := by
  simp [outer, Matrix.vecMulVec, vectorize, Matrix.trace, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type]

/-- The partial trace is the actual rectangular Kraus channel, on all entries. -/
theorem discard_vectorize_outer (A : Matrix ι α ℂ) :
    (RectangularChannel.discardRight ι α).operator (outer (vectorize A)) = A * Aᴴ := by
  ext i j
  rw [RectangularChannel.discardRight_operator_apply]
  simp only [outer_apply, vectorize, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- A selected Gram factor is obtained from `Density.positive`. -/
def gram (ρ : Density ι) : Operator ι := Classical.choose (exists_gram ρ)

theorem gram_spec (ρ : Density ι) : ρ.matrix = gram ρ * (gram ρ)ᴴ :=
  Classical.choose_spec (exists_gram ρ)

def purificationVector (ρ : Density ι) : ι × ι → ℂ := vectorize (gram ρ)

theorem purificationVector_normalized (ρ : Density ι) :
    (outer (purificationVector ρ)).trace = 1 := by
  rw [purificationVector, vectorize_outer_trace, ← gram_spec, ρ.trace_one]

/-- A canonical choice of finite purification, without any external factor input. -/
def purification (ρ : Density ι) : Density (ι × ι) :=
  vectorState (purificationVector ρ) (purificationVector_normalized ρ)

@[simp] theorem purification_matrix (ρ : Density ι) :
    (purification ρ).matrix = outer (purificationVector ρ) := rfl

theorem purification_isPure (ρ : Density ι) : IsPure (purification ρ) :=
  vectorState_isPure (purificationVector ρ) (purificationVector_normalized ρ)

theorem purification_marginal (ρ : Density ι) :
    (RectangularChannel.discardRight ι ι).state (purification ρ) = ρ := by
  apply Density.ext
  change (RectangularChannel.discardRight ι ι).operator
    (outer (vectorize (gram ρ))) = ρ.matrix
  rw [discard_vectorize_outer, ← gram_spec]

/-- Every finite density has a pure extension in the entire joint density space.
The carrier may be empty in the signature; its trace-one input already rules out
that case. No Gram witness or purity conclusion is supplied as an assumption. -/
theorem exists_purification (ρ : Density ι) :
    ∃ Ψ : Density (ι × ι), IsPure Ψ ∧
      (RectangularChannel.discardRight ι ι).state Ψ = ρ :=
  ⟨purification ρ, purification_isPure ρ, purification_marginal ρ⟩

omit [DecidableEq ι] in
theorem density_empty_elim [IsEmpty ι] (ρ : Density ι) : False := by
  have h := ρ.trace_one
  simp [Matrix.trace] at h

/-- The product state is the actual Kronecker product of arbitrary densities. -/
def product (ρ : Density ι) (σ : Density α) : Density (ι × α) where
  matrix := ρ.matrix ⊗ₖ σ.matrix
  positive := ρ.positive.kronecker σ.positive
  trace_one := by rw [Matrix.trace_kronecker, ρ.trace_one, σ.trace_one, mul_one]

omit [DecidableEq ι] [DecidableEq α] in
@[simp] theorem product_matrix (ρ : Density ι) (σ : Density α) :
    (product ρ σ).matrix = ρ.matrix ⊗ₖ σ.matrix := rfl

theorem discard_product (ρ : Density ι) (σ : Density α) :
    (RectangularChannel.discardRight ι α).state (product ρ σ) = ρ := by
  apply Density.ext
  ext i j
  rw [RectangularChannel.state_matrix, product_matrix,
    RectangularChannel.discardRight_operator_apply]
  simp only [Matrix.kronecker_apply]
  rw [← Finset.mul_sum]
  change ρ.matrix i j * σ.matrix.trace = ρ.matrix i j
  rw [σ.trace_one, mul_one]

theorem probability_mix (E : Effect ι) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ρ σ : Density ι) :
    E.probability (mix t ht0 ht1 ρ σ) =
      t * E.probability ρ + (1 - t) * E.probability σ := by
  exact (pairing_add_right E.matrix (t • ρ.matrix) ((1 - t) • σ.matrix)).trans
    (by rw [pairing_smul_right, pairing_smul_right]; rfl)

theorem state_mix {ο κ : Type*} [Fintype ο] [DecidableEq ο] [Fintype κ]
    (C : RectangularChannel ι ο κ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ρ σ : Density ι) :
    C.state (mix t ht0 ht1 ρ σ) = mix t ht0 ht1 (C.state ρ) (C.state σ) := by
  apply Density.ext
  change C.operator (t • ρ.matrix + (1 - t) • σ.matrix) =
    t • C.operator ρ.matrix + (1 - t) • C.operator σ.matrix
  rw [C.operator_add, C.operator_real_smul, C.operator_real_smul]

end
end UEOTQM.QuantumPurification
