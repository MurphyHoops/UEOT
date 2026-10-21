import UEOTQM.PurificationIsometry
import Mathlib.Analysis.Matrix.PosDef

/-!
# Exact finite auxiliary dimension for purification

The lower bound uses actual matrix rank and the converse convex-purity theorem.
The upper bound compresses the spectral Gram factor to its nonzero eigenvalues,
then uses a proved coordinate isometry into the requested auxiliary carrier.
No factorization, spectral support size, or purity witness is assumed as input.
-/

namespace UEOTQM.QuantumPurification

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker

noncomputable section

universe u v
variable {ι : Type u} {α : Type v} [Fintype ι] [DecidableEq ι]
  [Fintype α] [DecidableEq α]

/-- The nonzero spectral support of the actual input density matrix. -/
abbrev SpectralSupport (ρ : Density ι) :=
  {i : ι // ρ.positive.isHermitian.eigenvalues i ≠ 0}

instance spectralSupportFintype (ρ : Density ι) : Fintype (SpectralSupport ρ) := by
  classical
  exact inferInstanceAs (Fintype {i : ι // ρ.positive.isHermitian.eigenvalues i ≠ 0})

instance spectralSupportDecidableEq (ρ : Density ι) : DecidableEq (SpectralSupport ρ) :=
  inferInstanceAs (DecidableEq {i : ι // ρ.positive.isHermitian.eigenvalues i ≠ 0})

/-- The chosen spectral support has exactly the actual complex matrix rank. -/
theorem spectralSupport_card (ρ : Density ι) :
    Fintype.card (SpectralSupport ρ) = ρ.matrix.rank := by
  classical
  exact ρ.positive.isHermitian.rank_eq_card_non_zero_eigs.symm

/-- Only nonzero eigenvalues contribute columns to this actual Gram factor. -/
def supportedGram (ρ : Density ι) : Matrix ι (SpectralSupport ρ) ℂ :=
  fun i a => ρ.positive.isHermitian.eigenvectorUnitary i a.val *
    (Real.sqrt (ρ.positive.isHermitian.eigenvalues a.val) : ℂ)

/-- Entrywise finite spectral expansion, with the complex conjugation explicit. -/
theorem density_spectral_expansion (ρ : Density ι) (i j : ι) :
    ρ.matrix i j = ∑ a,
      ρ.positive.isHermitian.eigenvectorUnitary i a *
      (ρ.positive.isHermitian.eigenvalues a : ℂ) *
      star (ρ.positive.isHermitian.eigenvectorUnitary j a) := by
  have h := congrFun (congrFun ρ.positive.isHermitian.spectral_theorem i) j
  simpa [Unitary.conjStarAlgAut_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.diagonal_apply] using h

/-- The compressed factor still has the original density as its full Gram matrix.
Zero spectral values are removed only after their actual terms have vanished. -/
theorem supportedGram_spec (ρ : Density ι) :
    ρ.matrix = supportedGram ρ * (supportedGram ρ)ᴴ := by
  classical
  ext i j
  rw [density_spectral_expansion, Matrix.mul_apply]
  apply Finset.sum_congr_set {a : ι | ρ.positive.isHermitian.eigenvalues a ≠ 0}
  · intro a ha
    simp only [Matrix.conjTranspose_apply, supportedGram, map_mul, Complex.star_def,
      Complex.conj_ofReal]
    have hs : (Real.sqrt (ρ.positive.isHermitian.eigenvalues a) : ℂ) *
        (Real.sqrt (ρ.positive.isHermitian.eigenvalues a) : ℂ) =
        (ρ.positive.isHermitian.eigenvalues a : ℂ) := by
      rw [← Complex.ofReal_mul, ← pow_two,
        Real.sq_sqrt (ρ.positive.eigenvalues_nonneg a)]
    rw [← hs]
    ring
  · intro a ha
    have hz : ρ.positive.isHermitian.eigenvalues a = 0 := by simpa using ha
    simp [hz]

/-- The spectral support purification vector is normalized by the actual trace. -/
theorem supportedGram_vector_normalized (ρ : Density ι) :
    (outer (vectorize (supportedGram ρ))).trace = 1 := by
  rw [vectorize_outer_trace, ← supportedGram_spec, ρ.trace_one]

/-- A pure extension whose auxiliary dimension is exactly the input matrix rank. -/
def supportPurification (ρ : Density ι) : Density (ι × SpectralSupport ρ) :=
  vectorState (vectorize (supportedGram ρ)) (supportedGram_vector_normalized ρ)

@[simp] theorem supportPurification_matrix (ρ : Density ι) :
    (supportPurification ρ).matrix = outer (vectorize (supportedGram ρ)) := rfl

theorem supportPurification_isPure (ρ : Density ι) : IsPure (supportPurification ρ) :=
  vectorState_isPure _ _

/-- The marginal is the original density on all matrix entries. -/
theorem supportPurification_marginal (ρ : Density ι) :
    (RectangularChannel.discardRight ι (SpectralSupport ρ)).state
      (supportPurification ρ) = ρ := by
  apply Density.ext
  change (RectangularChannel.discardRight ι (SpectralSupport ρ)).operator
    (outer (vectorize (supportedGram ρ))) = ρ.matrix
  rw [discard_vectorize_outer, ← supportedGram_spec]

/-- Every full convex-pure extension obeys the actual matrix-rank lower bound. -/
theorem rank_marginal_le_auxiliary_card (Ψ : Density (ι × α)) (hΨ : IsPure Ψ) :
    ((RectangularChannel.discardRight ι α).state Ψ).matrix.rank ≤ Fintype.card α := by
  obtain ⟨ψ, _, hψ⟩ := hΨ.exists_vector Ψ
  let A : Matrix ι α ℂ := fun i a => ψ (i, a)
  have hA : ((RectangularChannel.discardRight ι α).state Ψ).matrix = A * Aᴴ := by
    change (RectangularChannel.discardRight ι α).operator Ψ.matrix = _
    rw [hψ]
    exact discard_vectorize_outer A
  rw [hA, Matrix.rank_self_mul_conjTranspose]
  exact Matrix.rank_le_card_width A

/-- An arbitrary requested carrier of sufficient size supports a real pure extension. -/
theorem exists_purification_of_rank_le (ρ : Density ι)
    (h : ρ.matrix.rank ≤ Fintype.card α) :
    ∃ Ψ : Density (ι × α), IsPure Ψ ∧
      (RectangularChannel.discardRight ι α).state Ψ = ρ := by
  have hc : Fintype.card (SpectralSupport ρ) ≤ Fintype.card α := by
    rwa [spectralSupport_card]
  obtain ⟨J, hJ⟩ := exists_matrix_isometry_of_card_le hc
  refine ⟨(auxiliaryEmbeddingChannel (ι := ι) J hJ).state (supportPurification ρ),
    auxiliaryEmbeddingChannel_preserves_purity J hJ _ (supportPurification_isPure ρ), ?_⟩
  rw [auxiliaryEmbeddingChannel_discard_state, supportPurification_marginal]

/-- Exact purification existence criterion in the original full density space. -/
theorem exists_purification_iff_rank_le (ρ : Density ι) :
    (∃ Ψ : Density (ι × α), IsPure Ψ ∧
      (RectangularChannel.discardRight ι α).state Ψ = ρ) ↔
      ρ.matrix.rank ≤ Fintype.card α := by
  constructor
  · rintro ⟨Ψ, hΨ, hm⟩
    rw [← hm]
    exact rank_marginal_le_auxiliary_card Ψ hΨ
  · exact exists_purification_of_rank_le ρ

/-- The lower bound is attained on the explicitly requested `Fin rank` carrier. -/
theorem exists_minimal_purification (ρ : Density ι) :
    ∃ Ψ : Density (ι × Fin ρ.matrix.rank), IsPure Ψ ∧
      (RectangularChannel.discardRight ι (Fin ρ.matrix.rank)).state Ψ = ρ := by
  apply exists_purification_of_rank_le
  simp

/-- Smaller finite auxiliary carriers cannot purify the actual state. -/
theorem no_purification_of_card_lt_rank (ρ : Density ι)
    (h : Fintype.card α < ρ.matrix.rank) :
    ¬ ∃ Ψ : Density (ι × α), IsPure Ψ ∧
      (RectangularChannel.discardRight ι α).state Ψ = ρ := by
  rw [exists_purification_iff_rank_le]
  exact Nat.not_le_of_lt h

/-- Rank zero is excluded by the same exact construction and trace-one boundary. -/
theorem density_rank_pos (ρ : Density ι) : 0 < ρ.matrix.rank := by
  by_contra h
  have hz : ρ.matrix.rank = 0 := Nat.eq_zero_of_not_pos h
  obtain ⟨Ψ, _, _⟩ := exists_minimal_purification ρ
  haveI : IsEmpty (Fin ρ.matrix.rank) := hz ▸ inferInstance
  exact density_empty_elim Ψ

/-- An empty auxiliary system cannot support a pure extension of a density input. -/
theorem no_purification_empty_auxiliary [IsEmpty α] (ρ : Density ι) :
    ¬ ∃ Ψ : Density (ι × α), IsPure Ψ ∧
      (RectangularChannel.discardRight ι α).state Ψ = ρ := by
  apply no_purification_of_card_lt_rank
  simpa using density_rank_pos ρ

end
end UEOTQM.QuantumPurification
