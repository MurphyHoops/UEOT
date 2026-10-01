import UEOT.V3.Compression.TopologyChangingGoaSharpSingularValue
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Zero-mass dimension adapter for sharp GOA spectral stability

The sharp singular-value Track-S theorem is naturally stated on the
zero-total-mass signed-law subspace.  Its smallest-valid-singular-value index
requires this subspace to have positive finrank.

For a finite nonempty state space `S`, that abstract linear-algebra condition
has a simple exact interpretation:

`finrank(zero-mass) + 1 = card S`.

Hence the zero-mass subspace has positive dimension exactly when `S` has at
least two states.  This module proves that identity and exposes a user-facing
sharp stationary-tracking theorem with hypothesis `1 < card S` instead of an
internal finrank condition.
-/

namespace UEOT.V3.Compression.TopologyChangingGoaZeroMassDimension

open UEOT.V3
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.InvariantSetGaugeInvariance
open UEOT.V3.Compression.TopologyChangingGoaRestrictedResidualAdapter
open UEOT.V3.Compression.TopologyChangingGoaSharpSingularValue

universe uS

noncomputable section

variable {S : Type uS} [Fintype S] [Nonempty S]

noncomputable local instance stateDecidableEq : DecidableEq S :=
  Classical.decEq S

local instance stateMeasurableSpace : MeasurableSpace S := ⊤

/-- The total-mass functional on Euclidean signed laws is nonzero whenever the
finite state space is nonempty. -/
theorem euclideanSum_ne_zero : euclideanSum (S := S) ≠ 0 := by
  intro hzero
  let oneVec : EuclideanSpace ℝ S :=
    WithLp.toLp 2 (fun _ => (1 : ℝ))
  have happ :=
    congrArg (fun f : EuclideanSpace ℝ S →ₗ[ℝ] ℝ => f oneVec) hzero
  simp [euclideanSum, oneVec] at happ

/-- Exact dimension formula for the zero-total-mass signed-law subspace. -/
theorem finrank_zeroSumEuclidean_add_one :
    Module.finrank ℝ (zeroSumEuclidean (S := S)) + 1 = Fintype.card S := by
  unfold zeroSumEuclidean
  have h :=
    Module.Dual.finrank_ker_add_one_of_ne_zero
      (euclideanSum_ne_zero (S := S))
  rw [finrank_euclideanSpace] at h
  exact h

/-- The zero-mass signed-law subspace is nontrivial exactly when the state
space has at least two elements. -/
theorem zeroSum_finrank_pos_iff_card_one_lt :
    0 < Module.finrank ℝ (zeroSumEuclidean (S := S)) ↔
      1 < Fintype.card S := by
  have hdim := finrank_zeroSumEuclidean_add_one (S := S)
  omega

/-- Under the natural two-or-more-state condition, restricted injectivity makes
the explicit smallest residual singular value strictly positive. -/
theorem restrictedMinSingularValue_pos_of_card_one_lt
    (P : Matrix S S ℝ)
    (hcard : 1 < Fintype.card S)
    (hinj : Function.Injective (zeroSumResidualLinear P)) :
    0 < restrictedMinSingularValue P := by
  exact restrictedMinSingularValue_pos P
    ((zeroSum_finrank_pos_iff_card_one_lt (S := S)).2 hcard) hinj

/-- **User-facing sharp spectral GOA tracking theorem.**

For a finite stochastic system with at least two states, if the source
zero-mass residual restriction is injective and the target kernel has uniform
row-TV defect `epsilon`, then a target invariant law lies in the explicit tube

`sqrt(card S) * epsilon / restrictedMinSingularValue P`

around the selected source stationary branch. -/
theorem sharp_stationary_tracking_of_card_one_lt
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (Q : Matrix S S ℝ) (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (muStar : stdSimplex ℝ S)
    (hmuStar : step P hP muStar = muStar)
    (epsilon : ℝ)
    (hcard : 1 < Fintype.card S)
    (hinj : Function.Injective (zeroSumResidualLinear P))
    (hrow : ∀ x, crossRowTV P hP Q hQ x ≤ epsilon) :
    ∃ muhat : stdSimplex ℝ S,
      muhat ∈ invariantLawSet Q hQ ∧
      lawTV muStar muhat ≤
        Real.sqrt (Fintype.card S) * epsilon /
          restrictedMinSingularValue P := by
  exact sharp_stationary_tracking_of_restricted_injective
    P hP Q hQ muStar hmuStar epsilon
    ((zeroSum_finrank_pos_iff_card_one_lt (S := S)).2 hcard)
    hinj hrow

end


end UEOT.V3.Compression.TopologyChangingGoaZeroMassDimension
