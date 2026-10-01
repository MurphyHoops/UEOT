import UEOT.V3.Compression.TopologyChangingGoaRestrictedResidualAdapter

/-!
# Sharp smallest-singular-value certificate for topology-changing GOA stability

The previous Track-S checkpoints established the finite-dimensional chain

`restricted residual injective`

`↔ all relevant singular values are positive`

`↔ there exists some positive Euclidean lower-gain constant`.

This module identifies an explicit canonical lower-gain constant: the final
valid indexed singular value of the finite-dimensional domain.

The general linear-algebra theorem proved here is

`σ_min(T) * ‖x‖ ≤ ‖T x‖`

for a nonzero finite-dimensional real inner-product domain.  Applying it to the
zero-mass residual restriction gives an explicit spectral robustness radius for
the selected GOA stationary branch.

The zero-dimensional case is intentionally excluded from the `σ_min` indexing
statement because there is no final valid singular-value index when the domain
has finrank zero.
-/

namespace UEOT.V3.Compression.TopologyChangingGoaSharpSingularValue

open scoped RealInnerProductSpace

open UEOT.V3
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.InvariantSetGaugeInvariance
open UEOT.V3.Compression.TopologyChangingGoaSpectralIsolation
open UEOT.V3.Compression.TopologyChangingGoaRestrictedResidualAdapter

universe uE uF uS

noncomputable section

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {F : Type uF} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- **Smallest-singular-value lower bound.**

For a nonzero finite-dimensional real inner-product domain, the final valid
indexed singular value is a global Euclidean lower-gain constant. -/
theorem smallest_singularValue_mul_norm_le
    (T : E →ₗ[ℝ] F)
    (hpos : 0 < Module.finrank ℝ E)
    (x : E) :
    T.singularValues (Module.finrank ℝ E - 1) * ‖x‖ ≤ ‖T x‖ := by
  let n := Module.finrank ℝ E
  have hn : Module.finrank ℝ E = n := rfl
  have hnpos : 0 < n := by simpa [n] using hpos
  let A : E →ₗ[ℝ] E := LinearMap.adjoint T ∘ₗ T
  have hA : A.IsSymmetric := by
    simpa [A] using T.isSymmetric_adjoint_comp_self
  let b : OrthonormalBasis (Fin n) ℝ E := hA.eigenvectorBasis hn
  let last : Fin n := ⟨n - 1, by omega⟩
  have hmin (i : Fin n) :
      hA.eigenvalues hn last ≤ hA.eigenvalues hn i := by
    apply hA.eigenvalues_antitone hn
    apply Fin.le_iff_val_le_val.mpr
    dsimp [last]
    omega
  have hcoord (i : Fin n) :
      inner ℝ (b i) (A x) =
        hA.eigenvalues hn i * inner ℝ (b i) x := by
    have hdiag := hA.eigenvectorBasis_apply_self_apply hn x i
    simpa [b, OrthonormalBasis.repr_apply_apply] using hdiag
  have hquad :
      hA.eigenvalues hn last * ‖x‖ ^ 2 ≤ inner ℝ x (A x) := by
    rw [← b.sum_sq_inner_right x]
    rw [← b.sum_inner_mul_inner x (A x)]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [hcoord i]
    rw [real_inner_comm x (b i)]
    have hs : 0 ≤ inner ℝ (b i) x ^ 2 := sq_nonneg _
    nlinarith [hmin i]
  have hTx : inner ℝ x (A x) = ‖T x‖ ^ 2 := by
    rw [show A x = LinearMap.adjoint T (T x) by rfl]
    rw [LinearMap.adjoint_inner_right]
    exact real_inner_self_eq_norm_sq (T x)
  have hsig :
      T.singularValues (n - 1) ^ 2 = hA.eigenvalues hn last := by
    simpa [last, n, A] using T.sq_singularValues_fin hn last
  rw [hTx, ← hsig] at hquad
  have hsq :
      (T.singularValues (n - 1) * ‖x‖) ^ 2 ≤ ‖T x‖ ^ 2 := by
    nlinarith [hquad]
  have hleft : 0 ≤ T.singularValues (n - 1) * ‖x‖ :=
    mul_nonneg (T.singularValues_nonneg _) (norm_nonneg _)
  exact (sq_le_sq₀ hleft (norm_nonneg _)).mp hsq


variable {S : Type uS} [Fintype S] [Nonempty S]

noncomputable local instance stateDecidableEq : DecidableEq S :=
  Classical.decEq S

local instance stateMeasurableSpace : MeasurableSpace S := ⊤

/-- The final valid singular value of the zero-mass residual restriction.

This definition is meaningful as a sharp certificate only when the restricted
domain has positive finrank; the subsequent theorems state that requirement
explicitly. -/
def restrictedMinSingularValue (P : Matrix S S ℝ) : ℝ :=
  (zeroSumResidualLinear P).singularValues
    (Module.finrank ℝ (zeroSumEuclidean (S := S)) - 1)

/-- Under restricted injectivity, the explicit final valid singular value is
strictly positive. -/
theorem restrictedMinSingularValue_pos
    (P : Matrix S S ℝ)
    (hpos : 0 < Module.finrank ℝ (zeroSumEuclidean (S := S)))
    (hinj : Function.Injective (zeroSumResidualLinear P)) :
    0 < restrictedMinSingularValue P := by
  have hall := (restricted_injective_iff_all_singularValues_pos P).1 hinj
  unfold restrictedMinSingularValue
  apply hall
  omega

/-- Restricted injectivity yields the S1 Euclidean lower-gain certificate with
the explicit smallest valid singular value itself as `kappa`. -/
theorem sharp_l2LowerSingularBound_of_restricted_injective
    (P : Matrix S S ℝ)
    (hpos : 0 < Module.finrank ℝ (zeroSumEuclidean (S := S)))
    (hinj : Function.Injective (zeroSumResidualLinear P)) :
    ZeroSumL2LowerSingularBound P (restrictedMinSingularValue P) := by
  refine ⟨restrictedMinSingularValue_pos P hpos hinj, ?_⟩
  intro v hv
  have hmem :
      (WithLp.toLp 2 v : EuclideanSpace ℝ S) ∈ zeroSumEuclidean (S := S) :=
    (zeroSum_mem_iff v).2 hv
  let x : zeroSumEuclidean (S := S) := ⟨WithLp.toLp 2 v, hmem⟩
  have hsharp := smallest_singularValue_mul_norm_le
    (zeroSumResidualLinear P) hpos x
  have hxnorm : ‖(x : EuclideanSpace ℝ S)‖ = signedL2 v := by
    symm
    exact signedL2_eq_euclidean_norm v
  have hmapEq :
      (residualEuclideanLinear P) (WithLp.toLp 2 v) =
        (WithLp.toLp 2 (signedResidual P v) : EuclideanSpace ℝ S) := by
    rw [WithLp.ext_iff]
    exact residualEuclideanLinear_ofLp P v
  have hmapNorm :
      ‖(residualEuclideanLinear P) (WithLp.toLp 2 v)‖ =
        signedL2 (signedResidual P v) := by
    rw [hmapEq]
    symm
    exact signedL2_eq_euclidean_norm (signedResidual P v)
  simpa [restrictedMinSingularValue, zeroSumResidualLinear, x, hxnorm, hmapNorm]
    using hsharp

/-- **Explicit spectral GOA robustness certificate.**

When the zero-mass residual restriction has positive dimension and is
injective, a target stochastic kernel within uniform row-TV defect `epsilon`
has an invariant law inside the explicit tube

`sqrt(card S) * epsilon / restrictedMinSingularValue P`.

The denominator is now the actual final valid indexed singular value of the
restricted residual operator, not merely an existential lower-gain witness. -/
theorem sharp_stationary_tracking_of_restricted_injective
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (Q : Matrix S S ℝ) (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (muStar : stdSimplex ℝ S)
    (hmuStar : step P hP muStar = muStar)
    (epsilon : ℝ)
    (hpos : 0 < Module.finrank ℝ (zeroSumEuclidean (S := S)))
    (hinj : Function.Injective (zeroSumResidualLinear P))
    (hrow : ∀ x, crossRowTV P hP Q hQ x ≤ epsilon) :
    ∃ muhat : stdSimplex ℝ S,
      muhat ∈ invariantLawSet Q hQ ∧
      lawTV muStar muhat ≤
        Real.sqrt (Fintype.card S) * epsilon /
          restrictedMinSingularValue P := by
  exact l2LowerSingularBound_stationary_tracking
    P hP Q hQ muStar hmuStar
    (restrictedMinSingularValue P) epsilon
    (sharp_l2LowerSingularBound_of_restricted_injective P hpos hinj) hrow

end


end UEOT.V3.Compression.TopologyChangingGoaSharpSingularValue
