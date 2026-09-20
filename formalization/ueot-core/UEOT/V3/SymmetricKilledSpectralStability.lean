import UEOT.V3.PathError
import UEOT.V3.FiniteDiscountedApproxQuotient
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Tactic


/-!
# P-GOA-04 — symmetric killed-kernel spectral stability

This module formalizes frozen UEOT Core v3 §21.5.  The source regime is finite,
symmetric, entrywise nonnegative, irreducible and row-substochastic.  The
perturbation is measured in the genuine Euclidean L2 operator norm.

The spectral datum `PrincipalGap` is the Rayleigh-variational form of
“positive unit principal eigenvector with second eigenvalue `lambda2`”: the
principal Rayleigh quotient is at most `rho`, while every vector orthogonal to
the principal vector has Rayleigh quotient at most `lambda2`.  This is not an
extra eigenvector-closeness hypothesis.

The proof follows the frozen source argument: principal-eigenvalue perturbation,
orthogonal residual control by the spectral gap, positive-vector angle control,
and the exact finite-alphabet `TV = 1/2 L1` identity for squared coordinates.
-/

namespace UEOT.V3.SymmetricKilledSpectralStability

noncomputable section
open scoped BigOperators RealInnerProductSpace Matrix.Norms.L2Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure PrincipalEigenpair (T : E →L[ℝ] E) (u : E) (rho : ℝ) : Prop where
  unit : ‖u‖ = 1
  eigen : T u = rho • u
  top : ∀ x, inner ℝ (T x) x ≤ rho * ‖x‖ ^ 2

structure PrincipalGap (T : E →L[ℝ] E) (u : E) (rho lambda2 : ℝ) : Prop where
  unit : ‖u‖ = 1
  eigen : T u = rho • u
  top : ∀ x, inner ℝ (T x) x ≤ rho * ‖x‖ ^ 2
  orthogonal_le : ∀ x, inner ℝ x u = 0 → inner ℝ (T x) x ≤ lambda2 * ‖x‖ ^ 2

lemma PrincipalGap.toPrincipalEigenpair
    {T : E →L[ℝ] E} {u : E} {rho lambda2 : ℝ}
    (h : PrincipalGap T u rho lambda2) : PrincipalEigenpair T u rho :=
  ⟨h.unit, h.eigen, h.top⟩

lemma perturb_inner_abs_le
    (A B : E →L[ℝ] E) (x y : E) (eta : ℝ)
    (hAB : ‖B - A‖ ≤ eta) :
    |inner ℝ ((B - A) x) y| ≤ eta * ‖x‖ * ‖y‖ := by
  calc
    |inner ℝ ((B - A) x) y| ≤ ‖(B - A) x‖ * ‖y‖ := abs_real_inner_le_norm _ _
    _ ≤ (‖B - A‖ * ‖x‖) * ‖y‖ := by
      gcongr
      exact (B - A).le_opNorm x
    _ ≤ (eta * ‖x‖) * ‖y‖ := by
      gcongr
    _ = eta * ‖x‖ * ‖y‖ := by ring

lemma principal_eigenvalue_perturbation
    (A B : E →L[ℝ] E) (u v : E) (rho sigma eta : ℝ)
    (hu : PrincipalEigenpair A u rho)
    (hv : PrincipalEigenpair B v sigma)
    (hAB : ‖B - A‖ ≤ eta) :
    |sigma - rho| ≤ eta := by
  have heta : 0 ≤ eta := (norm_nonneg (B - A)).trans hAB
  have hBinner : inner ℝ (B v) v = sigma := by
    rw [hv.eigen, real_inner_smul_left, real_inner_self_eq_norm_sq, hv.unit]
    norm_num
  have hAinner : inner ℝ (A u) u = rho := by
    rw [hu.eigen, real_inner_smul_left, real_inner_self_eq_norm_sq, hu.unit]
    norm_num
  have hpert_v : |inner ℝ ((B - A) v) v| ≤ eta := by
    have h := perturb_inner_abs_le A B v v eta hAB
    simpa [hv.unit] using h
  have hpert_u : |inner ℝ ((B - A) u) u| ≤ eta := by
    have h := perturb_inner_abs_le A B u u eta hAB
    simpa [hu.unit] using h
  have hupper : sigma ≤ rho + eta := by
    have hdecomp : inner ℝ (B v) v = inner ℝ (A v) v + inner ℝ ((B - A) v) v := by
      have heq : B v = A v + (B - A) v := by simp
      rw [heq, inner_add_left]
    have htop := hu.top v
    rw [hv.unit] at htop
    norm_num at htop
    have hp := (le_abs_self (inner ℝ ((B - A) v) v)).trans hpert_v
    linarith
  have hlower : rho ≤ sigma + eta := by
    have hdecomp : inner ℝ (A u) u = inner ℝ (B u) u - inner ℝ ((B - A) u) u := by
      have heq : A u = B u - (B - A) u := by simp
      rw [heq, inner_sub_left]
    have htop := hv.top u
    rw [hu.unit] at htop
    norm_num at htop
    have hp := (neg_le_of_abs_le hpert_u)
    linarith
  exact abs_le.2 ⟨by linarith, by linarith⟩

lemma orthogonal_residual_bound
    (A B : E →L[ℝ] E) (u v : E)
    (rho sigma lambda2 g eta : ℝ)
    (hu : PrincipalGap A u rho lambda2)
    (hv : PrincipalEigenpair B v sigma)
    (hgap : g = rho - lambda2) (hg : 0 < g)
    (hAB : ‖B - A‖ ≤ eta) (heta : eta < g / 2) :
    let c := inner ℝ u v
    let w := v - c • u
    ‖w‖ ≤ 2 * eta / g := by
  dsimp
  let c : ℝ := inner ℝ u v
  let w : E := v - c • u
  have heta0 : 0 ≤ eta := (norm_nonneg (B - A)).trans hAB
  have hclose := principal_eigenvalue_perturbation A B u v rho sigma eta hu.toPrincipalEigenpair hv hAB
  have hsigma_lower : rho - eta ≤ sigma := by
    have := (abs_le.mp hclose).1
    linarith
  have hgw : 0 < g - eta := by linarith
  have hwu : inner ℝ w u = 0 := by
    simp only [w, c, inner_sub_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hu.unit, one_pow, mul_one]
    rw [real_inner_comm v u]
    exact sub_self _
  have huw : inner ℝ u w = 0 := by simpa [real_inner_comm] using hwu
  have hv_decomp : v = c • u + w := by simp [w]
  have hvw : inner ℝ v w = ‖w‖ ^ 2 := by
    rw [hv_decomp, inner_add_left, real_inner_smul_left, huw]
    simp [real_inner_self_eq_norm_sq]
  have hAuw : inner ℝ (A u) w = 0 := by
    rw [hu.eigen, real_inner_smul_left, huw, mul_zero]
  have hAv : A v = c • A u + A w := by rw [hv_decomp, map_add, map_smul]
  have henergy :
      sigma * ‖w‖ ^ 2 = inner ℝ (A w) w + inner ℝ ((B - A) v) w := by
    calc
      sigma * ‖w‖ ^ 2 = inner ℝ (sigma • v) w := by rw [real_inner_smul_left, hvw]
      _ = inner ℝ (B v) w := by rw [hv.eigen]
      _ = inner ℝ (A v + (B - A) v) w := by congr 1; simp
      _ = inner ℝ (A v) w + inner ℝ ((B - A) v) w := by rw [inner_add_left]
      _ = inner ℝ (A w) w + inner ℝ ((B - A) v) w := by
        rw [hAv, inner_add_left, real_inner_smul_left, hAuw, mul_zero, zero_add]
  have hgap_energy := hu.orthogonal_le w hwu
  have hpert : |inner ℝ ((B - A) v) w| ≤ eta * ‖w‖ := by
    have h := perturb_inner_abs_le A B v w eta hAB
    simpa [hv.unit] using h
  have hraw : (sigma - lambda2) * ‖w‖ ^ 2 ≤ eta * ‖w‖ := by
    have hp := (le_abs_self (inner ℝ ((B - A) v) w)).trans hpert
    nlinarith
  have hcoef : g - eta ≤ sigma - lambda2 := by
    rw [hgap]
    linarith
  have hraw' : (g - eta) * ‖w‖ ^ 2 ≤ eta * ‖w‖ := by
    calc
      (g - eta) * ‖w‖ ^ 2 ≤ (sigma - lambda2) * ‖w‖ ^ 2 := by
        gcongr
      _ ≤ eta * ‖w‖ := hraw
  by_cases hw : w = 0
  · change ‖w‖ ≤ 2 * eta / g
    rw [hw, norm_zero]
    positivity
  · have hwnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have hcancel : (g - eta) * ‖w‖ ≤ eta := by
      refine le_of_mul_le_mul_right ?_ hwnorm
      simpa [mul_assoc, pow_two] using hraw'
    have hfrac : ‖w‖ ≤ eta / (g - eta) := (le_div_iff₀ hgw).2 (by
      simpa [mul_comm] using hcancel)
    have hfrac2 : eta / (g - eta) ≤ 2 * eta / g := by
      apply (div_le_div_iff₀ hgw hg).2
      nlinarith
    exact hfrac.trans hfrac2


lemma unit_distance_le_sqrtTwo_residual
    (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hc : 0 ≤ inner ℝ u v) :
    let c := inner ℝ u v
    let w := v - c • u
    ‖u - v‖ ≤ Real.sqrt 2 * ‖w‖ := by
  dsimp
  let c : ℝ := inner ℝ u v
  let w : E := v - c • u
  have hc_le : c ≤ 1 := by
    have h := abs_real_inner_le_norm u v
    rw [hu, hv, mul_one] at h
    exact (le_abs_self c).trans h
  have hw_sq : ‖w‖ ^ 2 = 1 - c ^ 2 := by
    change ‖v - c • u‖ ^ 2 = 1 - c ^ 2
    rw [norm_sub_sq_real, hv, norm_smul, hu]
    simp only [one_pow, mul_one]
    have hiv : inner ℝ v u = c := by simpa [c, real_inner_comm]
    rw [real_inner_smul_right, hiv]
    rw [Real.norm_eq_abs, sq_abs]
    ring
  have hdist_sq : ‖u - v‖ ^ 2 = 2 - 2 * c := by
    rw [norm_sub_sq_real, hu, hv]
    simp [c]
    ring
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), hdist_sq, hw_sq]
  nlinarith

open MeasureTheory
open UEOT.V3.TotalVariation

lemma pmf_tv_eq_half_sum_abs
    {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (p q : PMF ι) :
    tvDist p.toMeasure q.toMeasure =
      (1 / 2 : ℝ) * ∑ i, |(p i).toReal - (q i).toReal| := by
  rw [UEOT.V3.PathError.tvDist_eq_one_sub_pmfCommonMass]
  have hp_sum : (∑ i, (p i).toReal) = 1 := by
    have h := congrArg ENNReal.toReal (PMF.tsum_coe p)
    rw [tsum_fintype, ENNReal.toReal_sum (fun x _ => PMF.apply_ne_top p x)] at h
    simpa using h
  have hq_sum : (∑ i, (q i).toReal) = 1 := by
    have h := congrArg ENNReal.toReal (PMF.tsum_coe q)
    rw [tsum_fintype, ENNReal.toReal_sum (fun x _ => PMF.apply_ne_top q x)] at h
    simpa using h
  have habs :
      (∑ i, |(p i).toReal - (q i).toReal|) =
        2 * (1 - UEOT.V3.PathError.pmfCommonMass p q) := by
    rw [show (∑ i, |(p i).toReal - (q i).toReal|) =
        ∑ i, ((p i).toReal + (q i).toReal - 2 * min (p i).toReal (q i).toReal) by
      apply Finset.sum_congr rfl
      intro i _
      have hp : 0 ≤ (p i).toReal := ENNReal.toReal_nonneg
      have hq : 0 ≤ (q i).toReal := ENNReal.toReal_nonneg
      by_cases hle : (p i).toReal ≤ (q i).toReal
      · rw [min_eq_left hle, abs_of_nonpos (sub_nonpos.mpr hle)]
        ring
      · have hge : (q i).toReal ≤ (p i).toReal := le_of_not_ge hle
        rw [min_eq_right hge, abs_of_nonneg (sub_nonneg.mpr hge)]
        ring]
    unfold UEOT.V3.PathError.pmfCommonMass
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hp_sum, hq_sum]
    ring
  rw [habs]
  ring

variable {ι : Type*} [Fintype ι]

noncomputable def squarePMF (u : EuclideanSpace ℝ ι) (hu : ‖u‖ = 1) : PMF ι :=
  UEOT.V3.FiniteDiscountedControl.FiniteProbabilityRow.ofRealRow
    (fun i => (u i) ^ 2) (fun i => sq_nonneg (u i)) (by
      rw [← EuclideanSpace.real_norm_sq_eq u, hu]
      norm_num)

@[simp] lemma squarePMF_toReal (u : EuclideanSpace ℝ ι) (hu : ‖u‖ = 1) (i : ι) :
    ((squarePMF u hu) i).toReal = (u i) ^ 2 := by
  exact UEOT.V3.FiniteDiscountedControl.FiniteProbabilityRow.ofRealRow_apply_toReal _ _ _ _

lemma squareLaw_tv_eq_half_sum_abs
    (u v : EuclideanSpace ℝ ι) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    letI : MeasurableSpace ι := ⊤
    tvDist (squarePMF u hu).toMeasure (squarePMF v hv).toMeasure =
      (1 / 2 : ℝ) * ∑ i, |(u i) ^ 2 - (v i) ^ 2| := by
  letI : MeasurableSpace ι := ⊤
  rw [pmf_tv_eq_half_sum_abs]
  simp only [squarePMF_toReal]

lemma half_sum_abs_sq_sub_le_norm_sub
    (u v : EuclideanSpace ℝ ι) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    (1 / 2 : ℝ) * ∑ i, |(u i) ^ 2 - (v i) ^ 2| ≤ ‖u - v‖ := by
  have hpoint : ∀ i, |(u i) ^ 2 - (v i) ^ 2| = |u i - v i| * |u i + v i| := by
    intro i
    rw [show (u i) ^ 2 - (v i) ^ 2 = (u i - v i) * (u i + v i) by ring, abs_mul]
  simp_rw [hpoint]
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset ι)
    (fun i => |u i - v i|) (fun i => |u i + v i|)
  simp only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte] at hcs
  have hminus : Real.sqrt (∑ i, |u i - v i| ^ 2) = ‖u - v‖ := by
    rw [EuclideanSpace.norm_eq]
    congr 1
  have hplus : Real.sqrt (∑ i, |u i + v i| ^ 2) = ‖u + v‖ := by
    rw [EuclideanSpace.norm_eq]
    congr 1
  rw [hminus, hplus] at hcs
  have hplus_le : ‖u + v‖ ≤ 2 := by
    calc
      ‖u + v‖ ≤ ‖u‖ + ‖v‖ := norm_add_le _ _
      _ = 2 := by rw [hu, hv]; norm_num
  have hprod : (∑ i, |u i - v i| * |u i + v i|) ≤ 2 * ‖u - v‖ := by
    calc
      _ ≤ ‖u - v‖ * ‖u + v‖ := hcs
      _ ≤ ‖u - v‖ * 2 := by gcongr
      _ = 2 * ‖u - v‖ := by ring
  nlinarith

lemma squareLaw_tv_le_norm_sub
    (u v : EuclideanSpace ℝ ι) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    letI : MeasurableSpace ι := ⊤
    tvDist (squarePMF u hu).toMeasure (squarePMF v hv).toMeasure ≤ ‖u - v‖ := by
  letI : MeasurableSpace ι := ⊤
  rw [squareLaw_tv_eq_half_sum_abs u v hu hv]
  exact half_sum_abs_sq_sub_le_norm_sub u v hu hv

lemma euclidean_inner_nonneg_of_coords_nonneg
    (u v : EuclideanSpace ℝ ι)
    (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i) :
    0 ≤ inner ℝ u v := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [RCLike.star_def, starRingEnd_apply, star_id_of_comm]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hv i) (hu i)

lemma spectral_squareLaw_stability
    (A B : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    (u v : EuclideanSpace ℝ ι)
    (rho sigma lambda2 g eta : ℝ)
    (hu : PrincipalGap A u rho lambda2)
    (hv : PrincipalEigenpair B v sigma)
    (hu_nonneg : ∀ i, 0 ≤ u i) (hv_nonneg : ∀ i, 0 ≤ v i)
    (hgap : g = rho - lambda2) (hg : 0 < g)
    (hAB : ‖B - A‖ ≤ eta) (heta : eta < g / 2) :
    |sigma - rho| ≤ eta ∧
      letI : MeasurableSpace ι := ⊤
      tvDist (squarePMF u hu.unit).toMeasure (squarePMF v hv.unit).toMeasure ≤
        2 * Real.sqrt 2 * eta / g := by
  have heig := principal_eigenvalue_perturbation A B u v rho sigma eta
    hu.toPrincipalEigenpair hv hAB
  refine ⟨heig, ?_⟩
  letI : MeasurableSpace ι := ⊤
  let c : ℝ := inner ℝ u v
  let w : EuclideanSpace ℝ ι := v - c • u
  have hw : ‖w‖ ≤ 2 * eta / g := by
    simpa [c, w] using
      (orthogonal_residual_bound A B u v rho sigma lambda2 g eta hu hv hgap hg hAB heta)
  have hc : 0 ≤ inner ℝ u v :=
    euclidean_inner_nonneg_of_coords_nonneg u v hu_nonneg hv_nonneg
  have hd : ‖u - v‖ ≤ Real.sqrt 2 * ‖w‖ := by
    simpa [c, w] using unit_distance_le_sqrtTwo_residual u v hu.unit hv.unit hc
  have htv := squareLaw_tv_le_norm_sub u v hu.unit hv.unit
  calc
    tvDist (squarePMF u hu.unit).toMeasure (squarePMF v hv.unit).toMeasure
        ≤ ‖u - v‖ := htv
    _ ≤ Real.sqrt 2 * ‖w‖ := hd
    _ ≤ Real.sqrt 2 * (2 * eta / g) := by
      gcongr
    _ = 2 * Real.sqrt 2 * eta / g := by ring

structure SymmetricKilledKernel (ι : Type*) [Fintype ι] where
  matrix : Matrix ι ι ℝ
  symmetric : matrix.IsSymm
  nonneg : ∀ i j, 0 ≤ matrix i j
  irreducible : matrix.IsIrreducible
  substochastic : ∀ i, ∑ j, matrix i j ≤ 1

namespace SymmetricKilledKernel

variable [DecidableEq ι]

noncomputable def operator (K : SymmetricKilledKernel ι) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) K.matrix

lemma operator_isSymmetric (K : SymmetricKilledKernel ι) :
    (K.operator : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι).IsSymmetric := by
  change (Matrix.toEuclideanLin K.matrix).IsSymmetric
  exact Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((Matrix.isHermitian_iff_isSymm).2 K.symmetric)

lemma perturbation_symmetric (K L : SymmetricKilledKernel ι) :
    (K.matrix - L.matrix).IsSymm :=
  K.symmetric.sub L.symmetric

lemma operator_sub (K L : SymmetricKilledKernel ι) :
    K.operator - L.operator = Matrix.toEuclideanCLM (𝕜 := ℝ) (K.matrix - L.matrix) := by
  simp [operator]

lemma norm_operator_sub (K L : SymmetricKilledKernel ι) :
    ‖K.operator - L.operator‖ = ‖K.matrix - L.matrix‖ := by
  rw [operator_sub, Matrix.l2_opNorm_toEuclideanCLM]

end SymmetricKilledKernel

/-- Source-facing P-GOA-04, with `lambda2` encoded through its exact Rayleigh
variational property on the orthogonal complement of the positive principal
vector. The matrix norm is Mathlib's genuine Euclidean L2 operator norm. -/
theorem p_goa_04
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K Khat : SymmetricKilledKernel ι)
    (u uhat : EuclideanSpace ℝ ι)
    (rho rhohat lambda2 g eta : ℝ)
    (hu : PrincipalGap K.operator u rho lambda2)
    (huhat : PrincipalEigenpair Khat.operator uhat rhohat)
    (hu_pos : ∀ i, 0 < u i) (huhat_pos : ∀ i, 0 < uhat i)
    (hgap : g = rho - lambda2) (hg : 0 < g)
    (hpert : ‖Khat.matrix - K.matrix‖ ≤ eta)
    (heta : eta < g / 2) :
    |rhohat - rho| ≤ eta ∧
      letI : MeasurableSpace ι := ⊤
      tvDist (squarePMF u hu.unit).toMeasure (squarePMF uhat huhat.unit).toMeasure ≤
        2 * Real.sqrt 2 * eta / g := by
  have hop : ‖Khat.operator - K.operator‖ ≤ eta := by
    rw [SymmetricKilledKernel.norm_operator_sub]
    exact hpert
  exact spectral_squareLaw_stability K.operator Khat.operator u uhat
    rho rhohat lambda2 g eta hu huhat
    (fun i => (hu_pos i).le) (fun i => (huhat_pos i).le)
    hgap hg hop heta

end

end UEOT.V3.SymmetricKilledSpectralStability
