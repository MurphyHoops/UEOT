import UEOT.V3.FiniteDobrushin
import UEOT.V3.PathError
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# P-GOA-03 — recurrent-decomposition stability, algebraic layer

This file develops the matrix perturbation half of frozen UEOT Core v3 §21.4.
The source norm is the maximum absolute row-sum norm.  Mathlib's scoped
`Matrix.Norms.Operator` instance is exactly that norm:

`‖A‖∞ = max_i ∑_j |A i j|`.

For a transient block `Q`, a two-sided fundamental matrix `N = (I-Q)⁻¹`, and a
perturbed block `Qhat`, the source smallness condition `‖N‖∞ * epsQ < 1`
produces the perturbed inverse through a Neumann series and yields the exact
resolvent constants used in P-GOA-03.  For a direct-entry matrix `R` whose rows
are subprobabilities, this gives the exact source absorption-matrix bound for
`H = N R`.

The recurrent-class/Cesàro-mixture layer is added separately below this
algebraic core; no change of recurrent support is hidden in the perturbation
argument.
-/

namespace UEOT.V3.FiniteRecurrentDecompositionStability

noncomputable section

open scoped BigOperators Matrix.Norms.Operator

universe uT uC uS

variable {T : Type uT} [Fintype T] [DecidableEq T] [Nonempty T]

open MeasureTheory

/-- Probability mixture over a finite family of recurrent-class laws.  In the
finite recurrent decomposition this is the Cesàro limit obtained by weighting
each class law by the corresponding absorption probability. -/
noncomputable def recurrentMixture
    {C : Type uC} {S : Type uS} [Fintype C] [Fintype S]
    (w : stdSimplex ℝ C) (pi : C → stdSimplex ℝ S) : stdSimplex ℝ S := by
  refine ⟨fun s => ∑ j, w.1 j * (pi j).1 s, ?_, ?_⟩
  · intro s
    exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (stdSimplex.zero_le w j) (stdSimplex.zero_le (pi j) s)
  · rw [Finset.sum_comm]
    calc
      (∑ j, ∑ s, w.1 j * (pi j).1 s) =
          ∑ j, w.1 j * ∑ s, (pi j).1 s := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
      _ = ∑ j, w.1 j := by
        apply Finset.sum_congr rfl
        intro j _
        have hpi : (∑ s, (pi j).1 s) = 1 := stdSimplex.sum_eq_one (pi j)
        rw [hpi, mul_one]
      _ = 1 := stdSimplex.sum_eq_one w

@[simp] lemma recurrentMixture_apply
    {C : Type uC} {S : Type uS} [Fintype C] [Fintype S]
    (w : stdSimplex ℝ C) (pi : C → stdSimplex ℝ S) (s : S) :
    (recurrentMixture w pi).1 s = ∑ j, w.1 j * (pi j).1 s := rfl

/-- Finite PMF total variation is one half of the coordinatewise `L1` distance.
This local generic bridge avoids making P-GOA-03 depend on the later P-GOA-04
spectral-stability module merely for the same elementary finite identity. -/
lemma pmf_tv_eq_half_sum_abs
    {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (p q : PMF ι) :
    UEOT.V3.TotalVariation.tvDist p.toMeasure q.toMeasure =
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

/-- The canonical UEOT finite-law TV normalization used by P-GOA-02 is exactly
one half of coordinate `L1`. -/
lemma lawTV_eq_half_sum_abs
    {S : Type uS} [Fintype S]
    (mu nu : stdSimplex ℝ S) :
    UEOT.V3.FiniteDobrushin.lawTV mu nu =
      (1 / 2 : ℝ) * ∑ s, |mu.1 s - nu.1 s| := by
  classical
  letI : MeasurableSpace S := ⊤
  unfold UEOT.V3.FiniteDobrushin.lawTV
  change UEOT.V3.TotalVariation.tvDist
      (UEOT.V3.FiniteDobrushin.simplexPMF mu).toMeasure
      (UEOT.V3.FiniteDobrushin.simplexPMF nu).toMeasure = _
  rw [pmf_tv_eq_half_sum_abs]
  simp only [UEOT.V3.FiniteDobrushin.simplexPMF_toReal]

/-- Every individual row `L1` norm is bounded by Mathlib's exact matrix
maximum absolute row-sum norm. -/
lemma row_l1_le_linfty_opNorm
    {m : Type*} {n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (i : m) :
    ∑ j, |A i j| ≤ ‖A‖ := by
  rw [Matrix.linfty_opNorm_def]
  have hnn :
      (∑ j : n, ‖A i j‖₊) ≤
        (Finset.univ : Finset m).sup (fun k : m => ∑ j : n, ‖A k j‖₊) :=
    Finset.le_sup (f := fun k : m => ∑ j : n, ‖A k j‖₊) (Finset.mem_univ i)
  have hcoe := NNReal.coe_le_coe.mpr hnn
  simpa [NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs] using hcoe

/-- Changing only recurrent-class absorption weights changes the induced
mixture by at most the `L1` change of those weights. -/
lemma recurrentMixture_weight_l1_le
    {C : Type uC} {S : Type uS} [Fintype C] [Fintype S]
    (w what : stdSimplex ℝ C) (pi : C → stdSimplex ℝ S) :
    (∑ s, |(recurrentMixture w pi).1 s - (recurrentMixture what pi).1 s|) ≤
      ∑ j, |w.1 j - what.1 j| := by
  classical
  have hpoint (s : S) :
      (recurrentMixture w pi).1 s - (recurrentMixture what pi).1 s =
        ∑ j, (w.1 j - what.1 j) * (pi j).1 s := by
    rw [recurrentMixture_apply, recurrentMixture_apply, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hpoint]
  calc
    (∑ s, |∑ j, (w.1 j - what.1 j) * (pi j).1 s|) ≤
        ∑ s, ∑ j, |(w.1 j - what.1 j) * (pi j).1 s| := by
      apply Finset.sum_le_sum
      intro s _
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, ∑ s, |(w.1 j - what.1 j) * (pi j).1 s| :=
      Finset.sum_comm
    _ = ∑ j, |w.1 j - what.1 j| := by
      apply Finset.sum_congr rfl
      intro j _
      calc
        (∑ s, |(w.1 j - what.1 j) * (pi j).1 s|) =
            ∑ s, |w.1 j - what.1 j| * (pi j).1 s := by
          apply Finset.sum_congr rfl
          intro s _
          have hs : 0 ≤ (pi j).1 s := stdSimplex.zero_le (pi j) s
          rw [abs_mul, abs_of_nonneg hs]
        _ = |w.1 j - what.1 j| * ∑ s, (pi j).1 s := by
          rw [Finset.mul_sum]
        _ = |w.1 j - what.1 j| := by
          have hsum : (∑ s, (pi j).1 s) = 1 := stdSimplex.sum_eq_one (pi j)
          rw [hsum, mul_one]

/-- With fixed recurrent-class weights, classwise TV errors average with those
weights. -/
lemma recurrentMixture_class_l1_le
    {C : Type uC} {S : Type uS} [Fintype C] [Fintype S]
    (w : stdSimplex ℝ C) (pi pihat : C → stdSimplex ℝ S) :
    (∑ s, |(recurrentMixture w pi).1 s - (recurrentMixture w pihat).1 s|) ≤
      ∑ j, w.1 j * ∑ s, |(pi j).1 s - (pihat j).1 s| := by
  classical
  have hpoint (s : S) :
      (recurrentMixture w pi).1 s - (recurrentMixture w pihat).1 s =
        ∑ j, w.1 j * ((pi j).1 s - (pihat j).1 s) := by
    rw [recurrentMixture_apply, recurrentMixture_apply, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hpoint]
  calc
    (∑ s, |∑ j, w.1 j * ((pi j).1 s - (pihat j).1 s)|) ≤
        ∑ s, ∑ j, |w.1 j * ((pi j).1 s - (pihat j).1 s)| := by
      apply Finset.sum_le_sum
      intro s _
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, ∑ s, |w.1 j * ((pi j).1 s - (pihat j).1 s)| :=
      Finset.sum_comm
    _ = ∑ j, w.1 j * ∑ s, |(pi j).1 s - (pihat j).1 s| := by
      apply Finset.sum_congr rfl
      intro j _
      calc
        (∑ s, |w.1 j * ((pi j).1 s - (pihat j).1 s)|) =
            ∑ s, w.1 j * |(pi j).1 s - (pihat j).1 s| := by
          apply Finset.sum_congr rfl
          intro s _
          have hw : 0 ≤ w.1 j := stdSimplex.zero_le w j
          rw [abs_mul, abs_of_nonneg hw]
        _ = w.1 j * ∑ s, |(pi j).1 s - (pihat j).1 s| := by
          rw [Finset.mul_sum]

/-- Source mixture-triangle estimate before substituting the matrix absorption
bound.  The coefficient `1/2` is the canonical finite-TV normalization. -/
lemma recurrentMixture_tv_le
    {C : Type uC} {S : Type uS} [Fintype C] [Fintype S]
    (w what : stdSimplex ℝ C)
    (pi pihat : C → stdSimplex ℝ S)
    (epsStat : C → ℝ)
    (hstat : ∀ j, UEOT.V3.FiniteDobrushin.lawTV (pi j) (pihat j) ≤ epsStat j) :
    UEOT.V3.FiniteDobrushin.lawTV
        (recurrentMixture w pi) (recurrentMixture what pihat) ≤
      (1 / 2 : ℝ) * (∑ j, |w.1 j - what.1 j|) +
        ∑ j, what.1 j * epsStat j := by
  classical
  have htri := UEOT.V3.FiniteDobrushin.lawTV_triangle
    (recurrentMixture w pi) (recurrentMixture what pi) (recurrentMixture what pihat)
  have hweight :
      UEOT.V3.FiniteDobrushin.lawTV
          (recurrentMixture w pi) (recurrentMixture what pi) ≤
        (1 / 2 : ℝ) * ∑ j, |w.1 j - what.1 j| := by
    rw [lawTV_eq_half_sum_abs]
    exact mul_le_mul_of_nonneg_left (recurrentMixture_weight_l1_le w what pi) (by norm_num)
  have hclass :
      UEOT.V3.FiniteDobrushin.lawTV
          (recurrentMixture what pi) (recurrentMixture what pihat) ≤
        ∑ j, what.1 j * epsStat j := by
    rw [lawTV_eq_half_sum_abs]
    calc
      (1 / 2 : ℝ) *
          (∑ s, |(recurrentMixture what pi).1 s -
            (recurrentMixture what pihat).1 s|) ≤
          (1 / 2 : ℝ) *
            (∑ j, what.1 j * ∑ s, |(pi j).1 s - (pihat j).1 s|) :=
        mul_le_mul_of_nonneg_left (recurrentMixture_class_l1_le what pi pihat) (by norm_num)
      _ = ∑ j, what.1 j *
          ((1 / 2 : ℝ) * ∑ s, |(pi j).1 s - (pihat j).1 s|) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = ∑ j, what.1 j *
          UEOT.V3.FiniteDobrushin.lawTV (pi j) (pihat j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [lawTV_eq_half_sum_abs]
      _ ≤ ∑ j, what.1 j * epsStat j := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (hstat j) (stdSimplex.zero_le what j)
  linarith

/-- Neumann-series bound in the exact maximum absolute row-sum matrix norm. -/
lemma norm_inverse_one_sub_le (E : Matrix T T ℝ) (hE : ‖E‖ < 1) :
    ‖Ring.inverse (1 - E)‖ ≤ (1 - ‖E‖)⁻¹ := by
  rw [NormedRing.inverse_one_sub E hE]
  change ‖∑' k : ℕ, E ^ k‖ ≤ (1 - ‖E‖)⁻¹
  have hsE : Summable (fun k : ℕ => ‖E ^ k‖) := by
    apply Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => norm_pow_le E k)
    exact summable_geometric_of_lt_one (norm_nonneg E) hE
  calc
    ‖∑' k : ℕ, E ^ k‖ ≤ ∑' k : ℕ, ‖E ^ k‖ := norm_tsum_le_tsum_norm hsE
    _ ≤ ∑' k : ℕ, ‖E‖ ^ k := by
      exact Summable.tsum_le_tsum (fun k => norm_pow_le E k) hsE
        (summable_geometric_of_lt_one (norm_nonneg E) hE)
    _ = (1 - ‖E‖)⁻¹ := by
      have hgeom := tsum_geometric_of_norm_lt_one (ξ := ‖E‖) (by
        simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg E)] using hE)
      simpa using hgeom

/-- Exact resolvent perturbation estimate used in frozen §21.4.

`hNl` and `hNr` express the source identity `N = (I-Q)⁻¹` without choosing a
separate matrix-inverse convention.  The returned matrix is a two-sided inverse
of `I-Qhat` and satisfies both source Neumann bounds. -/
lemma perturbed_resolvent
    (Q Qhat N : Matrix T T ℝ) (epsQ : ℝ)
    (hNl : N * (1 - Q) = 1) (hNr : (1 - Q) * N = 1)
    (hQ : ‖Qhat - Q‖ ≤ epsQ)
    (hsmall : ‖N‖ * epsQ < 1) :
    let D := Qhat - Q
    let E := N * D
    let G := Ring.inverse (1 - E)
    let Nhat := G * N
    ((1 - Qhat) * Nhat = 1 ∧ Nhat * (1 - Qhat) = 1) ∧
      ‖Nhat‖ ≤ ‖N‖ / (1 - ‖N‖ * epsQ) ∧
      ‖Nhat - N‖ ≤ ‖N‖ ^ 2 * epsQ / (1 - ‖N‖ * epsQ) := by
  dsimp only
  let D : Matrix T T ℝ := Qhat - Q
  let E : Matrix T T ℝ := N * D
  let G : Matrix T T ℝ := Ring.inverse (1 - E)
  let Nhat : Matrix T T ℝ := G * N
  have hE_le : ‖E‖ ≤ ‖N‖ * epsQ := by
    calc
      ‖E‖ = ‖N * D‖ := rfl
      _ ≤ ‖N‖ * ‖D‖ := Matrix.linfty_opNorm_mul N D
      _ ≤ ‖N‖ * epsQ :=
        mul_le_mul_of_nonneg_left (by simpa [D] using hQ) (norm_nonneg N)
  have hE : ‖E‖ < 1 := hE_le.trans_lt hsmall
  have hunit : IsUnit (1 - E) := isUnit_one_sub_of_norm_lt_one hE
  have hGleft : G * (1 - E) = 1 := by
    exact Ring.inverse_mul_cancel (1 - E) hunit
  have hGright : (1 - E) * G = 1 := by
    exact Ring.mul_inverse_cancel (1 - E) hunit
  have hfactor : 1 - Qhat = (1 - Q) * (1 - E) := by
    dsimp [E, D]
    calc
      1 - Qhat = (1 - Q) - (Qhat - Q) := by abel
      _ = (1 - Q) - ((1 - Q) * N) * (Qhat - Q) := by rw [hNr, one_mul]
      _ = (1 - Q) * (1 - N * (Qhat - Q)) := by noncomm_ring
  have hleft : (1 - Qhat) * Nhat = 1 := by
    rw [hfactor]
    dsimp [Nhat]
    calc
      ((1 - Q) * (1 - E)) * (G * N) =
          (1 - Q) * ((1 - E) * G) * N := by noncomm_ring
      _ = (1 - Q) * N := by rw [hGright, mul_one]
      _ = 1 := hNr
  have hright : Nhat * (1 - Qhat) = 1 := by
    rw [hfactor]
    dsimp [Nhat]
    calc
      (G * N) * ((1 - Q) * (1 - E)) =
          G * (N * (1 - Q)) * (1 - E) := by noncomm_ring
      _ = G * (1 - E) := by rw [hNl, mul_one]
      _ = 1 := hGleft
  have hden : 0 < 1 - ‖N‖ * epsQ := sub_pos.mpr hsmall
  have hG : ‖G‖ ≤ (1 - ‖N‖ * epsQ)⁻¹ := by
    calc
      ‖G‖ ≤ (1 - ‖E‖)⁻¹ := norm_inverse_one_sub_le E hE
      _ ≤ (1 - ‖N‖ * epsQ)⁻¹ := by
        rw [inv_le_inv₀ (sub_pos.mpr hE) hden]
        linarith [hE_le]
  have hNhat : ‖Nhat‖ ≤ ‖N‖ / (1 - ‖N‖ * epsQ) := by
    calc
      ‖Nhat‖ = ‖G * N‖ := rfl
      _ ≤ ‖G‖ * ‖N‖ := Matrix.linfty_opNorm_mul G N
      _ ≤ (1 - ‖N‖ * epsQ)⁻¹ * ‖N‖ :=
        mul_le_mul_of_nonneg_right hG (norm_nonneg N)
      _ = ‖N‖ / (1 - ‖N‖ * epsQ) := by rw [div_eq_mul_inv]; ring
  have hGsub : G - 1 = G * E := by
    have h : G - G * E = 1 := by
      simpa [mul_sub] using hGleft
    calc
      G - 1 = G - (G - G * E) := by rw [h]
      _ = G * E := by abel
  have hdiff : Nhat - N = (G * E) * N := by
    dsimp [Nhat]
    rw [← hGsub]
    noncomm_ring
  have hNdiff : ‖Nhat - N‖ ≤ ‖N‖ ^ 2 * epsQ / (1 - ‖N‖ * epsQ) := by
    rw [hdiff]
    calc
      ‖(G * E) * N‖ ≤ ‖G * E‖ * ‖N‖ := Matrix.linfty_opNorm_mul (G * E) N
      _ ≤ (‖G‖ * ‖E‖) * ‖N‖ := by
        gcongr
        exact Matrix.linfty_opNorm_mul G E
      _ ≤ ((1 - ‖N‖ * epsQ)⁻¹ * (‖N‖ * epsQ)) * ‖N‖ := by gcongr
      _ = ‖N‖ ^ 2 * epsQ / (1 - ‖N‖ * epsQ) := by
        rw [div_eq_mul_inv]
        ring
  have hout :
      ((1 - Qhat) * Nhat = 1 ∧ Nhat * (1 - Qhat) = 1) ∧
        ‖Nhat‖ ≤ ‖N‖ / (1 - ‖N‖ * epsQ) ∧
        ‖Nhat - N‖ ≤ ‖N‖ ^ 2 * epsQ / (1 - ‖N‖ * epsQ) :=
    ⟨⟨hleft, hright⟩, hNhat, hNdiff⟩
  simpa [D, E, G, Nhat] using hout

/-- A nonnegative direct-entry matrix with subprobability rows has source
maximum absolute row-sum norm at most one. -/
lemma linfty_norm_le_one_of_nonneg_rowSum_le_one
    {m : Type*} {C : Type uC} [Fintype m] [Fintype C]
    (R : Matrix m C ℝ)
    (hnonneg : ∀ i j, 0 ≤ R i j)
    (hrows : ∀ i, ∑ j, R i j ≤ 1) :
    ‖R‖ ≤ 1 := by
  rw [Matrix.linfty_opNorm_def]
  norm_cast
  apply Finset.sup_le
  intro i _hi
  apply NNReal.coe_le_coe.mp
  simpa [NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs,
    abs_of_nonneg (hnonneg i _)] using hrows i

/-- Frozen §21.4 absorption-matrix perturbation bound.

Here `R` is the direct-entry probability matrix into the recurrent classes,
`H = N R`, and the Neumann construction supplies the perturbed fundamental
matrix and `Hhat`.  The conclusion has exactly the source numerator and
denominator. -/
lemma absorption_matrix_bound
    {C : Type uC} [Fintype C]
    (Q Qhat N : Matrix T T ℝ)
    (R Rhat : Matrix T C ℝ)
    (epsQ epsR : ℝ)
    (hNl : N * (1 - Q) = 1) (hNr : (1 - Q) * N = 1)
    (hQ : ‖Qhat - Q‖ ≤ epsQ)
    (hR : ‖Rhat - R‖ ≤ epsR)
    (hRnonneg : ∀ i j, 0 ≤ R i j)
    (hRrows : ∀ i, ∑ j, R i j ≤ 1)
    (hsmall : ‖N‖ * epsQ < 1) :
    let D := Qhat - Q
    let E := N * D
    let G := Ring.inverse (1 - E)
    let Nhat := G * N
    let H := N * R
    let Hhat := Nhat * Rhat
    ‖Hhat - H‖ ≤
      (‖N‖ ^ 2 * epsQ + ‖N‖ * epsR) / (1 - ‖N‖ * epsQ) := by
  dsimp only
  let D : Matrix T T ℝ := Qhat - Q
  let E : Matrix T T ℝ := N * D
  let G : Matrix T T ℝ := Ring.inverse (1 - E)
  let Nhat : Matrix T T ℝ := G * N
  let H : Matrix T C ℝ := N * R
  let Hhat : Matrix T C ℝ := Nhat * Rhat
  have hres := perturbed_resolvent Q Qhat N epsQ hNl hNr hQ hsmall
  change ((1 - Qhat) * (Ring.inverse (1 - N * (Qhat - Q)) * N) = 1 ∧
      (Ring.inverse (1 - N * (Qhat - Q)) * N) * (1 - Qhat) = 1) ∧
      ‖Ring.inverse (1 - N * (Qhat - Q)) * N‖ ≤ ‖N‖ / (1 - ‖N‖ * epsQ) ∧
      ‖Ring.inverse (1 - N * (Qhat - Q)) * N - N‖ ≤
        ‖N‖ ^ 2 * epsQ / (1 - ‖N‖ * epsQ) at hres
  have hNhat := hres.2.1
  have hNdiff := hres.2.2
  have hRn : ‖R‖ ≤ 1 :=
    linfty_norm_le_one_of_nonneg_rowSum_le_one R hRnonneg hRrows
  have hepsQ : 0 ≤ epsQ := (norm_nonneg (Qhat - Q)).trans hQ
  have hepsR : 0 ≤ epsR := (norm_nonneg (Rhat - R)).trans hR
  have hden : 0 < 1 - ‖N‖ * epsQ := sub_pos.mpr hsmall
  have hid : Hhat - H = (Nhat - N) * R + Nhat * (Rhat - R) := by
    dsimp [Hhat, H]
    rw [Matrix.sub_mul, Matrix.mul_sub]
    abel
  have hfirst_nonneg : 0 ≤ ‖N‖ ^ 2 * epsQ / (1 - ‖N‖ * epsQ) :=
    div_nonneg (mul_nonneg (sq_nonneg _) hepsQ) hden.le
  rw [hid]
  calc
    ‖(Nhat - N) * R + Nhat * (Rhat - R)‖
        ≤ ‖(Nhat - N) * R‖ + ‖Nhat * (Rhat - R)‖ := norm_add_le _ _
    _ ≤ (‖Nhat - N‖ * ‖R‖) + (‖Nhat‖ * ‖Rhat - R‖) := by
      gcongr
      · exact Matrix.linfty_opNorm_mul (Nhat - N) R
      · exact Matrix.linfty_opNorm_mul Nhat (Rhat - R)
    _ ≤ (‖N‖ ^ 2 * epsQ / (1 - ‖N‖ * epsQ)) * 1 +
        (‖N‖ / (1 - ‖N‖ * epsQ)) * epsR := by gcongr
    _ = (‖N‖ ^ 2 * epsQ + ‖N‖ * epsR) / (1 - ‖N‖ * epsQ) := by
      field_simp [ne_of_gt hden]

/-- The Neumann-constructed perturbed inverse is the unique inverse already
present in a valid perturbed recurrent decomposition. -/
lemma perturbed_resolvent_eq_existing
    (Q Qhat N Nhat : Matrix T T ℝ) (epsQ : ℝ)
    (hNl : N * (1 - Q) = 1) (hNr : (1 - Q) * N = 1)
    (hNhatl : Nhat * (1 - Qhat) = 1)
    (hQ : ‖Qhat - Q‖ ≤ epsQ)
    (hsmall : ‖N‖ * epsQ < 1) :
    Nhat = Ring.inverse (1 - N * (Qhat - Q)) * N := by
  have hres := perturbed_resolvent Q Qhat N epsQ hNl hNr hQ hsmall
  change
    (((1 - Qhat) * (Ring.inverse (1 - N * (Qhat - Q)) * N) = 1 ∧
        (Ring.inverse (1 - N * (Qhat - Q)) * N) * (1 - Qhat) = 1) ∧
      ‖Ring.inverse (1 - N * (Qhat - Q)) * N‖ ≤ ‖N‖ / (1 - ‖N‖ * epsQ) ∧
      ‖Ring.inverse (1 - N * (Qhat - Q)) * N - N‖ ≤
        ‖N‖ ^ 2 * epsQ / (1 - ‖N‖ * epsQ)) at hres
  let Nstar : Matrix T T ℝ := Ring.inverse (1 - N * (Qhat - Q)) * N
  have hstar : (1 - Qhat) * Nstar = 1 := by
    simpa [Nstar] using hres.1.1
  calc
    Nhat = Nhat * 1 := by rw [mul_one]
    _ = Nhat * ((1 - Qhat) * Nstar) := by rw [hstar]
    _ = (Nhat * (1 - Qhat)) * Nstar := by rw [Matrix.mul_assoc]
    _ = Nstar := by rw [hNhatl, one_mul]
    _ = Ring.inverse (1 - N * (Qhat - Q)) * N := rfl

/-- The frozen absorption-matrix bound for an already specified perturbed
fundamental matrix `Nhat=(I-Qhat)⁻¹`. -/
lemma absorption_matrix_bound_of_inverses
    {C : Type uC} [Fintype C]
    (Q Qhat N Nhat : Matrix T T ℝ)
    (R Rhat : Matrix T C ℝ)
    (epsQ epsR : ℝ)
    (hNl : N * (1 - Q) = 1) (hNr : (1 - Q) * N = 1)
    (hNhatl : Nhat * (1 - Qhat) = 1)
    (hQ : ‖Qhat - Q‖ ≤ epsQ)
    (hR : ‖Rhat - R‖ ≤ epsR)
    (hRnonneg : ∀ i j, 0 ≤ R i j)
    (hRrows : ∀ i, ∑ j, R i j ≤ 1)
    (hsmall : ‖N‖ * epsQ < 1) :
    ‖Nhat * Rhat - N * R‖ ≤
      (‖N‖ ^ 2 * epsQ + ‖N‖ * epsR) / (1 - ‖N‖ * epsQ) := by
  have hNhat :=
    perturbed_resolvent_eq_existing Q Qhat N Nhat epsQ hNl hNr hNhatl hQ hsmall
  rw [hNhat]
  simpa only using
    (absorption_matrix_bound Q Qhat N R Rhat epsQ epsR
      hNl hNr hQ hR hRnonneg hRrows hsmall)

/-- Source-level finite transient/recurrent block decomposition.  The same
transient type `T` and recurrent-class index type `C` are shared by baseline and
perturbed data in P-GOA-03.  `block_row_sum` is the statement that a transient
row either remains transient through `Q` or enters one recurrent class through
`R`; `fundamental_nonneg` records the standard nonnegativity of the transient
fundamental matrix. -/
structure RecurrentBlockDecomposition
    (T : Type uT) (C : Type uC) [Fintype T] [DecidableEq T] [Fintype C] where
  Q : Matrix T T ℝ
  R : Matrix T C ℝ
  N : Matrix T T ℝ
  q_nonneg : ∀ i j, 0 ≤ Q i j
  r_nonneg : ∀ i j, 0 ≤ R i j
  block_row_sum : ∀ i, (∑ j, Q i j) + ∑ c, R i c = 1
  fundamental_nonneg : ∀ i j, 0 ≤ N i j
  inverse_left : N * (1 - Q) = 1
  inverse_right : (1 - Q) * N = 1

namespace RecurrentBlockDecomposition

variable {C : Type uC} [Fintype C]

/-- Direct-entry rows are subprobabilities, hence have row-sum norm at most
one.  This is the source fact `‖R‖∞≤1`, derived from the block semantics. -/
lemma direct_row_sum_le_one (D : RecurrentBlockDecomposition T C) (i : T) :
    ∑ c, D.R i c ≤ 1 := by
  have hq : 0 ≤ ∑ j, D.Q i j :=
    Finset.sum_nonneg fun j _ => D.q_nonneg i j
  linarith [D.block_row_sum i]

lemma direct_norm_le_one (D : RecurrentBlockDecomposition T C) : ‖D.R‖ ≤ 1 :=
  linfty_norm_le_one_of_nonneg_rowSum_le_one D.R D.r_nonneg D.direct_row_sum_le_one

/-- The absorption matrix of a valid recurrent decomposition. -/
noncomputable def H (D : RecurrentBlockDecomposition T C) : Matrix T C ℝ :=
  D.N * D.R

lemma H_nonneg (D : RecurrentBlockDecomposition T C) (i : T) (c : C) :
    0 ≤ D.H i c := by
  change 0 ≤ ∑ k, D.N i k * D.R k c
  exact Finset.sum_nonneg fun k _ =>
    mul_nonneg (D.fundamental_nonneg i k) (D.r_nonneg k c)

lemma residual_row_sum (D : RecurrentBlockDecomposition T C) (k : T) :
    ∑ j, ((1 : Matrix T T ℝ) - D.Q) k j = 1 - ∑ j, D.Q k j := by
  simp_rw [Matrix.sub_apply]
  rw [Finset.sum_sub_distrib]
  simp [Matrix.one_apply]

lemma H_row_sum (D : RecurrentBlockDecomposition T C) (i : T) :
    ∑ c, D.H i c = 1 := by
  have hRmass (k : T) : ∑ c, D.R k c = 1 - ∑ j, D.Q k j := by
    linarith [D.block_row_sum k]
  calc
    (∑ c, D.H i c) = ∑ c, ∑ k, D.N i k * D.R k c := rfl
    _ = ∑ k, ∑ c, D.N i k * D.R k c := Finset.sum_comm
    _ = ∑ k, D.N i k * ∑ c, D.R k c := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
    _ = ∑ k, D.N i k * (1 - ∑ j, D.Q k j) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hRmass k]
    _ = ∑ k, D.N i k * ∑ j, ((1 : Matrix T T ℝ) - D.Q) k j := by
      apply Finset.sum_congr rfl
      intro k _
      rw [D.residual_row_sum k]
    _ = ∑ k, ∑ j, D.N i k * ((1 : Matrix T T ℝ) - D.Q) k j := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
    _ = ∑ j, ∑ k, D.N i k * ((1 : Matrix T T ℝ) - D.Q) k j := Finset.sum_comm
    _ = ∑ j, (D.N * ((1 : Matrix T T ℝ) - D.Q)) i j := rfl
    _ = ∑ j, (1 : Matrix T T ℝ) i j := by rw [D.inverse_left]
    _ = 1 := by simp [Matrix.one_apply]

/-- Absorption weights for one transient initial state, derived rather than
assumed from the recurrent block decomposition. -/
noncomputable def absorptionWeights (D : RecurrentBlockDecomposition T C) (i : T) :
    stdSimplex ℝ C :=
  ⟨D.H i, D.H_nonneg i, D.H_row_sum i⟩

@[simp] lemma absorptionWeights_apply
    (D : RecurrentBlockDecomposition T C) (i : T) (c : C) :
    (D.absorptionWeights i).1 c = D.H i c := rfl

end RecurrentBlockDecomposition

/-- Unit recurrent-class weight used when the common initial state already lies
inside a recurrent class. -/
noncomputable def recurrentClassVertex
    {C : Type uC} [Fintype C] (c : C) : stdSimplex ℝ C := by
  classical
  exact ⟨Pi.single c 1, single_mem_stdSimplex ℝ c⟩

/-- Absorption weights induced by an arbitrary common initial state.  A
transient start uses the corresponding row of `H`; a start already in recurrent
class `c` has the unchanged unit weight on `c`. -/
noncomputable def initialAbsorptionWeights
    {C : Type uC} [Fintype C]
    (D : RecurrentBlockDecomposition T C) (x0 : T ⊕ C) : stdSimplex ℝ C :=
  match x0 with
  | Sum.inl i => D.absorptionWeights i
  | Sum.inr c => recurrentClassVertex c

/-- Shared recurrent-class supports.  P-GOA-03 uses one value of this structure
for both the baseline and perturbed class laws, so a perturbation that changes a
recurrent support is not representable by the theorem interface. -/
structure RecurrentClassSupports
    (C : Type uC) (S : Type uS) where
  carrier : C → Set S
  nonempty : ∀ j, (carrier j).Nonempty
  disjoint : ∀ {j k}, j ≠ k → Disjoint (carrier j) (carrier k)

/-- A family of probability laws carried by one fixed family of recurrent
classes.  In P-GOA-03 these are the within-class invariant laws supplied by the
finite recurrent decomposition. -/
structure RecurrentClassLaws
    {C : Type uC} {S : Type uS} [Fintype S]
    (K : RecurrentClassSupports C S) where
  law : C → stdSimplex ℝ S
  supported : ∀ j s, (law j).1 s ≠ 0 → s ∈ K.carrier j

/-- For the same transient initial state, the `L1` change in absorption weights
is bounded by the maximum absolute row-sum norm of the absorption-matrix
perturbation. -/
lemma absorptionWeights_l1_le_norm
    {C : Type uC} [Fintype C]
    (D Dhat : RecurrentBlockDecomposition T C) (i : T) :
    (∑ c, |(D.absorptionWeights i).1 c - (Dhat.absorptionWeights i).1 c|) ≤
      ‖Dhat.H - D.H‖ := by
  have hrow := row_l1_le_linfty_opNorm (Dhat.H - D.H) i
  simpa only [RecurrentBlockDecomposition.absorptionWeights_apply,
    Matrix.sub_apply, abs_sub_comm] using hrow

/-- The same-initial-state absorption-weight `L1` bound.  For a transient start
this is a row of `Hhat-H`; for a recurrent start the two weights coincide. -/
lemma initialAbsorptionWeights_l1_le_norm
    {C : Type uC} [Fintype C]
    (D Dhat : RecurrentBlockDecomposition T C) (x0 : T ⊕ C) :
    (∑ c, |(initialAbsorptionWeights D x0).1 c -
      (initialAbsorptionWeights Dhat x0).1 c|) ≤ ‖Dhat.H - D.H‖ := by
  classical
  cases x0 with
  | inl i =>
      exact absorptionWeights_l1_le_norm D Dhat i
  | inr c =>
      simp [initialAbsorptionWeights, recurrentClassVertex]

/-- **P-GOA-03.** Stability of a finite recurrent decomposition under a
perturbation preserving the same transient set and the same recurrent-class
supports.

The first clause is the exact frozen §21.4 absorption-matrix estimate in the
maximum absolute row-sum norm.  The second clause constructs the two induced
Cesàro-limit mixtures from the same initial transient state and derives the
source TV estimate with the canonical `1/2` coefficient.  Because baseline and
perturbed class laws share one `RecurrentClassSupports`, this theorem does not
apply when recurrent support changes. -/
theorem p_goa_03
    {C : Type uC} {S : Type uS} [Fintype C] [Fintype S]
    (D Dhat : RecurrentBlockDecomposition T C)
    (epsQ epsR : ℝ)
    (hQ : ‖Dhat.Q - D.Q‖ ≤ epsQ)
    (hR : ‖Dhat.R - D.R‖ ≤ epsR)
    (hsmall : ‖D.N‖ * epsQ < 1)
    (x0 : T ⊕ C)
    (K : RecurrentClassSupports C S)
    (pi pihat : RecurrentClassLaws K)
    (epsStat : C → ℝ)
    (hstat : ∀ j,
      UEOT.V3.FiniteDobrushin.lawTV (pi.law j) (pihat.law j) ≤ epsStat j) :
    ‖Dhat.H - D.H‖ ≤
        (‖D.N‖ ^ 2 * epsQ + ‖D.N‖ * epsR) / (1 - ‖D.N‖ * epsQ) ∧
      UEOT.V3.FiniteDobrushin.lawTV
          (recurrentMixture (initialAbsorptionWeights D x0) pi.law)
          (recurrentMixture (initialAbsorptionWeights Dhat x0) pihat.law) ≤
        (1 / 2 : ℝ) *
            ((‖D.N‖ ^ 2 * epsQ + ‖D.N‖ * epsR) / (1 - ‖D.N‖ * epsQ)) +
          ∑ j, (initialAbsorptionWeights Dhat x0).1 j * epsStat j := by
  classical
  have hHraw := absorption_matrix_bound_of_inverses
    D.Q Dhat.Q D.N Dhat.N D.R Dhat.R epsQ epsR
    D.inverse_left D.inverse_right Dhat.inverse_left
    hQ hR D.r_nonneg D.direct_row_sum_le_one hsmall
  have hH :
      ‖Dhat.H - D.H‖ ≤
        (‖D.N‖ ^ 2 * epsQ + ‖D.N‖ * epsR) / (1 - ‖D.N‖ * epsQ) := by
    simpa [RecurrentBlockDecomposition.H] using hHraw
  have hweight := initialAbsorptionWeights_l1_le_norm D Dhat x0
  have hweightBH :
      (∑ j, |(initialAbsorptionWeights D x0).1 j -
        (initialAbsorptionWeights Dhat x0).1 j|) ≤
        (‖D.N‖ ^ 2 * epsQ + ‖D.N‖ * epsR) / (1 - ‖D.N‖ * epsQ) :=
    hweight.trans hH
  have hmix := recurrentMixture_tv_le
    (initialAbsorptionWeights D x0) (initialAbsorptionWeights Dhat x0)
    pi.law pihat.law epsStat hstat
  constructor
  · exact hH
  · calc
      UEOT.V3.FiniteDobrushin.lawTV
          (recurrentMixture (initialAbsorptionWeights D x0) pi.law)
          (recurrentMixture (initialAbsorptionWeights Dhat x0) pihat.law) ≤
        (1 / 2 : ℝ) *
            (∑ j, |(initialAbsorptionWeights D x0).1 j -
              (initialAbsorptionWeights Dhat x0).1 j|) +
          ∑ j, (initialAbsorptionWeights Dhat x0).1 j * epsStat j := hmix
      _ ≤ (1 / 2 : ℝ) *
            ((‖D.N‖ ^ 2 * epsQ + ‖D.N‖ * epsR) / (1 - ‖D.N‖ * epsQ)) +
          ∑ j, (initialAbsorptionWeights Dhat x0).1 j * epsStat j := by
        gcongr

end

end UEOT.V3.FiniteRecurrentDecompositionStability
