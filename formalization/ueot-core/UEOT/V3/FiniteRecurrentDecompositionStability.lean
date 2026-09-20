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

variable {T : Type uT} [Fintype T] [DecidableEq T]

open MeasureTheory Filter Topology

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
lemma norm_inverse_one_sub_le [Nonempty T]
    (E : Matrix T T ℝ) (hE : ‖E‖ < 1) :
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
    [Nonempty T]
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
    [Nonempty T]
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
    [Nonempty T]
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
    [Nonempty T]
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

@[simp] lemma recurrentClassVertex_apply
    {C : Type uC} [Fintype C] [DecidableEq C] (c d : C) :
    (recurrentClassVertex c).1 d = if c = d then 1 else 0 := by
  classical
  by_cases hcd : c = d
  · subst d
    simp [recurrentClassVertex, Pi.single_apply]
  · simp [recurrentClassVertex, Pi.single_apply, hcd]

/-- A fixed recurrent partition of the nontransient state type `R`.  Baseline
and perturbed chains in P-GOA-03 share one value of this structure, so the
transient set and every recurrent-class carrier are literally unchanged. -/
structure RecurrentPartition (R : Type uS) (C : Type uC) where
  classOf : R → C
  class_nonempty : ∀ c, ∃ r, classOf r = c

abbrev FullState (T : Type uT) (R : Type uS) := T ⊕ R

/-- Class mass of a law on the canonical transient/recurrent sum state space. -/
noncomputable def recurrentClassMass
    {R : Type uS} {C : Type uC} [Fintype R] [Fintype C] [DecidableEq C]
    (K : RecurrentPartition R C)
    (mu : stdSimplex ℝ (FullState T R)) (c : C) : ℝ :=
  ∑ r, if K.classOf r = c then mu.1 (Sum.inr r) else 0

/-- Restriction of a full-state law to one recurrent class, kept as a
non-normalized vector. -/
noncomputable def recurrentClassRestriction
    {R : Type uS} {C : Type uC} [Fintype R] [Fintype C] [DecidableEq C]
    (K : RecurrentPartition R C)
    (mu : stdSimplex ℝ (FullState T R)) (c : C) : FullState T R → ℝ
  | Sum.inl _ => 0
  | Sum.inr r => if K.classOf r = c then mu.1 (Sum.inr r) else 0

/-- The source absorption potential of class `c`: on transient states it is the
corresponding row of `H=NR`, and on recurrent states it is the class indicator. -/
noncomputable def absorptionPotential
    {R : Type uS} {C : Type uC} [Fintype R] [Fintype C] [DecidableEq C]
    (K : RecurrentPartition R C)
    (D : RecurrentBlockDecomposition T C) (c : C) : FullState T R → ℝ
  | Sum.inl i => D.H i c
  | Sum.inr r => if K.classOf r = c then 1 else 0

/-- Actual same-initial-state class weights.  Transient starts use the row of
`H`; recurrent starts use the vertex of their (fixed) recurrent class. -/
noncomputable def initialClassWeights
    {R : Type uS} {C : Type uC} [Fintype R] [Fintype C]
    (K : RecurrentPartition R C)
    (D : RecurrentBlockDecomposition T C) (x0 : FullState T R) : stdSimplex ℝ C :=
  match x0 with
  | Sum.inl i => D.absorptionWeights i
  | Sum.inr r => recurrentClassVertex (K.classOf r)

@[simp] lemma initialClassWeights_apply
    {R : Type uS} {C : Type uC} [Fintype R] [Fintype C] [DecidableEq C]
    (K : RecurrentPartition R C)
    (D : RecurrentBlockDecomposition T C) (x0 : FullState T R) (c : C) :
    (initialClassWeights K D x0).1 c = absorptionPotential K D c x0 := by
  classical
  cases x0 with
  | inl i => rfl
  | inr r =>
      simpa [initialClassWeights, absorptionPotential] using
        (recurrentClassVertex_apply (K.classOf r) c)

/-- A source-semantic finite recurrent decomposition for an actual stochastic
kernel on one state space.  The recurrent-class partition `K` is external and
shared by baseline and perturbation.  `Q` and `R` are tied to the actual kernel;
recurrent rows cannot leave their class; and `classLaw` is the actual classwise
invariant law with exact carrier.

`class_communicates` is the actual full-kernel irreducibility condition inside
each closed recurrent class.  Strict positivity and uniqueness of the class
invariant laws, the stationary class formula, and the full periodic-safe Cesàro
limit are all derived below; none is a primitive theorem hypothesis. -/
structure FiniteRecurrentDecomposition
    {R : Type uS} {C : Type uC}
    [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]
    (K : RecurrentPartition R C) where
  P : Matrix (FullState T R) (FullState T R) ℝ
  stochastic : P ∈ Matrix.rowStochastic ℝ (FullState T R)
  block : RecurrentBlockDecomposition T C
  q_link : ∀ i j, block.Q i j = P (Sum.inl i) (Sum.inl j)
  r_link : ∀ i c,
    block.R i c = ∑ r, P (Sum.inl i) (Sum.inr r) * if K.classOf r = c then 1 else 0
  recurrent_to_transient_zero : ∀ r j, P (Sum.inr r) (Sum.inl j) = 0
  recurrent_cross_zero : ∀ r s, K.classOf r ≠ K.classOf s →
    P (Sum.inr r) (Sum.inr s) = 0
  classLaw : C → stdSimplex ℝ (FullState T R)
  classLaw_transient_zero : ∀ c i, (classLaw c).1 (Sum.inl i) = 0
  classLaw_other_zero : ∀ c r, K.classOf r ≠ c → (classLaw c).1 (Sum.inr r) = 0
  classLaw_invariant : ∀ c, Matrix.vecMul (classLaw c).1 P = (classLaw c).1
  class_communicates : ∀ c r s,
    K.classOf r = c → K.classOf s = c →
    ∃ n > 0, 0 < (P ^ n) (Sum.inr r) (Sum.inr s)

namespace FiniteRecurrentDecomposition

variable {T : Type uT} [Fintype T] [DecidableEq T]
variable {R : Type uS} {C : Type uC}
  [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]
  {K : RecurrentPartition R C}

/-- Audit-facing extensional form of `q_link`: the stored transient block is
exactly the restriction of the actual kernel to transient states. -/
lemma block_Q_eq_kernelRestriction
    (M : FiniteRecurrentDecomposition (T := T) K) :
    M.block.Q = fun i j => M.P (Sum.inl i) (Sum.inl j) := by
  ext i j
  exact M.q_link i j

/-- Audit-facing extensional form of `r_link`: the stored direct-entry block is
exactly the actual one-step probability of entering each recurrent class. -/
lemma block_R_eq_directClassEntry
    (M : FiniteRecurrentDecomposition (T := T) K) :
    M.block.R = fun i c =>
      ∑ r, M.P (Sum.inl i) (Sum.inr r) * if K.classOf r = c then 1 else 0 := by
  ext i c
  exact M.r_link i c

/-- The block identity `H = QH + R`, derived from `H=NR` and `(I-Q)N=I`. -/
lemma H_eq_QH_add_R (M : FiniteRecurrentDecomposition (T := T) K) :
    M.block.H = M.block.Q * M.block.H + M.block.R := by
  have hres : (1 - M.block.Q) * M.block.H = M.block.R := by
    calc
      (1 - M.block.Q) * M.block.H =
          ((1 - M.block.Q) * M.block.N) * M.block.R := by
        rw [RecurrentBlockDecomposition.H, Matrix.mul_assoc]
      _ = (1 : Matrix T T ℝ) * M.block.R := by rw [M.block.inverse_right]
      _ = M.block.R := Matrix.one_mul _
  have hsub : M.block.H - M.block.Q * M.block.H = M.block.R := by
    simpa only [Matrix.sub_mul, Matrix.one_mul] using hres
  apply Matrix.ext
  intro i c
  have hic := congrFun (congrFun hsub i) c
  simp only [Matrix.sub_apply, Matrix.add_apply] at hic ⊢
  linarith

/-- The source absorption potential is harmonic for the actual full kernel. -/
lemma absorptionPotential_harmonic
    (M : FiniteRecurrentDecomposition (T := T) K) (c : C) :
    Matrix.mulVec
        (M.P : Matrix (FullState T R) (FullState T R) ℝ)
        (absorptionPotential (T := T) K M.block c) =
      absorptionPotential (T := T) K M.block c := by
  classical
  funext x
  cases x with
  | inl i =>
      rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
      simp only [absorptionPotential]
      have hH := congrFun (congrFun
        (H_eq_QH_add_R (R := R) (C := C) (K := K) M) i) c
      simp only [Matrix.add_apply, Matrix.mul_apply] at hH
      calc
        (∑ j, M.P (Sum.inl i) (Sum.inl j) * M.block.H j c) +
            ∑ r, M.P (Sum.inl i) (Sum.inr r) *
              (if K.classOf r = c then 1 else 0) =
          (∑ j, M.block.Q i j * M.block.H j c) + M.block.R i c := by
            congr 1
            · apply Finset.sum_congr rfl
              intro j _
              rw [M.q_link i j]
            · rw [M.r_link i c]
        _ = M.block.H i c := hH.symm
  | inr r =>
      rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
      simp only [absorptionPotential]
      have hrow := Matrix.sum_row_of_mem_rowStochastic M.stochastic (Sum.inr r)
      rw [Fintype.sum_sum_type] at hrow
      have htrans : (∑ j, M.P (Sum.inr r) (Sum.inl j)) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        exact M.recurrent_to_transient_zero r j
      rw [htrans, zero_add] at hrow
      have htransH :
          (∑ j, M.P (Sum.inr r) (Sum.inl j) * M.block.H j c) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        rw [M.recurrent_to_transient_zero r j, zero_mul]
      rw [htransH, zero_add]
      by_cases hrc : K.classOf r = c
      · rw [if_pos hrc]
        have hsame :
            (∑ s, M.P (Sum.inr r) (Sum.inr s) *
              (if K.classOf s = c then 1 else 0)) =
              ∑ s, M.P (Sum.inr r) (Sum.inr s) := by
          apply Finset.sum_congr rfl
          intro s _
          by_cases hsc : K.classOf s = c
          · simp [hsc]
          · have hrs : K.classOf r ≠ K.classOf s := by
              intro hrs
              apply hsc
              calc
                K.classOf s = K.classOf r := hrs.symm
                _ = c := hrc
            rw [M.recurrent_cross_zero r s hrs]
            simp [hsc]
        rw [hsame, hrow]
      · rw [if_neg hrc]
        apply Finset.sum_eq_zero
        intro s _
        by_cases hsc : K.classOf s = c
        · have hrs : K.classOf r ≠ K.classOf s := by
            intro hrs
            apply hrc
            calc
              K.classOf r = K.classOf s := hrs
              _ = c := hsc
          rw [M.recurrent_cross_zero r s hrs]
          simp [hsc]
        · simp [hsc]

/-- Any invariant law of the full chain has zero transient mass.  This is the
finite recurrent-decomposition fact encoded by invertibility of `I-Q`. -/
lemma invariant_transient_zero
    (M : FiniteRecurrentDecomposition (T := T) K)
    (mu : stdSimplex ℝ (FullState T R))
    (hinv : Matrix.vecMul mu.1 M.P = mu.1) :
    ∀ i, mu.1 (Sum.inl i) = 0 := by
  classical
  let v : T → ℝ := fun i => mu.1 (Sum.inl i)
  have hvQ : Matrix.vecMul v M.block.Q = v := by
    funext j
    have hj := congrFun hinv (Sum.inl j)
    rw [Matrix.vecMul, dotProduct, Fintype.sum_sum_type] at hj
    simp only [v]
    have hrec : (∑ r, mu.1 (Sum.inr r) * M.P (Sum.inr r) (Sum.inl j)) = 0 := by
      apply Finset.sum_eq_zero
      intro r _
      rw [M.recurrent_to_transient_zero r j, mul_zero]
    rw [hrec, add_zero] at hj
    simpa only [Matrix.vecMul, dotProduct, ← M.q_link] using hj
  have hzero : Matrix.vecMul v (1 - M.block.Q) = 0 := by
    rw [Matrix.vecMul_sub, Matrix.vecMul_one, hvQ, sub_self]
  have hv : v = 0 := by
    calc
      v = Matrix.vecMul v 1 := by rw [Matrix.vecMul_one]
      _ = Matrix.vecMul v ((1 - M.block.Q) * M.block.N) := by rw [M.block.inverse_right]
      _ = Matrix.vecMul (Matrix.vecMul v (1 - M.block.Q)) M.block.N := by
        rw [Matrix.vecMul_vecMul]
      _ = 0 := by rw [hzero, Matrix.zero_vecMul]
  intro i
  exact congrFun hv i

/-- An invariant row vector is invariant under every matrix power. -/
lemma vecMul_pow_eq_of_invariant
    (M : FiniteRecurrentDecomposition (T := T) K)
    (v : FullState T R → ℝ)
    (hinv : Matrix.vecMul v M.P = v) :
    ∀ n : ℕ, Matrix.vecMul v (M.P ^ n) = v := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hinv]

/-- Strict positivity of the class invariant law is derived from probability
mass, exact class support, invariance and communication; it is not an extra
P-GOA-03 hypothesis. -/
lemma classLaw_positive
    (M : FiniteRecurrentDecomposition (T := T) K)
    (c : C) (r : R) (hrc : K.classOf r = c) :
    0 < (M.classLaw c).1 (Sum.inr r) := by
  classical
  have hsum : (∑ x, (M.classLaw c).1 x) = 1 := stdSimplex.sum_eq_one (M.classLaw c)
  have hsumpos : 0 < ∑ x, (M.classLaw c).1 x := by simpa [hsum]
  obtain ⟨x, _hx, hxpos⟩ :=
    (Finset.sum_pos_iff_of_nonneg
      (fun x _ => stdSimplex.zero_le (M.classLaw c) x)).mp hsumpos
  obtain ⟨s, hsc, hspos⟩ : ∃ s : R, K.classOf s = c ∧ 0 < (M.classLaw c).1 (Sum.inr s) := by
    cases x with
    | inl i =>
        change 0 < (M.classLaw c).1 (Sum.inl i) at hxpos
        rw [M.classLaw_transient_zero c i] at hxpos
        exact (lt_irrefl 0 hxpos).elim
    | inr s =>
        change 0 < (M.classLaw c).1 (Sum.inr s) at hxpos
        by_cases hsc : K.classOf s = c
        · exact ⟨s, hsc, hxpos⟩
        · rw [M.classLaw_other_zero c s hsc] at hxpos
          exact (lt_irrefl 0 hxpos).elim
  obtain ⟨n, _hn, hpath⟩ := M.class_communicates c s r hsc hrc
  have hpow := M.vecMul_pow_eq_of_invariant (M.classLaw c).1 (M.classLaw_invariant c) n
  have hcomp := congrFun hpow (Sum.inr r)
  rw [Matrix.vecMul, dotProduct] at hcomp
  have hnonnegP : ∀ i j, 0 ≤ M.P i j := fun i j =>
    Matrix.nonneg_of_mem_rowStochastic M.stochastic
  have hsumstrict :
      0 < ∑ x, (M.classLaw c).1 x * (M.P ^ n) x (Sum.inr r) := by
    apply (Finset.sum_pos_iff_of_nonneg (fun x _ =>
      mul_nonneg (stdSimplex.zero_le (M.classLaw c) x)
        (Matrix.pow_apply_nonneg hnonnegP n x (Sum.inr r)))).2
    exact ⟨Sum.inr s, Finset.mem_univ _, mul_pos hspos hpath⟩
  exact hcomp ▸ hsumstrict

/-- The non-normalized restriction of an invariant law to one closed recurrent
class is itself invariant. -/
lemma recurrentClassRestriction_invariant
    (M : FiniteRecurrentDecomposition (T := T) K)
    (mu : stdSimplex ℝ (FullState T R))
    (hinv : Matrix.vecMul mu.1 M.P = mu.1)
    (htrans : ∀ i, mu.1 (Sum.inl i) = 0)
    (c : C) :
    Matrix.vecMul (recurrentClassRestriction K mu c) M.P =
      recurrentClassRestriction K mu c := by
  classical
  funext y
  cases y with
  | inl j =>
      rw [Matrix.vecMul, dotProduct, Fintype.sum_sum_type]
      simp only [recurrentClassRestriction]
      simp [M.recurrent_to_transient_zero]
  | inr s =>
      rw [Matrix.vecMul, dotProduct, Fintype.sum_sum_type]
      simp only [recurrentClassRestriction]
      by_cases hsc : K.classOf s = c
      · rw [if_pos hsc]
        have hs := congrFun hinv (Sum.inr s)
        rw [Matrix.vecMul, dotProduct, Fintype.sum_sum_type] at hs
        have ht :
            (∑ i, mu.1 (Sum.inl i) * M.P (Sum.inl i) (Sum.inr s)) = 0 := by
          apply Finset.sum_eq_zero
          intro i _
          rw [htrans i, zero_mul]
        rw [ht, zero_add] at hs
        have hrec :
            (∑ r, (if K.classOf r = c then mu.1 (Sum.inr r) else 0) *
              M.P (Sum.inr r) (Sum.inr s)) =
              ∑ r, mu.1 (Sum.inr r) * M.P (Sum.inr r) (Sum.inr s) := by
          apply Finset.sum_congr rfl
          intro r _
          by_cases hrc : K.classOf r = c
          · simp [hrc]
          · have hrs : K.classOf r ≠ K.classOf s := by
              intro hrs
              apply hrc
              calc
                K.classOf r = K.classOf s := hrs
                _ = c := hsc
            rw [if_neg hrc, zero_mul, M.recurrent_cross_zero r s hrs, mul_zero]
        rw [hrec, hs]
        simp
      · rw [if_neg hsc]
        have ht :
            (∑ i, (0 : ℝ) * M.P (Sum.inl i) (Sum.inr s)) = 0 := by simp
        rw [ht, zero_add]
        apply Finset.sum_eq_zero
        intro r _
        by_cases hrc : K.classOf r = c
        · have hrs : K.classOf r ≠ K.classOf s := by
            intro hrs
            apply hsc
            calc
              K.classOf s = K.classOf r := hrs.symm
              _ = c := hrc
          rw [if_pos hrc, M.recurrent_cross_zero r s hrs, mul_zero]
        · simp [hrc]

/-- Total mass of the class restriction is exactly `recurrentClassMass`. -/
lemma recurrentClassRestriction_sum
    (M : FiniteRecurrentDecomposition (T := T) K)
    (mu : stdSimplex ℝ (FullState T R)) (c : C) :
    (∑ x, recurrentClassRestriction K mu c x) = recurrentClassMass K mu c := by
  classical
  rw [Fintype.sum_sum_type]
  simp [recurrentClassRestriction, recurrentClassMass]

/-- An invariant law with no transient mass is, on each irreducible recurrent
class, its class mass times the class invariant law.  This is derived from
communication by a finite maximum-ratio argument rather than assumed in the
decomposition certificate. -/
lemma stationary_class_formula
    (M : FiniteRecurrentDecomposition (T := T) K)
    (mu : stdSimplex ℝ (FullState T R))
    (hinv : Matrix.vecMul mu.1 M.P = mu.1)
    (htrans : ∀ i, mu.1 (Sum.inl i) = 0)
    (r : R) :
    mu.1 (Sum.inr r) =
      recurrentClassMass K mu (K.classOf r) *
        (M.classLaw (K.classOf r)).1 (Sum.inr r) := by
  classical
  let c : C := K.classOf r
  let S : Finset R := Finset.univ.filter (fun s => K.classOf s = c)
  have hS : S.Nonempty := by
    obtain ⟨s, hs⟩ := K.class_nonempty c
    exact ⟨s, by simp [S, hs]⟩
  let ratio : R → ℝ := fun s =>
    mu.1 (Sum.inr s) / (M.classLaw c).1 (Sum.inr s)
  obtain ⟨rstar, hrstarS, hmax⟩ := Finset.exists_max_image S ratio hS
  have hrstarc : K.classOf rstar = c := by
    simpa [S] using hrstarS
  let a : ℝ := ratio rstar
  let v : FullState T R → ℝ := recurrentClassRestriction K mu c
  let d : FullState T R → ℝ := a • (M.classLaw c).1 - v
  have hv_inv : Matrix.vecMul v M.P = v := by
    simpa [v] using M.recurrentClassRestriction_invariant mu hinv htrans c
  have hd_inv : Matrix.vecMul d M.P = d := by
    dsimp [d]
    rw [Matrix.sub_vecMul, Matrix.smul_vecMul, M.classLaw_invariant c, hv_inv]
  have hd_nonneg : ∀ x, 0 ≤ d x := by
    intro x
    cases x with
    | inl i =>
        change 0 ≤ a * (M.classLaw c).1 (Sum.inl i) - v (Sum.inl i)
        rw [M.classLaw_transient_zero c i]
        simp [v, recurrentClassRestriction]
    | inr s =>
        by_cases hsc : K.classOf s = c
        · have hp := M.classLaw_positive c s hsc
          have hrs : ratio s ≤ ratio rstar := hmax s (by simp [S, hsc])
          have hle : mu.1 (Sum.inr s) ≤ a * (M.classLaw c).1 (Sum.inr s) := by
            apply (div_le_iff₀ hp).mp
            simpa [a] using hrs
          change 0 ≤ a * (M.classLaw c).1 (Sum.inr s) - v (Sum.inr s)
          rw [show v (Sum.inr s) = mu.1 (Sum.inr s) by
            simp [v, recurrentClassRestriction, hsc]]
          exact sub_nonneg.mpr hle
        · change 0 ≤ a * (M.classLaw c).1 (Sum.inr s) - v (Sum.inr s)
          rw [M.classLaw_other_zero c s hsc]
          simp [v, recurrentClassRestriction, hsc]
  have hpstar := M.classLaw_positive c rstar hrstarc
  have hdstar : d (Sum.inr rstar) = 0 := by
    change a * (M.classLaw c).1 (Sum.inr rstar) - v (Sum.inr rstar) = 0
    rw [show v (Sum.inr rstar) = mu.1 (Sum.inr rstar) by
      simp [v, recurrentClassRestriction, hrstarc]]
    dsimp [a, ratio]
    rw [div_mul_cancel₀ _ (ne_of_gt hpstar), sub_self]
  have hdpow := M.vecMul_pow_eq_of_invariant d hd_inv
  have hnonnegP : ∀ i j, 0 ≤ M.P i j := fun i j =>
    Matrix.nonneg_of_mem_rowStochastic M.stochastic
  have hdclass : ∀ s, K.classOf s = c → d (Sum.inr s) = 0 := by
    intro s hsc
    have hds0 := hd_nonneg (Sum.inr s)
    by_contra hne
    have hdspos : 0 < d (Sum.inr s) := lt_of_le_of_ne hds0 (Ne.symm hne)
    obtain ⟨n, _hn, hpath⟩ := M.class_communicates c s rstar hsc hrstarc
    have hpow := congrFun (hdpow n) (Sum.inr rstar)
    rw [Matrix.vecMul, dotProduct, hdstar] at hpow
    have hsumpos :
        0 < ∑ x, d x * (M.P ^ n) x (Sum.inr rstar) := by
      apply (Finset.sum_pos_iff_of_nonneg (fun x _ =>
        mul_nonneg (hd_nonneg x)
          (Matrix.pow_apply_nonneg hnonnegP n x (Sum.inr rstar)))).2
      exact ⟨Sum.inr s, Finset.mem_univ _, mul_pos hdspos hpath⟩
    linarith
  have hdall : ∀ x, d x = 0 := by
    intro x
    cases x with
    | inl i =>
        change a * (M.classLaw c).1 (Sum.inl i) - v (Sum.inl i) = 0
        rw [M.classLaw_transient_zero c i]
        simp [v, recurrentClassRestriction]
    | inr s =>
        by_cases hsc : K.classOf s = c
        · exact hdclass s hsc
        · change a * (M.classLaw c).1 (Sum.inr s) - v (Sum.inr s) = 0
          rw [M.classLaw_other_zero c s hsc]
          simp [v, recurrentClassRestriction, hsc]
  have hsumd : (∑ x, d x) = 0 := Finset.sum_eq_zero fun x _ => hdall x
  have hpisum : (∑ x, (M.classLaw c).1 x) = 1 := stdSimplex.sum_eq_one (M.classLaw c)
  have hvsum : (∑ x, v x) = recurrentClassMass K mu c := by
    simpa [v] using M.recurrentClassRestriction_sum mu c
  have ha : a = recurrentClassMass K mu c := by
    have hexpand :
        (∑ x, d x) = a * (∑ x, (M.classLaw c).1 x) - ∑ x, v x := by
      dsimp [d]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib,
        ← Finset.mul_sum]
    rw [hexpand, hpisum, hvsum, mul_one] at hsumd
    linarith
  have hdr : d (Sum.inr r) = 0 := hdclass r rfl
  change a * (M.classLaw c).1 (Sum.inr r) - v (Sum.inr r) = 0 at hdr
  have hvr : v (Sum.inr r) = mu.1 (Sum.inr r) := by
    simp [v, recurrentClassRestriction, c]
  rw [hvr] at hdr
  change mu.1 (Sum.inr r) =
    recurrentClassMass K mu c * (M.classLaw c).1 (Sum.inr r)
  rw [← ha]
  linarith

/-- A harmonic observable has the same expectation under every Cesàro average. -/
lemma cesaro_dot_harmonic
    (M : FiniteRecurrentDecomposition (T := T) K)
    (mu0 : stdSimplex ℝ (FullState T R))
    (h : FullState T R → ℝ)
    (hh : Matrix.mulVec M.P h = h) (n : ℕ) :
    (UEOT.V3.FiniteCesaroInvariant.cesaroRow M.P M.stochastic mu0 n).1 ⬝ᵥ h =
      mu0.1 ⬝ᵥ h := by
  classical
  have hpow : ∀ t : ℕ, Matrix.mulVec (M.P ^ t) h = h := by
    intro t
    induction t with
    | zero => simp
    | succ t iht =>
        rw [pow_succ, ← Matrix.mulVec_mulVec, hh, iht]
  have horbit : ∀ t : ℕ,
      (UEOT.V3.FiniteCesaroInvariant.orbit M.P M.stochastic mu0 t).1 ⬝ᵥ h =
        mu0.1 ⬝ᵥ h := by
    intro t
    change Matrix.vecMul mu0.1 (M.P ^ t) ⬝ᵥ h = mu0.1 ⬝ᵥ h
    rw [← Matrix.dotProduct_mulVec, hpow t]
  change
    (((((n + 1 : ℕ) : ℝ)⁻¹) •
      ∑ t ∈ Finset.range (n + 1),
        (UEOT.V3.FiniteCesaroInvariant.orbit M.P M.stochastic mu0 t : FullState T R → ℝ)) ⬝ᵥ h) =
      mu0.1 ⬝ᵥ h
  rw [smul_dotProduct, sum_dotProduct]
  have hsum :
      (∑ t ∈ Finset.range (n + 1),
        (UEOT.V3.FiniteCesaroInvariant.orbit M.P M.stochastic mu0 t : FullState T R → ℝ) ⬝ᵥ h) =
        (n + 1 : ℕ) • (mu0.1 ⬝ᵥ h) := by
    have hs := Finset.sum_eq_card_nsmul
      (s := Finset.range (n + 1))
      (f := fun t =>
        (UEOT.V3.FiniteCesaroInvariant.orbit M.P M.stochastic mu0 t : FullState T R → ℝ) ⬝ᵥ h)
      (b := mu0.1 ⬝ᵥ h) (fun t _ => horbit t)
    simpa using hs
  rw [hsum]
  simp only [nsmul_eq_mul]
  have hN : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hN, one_mul]

/-- Class mass equals expectation of the class absorption potential once
transient mass is zero. -/
lemma dot_absorptionPotential_eq_classMass
    (M : FiniteRecurrentDecomposition (T := T) K)
    (mu : stdSimplex ℝ (FullState T R))
    (htrans : ∀ i, mu.1 (Sum.inl i) = 0) (c : C) :
    mu.1 ⬝ᵥ absorptionPotential K M.block c = recurrentClassMass K mu c := by
  classical
  rw [dotProduct, Fintype.sum_sum_type]
  simp only [absorptionPotential]
  unfold recurrentClassMass
  have ht : (∑ i, mu.1 (Sum.inl i) * M.block.H i c) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [htrans i, zero_mul]
  rw [ht, zero_add]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hrc : K.classOf r = c <;> simp [absorptionPotential, hrc]

/-- A convergent subsequence of Cesàro averages preserves every harmonic
observable. -/
lemma harmonic_moment_of_cesaro_subseq
    (M : FiniteRecurrentDecomposition (T := T) K)
    (mu0 nu : stdSimplex ℝ (FullState T R))
    (h : FullState T R → ℝ)
    (hh : Matrix.mulVec M.P h = h)
    (phi : ℕ → ℕ) (hlim :
      Tendsto (UEOT.V3.FiniteCesaroInvariant.cesaroRow M.P M.stochastic mu0 ∘ phi)
        atTop (𝓝 nu)) :
    nu.1 ⬝ᵥ h = mu0.1 ⬝ᵥ h := by
  classical
  have hcont : Continuous (fun mu : stdSimplex ℝ (FullState T R) => mu.1 ⬝ᵥ h) := by
    exact continuous_subtype_val.dotProduct continuous_const
  have hleft := (hcont.tendsto nu).comp hlim
  have hright : Tendsto
      (fun _ : ℕ => mu0.1 ⬝ᵥ h) atTop (𝓝 (mu0.1 ⬝ᵥ h)) := tendsto_const_nhds
  have heq :
      (fun n : ℕ =>
        (UEOT.V3.FiniteCesaroInvariant.cesaroRow M.P M.stochastic mu0 (phi n)).1 ⬝ᵥ h) =
      (fun _ : ℕ => mu0.1 ⬝ᵥ h) := by
    funext n
    exact M.cesaro_dot_harmonic mu0 h hh (phi n)
  have hleft' : Tendsto
      (fun n : ℕ =>
        (UEOT.V3.FiniteCesaroInvariant.cesaroRow M.P M.stochastic mu0 (phi n)).1 ⬝ᵥ h)
      atTop (𝓝 (nu.1 ⬝ᵥ h)) := by
    simpa [Function.comp_def] using hleft
  rw [heq] at hleft'
  exact tendsto_nhds_unique hleft' hright

/-- The canonical pure initial law at one full state. -/
noncomputable def pureFullLaw (x0 : FullState T R) : stdSimplex ℝ (FullState T R) :=
  UEOT.V3.FiniteDobrushin.pureSimplex x0

@[simp] lemma pureFullLaw_apply (x0 y : FullState T R) :
    (pureFullLaw x0).1 y = if y = x0 then 1 else 0 := by
  classical
  simp [pureFullLaw, UEOT.V3.FiniteDobrushin.pureSimplex, Pi.single_apply]

/-- Every Cesàro cluster point is the absorption-weighted recurrent-class
mixture.  This is the periodic-safe finite recurrent-decomposition bridge that
the frozen §21.4 perturbation theorem needs. -/
lemma cesaro_cluster_eq_recurrentMixture
    (M : FiniteRecurrentDecomposition (T := T) K)
    (x0 : FullState T R)
    (nu : stdSimplex ℝ (FullState T R))
    (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (hlim : Tendsto
      (UEOT.V3.FiniteCesaroInvariant.cesaroRow M.P M.stochastic (pureFullLaw x0) ∘ phi)
      atTop (𝓝 nu)) :
    nu = recurrentMixture (initialClassWeights K M.block x0) M.classLaw := by
  classical
  have hinv := (UEOT.V3.FiniteCesaroInvariant.p_goa_01
    M.P M.stochastic (pureFullLaw x0)).2 nu phi hphi hlim
  have htrans := M.invariant_transient_zero nu hinv
  have hmass : ∀ c, recurrentClassMass K nu c = (initialClassWeights K M.block x0).1 c := by
    intro c
    have hmom := M.harmonic_moment_of_cesaro_subseq
      (pureFullLaw x0) nu (absorptionPotential K M.block c)
      (M.absorptionPotential_harmonic c) phi hlim
    rw [M.dot_absorptionPotential_eq_classMass nu htrans c] at hmom
    have hpure :
        (pureFullLaw x0).1 ⬝ᵥ absorptionPotential K M.block c =
          absorptionPotential K M.block c x0 := by
      rw [dotProduct]
      classical
      simp [pureFullLaw_apply]
    rw [hpure, ← initialClassWeights_apply] at hmom
    exact hmom
  apply Subtype.ext
  funext x
  cases x with
  | inl i =>
      rw [htrans i, recurrentMixture_apply]
      symm
      apply Finset.sum_eq_zero
      intro c _
      rw [M.classLaw_transient_zero c i, mul_zero]
  | inr r =>
      rw [recurrentMixture_apply]
      have hformula := M.stationary_class_formula nu hinv htrans r
      rw [hmass (K.classOf r)] at hformula
      rw [hformula]
      symm
      apply Finset.sum_eq_single (K.classOf r)
      · intro c _ hc
        have hne : K.classOf r ≠ c := Ne.symm hc
        rw [M.classLaw_other_zero c r hne, mul_zero]
      · intro hnot
        exact (hnot (Finset.mem_univ _)).elim

/-- Full Cesàro convergence for a certified finite recurrent decomposition,
including periodic recurrent classes. -/
theorem cesaro_tendsto_recurrentMixture
    (M : FiniteRecurrentDecomposition (T := T) K) (x0 : FullState T R) :
    Tendsto
      (UEOT.V3.FiniteCesaroInvariant.cesaroRow M.P M.stochastic (pureFullLaw x0))
      atTop
      (𝓝 (recurrentMixture (initialClassWeights K M.block x0) M.classLaw)) := by
  classical
  refine IsCompact.tendsto_nhds_of_unique_mapClusterPt
    (isCompact_univ : IsCompact (Set.univ : Set (stdSimplex ℝ (FullState T R))))
    (by simp) ?_
  intro nu _ hcluster
  rcases hcluster.tendsto_subseq with ⟨phi, hphi, hlim⟩
  exact M.cesaro_cluster_eq_recurrentMixture x0 nu phi hphi hlim

end FiniteRecurrentDecomposition

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

/-- The same-initial-state absorption-weight `L1` bound. -/
lemma initialClassWeights_l1_le_norm
    {R : Type uS} {C : Type uC} [Fintype R] [Fintype C]
    (K : RecurrentPartition R C)
    (D Dhat : RecurrentBlockDecomposition T C) (x0 : FullState T R) :
    (∑ c, |(initialClassWeights K D x0).1 c -
      (initialClassWeights K Dhat x0).1 c|) ≤ ‖Dhat.H - D.H‖ := by
  classical
  cases x0 with
  | inl i => exact absorptionWeights_l1_le_norm D Dhat i
  | inr r => simp [initialClassWeights, recurrentClassVertex]

/-- **P-GOA-03.** Stability of a finite recurrent decomposition under a
perturbation preserving the exact same transient state type and exact same
recurrent-class partition.

Unlike the algebraic helper proved earlier in this file, this source-facing
theorem is tied to two actual stochastic kernels on one common state space.  It
also proves that the displayed recurrent mixtures are the actual periodic-safe
Cesàro limits from the same initial state before applying the frozen TV bound. -/
theorem p_goa_03
    {R : Type uS} {C : Type uC}
    [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]
    (K : RecurrentPartition R C)
    (M Mhat : FiniteRecurrentDecomposition (T := T) K)
    (epsQ epsR : ℝ)
    (hQ : ‖Mhat.block.Q - M.block.Q‖ ≤ epsQ)
    (hR : ‖Mhat.block.R - M.block.R‖ ≤ epsR)
    (hsmall : ‖M.block.N‖ * epsQ < 1)
    (x0 : FullState T R)
    (epsStat : C → ℝ)
    (hstat : ∀ j,
      UEOT.V3.FiniteDobrushin.lawTV (M.classLaw j) (Mhat.classLaw j) ≤ epsStat j) :
    let nu := recurrentMixture (initialClassWeights K M.block x0) M.classLaw
    let nuhat := recurrentMixture (initialClassWeights K Mhat.block x0) Mhat.classLaw
    ‖Mhat.block.H - M.block.H‖ ≤
        (‖M.block.N‖ ^ 2 * epsQ + ‖M.block.N‖ * epsR) /
          (1 - ‖M.block.N‖ * epsQ) ∧
      Tendsto
        (UEOT.V3.FiniteCesaroInvariant.cesaroRow M.P M.stochastic (FiniteRecurrentDecomposition.pureFullLaw x0))
        atTop (𝓝 nu) ∧
      Tendsto
        (UEOT.V3.FiniteCesaroInvariant.cesaroRow Mhat.P Mhat.stochastic (FiniteRecurrentDecomposition.pureFullLaw x0))
        atTop (𝓝 nuhat) ∧
      UEOT.V3.FiniteDobrushin.lawTV nu nuhat ≤
        (1 / 2 : ℝ) *
            ((‖M.block.N‖ ^ 2 * epsQ + ‖M.block.N‖ * epsR) /
              (1 - ‖M.block.N‖ * epsQ)) +
          ∑ j, (initialClassWeights K Mhat.block x0).1 j * epsStat j := by
  classical
  dsimp only
  have hH :
      ‖Mhat.block.H - M.block.H‖ ≤
        (‖M.block.N‖ ^ 2 * epsQ + ‖M.block.N‖ * epsR) /
          (1 - ‖M.block.N‖ * epsQ) := by
    rcases isEmpty_or_nonempty T with hT | hT
    · letI := hT
      have hHeq : Mhat.block.H = M.block.H := Subsingleton.elim _ _
      have hNzero : M.block.N = 0 := Subsingleton.elim _ _
      simp [hHeq, hNzero]
    · letI := hT
      have hHraw := absorption_matrix_bound_of_inverses
        M.block.Q Mhat.block.Q M.block.N Mhat.block.N M.block.R Mhat.block.R epsQ epsR
        M.block.inverse_left M.block.inverse_right Mhat.block.inverse_left
        hQ hR M.block.r_nonneg M.block.direct_row_sum_le_one hsmall
      simpa [RecurrentBlockDecomposition.H] using hHraw
  have hweight := initialClassWeights_l1_le_norm K M.block Mhat.block x0
  have hweightBH :
      (∑ j, |(initialClassWeights K M.block x0).1 j -
        (initialClassWeights K Mhat.block x0).1 j|) ≤
        (‖M.block.N‖ ^ 2 * epsQ + ‖M.block.N‖ * epsR) /
          (1 - ‖M.block.N‖ * epsQ) := hweight.trans hH
  have hmix := recurrentMixture_tv_le
    (initialClassWeights K M.block x0) (initialClassWeights K Mhat.block x0)
    M.classLaw Mhat.classLaw epsStat hstat
  refine ⟨hH, ?_, ?_, ?_⟩
  · exact M.cesaro_tendsto_recurrentMixture x0
  · exact Mhat.cesaro_tendsto_recurrentMixture x0
  · calc
      UEOT.V3.FiniteDobrushin.lawTV
          (recurrentMixture (initialClassWeights K M.block x0) M.classLaw)
          (recurrentMixture (initialClassWeights K Mhat.block x0) Mhat.classLaw) ≤
        (1 / 2 : ℝ) *
            (∑ j, |(initialClassWeights K M.block x0).1 j -
              (initialClassWeights K Mhat.block x0).1 j|) +
          ∑ j, (initialClassWeights K Mhat.block x0).1 j * epsStat j := hmix
      _ ≤ (1 / 2 : ℝ) *
            ((‖M.block.N‖ ^ 2 * epsQ + ‖M.block.N‖ * epsR) /
              (1 - ‖M.block.N‖ * epsQ)) +
          ∑ j, (initialClassWeights K Mhat.block x0).1 j * epsStat j := by
        gcongr

end

end UEOT.V3.FiniteRecurrentDecompositionStability
