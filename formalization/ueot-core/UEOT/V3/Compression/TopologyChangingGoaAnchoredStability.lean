import UEOT.V3.Compression.TopologyChangingGoaStabilityCertificate

/-!
# Anchored stationary-branch stability

Global Dobrushin contraction is a strong sufficient certificate for tracking a
source invariant law under kernel perturbation.  The M-CF perturbation proof,
however, uses much less: it only needs the source dynamics to contract
distances **from the selected stationary branch** toward every comparison law.

This module isolates that weaker radial condition.

For a source invariant law `muStar`, define an anchored contraction factor
`alpha < 1` by

`D_TV(P muStar, P nu) <= alpha * D_TV(muStar, nu)`

for every law `nu`.  Because `muStar` is fixed by `P`, this is exactly the
one-sided contraction estimate needed in the stationary perturbation argument.

The target kernel need not share the source recurrent partition and need not be
contractive.  Finite-state target invariant existence is still supplied by
P-GOA-01.
-/

namespace UEOT.V3.Compression.TopologyChangingGoaAnchoredStability

open UEOT.V3
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.InvariantSetGaugeInvariance
open UEOT.V3.Compression.ContractiveFixedPoint

universe uS

noncomputable section

variable {S : Type uS} [Fintype S] [Nonempty S]

noncomputable local instance stateDecidableEq : DecidableEq S :=
  Classical.decEq S

/-- One-sided/radial contraction around one selected law.  This is weaker in
form than global pairwise Dobrushin contraction: only distances from `muStar`
must contract. -/
structure AnchoredLawContraction
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (muStar : stdSimplex ℝ S) (alpha : ℝ) : Prop where
  alpha_nonneg : 0 ≤ alpha
  alpha_lt_one : alpha < 1
  contract : ∀ nu,
    lawTV (step P hP muStar) (step P hP nu) ≤
      alpha * lawTV muStar nu

/-- **Anchored stationary-branch perturbation theorem.**

If the selected source invariant law has a strict anchored contraction
certificate, then every finite stochastic target kernel with uniformly small
row-TV defect has at least one invariant law within the standard
`epsilon / (1-alpha)` tube.

No global source Dobrushin assumption and no target contraction assumption are
used. -/
theorem anchored_stationary_tracking
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (Q : Matrix S S ℝ) (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (muStar : stdSimplex ℝ S)
    (hmuStar : muStar ∈ invariantLawSet P hP)
    (alpha epsilon : ℝ)
    (hanchor : AnchoredLawContraction P hP muStar alpha)
    (hrow : ∀ x, crossRowTV P hP Q hQ x ≤ epsilon) :
    ∃ muhat : stdSimplex ℝ S,
      muhat ∈ invariantLawSet Q hQ ∧
      lawTV muStar muhat ≤ epsilon / (1 - alpha) := by
  rcases exists_invariant Q hQ with ⟨muhat, hmuhat⟩
  refine ⟨muhat, hmuhat, ?_⟩
  have htri := lawTV_triangle muStar (step P hP muhat) muhat
  have hcontract := hanchor.contract muhat
  rw [hmuStar] at hcontract
  have hkernel := tv_step_cross_le P hP Q hQ muhat epsilon hrow
  rw [hmuhat] at hkernel
  have hbound :
      lawTV muStar muhat ≤ alpha * lawTV muStar muhat + epsilon := by
    linarith
  have hden : 0 < 1 - alpha := sub_pos.mpr hanchor.alpha_lt_one
  rw [le_div_iff₀ hden]
  nlinarith

/-- Global strict Dobrushin contraction implies anchored contraction around any
selected law, so the anchored theorem genuinely extends the existing global
certificate interface. -/
theorem anchored_of_dobrushin
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (muStar : stdSimplex ℝ S)
    (halpha : dobrushinAlpha P hP < 1) :
    AnchoredLawContraction P hP muStar (dobrushinAlpha P hP) := by
  refine ⟨dobrushinAlpha_nonneg P hP, halpha, ?_⟩
  intro nu
  exact tv_step_le_dobrushin P hP muStar nu

/-- The previous global-Dobrushin tracking theorem is recovered immediately as
a specialization of the anchored theorem. -/
theorem prescribedInvariant_tracked_via_anchored_of_dobrushin
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (Q : Matrix S S ℝ) (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (halpha : dobrushinAlpha P hP < 1)
    (mu : stdSimplex ℝ S)
    (hmu : mu ∈ invariantLawSet P hP)
    (epsilon : ℝ)
    (hrow : ∀ x, crossRowTV P hP Q hQ x ≤ epsilon) :
    ∃ muhat : stdSimplex ℝ S,
      muhat ∈ invariantLawSet Q hQ ∧
      lawTV mu muhat ≤ epsilon / (1 - dobrushinAlpha P hP) := by
  exact anchored_stationary_tracking
    P hP Q hQ mu hmu (dobrushinAlpha P hP) epsilon
      (anchored_of_dobrushin P hP mu halpha) hrow

end


/-! ## Strict weakening witness: anchored contraction without global Dobrushin contraction -/

noncomputable section

local instance fourStateDecidableEq : DecidableEq (Fin 4) :=
  Classical.decEq (Fin 4)

/-- Selected stationary branch for the strictness witness. -/
noncomputable def strictWitnessLaw : stdSimplex ℝ (Fin 4) :=
  ⟨![(1 / 2 : ℝ), 1 / 2, 0, 0], by
    constructor
    · intro i
      fin_cases i <;> norm_num
    · rw [Fin.sum_univ_four]
      simp
      norm_num⟩

/-- A four-state kernel with one stable selected branch but globally maximally
separated transient rows:

* states `0` and `1` both map to the selected law `(1/2,1/2,0,0)`;
* state `2` maps to `delta_0`;
* state `3` maps to `delta_1`.

The selected branch contracts radially by `1/2`, while rows `2` and `3` remain
TV-distance one apart. -/
noncomputable def strictWitnessKernel : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(1 / 2 : ℝ), 1 / 2, 0, 0;
     1 / 2, 1 / 2, 0, 0;
     1,     0,     0, 0;
     0,     1,     0, 0]

theorem strictWitnessKernel_stochastic :
    strictWitnessKernel ∈ Matrix.rowStochastic ℝ (Fin 4) := by
  rw [Matrix.mem_rowStochastic_iff_sum]
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [strictWitnessKernel]
  · intro i
    fin_cases i <;> rw [Fin.sum_univ_four] <;>
      simp [strictWitnessKernel] <;> norm_num

theorem strictWitnessLaw_invariant :
    step strictWitnessKernel strictWitnessKernel_stochastic strictWitnessLaw =
      strictWitnessLaw := by
  apply Subtype.ext
  funext j
  rw [step_apply, Fin.sum_univ_four]
  fin_cases j <;> simp [strictWitnessKernel, strictWitnessLaw] <;> norm_num

private theorem strictWitness_step_apply_zero (nu : stdSimplex ℝ (Fin 4)) :
    (step strictWitnessKernel strictWitnessKernel_stochastic nu).1 0 =
      (1 / 2 : ℝ) * (nu.1 0 + nu.1 1) + nu.1 2 := by
  rw [step_apply, Fin.sum_univ_four]
  simp [strictWitnessKernel]
  ring

private theorem strictWitness_step_apply_one (nu : stdSimplex ℝ (Fin 4)) :
    (step strictWitnessKernel strictWitnessKernel_stochastic nu).1 1 =
      (1 / 2 : ℝ) * (nu.1 0 + nu.1 1) + nu.1 3 := by
  rw [step_apply, Fin.sum_univ_four]
  simp [strictWitnessKernel]
  ring

private theorem strictWitness_step_apply_two (nu : stdSimplex ℝ (Fin 4)) :
    (step strictWitnessKernel strictWitnessKernel_stochastic nu).1 2 = 0 := by
  rw [step_apply, Fin.sum_univ_four]
  simp [strictWitnessKernel]

private theorem strictWitness_step_apply_three (nu : stdSimplex ℝ (Fin 4)) :
    (step strictWitnessKernel strictWitnessKernel_stochastic nu).1 3 = 0 := by
  rw [step_apply, Fin.sum_univ_four]
  simp [strictWitnessKernel]

/-- Exact radial distance after one step: only the imbalance between the two
outside coordinates survives. -/
theorem strictWitness_lawTV_step
    (nu : stdSimplex ℝ (Fin 4)) :
    lawTV strictWitnessLaw
      (step strictWitnessKernel strictWitnessKernel_stochastic nu) =
      (1 / 2 : ℝ) * |nu.1 2 - nu.1 3| := by
  unfold lawTV UEOT.V3.FiniteDiscountedControl.FiniteProbabilityRow.tvDist
  letI : MeasurableSpace (Fin 4) := ⊤
  rw [UEOT.V3.FiniteRecurrentDecompositionStability.pmf_tv_eq_half_sum_abs]
  simp_rw [simplexPMF_toReal]
  rw [Fin.sum_univ_four]
  rw [strictWitness_step_apply_zero, strictWitness_step_apply_one,
    strictWitness_step_apply_two, strictWitness_step_apply_three]
  have hsum := stdSimplex.sum_eq_one nu
  rw [Fin.sum_univ_four] at hsum
  change nu.1 0 + nu.1 1 + nu.1 2 + nu.1 3 = 1 at hsum
  have h0 :
      (1 / 2 : ℝ) - ((1 / 2) * (nu.1 0 + nu.1 1) + nu.1 2) =
        (1 / 2) * (nu.1 3 - nu.1 2) := by
    linarith
  have h1 :
      (1 / 2 : ℝ) - ((1 / 2) * (nu.1 0 + nu.1 1) + nu.1 3) =
        (1 / 2) * (nu.1 2 - nu.1 3) := by
    linarith
  simp [strictWitnessLaw]
  have h0' :
      (2 : ℝ)⁻¹ - ((2 : ℝ)⁻¹ * (nu.1 0 + nu.1 1) + nu.1 2) =
        (2 : ℝ)⁻¹ * (nu.1 3 - nu.1 2) := by
    simpa [one_div] using h0
  have h1' :
      (2 : ℝ)⁻¹ - ((2 : ℝ)⁻¹ * (nu.1 0 + nu.1 1) + nu.1 3) =
        (2 : ℝ)⁻¹ * (nu.1 2 - nu.1 3) := by
    simpa [one_div] using h1
  rw [h0', h1']
  rw [abs_mul, abs_mul]
  norm_num
  rw [abs_sub_comm (nu.1 3) (nu.1 2)]
  ring

/-- Initial TV distance from the selected branch dominates the total mass on
the two outside states. -/
theorem strictWitness_outsideMass_le_lawTV
    (nu : stdSimplex ℝ (Fin 4)) :
    nu.1 2 + nu.1 3 ≤ lawTV strictWitnessLaw nu := by
  unfold lawTV UEOT.V3.FiniteDiscountedControl.FiniteProbabilityRow.tvDist
  letI : MeasurableSpace (Fin 4) := ⊤
  rw [UEOT.V3.FiniteRecurrentDecompositionStability.pmf_tv_eq_half_sum_abs]
  simp_rw [simplexPMF_toReal]
  rw [Fin.sum_univ_four]
  change nu.1 2 + nu.1 3 ≤ (1 / 2 : ℝ) *
    (|1 / 2 - nu.1 0| + |1 / 2 - nu.1 1| +
      |0 - nu.1 2| + |0 - nu.1 3|)
  have h2 : 0 ≤ nu.1 2 := stdSimplex.zero_le nu 2
  have h3 : 0 ≤ nu.1 3 := stdSimplex.zero_le nu 3
  rw [abs_of_nonpos (by linarith : 0 - nu.1 2 ≤ 0),
      abs_of_nonpos (by linarith : 0 - nu.1 3 ≤ 0)]
  ring_nf
  have hsum := stdSimplex.sum_eq_one nu
  rw [Fin.sum_univ_four] at hsum
  change nu.1 0 + nu.1 1 + nu.1 2 + nu.1 3 = 1 at hsum
  have htri := abs_add_le (1 / 2 - nu.1 0) (1 / 2 - nu.1 1)
  have hsumexpr :
      (1 / 2 - nu.1 0) + (1 / 2 - nu.1 1) = nu.1 2 + nu.1 3 := by
    linarith
  have hnon : 0 ≤ nu.1 2 + nu.1 3 := add_nonneg h2 h3
  have habs :
      |(1 / 2 - nu.1 0) + (1 / 2 - nu.1 1)| =
        nu.1 2 + nu.1 3 := by
    rw [hsumexpr, abs_of_nonneg hnon]
  rw [habs] at htri
  linarith

private theorem strictWitness_abs_outside_diff_le_mass
    (nu : stdSimplex ℝ (Fin 4)) :
    |nu.1 2 - nu.1 3| ≤ nu.1 2 + nu.1 3 := by
  have h2 : 0 ≤ nu.1 2 := stdSimplex.zero_le nu 2
  have h3 : 0 ≤ nu.1 3 := stdSimplex.zero_le nu 3
  rw [abs_le]
  constructor <;> linarith

/-- The selected stationary branch contracts toward itself by the strict factor
`1/2`. -/
theorem strictWitness_anchored_half :
    AnchoredLawContraction strictWitnessKernel strictWitnessKernel_stochastic
      strictWitnessLaw (1 / 2 : ℝ) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro nu
  rw [strictWitnessLaw_invariant, strictWitness_lawTV_step]
  have hdiff := strictWitness_abs_outside_diff_le_mass nu
  have hout := strictWitness_outsideMass_le_lawTV nu
  nlinarith

/-- The two transient rows are maximally separated in TV. -/
theorem strictWitness_rowTV_two_three :
    rowTV strictWitnessKernel strictWitnessKernel_stochastic 2 3 = 1 := by
  unfold rowTV UEOT.V3.FiniteDiscountedControl.FiniteProbabilityRow.tvDist
  letI : MeasurableSpace (Fin 4) := ⊤
  rw [UEOT.V3.FiniteRecurrentDecompositionStability.pmf_tv_eq_half_sum_abs]
  simp_rw [rowPMF_toReal]
  rw [Fin.sum_univ_four]
  simp [strictWitnessKernel]
  norm_num

theorem strictWitness_dobrushinAlpha_le_one :
    dobrushinAlpha strictWitnessKernel strictWitnessKernel_stochastic ≤ 1 := by
  unfold dobrushinAlpha
  apply Finset.sup'_le
  intro z hz
  unfold rowTV UEOT.V3.FiniteDiscountedControl.FiniteProbabilityRow.tvDist
  exact UEOT.V3.TotalVariation.tvDist_le_one _ _

/-- Despite the selected branch contracting by `1/2`, the global Dobrushin
coefficient is exactly `1`. -/
theorem strictWitness_dobrushinAlpha_eq_one :
    dobrushinAlpha strictWitnessKernel strictWitnessKernel_stochastic = 1 := by
  apply le_antisymm strictWitness_dobrushinAlpha_le_one
  have h := rowTV_le_dobrushinAlpha
    strictWitnessKernel strictWitnessKernel_stochastic (2 : Fin 4) (3 : Fin 4)
  rw [strictWitness_rowTV_two_three] at h
  exact h

/-- Machine-checked strictness of the weakening: the same source kernel admits
a strict anchored factor `1/2` around the selected stationary branch while it
fails every global Dobrushin certificate `alpha(P) < 1`. -/
theorem anchored_strictly_weaker_witness :
    AnchoredLawContraction strictWitnessKernel strictWitnessKernel_stochastic
        strictWitnessLaw (1 / 2 : ℝ) ∧
      ¬ dobrushinAlpha strictWitnessKernel strictWitnessKernel_stochastic < 1 := by
  refine ⟨strictWitness_anchored_half, ?_⟩
  rw [strictWitness_dobrushinAlpha_eq_one]
  exact lt_irrefl 1

end


end UEOT.V3.Compression.TopologyChangingGoaAnchoredStability
