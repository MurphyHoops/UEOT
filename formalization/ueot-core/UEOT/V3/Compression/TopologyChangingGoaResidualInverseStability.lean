import UEOT.V3.Compression.TopologyChangingGoaMultiStepAnchoredStability

/-!
# Residual-inverse stationary-branch stability

The previous topology-changing GOA lanes progressively weakened the source-side
stability certificate from global Dobrushin contraction, to one-step anchored
contraction, and then to fixed-horizon multi-step anchored contraction.

This module weakens the certificate again.  Instead of requiring any iterate to
contract distances toward the selected branch, it assumes only an a-posteriori
error bound: distance to the selected stationary branch is controlled by the
one-step fixed-point residual.

For a selected source stationary law `muStar`, the certificate is

`D_TV(muStar, nu) <= C * D_TV(P nu, nu)`.

If `muhat` is invariant for a target kernel `Q`, then
`D_TV(P muhat, muhat)` is at most the source/target one-step row defect.  Hence
the certificate immediately yields stationary-branch tracking with radius
`C * epsilon`.

The module also proves that every fixed-horizon multi-step anchored certificate
induces such a residual inverse, and gives a strict two-state witness showing
the converse fails: a deterministic flip chain has a residual-inverse constant
`1/2`, while every iterate is an isometry around its unique stationary branch,
so no strict multi-step anchored contraction exists at any horizon.
-/

namespace UEOT.V3.Compression.TopologyChangingGoaResidualInverseStability

open UEOT.V3
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.InvariantSetGaugeInvariance
open UEOT.V3.Compression.TopologyChangingGoaMultiStepAnchoredStability

universe uS

noncomputable section

variable {S : Type uS} [Fintype S] [Nonempty S]

noncomputable local instance stateDecidableEq : DecidableEq S :=
  Classical.decEq S

local instance stateMeasurableSpace : MeasurableSpace S := ⊤

/-- A branch-local inverse error bound for the fixed-point equation.  The
selected reference law is explicitly required to be stationary. -/
structure BranchResidualInverse
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (muStar : stdSimplex ℝ S) (C : ℝ) : Prop where
  stationary : step P hP muStar = muStar
  C_nonneg : 0 ≤ C
  bound : ∀ nu,
    lawTV muStar nu ≤ C * lawTV (step P hP nu) nu

/-- **Residual-inverse stationary tracking.**

If distance to one selected source stationary branch is controlled by its
source one-step residual, then any finite stochastic target kernel with
uniform row-TV defect `epsilon` has an invariant law within `C * epsilon` of
that branch.

No source or target contraction and no recurrent-partition lock is assumed. -/
theorem residual_stationary_tracking
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (Q : Matrix S S ℝ) (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (muStar : stdSimplex ℝ S)
    (C epsilon : ℝ)
    (hres : BranchResidualInverse P hP muStar C)
    (hrow : ∀ x, crossRowTV P hP Q hQ x ≤ epsilon) :
    ∃ muhat : stdSimplex ℝ S,
      muhat ∈ invariantLawSet Q hQ ∧
      lawTV muStar muhat ≤ C * epsilon := by
  rcases exists_invariant Q hQ with ⟨muhat, hmuhat⟩
  refine ⟨muhat, hmuhat, ?_⟩
  have hkernel := tv_step_cross_le P hP Q hQ muhat epsilon hrow
  rw [hmuhat] at hkernel
  have hbound := hres.bound muhat
  exact hbound.trans
    (mul_le_mul_of_nonneg_left hkernel hres.C_nonneg)

/-- Iterating one stochastic kernel preserves its ordinary TV
nonexpansiveness. -/
theorem iterate_nonexpansive
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S) :
    ∀ n : ℕ, ∀ mu nu : stdSimplex ℝ S,
      lawTV (((step P hP)^[n]) mu) (((step P hP)^[n]) nu) ≤
        lawTV mu nu := by
  intro n
  induction n with
  | zero =>
      intro mu nu
      simp
  | succ n ih =>
      intro mu nu
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact (tv_step_nonexpansive P hP _ _).trans (ih mu nu)

/-- The TV distance between consecutive orbit iterates never exceeds the
initial one-step fixed-point residual. -/
theorem iterate_increment_le_residual
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (nu : stdSimplex ℝ S) :
    ∀ n : ℕ,
      lawTV (((step P hP)^[n + 1]) nu) (((step P hP)^[n]) nu) ≤
        lawTV (step P hP nu) nu := by
  intro n
  rw [show n + 1 = n.succ by omega, Function.iterate_succ_apply]
  exact iterate_nonexpansive P hP n (step P hP nu) nu

/-- A fixed-horizon orbit can move from its initial law by at most the horizon
times the initial one-step residual. -/
theorem iterate_to_start_le_nat_mul_residual
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (nu : stdSimplex ℝ S) :
    ∀ n : ℕ,
      lawTV (((step P hP)^[n]) nu) nu ≤
        (n : ℝ) * lawTV (step P hP nu) nu := by
  intro n
  induction n with
  | zero =>
      simp [lawTV_self_eq_zero]
  | succ n ih =>
      have htriangle := lawTV_triangle
        (((step P hP)^[n + 1]) nu)
        (((step P hP)^[n]) nu) nu
      have hincrement := iterate_increment_le_residual P hP nu n
      calc
        lawTV (((step P hP)^[n + 1]) nu) nu
            ≤ lawTV (((step P hP)^[n + 1]) nu) (((step P hP)^[n]) nu) +
              lawTV (((step P hP)^[n]) nu) nu := htriangle
        _ ≤ lawTV (step P hP nu) nu +
              (n : ℝ) * lawTV (step P hP nu) nu :=
            add_le_add hincrement ih
        _ = (n.succ : ℝ) * lawTV (step P hP nu) nu := by
            rw [Nat.cast_succ]
            ring

/-- Every multi-step anchored contraction certificate yields a branch residual
inverse.  The residual constant is `steps / (1 - alpha)`.

This formally places residual-inverse stability below fixed-horizon anchored
contraction in the certificate hierarchy. -/
theorem residualInverse_of_multistep
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (muStar : stdSimplex ℝ S)
    (hmuStar : step P hP muStar = muStar)
    (steps : ℕ) (alpha : ℝ)
    (hmulti : MultiStepAnchoredLawContraction P hP muStar steps alpha) :
    BranchResidualInverse P hP muStar
      ((steps : ℝ) / (1 - alpha)) := by
  have hden : 0 < 1 - alpha := sub_pos.mpr hmulti.alpha_lt_one
  refine ⟨hmuStar, div_nonneg (Nat.cast_nonneg _) hden.le, ?_⟩
  intro nu
  have hfixed : ((step P hP)^[steps]) muStar = muStar :=
    UEOT.V3.Compression.ContractiveFixedPoint.ContractiveWith.iterate_fixed_of_fixed
      hmuStar steps
  have hcontract := hmulti.contract nu
  rw [hfixed] at hcontract
  have horbit := iterate_to_start_le_nat_mul_residual P hP nu steps
  have htriangle := lawTV_triangle
    muStar (((step P hP)^[steps]) nu) nu
  have hbound :
      lawTV muStar nu ≤
        alpha * lawTV muStar nu +
          (steps : ℝ) * lawTV (step P hP nu) nu := by
    linarith
  rw [div_mul_eq_mul_div]
  rw [le_div_iff₀ hden]
  nlinarith [lawTV_nonneg muStar nu,
    lawTV_nonneg (step P hP nu) nu]

end


/-! ## Strictness witness: deterministic flip -/

noncomputable section

local instance flipDecidableEq : DecidableEq (Fin 2) :=
  Classical.decEq (Fin 2)

local instance flipMeasurableSpace : MeasurableSpace (Fin 2) := ⊤

/-- Deterministic two-state flip. -/
noncomputable def residualWitnessKernel : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1;
     1, 0]

theorem residualWitnessKernel_stochastic :
    residualWitnessKernel ∈ Matrix.rowStochastic ℝ (Fin 2) := by
  rw [Matrix.mem_rowStochastic_iff_sum]
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [residualWitnessKernel]
  · intro i
    fin_cases i <;> rw [Fin.sum_univ_two] <;>
      norm_num [residualWitnessKernel]

/-- Unique stationary branch of the deterministic flip. -/
noncomputable def residualWitnessLaw : stdSimplex ℝ (Fin 2) :=
  ⟨![(1 / 2 : ℝ), 1 / 2], by
    constructor
    · intro i
      fin_cases i <;> norm_num
    · rw [Fin.sum_univ_two]
      norm_num⟩

theorem residualWitnessLaw_invariant :
    step residualWitnessKernel residualWitnessKernel_stochastic
        residualWitnessLaw = residualWitnessLaw := by
  apply Subtype.ext
  funext i
  rw [step_apply, Fin.sum_univ_two]
  fin_cases i <;> norm_num [residualWitnessKernel, residualWitnessLaw]

theorem residualWitness_step_coords (nu : stdSimplex ℝ (Fin 2)) :
    (step residualWitnessKernel residualWitnessKernel_stochastic nu).1 0 =
        nu.1 1 ∧
      (step residualWitnessKernel residualWitnessKernel_stochastic nu).1 1 =
        nu.1 0 := by
  constructor <;> rw [step_apply, Fin.sum_univ_two] <;>
    simp [residualWitnessKernel]

/-- Distance from the uniform stationary branch is the one-coordinate
deviation. -/
theorem residualWitness_tv_from_stationary
    (nu : stdSimplex ℝ (Fin 2)) :
    lawTV residualWitnessLaw nu = |nu.1 0 - 1 / 2| := by
  unfold lawTV UEOT.V3.FiniteDiscountedControl.FiniteProbabilityRow.tvDist
  rw [UEOT.V3.FiniteRecurrentDecompositionStability.pmf_tv_eq_half_sum_abs]
  simp_rw [simplexPMF_toReal]
  rw [Fin.sum_univ_two]
  have hsum := stdSimplex.sum_eq_one nu
  rw [Fin.sum_univ_two] at hsum
  change nu.1 0 + nu.1 1 = 1 at hsum
  simp [residualWitnessLaw]
  have hrearrange :
      (2 : ℝ)⁻¹ - nu.1 1 = nu.1 0 - (2 : ℝ)⁻¹ := by
    norm_num at hsum ⊢
    linarith
  rw [hrearrange]
  rw [abs_sub_comm ((2 : ℝ)⁻¹) (nu.1 0)]
  ring

/-- The fixed-point residual of the flip is exactly twice the distance to its
stationary branch. -/
theorem residualWitness_tv_residual
    (nu : stdSimplex ℝ (Fin 2)) :
    lawTV
        (step residualWitnessKernel residualWitnessKernel_stochastic nu) nu =
      2 * |nu.1 0 - 1 / 2| := by
  unfold lawTV UEOT.V3.FiniteDiscountedControl.FiniteProbabilityRow.tvDist
  rw [UEOT.V3.FiniteRecurrentDecompositionStability.pmf_tv_eq_half_sum_abs]
  simp_rw [simplexPMF_toReal]
  rw [Fin.sum_univ_two]
  rcases residualWitness_step_coords nu with ⟨h0, h1⟩
  rw [h0, h1]
  have hsum := stdSimplex.sum_eq_one nu
  rw [Fin.sum_univ_two] at hsum
  change nu.1 0 + nu.1 1 = 1 at hsum
  have hforward :
      nu.1 1 - nu.1 0 = -(2 * (nu.1 0 - 1 / 2)) := by
    linarith
  have hbackward :
      nu.1 0 - nu.1 1 = 2 * (nu.1 0 - 1 / 2) := by
    linarith
  rw [hforward, hbackward, abs_neg, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- Exact residual-inverse constant `1/2` for the deterministic flip. -/
theorem residualWitness_residualInverse :
    BranchResidualInverse
      residualWitnessKernel residualWitnessKernel_stochastic
      residualWitnessLaw (1 / 2 : ℝ) := by
  refine ⟨residualWitnessLaw_invariant, by norm_num, ?_⟩
  intro nu
  rw [residualWitness_tv_from_stationary, residualWitness_tv_residual]
  have hnonneg : 0 ≤ |nu.1 0 - 1 / 2| := abs_nonneg _
  nlinarith

/-- One deterministic flip preserves distance from the uniform stationary
branch. -/
theorem residualWitness_step_isometry_from_stationary
    (nu : stdSimplex ℝ (Fin 2)) :
    lawTV residualWitnessLaw
        (step residualWitnessKernel residualWitnessKernel_stochastic nu) =
      lawTV residualWitnessLaw nu := by
  rw [residualWitness_tv_from_stationary,
    residualWitness_tv_from_stationary]
  rcases residualWitness_step_coords nu with ⟨h0, h1⟩
  rw [h0]
  have hsum := stdSimplex.sum_eq_one nu
  rw [Fin.sum_univ_two] at hsum
  change nu.1 0 + nu.1 1 = 1 at hsum
  have hneg : nu.1 1 - 1 / 2 = -(nu.1 0 - 1 / 2) := by
    linarith
  rw [hneg, abs_neg]

/-- Every finite iterate of the deterministic flip is an isometry around the
selected stationary branch. -/
theorem residualWitness_iterate_distance_preserved
    (nu : stdSimplex ℝ (Fin 2)) :
    ∀ n : ℕ,
      lawTV residualWitnessLaw
          (((step residualWitnessKernel residualWitnessKernel_stochastic)^[n]) nu) =
        lawTV residualWitnessLaw nu := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      rw [residualWitness_step_isometry_from_stationary, ih]

private theorem residualWitness_pureZero_distance :
    lawTV residualWitnessLaw (pureSimplex (0 : Fin 2)) = 1 / 2 := by
  rw [residualWitness_tv_from_stationary]
  have hpure : (pureSimplex (0 : Fin 2)).1 0 = 1 := by
    change Function.update (fun _ : Fin 2 => (0 : ℝ)) 0 1 0 = 1
    simp
  rw [hpure]
  norm_num

/-- No strict fixed-horizon multi-step anchored contraction can hold for this
same selected branch, at any horizon or factor. -/
theorem residualWitness_no_multistep_anchored
    (steps : ℕ) (alpha : ℝ) :
    ¬ MultiStepAnchoredLawContraction
      residualWitnessKernel residualWitnessKernel_stochastic
      residualWitnessLaw steps alpha := by
  intro hmulti
  have hcontract := hmulti.contract (pureSimplex (0 : Fin 2))
  have hfixed :
      ((step residualWitnessKernel residualWitnessKernel_stochastic)^[steps])
          residualWitnessLaw = residualWitnessLaw :=
    UEOT.V3.Compression.ContractiveFixedPoint.ContractiveWith.iterate_fixed_of_fixed
      residualWitnessLaw_invariant steps
  rw [hfixed] at hcontract
  have hpreserved := residualWitness_iterate_distance_preserved
    (pureSimplex (0 : Fin 2)) steps
  rw [hpreserved, residualWitness_pureZero_distance] at hcontract
  nlinarith [hmulti.alpha_lt_one]

/-- **Strictness theorem.**  A branch residual inverse can exist even when no
strict fixed-horizon multi-step anchored contraction exists at any horizon.

Thus residual-inverse stability is a genuine weakening of the entire fixed-
horizon anchored hierarchy, not a renaming of it. -/
theorem residualInverse_strictly_weaker_witness :
    BranchResidualInverse
        residualWitnessKernel residualWitnessKernel_stochastic
        residualWitnessLaw (1 / 2 : ℝ) ∧
      ∀ (steps : ℕ) (alpha : ℝ),
        ¬ MultiStepAnchoredLawContraction
          residualWitnessKernel residualWitnessKernel_stochastic
          residualWitnessLaw steps alpha := by
  exact ⟨residualWitness_residualInverse,
    residualWitness_no_multistep_anchored⟩

end


end UEOT.V3.Compression.TopologyChangingGoaResidualInverseStability
