import UEOT.V3.Compression.TopologyChangingGoaAnchoredStability

/-!
# Multi-step anchored stationary-branch stability

One-step anchored contraction can still be stronger than necessary.  A finite
Markov system may fail to contract a selected stationary branch after one step
while a fixed iterate does contract it strictly.

This module isolates that weaker certificate and proves the corresponding
stationary perturbation theorem.

The main extra ingredient is a finite-horizon cross-kernel estimate.  Any
stochastic Markov step is nonexpansive in total variation, so if corresponding
rows of `P` and `Q` are uniformly within `epsilon`, then from the same initial
law

`D_TV(P^m mu, Q^m mu) <= m * epsilon`.

Combining this with an `m`-step anchored contraction factor `alpha < 1` yields

`D_TV(muStar, muhat) <= (m * epsilon) / (1 - alpha)`

for some target invariant law `muhat`.

The module also contains an explicit three-state strictness witness: no
one-step anchored factor below one exists around the selected stationary law,
but two steps collapse every law exactly onto that branch, giving two-step
anchored factor zero.
-/

namespace UEOT.V3.Compression.TopologyChangingGoaMultiStepAnchoredStability

open UEOT.V3
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.InvariantSetGaugeInvariance
open UEOT.V3.Compression.TopologyChangingGoaAnchoredStability

universe uS

noncomputable section

variable {S : Type uS} [Fintype S] [Nonempty S]

noncomputable local instance stateDecidableEq : DecidableEq S :=
  Classical.decEq S

local instance stateMeasurableSpace : MeasurableSpace S := ⊤

/-- Self total-variation distance vanishes. -/
theorem lawTV_self_eq_zero (mu : stdSimplex ℝ S) :
    lawTV mu mu = 0 := by
  unfold lawTV UEOT.V3.FiniteDiscountedControl.FiniteProbabilityRow.tvDist
  exact UEOT.V3.TotalVariation.tvDist_self_eq_zero _

/-- Every finite stochastic kernel has Dobrushin coefficient at most one. -/
theorem dobrushinAlpha_le_one
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S) :
    dobrushinAlpha P hP ≤ 1 := by
  unfold dobrushinAlpha
  apply Finset.sup'_le
  intro z hz
  unfold rowTV UEOT.V3.FiniteDiscountedControl.FiniteProbabilityRow.tvDist
  exact UEOT.V3.TotalVariation.tvDist_le_one _ _

/-- Any stochastic Markov step is nonexpansive in finite total variation. -/
theorem tv_step_nonexpansive
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (mu nu : stdSimplex ℝ S) :
    lawTV (step P hP mu) (step P hP nu) ≤ lawTV mu nu := by
  have hstep := tv_step_le_dobrushin P hP mu nu
  have halpha := dobrushinAlpha_le_one P hP
  have htv := lawTV_nonneg mu nu
  calc
    lawTV (step P hP mu) (step P hP nu)
        ≤ dobrushinAlpha P hP * lawTV mu nu := hstep
    _ ≤ 1 * lawTV mu nu :=
      mul_le_mul_of_nonneg_right halpha htv
    _ = lawTV mu nu := one_mul _

/-- Uniform one-step row-TV error accumulates at most linearly over a fixed
number of steps when the two chains start from the same law. -/
theorem iterate_cross_le_nat_mul
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (Q : Matrix S S ℝ) (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (epsilon : ℝ)
    (hrow : ∀ x, crossRowTV P hP Q hQ x ≤ epsilon)
    (mu : stdSimplex ℝ S) :
    ∀ n : ℕ,
      lawTV (((step P hP)^[n]) mu) (((step Q hQ)^[n]) mu) ≤
        (n : ℝ) * epsilon := by
  intro n
  induction n with
  | zero =>
      simp [lawTV_self_eq_zero]
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      calc
        lawTV
            (step P hP (((step P hP)^[n]) mu))
            (step Q hQ (((step Q hQ)^[n]) mu))
            ≤ lawTV
                (step P hP (((step P hP)^[n]) mu))
                (step P hP (((step Q hQ)^[n]) mu)) +
              lawTV
                (step P hP (((step Q hQ)^[n]) mu))
                (step Q hQ (((step Q hQ)^[n]) mu)) :=
          lawTV_triangle _ _ _
        _ ≤ lawTV (((step P hP)^[n]) mu) (((step Q hQ)^[n]) mu) + epsilon := by
          exact add_le_add
            (tv_step_nonexpansive P hP _ _)
            (tv_step_cross_le P hP Q hQ _ epsilon hrow)
        _ ≤ (n : ℝ) * epsilon + epsilon := by
          linarith
        _ = ((n : ℝ) + 1) * epsilon := by ring
        _ = (n.succ : ℝ) * epsilon := by rw [Nat.cast_succ]

/-- Strict contraction toward one selected law after a fixed positive number of
steps.  No one-step contraction is required. -/
structure MultiStepAnchoredLawContraction
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (muStar : stdSimplex ℝ S) (steps : ℕ) (alpha : ℝ) : Prop where
  steps_pos : 0 < steps
  alpha_nonneg : 0 ≤ alpha
  alpha_lt_one : alpha < 1
  contract : ∀ nu,
    lawTV (((step P hP)^[steps]) muStar) (((step P hP)^[steps]) nu) ≤
      alpha * lawTV muStar nu

/-- Ordinary one-step anchored contraction embeds into the multi-step interface
at horizon one. -/
theorem multistep_one_of_anchored
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (muStar : stdSimplex ℝ S) (alpha : ℝ)
    (hanchor : AnchoredLawContraction P hP muStar alpha) :
    MultiStepAnchoredLawContraction P hP muStar 1 alpha := by
  refine ⟨by norm_num, hanchor.alpha_nonneg, hanchor.alpha_lt_one, ?_⟩
  intro nu
  simpa using hanchor.contract nu

/-- **Multi-step anchored stationary-branch perturbation theorem.**

If the selected source invariant branch contracts after `steps` iterations by
`alpha < 1`, then any finite stochastic target kernel within uniform row-TV
error `epsilon` has an invariant law within

`(steps * epsilon) / (1 - alpha)`

of that source branch.

The target need not preserve source recurrent topology and need not itself be
contractive. -/
theorem multistep_anchored_stationary_tracking
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (Q : Matrix S S ℝ) (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (muStar : stdSimplex ℝ S)
    (hmuStar : muStar ∈ invariantLawSet P hP)
    (steps : ℕ) (alpha epsilon : ℝ)
    (hmulti : MultiStepAnchoredLawContraction P hP muStar steps alpha)
    (hrow : ∀ x, crossRowTV P hP Q hQ x ≤ epsilon) :
    ∃ muhat : stdSimplex ℝ S,
      muhat ∈ invariantLawSet Q hQ ∧
      lawTV muStar muhat ≤
        ((steps : ℝ) * epsilon) / (1 - alpha) := by
  rcases exists_invariant Q hQ with ⟨muhat, hmuhat⟩
  refine ⟨muhat, hmuhat, ?_⟩
  have hPfixed : ((step P hP)^[steps]) muStar = muStar :=
    UEOT.V3.Compression.ContractiveFixedPoint.ContractiveWith.iterate_fixed_of_fixed
      hmuStar steps
  have hQfixed : ((step Q hQ)^[steps]) muhat = muhat :=
    UEOT.V3.Compression.ContractiveFixedPoint.ContractiveWith.iterate_fixed_of_fixed
      hmuhat steps
  have hcontract := hmulti.contract muhat
  rw [hPfixed] at hcontract
  have hkernel := iterate_cross_le_nat_mul
    P hP Q hQ epsilon hrow muhat steps
  rw [hQfixed] at hkernel
  have htri := lawTV_triangle
    muStar (((step P hP)^[steps]) muhat) muhat
  have hbound :
      lawTV muStar muhat ≤
        alpha * lawTV muStar muhat + (steps : ℝ) * epsilon := by
    linarith
  have hden : 0 < 1 - alpha := sub_pos.mpr hmulti.alpha_lt_one
  rw [le_div_iff₀ hden]
  nlinarith

end


/-! ## Strictness witness: no one-step anchored contraction, exact two-step collapse -/

noncomputable section

local instance threeStateDecidableEq : DecidableEq (Fin 3) :=
  Classical.decEq (Fin 3)

local instance threeStateMeasurableSpace : MeasurableSpace (Fin 3) := ⊤

@[simp] private theorem fin3_zero_ne_one : (0 : Fin 3) ≠ 1 := by omega
@[simp] private theorem fin3_zero_ne_two : (0 : Fin 3) ≠ 2 := by omega
@[simp] private theorem fin3_one_ne_zero : (1 : Fin 3) ≠ 0 := by omega
@[simp] private theorem fin3_one_ne_two : (1 : Fin 3) ≠ 2 := by omega
@[simp] private theorem fin3_two_ne_zero : (2 : Fin 3) ≠ 0 := by omega
@[simp] private theorem fin3_two_ne_one : (2 : Fin 3) ≠ 1 := by omega

/-- Explicit point mass at state `0`, used as the selected stationary branch. -/
noncomputable def multiStepWitnessLaw : stdSimplex ℝ (Fin 3) :=
  ⟨fun i => if i = 0 then 1 else 0, by
    constructor
    · intro i
      by_cases hi : i = 0 <;> simp [hi]
    · rw [Fin.sum_univ_three]
      simp⟩

/-- Explicit comparison point mass at state `1`. -/
noncomputable def multiStepWitnessDeltaOne : stdSimplex ℝ (Fin 3) :=
  ⟨fun i => if i = 1 then 1 else 0, by
    constructor
    · intro i
      by_cases hi : i = 1 <;> simp [hi]
    · rw [Fin.sum_univ_three]
      simp⟩

/-- Explicit point mass at state `2`. -/
noncomputable def multiStepWitnessDeltaTwo : stdSimplex ℝ (Fin 3) :=
  ⟨fun i => if i = 2 then 1 else 0, by
    constructor
    · intro i
      by_cases hi : i = 2 <;> simp [hi]
    · rw [Fin.sum_univ_three]
      simp⟩

/-- State `0` is absorbing, state `1` moves to state `2`, and state `2` moves
to state `0`.  One step can preserve full TV distance from the selected branch,
but two steps send every state to `0`. -/
noncomputable def multiStepWitnessKernel : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j =>
    if i = 0 then
      if j = 0 then 1 else 0
    else if i = 1 then
      if j = 2 then 1 else 0
    else
      if j = 0 then 1 else 0

theorem multiStepWitnessKernel_stochastic :
    multiStepWitnessKernel ∈ Matrix.rowStochastic ℝ (Fin 3) := by
  rw [Matrix.mem_rowStochastic_iff_sum]
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [multiStepWitnessKernel]
  · intro i
    fin_cases i <;> rw [Fin.sum_univ_three] <;>
      simp [multiStepWitnessKernel]

theorem multiStepWitnessLaw_invariant :
    step multiStepWitnessKernel multiStepWitnessKernel_stochastic
        multiStepWitnessLaw = multiStepWitnessLaw := by
  apply Subtype.ext
  funext j
  rw [step_apply, Fin.sum_univ_three]
  fin_cases j <;>
    simp [multiStepWitnessKernel, multiStepWitnessLaw]

private theorem multiStepWitness_step_zero (nu : stdSimplex ℝ (Fin 3)) :
    (step multiStepWitnessKernel multiStepWitnessKernel_stochastic nu).1 0 =
      nu.1 0 + nu.1 2 := by
  rw [step_apply, Fin.sum_univ_three]
  simp [multiStepWitnessKernel]

private theorem multiStepWitness_step_one (nu : stdSimplex ℝ (Fin 3)) :
    (step multiStepWitnessKernel multiStepWitnessKernel_stochastic nu).1 1 = 0 := by
  rw [step_apply, Fin.sum_univ_three]
  simp [multiStepWitnessKernel]

private theorem multiStepWitness_step_two (nu : stdSimplex ℝ (Fin 3)) :
    (step multiStepWitnessKernel multiStepWitnessKernel_stochastic nu).1 2 =
      nu.1 1 := by
  rw [step_apply, Fin.sum_univ_three]
  simp [multiStepWitnessKernel]

/-- Two steps collapse every initial law exactly onto the selected stationary
branch. -/
theorem multiStepWitness_twoStep_collapse
    (nu : stdSimplex ℝ (Fin 3)) :
    ((step multiStepWitnessKernel multiStepWitnessKernel_stochastic)^[2]) nu =
      multiStepWitnessLaw := by
  rw [show ((step multiStepWitnessKernel multiStepWitnessKernel_stochastic)^[2]) nu =
      step multiStepWitnessKernel multiStepWitnessKernel_stochastic
        (step multiStepWitnessKernel multiStepWitnessKernel_stochastic nu) by
      simp [Function.iterate_succ_apply']]
  apply Subtype.ext
  funext j
  fin_cases j
  · change
      (step multiStepWitnessKernel multiStepWitnessKernel_stochastic
        (step multiStepWitnessKernel multiStepWitnessKernel_stochastic nu)).1 0 =
        multiStepWitnessLaw.1 0
    rw [multiStepWitness_step_zero]
    rw [multiStepWitness_step_zero, multiStepWitness_step_two]
    have hsum := stdSimplex.sum_eq_one nu
    rw [Fin.sum_univ_three] at hsum
    change nu.1 0 + nu.1 1 + nu.1 2 = 1 at hsum
    have hlaw : multiStepWitnessLaw.1 0 = 1 := by
      simp [multiStepWitnessLaw]
    rw [hlaw]
    linarith
  · change
      (step multiStepWitnessKernel multiStepWitnessKernel_stochastic
        (step multiStepWitnessKernel multiStepWitnessKernel_stochastic nu)).1 1 =
        multiStepWitnessLaw.1 1
    rw [multiStepWitness_step_one]
    simp [multiStepWitnessLaw]
  · change
      (step multiStepWitnessKernel multiStepWitnessKernel_stochastic
        (step multiStepWitnessKernel multiStepWitnessKernel_stochastic nu)).1 2 =
        multiStepWitnessLaw.1 2
    rw [multiStepWitness_step_two]
    rw [multiStepWitness_step_one]
    simp [multiStepWitnessLaw]

/-- Exact two-step anchored factor zero. -/
theorem multiStepWitness_twoStep_anchored_zero :
    MultiStepAnchoredLawContraction
      multiStepWitnessKernel multiStepWitnessKernel_stochastic
      multiStepWitnessLaw 2 0 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  intro nu
  rw [multiStepWitness_twoStep_collapse nu]
  rw [multiStepWitness_twoStep_collapse multiStepWitnessLaw]
  rw [lawTV_self_eq_zero]
  simp

private theorem multiStepWitness_step_pureOne :
    step multiStepWitnessKernel multiStepWitnessKernel_stochastic
        multiStepWitnessDeltaOne =
      multiStepWitnessDeltaTwo := by
  apply Subtype.ext
  funext j
  rw [step_apply, Fin.sum_univ_three]
  fin_cases j <;>
    simp [multiStepWitnessKernel, multiStepWitnessDeltaOne,
      multiStepWitnessDeltaTwo]

private theorem multiStepWitness_lawTV_pureZero_pureOne :
    lawTV multiStepWitnessLaw multiStepWitnessDeltaOne = 1 := by
  unfold lawTV UEOT.V3.FiniteDiscountedControl.FiniteProbabilityRow.tvDist
  rw [UEOT.V3.FiniteRecurrentDecompositionStability.pmf_tv_eq_half_sum_abs]
  simp_rw [simplexPMF_toReal]
  rw [Fin.sum_univ_three]
  simp [multiStepWitnessLaw, multiStepWitnessDeltaOne]
  norm_num

private theorem multiStepWitness_lawTV_pureZero_pureTwo :
    lawTV multiStepWitnessLaw multiStepWitnessDeltaTwo = 1 := by
  unfold lawTV UEOT.V3.FiniteDiscountedControl.FiniteProbabilityRow.tvDist
  rw [UEOT.V3.FiniteRecurrentDecompositionStability.pmf_tv_eq_half_sum_abs]
  simp_rw [simplexPMF_toReal]
  rw [Fin.sum_univ_three]
  simp [multiStepWitnessLaw, multiStepWitnessDeltaTwo]
  norm_num

/-- No strict one-step anchored certificate can hold around the same selected
stationary law.  The comparison law `delta_1` remains TV-distance one after one
step because it moves to `delta_2`. -/
theorem multiStepWitness_no_oneStep_anchored
    (alpha : ℝ) :
    ¬ AnchoredLawContraction
      multiStepWitnessKernel multiStepWitnessKernel_stochastic
      multiStepWitnessLaw alpha := by
  intro hanchor
  have hc := hanchor.contract multiStepWitnessDeltaOne
  rw [multiStepWitnessLaw_invariant, multiStepWitness_step_pureOne] at hc
  change lawTV multiStepWitnessLaw multiStepWitnessDeltaTwo ≤
    alpha * lawTV multiStepWitnessLaw multiStepWitnessDeltaOne at hc
  rw [multiStepWitness_lawTV_pureZero_pureTwo,
    multiStepWitness_lawTV_pureZero_pureOne] at hc
  nlinarith [hanchor.alpha_lt_one]

/-- Machine-checked strictness: fixed-horizon multi-step anchored contraction
can hold even when every strict one-step anchored certificate fails. -/
theorem multistep_strictly_weaker_witness :
    MultiStepAnchoredLawContraction
        multiStepWitnessKernel multiStepWitnessKernel_stochastic
        multiStepWitnessLaw 2 0 ∧
      ∀ alpha : ℝ,
        ¬ AnchoredLawContraction
          multiStepWitnessKernel multiStepWitnessKernel_stochastic
          multiStepWitnessLaw alpha := by
  exact ⟨multiStepWitness_twoStep_anchored_zero,
    multiStepWitness_no_oneStep_anchored⟩

end


end UEOT.V3.Compression.TopologyChangingGoaMultiStepAnchoredStability
