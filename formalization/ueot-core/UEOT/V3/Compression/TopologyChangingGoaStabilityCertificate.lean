import UEOT.V3.Compression.TopologyChangingGoaSemantics
import UEOT.V3.Compression.ContractiveFixedPoint

/-!
# Positive stability certificate across topology-changing GOA regimes

`TopologyChangingGoaSemantics` proves that recurrent topology may genuinely
merge/split and that arbitrarily small support-opening perturbations can leave a
prescribed source invariant law a fixed TV distance from every target invariant
law.  That is a directional lower/Hausdorff-type no-go, not a claim that every
stationary-law continuity notion fails.

This module records the corresponding positive certificate already latent in
M-CF / P-GOA-02:

* if the **source** Markov operator has a strict Dobrushin contraction margin
  `alpha(P) < 1`, then every source invariant law can be tracked by at least one
  target invariant law under a row-TV kernel perturbation;
* the target need not preserve the same recurrent partition and need not itself
  be contractive;
* finite-state invariant-law existence for the target comes from frozen
  P-GOA-01;
* the tracking radius is `epsilon / (1 - alpha(P))`.

The two-state bifurcation counterexample is then shown to lie exactly on the
boundary `alpha(P) = 1`, explaining why it does not contradict the positive
certificate.

This is a sufficient stability certificate.  No claim is made that strict
Dobrushin contraction is the weakest possible assumption.
-/

namespace UEOT.V3.Compression.TopologyChangingGoaStabilityCertificate

open UEOT.V3
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.InvariantSetGaugeInvariance
open UEOT.V3.Compression.ContractiveFixedPoint
open UEOT.V3.Compression.TopologyChangingGoaSemantics

universe uS

noncomputable section

variable {S : Type uS} [Fintype S] [Nonempty S]

noncomputable local instance stateDecidableEq : DecidableEq S :=
  Classical.decEq S

/-- **Prescribed-source-law tracking under a source contraction margin.**

For any invariant law `mu` of a strictly Dobrushin-contractive source kernel,
every finite stochastic target kernel with uniformly small row-TV defect has at
least one invariant law `muhat` inside the standard perturbation tube.

Only the source requires a contraction margin.  Target invariant existence is
supplied by P-GOA-01, and no common recurrent partition is assumed. -/
theorem prescribedInvariant_tracked_of_dobrushin
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
  rcases exists_invariant Q hQ with ⟨muhat, hmuhat⟩
  refine ⟨muhat, hmuhat, ?_⟩
  exact stationary_perturbation_via_mcf
    P hP Q hQ halpha mu muhat hmu hmuhat epsilon hrow

/-- Set-valued lower tracking formulation: strict source contraction turns the
direction that failed in the topology-bifurcation counterexample into a valid
uniform statement for **every** source invariant law. -/
theorem invariantLawSet_lower_tracking_of_dobrushin
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (Q : Matrix S S ℝ) (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (halpha : dobrushinAlpha P hP < 1)
    (epsilon : ℝ)
    (hrow : ∀ x, crossRowTV P hP Q hQ x ≤ epsilon) :
    ∀ mu ∈ invariantLawSet P hP,
      ∃ muhat ∈ invariantLawSet Q hQ,
        lawTV mu muhat ≤ epsilon / (1 - dobrushinAlpha P hP) := by
  intro mu hmu
  exact prescribedInvariant_tracked_of_dobrushin
    P hP Q hQ halpha mu hmu epsilon hrow

end


/-! ## The two-state no-go source lies exactly at the contraction boundary -/

noncomputable section

local instance twoStateDecidableEq : DecidableEq (Fin 2) :=
  Classical.decEq (Fin 2)

local instance twoStateMeasurableSpace : MeasurableSpace (Fin 2) := ⊤

/-- The two absorbing source rows are TV-distance one apart. -/
theorem twoStateSource_rowTV_zero_one :
    rowTV twoStateSourceKernel twoStateSourceKernel_stochastic 0 1 = 1 := by
  unfold rowTV UEOT.V3.FiniteDiscountedControl.FiniteProbabilityRow.tvDist
  rw [UEOT.V3.FiniteRecurrentDecompositionStability.pmf_tv_eq_half_sum_abs]
  simp_rw [rowPMF_toReal]
  rw [Fin.sum_univ_two]
  norm_num [twoStateSourceKernel]

/-- Every Dobrushin row distance is at most one, hence so is the finite supremum
defining the coefficient. -/
theorem twoStateSource_dobrushinAlpha_le_one :
    dobrushinAlpha twoStateSourceKernel twoStateSourceKernel_stochastic ≤ 1 := by
  unfold dobrushinAlpha
  apply Finset.sup'_le
  intro z hz
  unfold rowTV UEOT.V3.FiniteDiscountedControl.FiniteProbabilityRow.tvDist
  exact UEOT.V3.TotalVariation.tvDist_le_one _ _

/-- The bifurcation source is exactly noncontractive in Dobrushin TV:
`alpha(P) = 1`. -/
theorem twoStateSource_dobrushinAlpha_eq_one :
    dobrushinAlpha twoStateSourceKernel twoStateSourceKernel_stochastic = 1 := by
  apply le_antisymm twoStateSource_dobrushinAlpha_le_one
  have h := rowTV_le_dobrushinAlpha
    twoStateSourceKernel twoStateSourceKernel_stochastic
      (0 : Fin 2) (1 : Fin 2)
  rw [twoStateSource_rowTV_zero_one] at h
  exact h

/-- Consequently the two-state no-go example cannot satisfy the positive
strict-contraction certificate. -/
theorem twoStateSource_not_dobrushin_contractive :
    ¬ dobrushinAlpha twoStateSourceKernel twoStateSourceKernel_stochastic < 1 := by
  rw [twoStateSource_dobrushinAlpha_eq_one]
  exact lt_irrefl 1

end


end UEOT.V3.Compression.TopologyChangingGoaStabilityCertificate
