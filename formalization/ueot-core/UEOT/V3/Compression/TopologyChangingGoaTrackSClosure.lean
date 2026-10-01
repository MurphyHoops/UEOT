import UEOT.V3.Compression.TopologyChangingGoaFunctionalGraphClassification
import UEOT.V3.Compression.TopologyChangingGoaRecurrentClassUniqueness

/-!
# Track S closure interface

This module is the final synthesis surface for the post-FINAL Track-S research
lane. It introduces no new primitive. Instead it exposes a compact machine-
checked interface relating four views of long-run stability on finite systems:
strict Dobrushin mixing, canonical direct-L1 residual isolation, uniqueness of
invariant probability semantics, and recurrent topology.

The general finite-Markov core is `kappa1*(P) > 0` iff unique invariant law.
Strict Dobrushin mixing is only a sufficient mechanism. For certified recurrent
decompositions, positivity is exactly one recurrent class; for deterministic
functional graphs, it is exactly one recurrent periodic orbit. Unique semantics
also unlocks the canonical kernel-specific stationary tracking radius.

This is post-FINAL, uncounted Track-S synthesis and does not change the frozen
four-generator core.
-/

namespace UEOT.V3.Compression.TopologyChangingGoaTrackSClosure

open UEOT.V3
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.InvariantSetGaugeInvariance
open UEOT.V3.Compression.TopologyChangingGoaRestrictedResidualAdapter
open UEOT.V3.Compression.TopologyChangingGoaL1ResidualConorm
open UEOT.V3.Compression.TopologyChangingGoaDobrushinL1Bridge
open UEOT.V3.Compression.TopologyChangingGoaInvariantUniquenessIsolation
open UEOT.V3.Compression.TopologyChangingGoaFunctionalGraphClassification
open UEOT.V3.Compression.TopologyChangingGoaRecurrentClassUniqueness

universe u
noncomputable section
variable {S : Type u} [Fintype S] [Nonempty S]
noncomputable local instance : DecidableEq S := Classical.decEq S
local instance : MeasurableSpace S := ⊤

/-- Strict one-step Dobrushin mixing is sufficient for unique invariant
probability semantics, but is not the defining condition. -/
theorem unique_invariant_law_of_strict_dobrushin
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hcard : 1 < Fintype.card S)
    (halpha : dobrushinAlpha P hP < 1) :
    ∃! mu : stdSimplex ℝ S, mu ∈ invariantLawSet P hP := by
  have hconorm : 0 < l1ResidualConorm P := by
    have hmargin : 0 < 1 - dobrushinAlpha P hP := sub_pos.mpr halpha
    have hle := one_sub_dobrushin_le_l1ResidualConorm P hP hcard halpha
    linarith
  exact (l1ResidualConorm_pos_iff_unique_invariant_law P hP hcard).1 hconorm

/-- Unique finite invariant semantics is enough to unlock the canonical
kernel-specific L1 stationary-tracking radius. -/
theorem canonical_l1_stationary_tracking_of_unique_invariant_law
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (Q : Matrix S S ℝ) (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (muStar : stdSimplex ℝ S)
    (hmuStar : muStar ∈ invariantLawSet P hP)
    (hunique : ∃! mu : stdSimplex ℝ S, mu ∈ invariantLawSet P hP)
    (epsilon : ℝ)
    (hcard : 1 < Fintype.card S)
    (hrow : ∀ x, crossRowTV P hP Q hQ x ≤ epsilon) :
    ∃ muhat : stdSimplex ℝ S,
      muhat ∈ invariantLawSet Q hQ ∧
      lawTV muStar muhat ≤ epsilon / l1ResidualConorm P := by
  have hsub : (invariantLawSet P hP).Subsingleton :=
    (invariantLawSet_subsingleton_iff_existsUnique P hP).2 hunique
  have hinj : Function.Injective (zeroSumResidualLinear P) :=
    (restricted_injective_iff_invariantLawSet_subsingleton P hP).2 hsub
  have hfix : step P hP muStar = muStar := by
    simpa [mem_invariantLawSet] using hmuStar
  exact canonical_l1_stationary_tracking
    P hP Q hQ muStar hfix epsilon hcard hinj hrow

/-- The final qualitative Track-S equivalence for arbitrary nontrivial finite
stochastic kernels. -/
theorem finite_markov_isolation_iff_unique_semantics
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hcard : 1 < Fintype.card S) :
    0 < l1ResidualConorm P ↔
      ∃! mu : stdSimplex ℝ S, mu ∈ invariantLawSet P hP :=
  l1ResidualConorm_pos_iff_unique_invariant_law P hP hcard

/-- Deterministic Track-S closure: operator isolation, unique invariant
semantics, and a single recurrent periodic orbit are the same qualitative
condition. -/
theorem deterministic_isolation_unique_semantics_periodic_orbit
    (f : S → S) (hcard : 1 < Fintype.card S) :
    (0 < l1ResidualConorm (detKernel f) ↔ HasUniquePeriodicOrbit f) ∧
    ((∃! mu : stdSimplex ℝ S,
        mu ∈ invariantLawSet (detKernel f) (detKernel_stochastic f)) ↔
      HasUniquePeriodicOrbit f) := by
  exact ⟨
    detKernel_l1ResidualConorm_pos_iff_unique_periodic_orbit f hcard,
    detKernel_unique_invariant_law_iff_unique_periodic_orbit f
  ⟩

/-- For deterministic kernels the one-step Dobrushin observable collapses to
a constant/nonconstant dichotomy, so it is strictly coarser than recurrent
orbit isolation. -/
theorem deterministic_dobrushin_dichotomy (f : S → S) :
    (dobrushinAlpha (detKernel f) (detKernel_stochastic f) = 0 ∧
      ∃ a : S, ∀ x, f x = a) ∨
    (dobrushinAlpha (detKernel f) (detKernel_stochastic f) = 1 ∧
      ∃ x y : S, f x ≠ f y) :=
  detKernel_dobrushin_dichotomy f

/-- For any certified finite recurrent decomposition on a nontrivial full
state space, positive canonical residual isolation is exactly uniqueness of the
recurrent-class index. -/
theorem certified_recurrent_decomposition_isolation_iff_unique_class
    {T : Type*} {R : Type*} {C : Type*}
    [Fintype T] [DecidableEq T] [Fintype R] [DecidableEq R]
    [Fintype C] [DecidableEq C]
    {K : UEOT.V3.FiniteRecurrentDecompositionStability.RecurrentPartition R C}
    (M : UEOT.V3.FiniteRecurrentDecompositionStability.FiniteRecurrentDecomposition
      (T := T) K)
    (hcard : 1 < Fintype.card
      (UEOT.V3.FiniteRecurrentDecompositionStability.FullState T R)) :
    0 < l1ResidualConorm M.P ↔ Subsingleton C :=
  l1ResidualConorm_pos_iff_recurrentClass_subsingleton M hcard

/-- Audit-hardened exact-cardinality form: for a nontrivial certified finite
recurrent decomposition, positive canonical residual isolation is equivalent
to the recurrent-class index having cardinality exactly one. -/
theorem certified_recurrent_decomposition_isolation_iff_exactly_one_class
    {T : Type*} {R : Type*} {C : Type*}
    [Fintype T] [DecidableEq T] [Fintype R] [DecidableEq R]
    [Fintype C] [DecidableEq C]
    {K : UEOT.V3.FiniteRecurrentDecompositionStability.RecurrentPartition R C}
    (M : UEOT.V3.FiniteRecurrentDecompositionStability.FiniteRecurrentDecomposition
      (T := T) K)
    (hcard : 1 < Fintype.card
      (UEOT.V3.FiniteRecurrentDecompositionStability.FullState T R)) :
    0 < l1ResidualConorm M.P ↔ Fintype.card C = 1 :=
  l1ResidualConorm_pos_iff_recurrentClass_card_eq_one M hcard

end
end UEOT.V3.Compression.TopologyChangingGoaTrackSClosure
