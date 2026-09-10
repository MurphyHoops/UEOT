import UEOT.V3.ViabilityStrategy
import UEOT.V3.ViabilityTrajectory

/-!
# P-PER-03 exact finite source wrapper

This module packages the finite deletion recursion, its exact winning-set
semantics, the stationary deterministic preserving selector, and the genuine
Ionescu--Tulcea all-times persistence witness into one source-facing theorem.

For finite PMF dynamics, `winningSet` uses the equivalent support-tree form of
almost-sure safety: an unsafe finite prefix has positive probability exactly
when all of its transition edges have positive PMF mass.
-/

namespace UEOT.V3.ViabilitySource

open Set
open UEOT.V3.ViabilityKernel
open UEOT.V3.ViabilityStrategy
open UEOT.V3.ViabilityTrajectory

universe uX uA

variable {X : Type uX} {A : Type uA}
variable [Fintype X] [Fintype A]
variable [MeasurableSpace X] [MeasurableSingletonClass X]

/-- **P-PER-03 (finite stochastic viability kernel).**

Starting from `K₀ = V` and repeatedly deleting states lacking an action whose
next-state law is supported on the current set, the recursion stabilizes after
finitely many steps.  The stabilized set is exactly the set of initial states
admitting a finite-history-dependent sure-safe strategy.  It also admits a
deterministic stationary preserving policy, and every initial law supported on
the kernel admits such a stationary policy whose genuine infinite trajectory
remains in the kernel with probability one. -/
theorem p_per_03
    [Nonempty A]
    (P : X → A → PMF X) (V : Set X) :
    ∃ (n : ℕ) (K : Set X),
      K = viabilityIter P V n ∧
      K ⊆ V ∧
      viabilityStep P K = K ∧
      K = winningSet P V ∧
      (∃ π : X → A, ∀ x ∈ K, StaysIn (P x (π x)) K) ∧
      (∀ μ : PMF X, StaysIn μ K →
        ∃ π : X → A,
          stationaryTrajMeasure P π μ {ω | ∀ k : ℕ, ω k ∈ K} = 1) := by
  obtain ⟨n, hfix, hwin⟩ := exists_stabilized_eq_winningSet P V
  have hKV : viabilityIter P V n ⊆ V := by
    simpa using (viabilityIter_antitone P V (Nat.zero_le n))
  refine ⟨n, viabilityIter P V n, rfl, hKV, hfix, hwin, ?_, ?_⟩
  · exact exists_stationary_policy_of_fixed P hfix
  · intro μ hμ
    exact exists_stationary_policy_all_times_of_fixed
      P hfix μ hμ (Set.toFinite (viabilityIter P V n)).measurableSet

end UEOT.V3.ViabilitySource
