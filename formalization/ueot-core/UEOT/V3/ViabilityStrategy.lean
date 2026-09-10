import UEOT.V3.ViabilityKernel

/-!
# P-PER-03 strategy semantics for finite viability

The source theorem characterizes the stabilized deletion kernel as the set of
states from which a strategy can keep the controlled chain in the persistence
domain forever with probability one.  This module supplies the missing general
strategy semantics.  A strategy may depend on the whole finite state history;
probability-one safety is represented by safety of every history reachable
through positive-probability support edges.

The main result proves that this history-dependent winning set is exactly the
finite stabilized viability kernel.  The companion `ViabilityTrajectory`
module realizes the stationary witness as a genuine Ionescu--Tulcea path law.
-/

namespace UEOT.V3.ViabilityStrategy

open Set
open UEOT.V3.ViabilityKernel

universe uX uA

variable {X : Type uX} {A : Type uA}
variable [Fintype X] [Fintype A]

/-- A deterministic strategy with unrestricted finite-state-history memory.
The list stores previous states in reverse chronological order; the first
argument is the current state. -/
abbrev HistoryStrategy (X : Type uX) (A : Type uA) :=
  X → List X → A

/-- Support-tree reachability under a history-dependent strategy.  Traversing
only PMF support edges is exactly the finite-state semantics relevant to an
almost-sure safety objective. -/
inductive Reachable
    (P : X → A → PMF X) (σ : HistoryStrategy X A) (x₀ : X) :
    X → List X → Prop
  | root : Reachable P σ x₀ x₀ []
  | step {x : X} {hist : List X} {y : X} :
      Reachable P σ x₀ x hist →
      y ∈ (P x (σ x hist)).support →
      Reachable P σ x₀ y (x :: hist)

/-- A strategy is surely safe from `x₀` when every support-reachable current
state remains in the declared persistence domain. -/
def SureSafeFrom
    (P : X → A → PMF X) (V : Set X) (x₀ : X)
    (σ : HistoryStrategy X A) : Prop :=
  ∀ ⦃x : X⦄ ⦃hist : List X⦄, Reachable P σ x₀ x hist → x ∈ V

/-- States admitting an arbitrary finite-history-dependent sure-safe strategy. -/
def winningSet (P : X → A → PMF X) (V : Set X) : Set X :=
  {x | ∃ σ : HistoryStrategy X A, SureSafeFrom P V x σ}

/-- After one realized transition, the residual policy is the original policy
with the old initial state appended to every local reverse history. -/
def tailStrategy
    (σ : HistoryStrategy X A) (x₀ : X) : HistoryStrategy X A :=
  fun x hist => σ x (hist ++ [x₀])

/-- Reachability under the residual strategy lifts to reachability under the
original strategy after the first support edge. -/
theorem reachable_tail_lift
    (P : X → A → PMF X) (σ : HistoryStrategy X A)
    {x₀ y : X}
    (hy : y ∈ (P x₀ (σ x₀ [])).support) :
    ∀ ⦃z : X⦄ ⦃hist : List X⦄,
      Reachable P (tailStrategy σ x₀) y z hist →
        Reachable P σ x₀ z (hist ++ [x₀]) := by
  intro z hist hz
  induction hz with
  | root =>
      have hroot : Reachable P σ x₀ x₀ [] := Reachable.root
      have hstep : Reachable P σ x₀ y [x₀] := Reachable.step hroot hy
      simpa using hstep
  | step hreach hnext ih =>
      have hnext' := hnext
      simp only [tailStrategy] at hnext'
      have hstep := Reachable.step ih hnext'
      simpa using hstep

/-- Every history-dependent winning state lies in the persistence domain. -/
theorem winningSet_subset
    (P : X → A → PMF X) (V : Set X) :
    winningSet P V ⊆ V := by
  rintro x ⟨σ, hσ⟩
  exact hσ (Reachable.root : Reachable P σ x x [])

/-- The full history-dependent winning set is controlled invariant.  The first
action of a sure-safe strategy has support entirely inside states from which
the corresponding residual strategy is again sure-safe. -/
theorem winningSet_controlledInvariant
    (P : X → A → PMF X) (V : Set X) :
    ControlledInvariant P (winningSet P V) := by
  rintro x ⟨σ, hσ⟩
  refine ⟨σ x [], ?_⟩
  unfold StaysIn
  intro y hy
  refine ⟨tailStrategy σ x, ?_⟩
  intro z hist hz
  exact hσ (reachable_tail_lift P σ hy hz)

/-- A stationary state-feedback policy as an unrestricted history strategy. -/
def stationaryHistoryStrategy (π : X → A) : HistoryStrategy X A :=
  fun x _ => π x

/-- Any fixed viability set is contained in the general winning set of every
larger persistence domain: its stationary preserving selector is already a
valid unrestricted strategy. -/
theorem fixed_subset_winningSet
    [Nonempty A]
    (P : X → A → PMF X) {K V : Set X}
    (hfix : viabilityStep P K = K) (hKV : K ⊆ V) :
    K ⊆ winningSet P V := by
  obtain ⟨π, hπ⟩ := exists_stationary_policy_of_fixed P hfix
  intro x hx
  let σ : HistoryStrategy X A := stationaryHistoryStrategy π
  have hsafeK : SureSafeFrom P K x σ := by
    intro z hist hz
    induction hz with
    | root => exact hx
    | step hreach hnext ih =>
        apply hπ _ ih
        simpa [σ, stationaryHistoryStrategy] using hnext
  refine ⟨σ, ?_⟩
  intro z hist hz
  exact hKV (hsafeK hz)

/-- Exact source-side winning-set characterization.  At a finite stabilization
index, the deletion kernel equals the set of states admitting an arbitrary
finite-history-dependent strategy that stays in `V` on every positive-support
branch. -/
theorem exists_stabilized_eq_winningSet
    [Nonempty A]
    (P : X → A → PMF X) (V : Set X) :
    ∃ n : ℕ,
      viabilityStep P (viabilityIter P V n) = viabilityIter P V n ∧
      viabilityIter P V n = winningSet P V := by
  obtain ⟨n, hn⟩ := exists_viabilityIter_fixed P V
  have hfix :
      viabilityStep P (viabilityIter P V n) = viabilityIter P V n := by
    simpa using hn
  have hKV : viabilityIter P V n ⊆ V := by
    simpa using (viabilityIter_antitone P V (Nat.zero_le n))
  have hwin_sub : winningSet P V ⊆ viabilityIter P V n :=
    controlledInvariant_subset_iter P V (winningSet P V)
      (winningSet_subset P V) (winningSet_controlledInvariant P V) n
  have hkernel_sub : viabilityIter P V n ⊆ winningSet P V :=
    fixed_subset_winningSet P hfix hKV
  exact ⟨n, hfix, Set.Subset.antisymm hkernel_sub hwin_sub⟩

end UEOT.V3.ViabilityStrategy
