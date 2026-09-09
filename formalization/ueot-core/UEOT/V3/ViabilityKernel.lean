import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic

/-!
# P-PER-03 foundation — finite controlled viability kernel

This module formalizes the finite-state/action deletion operator from the
source using genuine probability mass functions.  Probability-one retention is
represented by support containment and is bridged explicitly to
`PMF.toMeasure K = 1` for measurable `K`.

The module proves finite stabilization, existence of a deterministic stationary
one-step preserving policy at a fixed point, and maximality among controlled
invariant subsets of the persistence domain.  An infinite path-space
probability-one event remains a separate source-facing bridge before P-PER-03
is promoted in the coverage ledger.
-/

namespace UEOT.V3.ViabilityKernel

open Set

universe uX uA

variable {X : Type uX} {A : Type uA}
variable [Fintype X] [Fintype A]

/-- A PMF stays in `K` with probability one exactly when its support lies in
`K`.  This support form is convenient for the finite viability recursion. -/
def StaysIn (p : PMF X) (K : Set X) : Prop :=
  p.support ⊆ K

/-- The support formulation is literally the probability-one formulation used
in the manuscript whenever `K` is measurable. -/
theorem staysIn_iff_toMeasure_eq_one
    [MeasurableSpace X]
    (p : PMF X) {K : Set X} (hK : MeasurableSet K) :
    StaysIn p K ↔ p.toMeasure K = 1 := by
  simpa [StaysIn] using (p.toMeasure_apply_eq_one_iff hK).symm

/-- One deletion step:
keep exactly the currently viable states for which some action sends all
one-step probability mass back into the current set. -/
def viabilityStep (P : X → A → PMF X) (K : Set X) : Set X :=
  {x | x ∈ K ∧ ∃ a : A, StaysIn (P x a) K}

theorem viabilityStep_subset
    (P : X → A → PMF X) (K : Set X) :
    viabilityStep P K ⊆ K := by
  intro x hx
  exact hx.1

theorem viabilityStep_mono
    (P : X → A → PMF X) {K L : Set X}
    (hKL : K ⊆ L) :
    viabilityStep P K ⊆ viabilityStep P L := by
  rintro x ⟨hx, a, ha⟩
  exact ⟨hKL hx, a, ha.trans hKL⟩

/-- The source recursion `K₀ = V`, `Kₙ₊₁ = viabilityStep Kₙ`. -/
def viabilityIter (P : X → A → PMF X) (V : Set X) : ℕ → Set X
  | 0 => V
  | n + 1 => viabilityStep P (viabilityIter P V n)

@[simp] theorem viabilityIter_zero
    (P : X → A → PMF X) (V : Set X) :
    viabilityIter P V 0 = V := rfl

@[simp] theorem viabilityIter_succ
    (P : X → A → PMF X) (V : Set X) (n : ℕ) :
    viabilityIter P V (n + 1) =
      viabilityStep P (viabilityIter P V n) := rfl

theorem viabilityIter_succ_subset
    (P : X → A → PMF X) (V : Set X) :
    ∀ n : ℕ, viabilityIter P V (n + 1) ⊆ viabilityIter P V n := by
  intro n
  induction n with
  | zero =>
      exact viabilityStep_subset P V
  | succ n ih =>
      change
        viabilityStep P (viabilityIter P V (n + 1)) ⊆
          viabilityStep P (viabilityIter P V n)
      exact viabilityStep_mono P ih

theorem viabilityIter_antitone
    (P : X → A → PMF X) (V : Set X) :
    Antitone (viabilityIter P V) :=
  antitone_nat_of_succ_le (viabilityIter_succ_subset P V)

/-- On a finite state space the decreasing viability sequence must reach an
adjacent fixed point after finitely many deletion rounds. -/
theorem exists_viabilityIter_fixed
    (P : X → A → PMF X) (V : Set X) :
    ∃ n : ℕ, viabilityIter P V (n + 1) = viabilityIter P V n := by
  classical
  obtain ⟨i, j, hne, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite
      (α := ℕ) (viabilityIter P V)
  have hanti := viabilityIter_antitone P V
  rcases lt_or_gt_of_ne hne with hij | hji
  · refine ⟨i, Set.Subset.antisymm
        (viabilityIter_succ_subset P V i) ?_⟩
    have hs : i + 1 ≤ j := Nat.succ_le_iff.mpr hij
    have hsub := hanti hs
    rw [← heq] at hsub
    exact hsub
  · refine ⟨j, Set.Subset.antisymm
        (viabilityIter_succ_subset P V j) ?_⟩
    have hs : j + 1 ≤ i := Nat.succ_le_iff.mpr hji
    have hsub := hanti hs
    rw [heq] at hsub
    exact hsub

/-- A controlled invariant set admits at least one probability-one preserving
action at each of its states. -/
def ControlledInvariant (P : X → A → PMF X) (K : Set X) : Prop :=
  ∀ x ∈ K, ∃ a : A, StaysIn (P x a) K

theorem controlledInvariant_of_fixed
    (P : X → A → PMF X) {K : Set X}
    (hfix : viabilityStep P K = K) :
    ControlledInvariant P K := by
  intro x hx
  have hs : x ∈ viabilityStep P K := by
    rw [hfix]
    exact hx
  exact hs.2

/-- Every controlled invariant subset of the original persistence domain
survives every deletion round.  Hence the stabilized kernel is greatest among
such subsets. -/
theorem controlledInvariant_subset_iter
    (P : X → A → PMF X) (V K : Set X)
    (hKV : K ⊆ V) (hinv : ControlledInvariant P K) :
    ∀ n : ℕ, K ⊆ viabilityIter P V n := by
  intro n
  induction n with
  | zero =>
      simpa using hKV
  | succ n ih =>
      intro x hx
      refine ⟨ih hx, ?_⟩
      obtain ⟨a, ha⟩ := hinv x hx
      exact ⟨a, ha.trans ih⟩

/-- A fixed viability kernel admits a deterministic stationary policy whose
one-step transition support remains in the kernel. -/
theorem exists_stationary_policy_of_fixed
    [Nonempty A]
    (P : X → A → PMF X) {K : Set X}
    (hfix : viabilityStep P K = K) :
    ∃ π : X → A, ∀ x ∈ K, StaysIn (P x (π x)) K := by
  classical
  have hact : ∀ x, x ∈ K → ∃ a : A, StaysIn (P x a) K := by
    intro x hx
    exact controlledInvariant_of_fixed P hfix x hx
  let a₀ : A := Classical.choice (inferInstance : Nonempty A)
  let π : X → A := fun x =>
    if hx : x ∈ K then Classical.choose (hact x hx) else a₀
  refine ⟨π, ?_⟩
  intro x hx
  simp only [π, dif_pos hx]
  exact Classical.choose_spec (hact x hx)

/-- State marginals generated by a deterministic stationary policy. -/
def stationaryStateLaw
    (P : X → A → PMF X) (π : X → A) : PMF X → ℕ → PMF X
  | μ, 0 => μ
  | μ, n + 1 => (stationaryStateLaw P π μ n).bind fun x => P x (π x)

@[simp] theorem stationaryStateLaw_zero
    (P : X → A → PMF X) (π : X → A) (μ : PMF X) :
    stationaryStateLaw P π μ 0 = μ := rfl

@[simp] theorem stationaryStateLaw_succ
    (P : X → A → PMF X) (π : X → A) (μ : PMF X) (n : ℕ) :
    stationaryStateLaw P π μ (n + 1) =
      (stationaryStateLaw P π μ n).bind (fun x => P x (π x)) := rfl

/-- One-step support preservation by a stationary policy propagates to every
finite-time marginal. -/
theorem stationaryStateLaw_staysIn
    (P : X → A → PMF X) (π : X → A)
    (K : Set X) (μ : PMF X)
    (hμ : StaysIn μ K)
    (hπ : ∀ x ∈ K, StaysIn (P x (π x)) K) :
    ∀ n : ℕ, StaysIn (stationaryStateLaw P π μ n) K := by
  intro n
  induction n with
  | zero => simpa using hμ
  | succ n ih =>
      rw [stationaryStateLaw_succ]
      unfold StaysIn at ih ⊢
      rw [PMF.support_bind]
      refine iUnion_subset fun x => ?_
      refine iUnion_subset fun hx => ?_
      exact hπ x (ih hx)

/-- The policy extracted from a fixed viability kernel therefore keeps every
finite-time marginal in that kernel with probability one. -/
theorem exists_stationary_policy_all_marginals_of_fixed
    [Nonempty A] [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) {K : Set X}
    (hfix : viabilityStep P K = K)
    (μ : PMF X) (hμ : StaysIn μ K)
    (hK : MeasurableSet K) :
    ∃ π : X → A, ∀ n : ℕ,
      (stationaryStateLaw P π μ n).toMeasure K = 1 := by
  obtain ⟨π, hπ⟩ := exists_stationary_policy_of_fixed P hfix
  refine ⟨π, fun n => ?_⟩
  exact (staysIn_iff_toMeasure_eq_one
    (stationaryStateLaw P π μ n) hK).1
      (stationaryStateLaw_staysIn P π K μ hμ hπ n)

/-- Finite stabilization plus the two source-side structural consequences:
the fixed kernel is controlled invariant, contains every other controlled
invariant subset of `V`, and has a deterministic stationary preserving
policy. -/
theorem finite_viability_kernel_structure
    [Nonempty A]
    (P : X → A → PMF X) (V : Set X) :
    ∃ n : ℕ,
      let K := viabilityIter P V n
      viabilityStep P K = K ∧
        ControlledInvariant P K ∧
        (∀ K' : Set X, K' ⊆ V → ControlledInvariant P K' → K' ⊆ K) ∧
        ∃ π : X → A, ∀ x ∈ K, StaysIn (P x (π x)) K := by
  obtain ⟨n, hn⟩ := exists_viabilityIter_fixed P V
  refine ⟨n, ?_⟩
  have hfix : viabilityStep P (viabilityIter P V n) =
      viabilityIter P V n := by
    simpa using hn
  refine ⟨hfix, controlledInvariant_of_fixed P hfix, ?_, ?_⟩
  · intro K' hKV hinv
    exact controlledInvariant_subset_iter P V K' hKV hinv n
  · exact exists_stationary_policy_of_fixed P hfix

end UEOT.V3.ViabilityKernel
