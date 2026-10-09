import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreInfinitePathClosure
import Mathlib.Tactic

/-!
# Unified finite UEOT core: all-times source-level closure

The original P-ALG dynamics is first refined by its EXISTING coarsest
stable-partition theorem, then reconciled with the SISC kernel, then lifted
to P-QUO exact control, and finally connected to P-PER infinite-path law.

Crucially, ALL model components are induced from ONE finite Markov table:
transition weights are not assumed to equal another unrelated model.

The source safe predicate is REGISTERED through a protected output, and
the initial PMF must lie inside the discovered viable set. Neither
nonemptiness nor physical repair is claimed unconditionally.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open UEOT.V3.FiniteStablePartition
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.ViabilityKernel
open UEOT.V3.ViabilityTrajectory
open UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
open UEOT.V3.Compression.RecursiveSufficientState

universe uX uA uO

/-- Strongest current finite-Core *source coherent* endpoint.

Starting from a single normalized controlled process M and a declared
safety observation, the coarsest organization-preserving stable quotient
induces an exact control quotient. Its viability kernel has a genuine
discrete-time INFINITE path-law realization on the original microstate
space, preserving the original source-registered safety at ALL times.

The result does not equate the survival policy with Bellman greedy, nor
does it infer a physical program/material reproducer or endogenous GOA. -/
theorem single_source_terminal_object_viability_all_times
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (M : UEOT.V3.FiniteStablePartition.Model X A ℝ O)
    (B β : ℝ) (hr : ∀ x a, |M.reward x a| ≤ B)
    (hβpos : 0 < β) (hβlt : β < 1)
    (safe : O → Prop) :
    let S := terminalSetoid M
    let q := setoidRepresentation S
    letI : Fintype (ReachableState q) := Fintype.ofFinite _
    let Q := organizationalTerminalControl M B β hr hβpos hβlt
    let good : ReachableState q → Prop :=
      fun c => safe (quotientOutput M S (terminal_refines_initial M) c.1)
    (∀ x a z, Q.micro.transition x a z = M.transition a x z) ∧
    (∀ x, Q.micro.optimalValue x =
      Q.macroModel.optimalValue (Q.f x)) ∧
    ∃ n : ℕ, n ≤ Fintype.card (ReachableState q) ∧
      ∀ μ : PMF X,
        StaysIn μ {x | macroViable Q good n (Q.f x)} →
        ∃ pi : X → A,
          stationaryTrajMeasure
            (fun x a => Q.micro.transitionPMF x a) pi μ
            {ω | ∀ t : ℕ,
              macroViable Q good n (Q.f (ω t)) ∧
              safe (M.output (ω t))} = 1 := by
  classical
  let S := terminalSetoid M
  let q : X → Quotient S := setoidRepresentation S
  letI : Fintype (ReachableState q) := Fintype.ofFinite _
  let Q := organizationalTerminalControl M B β hr hβpos hβlt
  let good : ReachableState q → Prop :=
    fun c => safe (quotientOutput M S (terminal_refines_initial M) c.1)
  refine ⟨?_, Q.optimalValue_apply, ?_⟩
  · intro x a z
    rfl
  obtain ⟨n, hn, hall⟩ := exists_source_micro_all_times_viable_path_law Q good
  refine ⟨n, hn, ?_⟩
  intro μ hμ
  obtain ⟨pi, htraj⟩ := hall μ hμ
  refine ⟨pi, ?_⟩
  have hsafe : ∀ c, macroViable Q good n c → good c := by
    intro c hc
    cases n with
    | zero => exact hc
    | succ k => exact hc.1
  have hgood : ∀ x : X, good (Q.f x) ↔ safe (M.output x) := by
    intro x
    change safe (quotientOutput M S (terminal_refines_initial M) ⟦x⟧) ↔
      safe (M.output x)
    rw [quotientOutput_mk]
  have hevents :
      {ω : ℕ → X | ∀ t, macroViable Q good n (Q.f (ω t))} =
      {ω : ℕ → X | ∀ t, macroViable Q good n (Q.f (ω t)) ∧
        safe (M.output (ω t))} := by
    ext ω
    constructor
    · intro h t
      exact ⟨h t, (hgood (ω t)).mp (hsafe _ (h t))⟩
    · intro h t
      exact (h t).1
  rw [← hevents]
  exact htraj

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
