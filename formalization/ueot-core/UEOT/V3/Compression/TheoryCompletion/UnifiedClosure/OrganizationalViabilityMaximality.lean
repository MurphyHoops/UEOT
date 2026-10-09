import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.UnifiedCoreClosureCertificate
import Mathlib.Tactic

/-!
# Common-source core: representational minimality and viable-region maximality

The terminal controlled partition is the coarsest exact representation
preserving registered labels/rewards; independently the greatest controlled
invariant safe region can be synthesized. This module connects the two at
the ORIGINAL MICRO transition table, not by assuming an arbitrary macro
feedback, and shows any original-source controlled-invariant subset lies
inside the stabilized viability preimage.

This is a finite stochastic control theorem and does NOT infer physical
repair, endogenous goals, or historical/causal ancestry.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open UEOT.V3.FiniteStablePartition
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
open UEOT.V3.Compression.RecursiveSufficientState

universe uX uA uO

/-- Any controlled-invariant micro region within the ORIGINAL registered
safe condition is contained in EVERY synthesized viability horizon. The
action can depend on the original microstate; no quotient policy is assumed. -/
theorem source_invariant_enters_every_terminal_viability_horizon
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [Fintype A] [Nonempty A]
    (M : UEOT.V3.FiniteStablePartition.Model X A ℝ O)
    (B β : ℝ) (hr : ∀ x a, |M.reward x a| ≤ B)
    (hβpos : 0 < β) (hβlt : β < 1)
    (safe : O → Prop)
    (region : X → Prop)
    (hinside : ∀ x, region x → safe (M.output x))
    (hcontrol : ∀ x, region x →
      ∃ a : A, ∀ z : X, ¬ region z → M.transition a x z = 0) :
    let S := terminalSetoid M
    let q := setoidRepresentation S
    letI : Fintype (ReachableState q) := Fintype.ofFinite _
    let Q := organizationalTerminalControl M B β hr hβpos hβlt
    let good : ReachableState q → Prop :=
      fun c => safe (quotientOutput M S (terminal_refines_initial M) c.1)
    ∀ (n : ℕ) (x : X), region x → microViable Q good n x := by
  classical
  let S := terminalSetoid M
  let q := setoidRepresentation S
  letI : Fintype (ReachableState q) := Fintype.ofFinite _
  let Q := organizationalTerminalControl M B β hr hβpos hβlt
  let good : ReachableState q → Prop :=
    fun c => safe (quotientOutput M S (terminal_refines_initial M) c.1)
  change ∀ (n : ℕ) (x : X), region x → microViable Q good n x
  intro n
  induction n with
  | zero =>
      intro x hx
      change good (Q.f x)
      change safe (quotientOutput M S (terminal_refines_initial M) ⟦x⟧)
      rw [quotientOutput_mk]
      exact hinside x hx
  | succ n ih =>
      intro x hx
      change good (Q.f x) ∧ ∃ a : A, ∀ z : X,
        ¬ microViable Q good n z → Q.micro.transition x a z = 0
      constructor
      · change safe (quotientOutput M S (terminal_refines_initial M) ⟦x⟧)
        rw [quotientOutput_mk]
        exact hinside x hx
      · obtain ⟨a, ha⟩ := hcontrol x hx
        refine ⟨a, ?_⟩
        intro z hz
        have hnz : ¬ region z := fun hreg => hz (ih z hreg)
        change M.transition a x z = 0
        exact ha z hnz

/-- The *same* dynamics simultaneously induces the coarsest protected
controlled representation and the greatest controlled-invariant safe
region. Every source micro-invariant region is contained in that
greatest kernel; no saturation/fibre-closure of the candidate micro
region itself is required. -/
theorem terminal_organizational_quotient_maximal_micro_viability
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [Fintype A] [Nonempty A]
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
    (Stable M S ∧
      (∀ T : Setoid X, Refines T (initialSetoid M) →
        Stable M T → Refines T S)) ∧
    ∃ n : ℕ, n ≤ Fintype.card (ReachableState q) ∧
      (∀ x : X, microViable Q good n x ↔
        macroViable Q good n (Q.f x)) ∧
      (∀ region : X → Prop,
        (∀ x, region x → safe (M.output x)) →
        (∀ x, region x → ∃ a : A,
          ∀ z : X, ¬ region z → M.transition a x z = 0) →
        ∀ x, region x → microViable Q good n x) ∧
      (∀ x : X, macroViable Q good n (Q.f x) →
        ∃ a : A, ∀ z : X, ¬ macroViable Q good n (Q.f z) →
          M.transition a x z = 0) := by
  classical
  let S := terminalSetoid M
  let q := setoidRepresentation S
  letI : Fintype (ReachableState q) := Fintype.ofFinite _
  let Q := organizationalTerminalControl M B β hr hβpos hβlt
  let good : ReachableState q → Prop :=
    fun c => safe (quotientOutput M S (terminal_refines_initial M) c.1)
  refine ⟨⟨terminal_stable M, ?_⟩, ?_⟩
  · intro T hTinit hTstable
    exact terminal_coarsest M T hTinit hTstable
  obtain ⟨n, hn, hfix⟩ := exists_finite_viability_fixedpoint Q good
  refine ⟨n, hn, ?_, ?_, ?_⟩
  · exact fun x => micro_viability_iff_macro_viability Q good n x
  · intro region hinside hcontrol x hx
    exact source_invariant_enters_every_terminal_viability_horizon
      M B β hr hβpos hβlt safe region hinside hcontrol n x hx
  · intro x hx
    obtain ⟨a, ha⟩ :=
      macro_viable_fixedpoint_has_safe_action Q good n hfix (Q.f x) hx
    refine ⟨a, ?_⟩
    intro z hz
    have hz' : ¬ macroViable Q good n (Q.f z) := hz
    have hmacro := ha (Q.f z) hz'
    have hm := (macro_zero_outside_iff_micro_zero_outside
      Q (macroViable Q good n) x a).1 ha
    change M.transition a x z = 0
    exact hm z hz'

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
