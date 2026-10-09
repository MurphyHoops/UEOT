import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OrganizationalCoreAssembly
import Mathlib.Tactic

/-!
# Finite UEOT core source-assembly certificate

Construct one precise chain, all from the same registered finite controlled
state dynamics M:

P-ALG-01 terminating coarsest stable partition
  -> SISC concrete source-kernel consistency
  -> P-QUO-01 exact discounted control and causal optimality
  -> UMC V4 finite viability greatest fixed point and safe feedback.

No algorithm is duplicated. No physical self-production, history provenance,
unconditional Omega-loop, or endogenous purpose is claimed. A safety label is
assumed to be a function of the protected output signature.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open UEOT.V3.FiniteStablePartition
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
open UEOT.V3.Compression.RecursiveSufficientState

universe uX uA uO uG uP uR

/-- All registered CURRENT-state labels are protected in P-ALG's initial
partition. This is registration, not a physical model of production or
ancestral provenance. In particular an actual history-dependent program
cannot be inferred from an arbitrary state label. -/
def modelWithRegisteredOrganization
    {X : Type uX} {A : Type uA}
    {O : Type uO} {G : Type uG} {P : Type uP} {R : Type uR}
    [Fintype X]
    (K : FiniteControlledStochasticKernel X A)
    (observe : X → O)
    (organization : X → G)
    (program : X → P)
    (resource : X → R)
    (safe : X → Bool)
    (reward : X → A → ℝ) :
    UEOT.V3.FiniteStablePartition.Model X A ℝ
      (O × G × P × R × Bool) where
  transition := fun a x z => K.mass x a z
  reward := reward
  output := fun x => (observe x, organization x, program x, resource x, safe x)
  transition_nonneg := fun a x z => K.nonneg x a z
  transition_sum_one := fun a x => K.normalized x a

/-- Coarsest dynamic partition preserves every registered organizational
current-state interface simultaneously: not just predicted output. -/
theorem registered_organizational_attributes_preserved
    {X : Type uX} {A : Type uA}
    {O : Type uO} {G : Type uG} {P : Type uP} {R : Type uR}
    [Fintype X] [Fintype A]
    (K : FiniteControlledStochasticKernel X A)
    (observe : X → O) (organization : X → G)
    (program : X → P) (resource : X → R)
    (safe : X → Bool) (reward : X → A → ℝ)
    {x y : X}
    (h : (terminalSetoid (modelWithRegisteredOrganization
      K observe organization program resource safe reward)).r x y) :
    observe x = observe y ∧
    organization x = organization y ∧
    program x = program y ∧
    resource x = resource y ∧
    safe x = safe y ∧
    (∀ a, reward x a = reward y a) := by
  have hh := organizational_terminal_preserves_registered_interfaces
    (modelWithRegisteredOrganization
      K observe organization program resource safe reward) h
  rcases hh with ⟨hlabels,hreward⟩
  have hlabels' : (observe x, organization x, program x, resource x, safe x) =
    (observe y, organization y, program y, resource y, safe y) := hlabels
  simp only [Prod.mk.injEq] at hlabels'
  exact ⟨hlabels'.1, hlabels'.2.1, hlabels'.2.2.1,
    hlabels'.2.2.2.1, hlabels'.2.2.2.2, hreward⟩

/-- One common source creates a coarsest registered controlled quotient,
preserves the real source reward and transition, transports Bellman optimality,
and derives (rather than presupposes) a maximal viable region plus a
path-preserving feedback for the output-registered safety condition.

The viable region may be empty. Its nonemptiness is NOT an unconditional
corollary; V4 contains a separate nonvacuous four-state witness. -/
theorem unified_finite_core_control_and_viability
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
    (∀ x a z, Q.micro.transition x a z = M.transition a x z) ∧
    (∀ x a, Q.micro.reward x a = M.reward x a) ∧
    (∀ x, Q.micro.optimalValue x =
      Q.macroModel.optimalValue (Q.f x)) ∧
    (∀ x, good (Q.f x) ↔ safe (M.output x)) ∧
    (∃ n : ℕ, n ≤ Fintype.card (ReachableState q) ∧
      ∃ sigma : ReachableState q → A,
      ∀ (x : X) (path : List X),
        macroViable Q good n (Q.f x) →
        PositivePolicyRealization Q sigma x path →
        macroViable Q good n
          (Q.f (realizedPolicyEndpoint x path))) := by
  classical
  let S := terminalSetoid M
  let q : X → Quotient S := setoidRepresentation S
  letI : Fintype (ReachableState q) := Fintype.ofFinite _
  let Q := organizationalTerminalControl M B β hr hβpos hβlt
  let good : ReachableState q → Prop :=
    fun c => safe (quotientOutput M S (terminal_refines_initial M) c.1)
  dsimp only
  refine ⟨?_, ?_, Q.optimalValue_apply, ?_, ?_⟩
  · intro x a z
    rfl
  · intro x a
    change quotientReward M (terminalSetoid M)
      (terminal_refines_initial M) a ⟦x⟧ = M.reward x a
    exact quotientReward_mk M (terminalSetoid M)
      (terminal_refines_initial M) a x
  · intro x
    change safe (quotientOutput M (terminalSetoid M)
      (terminal_refines_initial M) ⟦x⟧) ↔ safe (M.output x)
    rw [quotientOutput_mk]
  · exact exists_derived_survival_controller Q good

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
