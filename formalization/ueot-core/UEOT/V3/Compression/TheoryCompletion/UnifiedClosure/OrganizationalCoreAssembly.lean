import UEOT.V3.PAlg01
import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCModelKernelReconciliation
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PredictiveOptimalControlLift
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ViabilityKernelIntertwining
import Mathlib.Tactic

/-!
# UMC: assemble the EXISTING finite stable-state algorithm with exact control and viability

This module does not implement a new partition-refinement algorithm. It uses
frozen P-ALG-01's terminalSetoid, SISC's proven model/kernel reconciliation,
and P-QUO-01's exact stochastic-control quotient. This eliminates a previously
disconnected source-model adapter.

Registered output may bundle observational, organizational, current resource,
current program, and safety signatures. Only *state-dependent registered
labels* are preserved: no historical provenance, material production, physical
Omega-loop or endogenous goal is inferred from an arbitrary label.

The exact controlled quotient constructed here uses the SAME source transition
matrix and the SAME source reward, rather than inventing independent macro
models. The maximal viability theorem is inherited from UMC V4.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open UEOT.V3.FiniteStablePartition
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
open UEOT.V3.Compression.RecursiveSufficientState

universe uX uA uO

/-- SISC + P-QUO bridge for ANY certified stable P-ALG partition. Source
transitions and source rewards are preserved literally. -/
noncomputable def exactControlFromStablePartition
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [Fintype A] [Nonempty A]
    (M : UEOT.V3.FiniteStablePartition.Model X A ℝ O)
    (S : Setoid X)
    (hinit : Refines S (initialSetoid M))
    (hstable : Stable M S)
    (B β : ℝ)
    (hr : ∀ x a, |M.reward x a| ≤ B)
    (hβpos : 0 < β) (hβlt : β < 1) :
    let q := setoidRepresentation S
    letI : Fintype (ReachableState q) := Fintype.ofFinite _
    ExactControlQuotient X (ReachableState q) (fun _ => A) := by
  classical
  let q : X → Quotient S := setoidRepresentation S
  letI : Fintype (ReachableState q) := Fintype.ofFinite _
  have hLump : StrongLumpability (modelAsFiniteKernel M) q :=
    (model_strongLumpability_iff_stable M S).2 hstable
  let rewardBar : ReachableState q → A → ℝ :=
    fun c a => quotientReward M S hinit a c.1
  have hbound : ∀ c a, |rewardBar c a| ≤ B := by
    intro c a
    obtain ⟨x, hx⟩ := c.property
    change |quotientReward M S hinit a c.1| ≤ B
    rw [← hx]
    exact hr x a
  exact exactControlFromStochasticQuotient (modelAsFiniteKernel M)
    q hLump rewardBar B β hbound hβpos hβlt

/-- No new refinement logic: reuse P-ALG's canonical coarsest stable partition
with SISC and P-QUO. All post-refinement control semantics share M's source. -/
noncomputable def organizationalTerminalControl
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [Fintype A] [Nonempty A]
    (M : UEOT.V3.FiniteStablePartition.Model X A ℝ O)
    (B β : ℝ)
    (hr : ∀ x a, |M.reward x a| ≤ B)
    (hβpos : 0 < β) (hβlt : β < 1) :
    let S := terminalSetoid M
    let q := setoidRepresentation S
    letI : Fintype (ReachableState q) := Fintype.ofFinite _
    ExactControlQuotient X (ReachableState q) (fun _ => A) := by
  exact exactControlFromStablePartition
    M (terminalSetoid M)
    (terminal_refines_initial M) (terminal_stable M)
    B β hr hβpos hβlt

/-- The canonical output/reward partition survives controlled refinement.
This is inherited rather than reproved from scratch. -/
theorem organizational_terminal_preserves_registered_interfaces
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [Fintype A]
    (M : UEOT.V3.FiniteStablePartition.Model X A ℝ O)
    {x y : X} (h : (terminalSetoid M).r x y) :
    M.output x = M.output y ∧
      ∀ a, M.reward x a = M.reward y a :=
  terminal_refines_initial M h

/-- No other stable representation preserving the same registered output and
all-action reward may be coarser than the constructed terminal quotient. -/
theorem organizational_terminal_is_coarsest
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [Fintype A]
    (M : UEOT.V3.FiniteStablePartition.Model X A ℝ O)
    (T : Setoid X)
    (houtputs : ∀ {x y}, T.r x y → M.output x = M.output y)
    (hrewards : ∀ {x y}, T.r x y → ∀ a, M.reward x a = M.reward y a)
    (hstable : Stable M T) :
    Refines T (terminalSetoid M) :=
  terminal_coarsest M T (fun _ _ h => ⟨houtputs h, hrewards h⟩) hstable

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
