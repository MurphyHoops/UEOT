import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportMemoryCheck
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteMemoryPhysicalSafety
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.HomogeneousMemorySurvival

/-!
# Executable synthesis of an autonomous support controller

The runtime consumes an explicit finite initial support, a decidable relation,
certification data and an ordered action list. It reuses the existing bounded
relation checker and selects the first winning action with `List.find?`.
The observation type need not be finite. Empty memory uses a fixed fallback.

Synthesis checks that the action list covers every action; repeated entries are
allowed and do not affect soundness. The first-match guarantee is relative to
that list, not a complexity claim. The recursive checker is reused without a
memoized fixed-point table, so no polynomial or table-iteration cost is claimed.
ponytail: retain the recursive checker until its measured cost blocks a concrete
finite input; that is the trigger to add a memoized winning-support table.

The three runtime functions and `Program` are computable. Only their PMF
interpretation uses `PMF.pure`. Exact source-support and initial-support matching
remain theorem premises, not empirical conclusions inferred from a finite table.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
namespace ExecutableSupportSynthesis

open MeasureTheory UEOT.V3.PathError SupportViabilityClosure

universe u

/-- A deterministic executable controller; probability is added only in its
semantic interpretation. The total memory type includes impossible records. -/
structure Program (X Y A : Type u) where
  initialMemory : Y → Finset X
  action : Finset X → A
  update : Finset X → A → Y → Finset X

namespace Program

/-- Replay only finite executable data, independently of the PMF interpretation. -/
def memory {X Y A : Type u} (program : Program X Y A) :
    ∀ n, CausalHistory Y (A × Y) n → Finset X
  | 0, y => program.initialMemory y
  | n + 1, h => program.update (program.memory n h.1) h.2.1 h.2.2

end Program

/-- Initialize from the explicit support table, not from an arbitrary PMF. -/
def initialMemory {X Y : Type u} [DecidableEq Y]
    (q : X → Y) (initial : Finset X) (y : Y) : Finset X :=
  initial.filter (fun x => q x = y)

/-- Reuse the existing executable relation successor at its fixed support time. -/
def nextMemory {X Y A : Type u} [Fintype X]
    [DecidableEq X] [DecidableEq Y]
    (q : X → Y) (R : X → A → X → Prop)
    [∀ x a z, Decidable (R x a z)]
    (S : Finset X) (a : A) (y : Y) : Finset X :=
  finiteRelationSuccessor q (fun _ => R) 0 S a y

/-- A nonempty current support must be certified by one common action, and
every nonempty observation successor must pass the established finite cutoff. -/
def stepCheck {X Y A : Type u} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq Y]
    (q : X → Y) (R : X → A → X → Prop) (C : X → A → Prop)
    [∀ x a z, Decidable (R x a z)] [∀ x a, Decidable (C x a)]
    (S : Finset X) (a : A) : Bool :=
  decide (S.Nonempty ∧ (∀ x ∈ S, C x a) ∧
    ∀ z : X, (nextMemory q R S a (q z)).Nonempty →
      finiteRelationViabilityCheck q (fun _ => R) (fun _ => C) 0
        (2 ^ Fintype.card X - 1) (nextMemory q R S a (q z)) = true)

/-- The first certified continuation in the caller's explicit order. -/
def findAction {X Y A : Type u} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq Y]
    (q : X → Y) (R : X → A → X → Prop) (C : X → A → Prop)
    [∀ x a z, Decidable (R x a z)] [∀ x a, Decidable (C x a)]
    (ordered : List A) (S : Finset X) : Option A :=
  ordered.find? (stepCheck q R C S)

/-- Total output, including empty or nonwinning memories. -/
def selectedAction {X Y A : Type u} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq Y]
    (q : X → Y) (R : X → A → X → Prop) (C : X → A → Prop)
    [∀ x a z, Decidable (R x a z)] [∀ x a, Decidable (C x a)]
    (ordered : List A) (fallback : A) (S : Finset X) : A :=
  (findAction q R C ordered S).getD fallback

/-- Package the three actual runtime functions without a probability oracle. -/
def buildProgram {X Y A : Type u} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq Y]
    (q : X → Y) (R : X → A → X → Prop) (C : X → A → Prop)
    [∀ x a z, Decidable (R x a z)] [∀ x a, Decidable (C x a)]
    (initial : Finset X) (ordered : List A) (fallback : A) : Program X Y A where
  initialMemory := initialMemory q initial
  action := selectedAction q R C ordered fallback
  update := nextMemory q R

/-- Check nonempty input, list coverage and initial viability before returning
runtime data. Duplicate actions are legal; an incomplete list is rejected. -/
def synthesize {X Y A : Type u} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq Y] [DecidableEq A]
    (q : X → Y) (R : X → A → X → Prop) (C : X → A → Prop)
    [∀ x a z, Decidable (R x a z)] [∀ x a, Decidable (C x a)]
    (initial : Finset X) (ordered : List A) (fallback : A) : Option (Program X Y A) :=
  if decide initial.Nonempty && decide (∀ a : A, a ∈ ordered) &&
      finiteMemoryCheck q R C initial then
    some (buildProgram q R C initial ordered fallback)
  else none

section FiniteSemantics

variable {X Y A : Type u} [Fintype X] [Fintype A]
variable [DecidableEq X] [DecidableEq Y]
variable (q : X → Y) (R : X → A → X → Prop) (C : X → A → Prop)
variable [∀ x a z, Decidable (R x a z)] [∀ x a, Decidable (C x a)]

/-- The executable checker has a pure relation meaning; no PMF or exact
support oracle is needed to establish its finite recursion. -/
theorem relationCheck_iff_viableWith :
    ∀ k n (S : Finset X),
      finiteRelationViabilityCheck q (fun _ => R) (fun _ => C) n k S = true ↔
        viableWith (fun _ => relationSuccessor q R) (fun _ => C) n k (↑S : Set X) := by
  intro k
  induction k with
  | zero => intro n S; simp [finiteRelationViabilityCheck, viableWith]
  | succ k ih =>
      intro n S
      simp only [finiteRelationViabilityCheck, decide_eq_true_eq, viableWith]
      constructor
      · rintro ⟨a, hcert, hnext⟩
        refine ⟨a, hcert, ?_⟩
        intro y hy
        obtain ⟨z, hz⟩ := hy
        have hobs : q z = y := hz.1
        have hfinite : (finiteRelationSuccessor q (fun _ => R) n S a (q z)).Nonempty := by
          change (↑(finiteRelationSuccessor q (fun _ => R) n S a (q z)) : Set X).Nonempty
          rw [finiteRelationSuccessor_coe_eq_relationSuccessor, hobs]
          exact ⟨z, hz⟩
        have hV := (ih (n + 1)
          (finiteRelationSuccessor q (fun _ => R) n S a (q z))).mp (hnext z hfinite)
        rw [finiteRelationSuccessor_coe_eq_relationSuccessor, hobs] at hV
        exact hV
      · rintro ⟨a, hcert, hnext⟩
        refine ⟨a, hcert, ?_⟩
        intro z hfinite
        apply (ih (n + 1) (finiteRelationSuccessor q (fun _ => R) n S a (q z))).mpr
        rw [finiteRelationSuccessor_coe_eq_relationSuccessor]
        apply hnext (q z)
        change (↑(finiteRelationSuccessor q (fun _ => R) n S a (q z)) : Set X).Nonempty at hfinite
        rwa [finiteRelationSuccessor_coe_eq_relationSuccessor] at hfinite

/-- The existing computable cutoff recognizes the greatest winning family
on every nonempty single-observation support. -/
theorem boundedCheck_iff_winning (S : Finset X)
    (hS : (↑S : Set X) ∈ supportArena q) :
    finiteRelationViabilityCheck q (fun _ => R) (fun _ => C) 0
      (2 ^ Fintype.card X - 1) S = true ↔
        (↑S : Set X) ∈ supportWinning q R C := by
  have hB : supportArenaCard q ≤ 2 ^ Fintype.card X - 1 := by
    have hbound := supportArenaCard_add_one_le_pow (X := X) q
    omega
  rw [relationCheck_iff_viableWith]
  rw [← mem_supportIterate_iff_viableWith q R C
    (2 ^ Fintype.card X - 1) 0 (↑S : Set X) hS]
  rw [supportIterate_eq_winning_of_card_le q R C _ hB]

/-- The runtime action test is exactly the winning-step obligation, with
the explicit empty-memory guard retained. -/
theorem stepCheck_iff (S : Finset X) (a : A) :
    stepCheck q R C S a = true ↔
      S.Nonempty ∧ (∀ x ∈ (↑S : Set X), C x a) ∧
        ∀ y : Y, (relationSuccessor q R (↑S : Set X) a y).Nonempty →
          relationSuccessor q R (↑S : Set X) a y ∈ supportWinning q R C := by
  simp only [stepCheck, decide_eq_true_eq]
  constructor
  · rintro ⟨hne, hcert, hnext⟩
    refine ⟨hne, hcert, ?_⟩
    intro y hy
    obtain ⟨z, hz⟩ := hy
    have hobs : q z = y := hz.1
    have hfinite : (nextMemory q R S a (q z)).Nonempty := by
      change (↑(nextMemory q R S a (q z)) : Set X).Nonempty
      rw [nextMemory, finiteRelationSuccessor_coe_eq_relationSuccessor, hobs]
      exact ⟨z, hz⟩
    have harena : (↑(nextMemory q R S a (q z)) : Set X) ∈ supportArena q := by
      rw [nextMemory, finiteRelationSuccessor_coe_eq_relationSuccessor, hobs]
      exact relationSuccessor_mem_arena q R (↑S : Set X) a y ⟨z, hz⟩
    have hwin := (boundedCheck_iff_winning q R C _ harena).mp (hnext z hfinite)
    rwa [nextMemory, finiteRelationSuccessor_coe_eq_relationSuccessor, hobs] at hwin
  · rintro ⟨hne, hcert, hnext⟩
    refine ⟨hne, hcert, ?_⟩
    intro z hfinite
    have hrel : (relationSuccessor q R (↑S : Set X) a (q z)).Nonempty := by
      change (↑(nextMemory q R S a (q z)) : Set X).Nonempty at hfinite
      rwa [nextMemory, finiteRelationSuccessor_coe_eq_relationSuccessor] at hfinite
    have harena : (↑(nextMemory q R S a (q z)) : Set X) ∈ supportArena q := by
      rw [nextMemory, finiteRelationSuccessor_coe_eq_relationSuccessor]
      exact relationSuccessor_mem_arena q R (↑S : Set X) a (q z) hrel
    apply (boundedCheck_iff_winning q R C _ harena).mpr
    rw [nextMemory, finiteRelationSuccessor_coe_eq_relationSuccessor]
    exact hnext (q z) hrel

/-- Returning an action also certifies that every earlier list entry failed
the same runtime test. Repeated entries require no extra assumption. -/
theorem findAction_eq_some_iff (ordered : List A) (S : Finset X) (a : A) :
    findAction q R C ordered S = some a ↔
      stepCheck q R C S a = true ∧
        ∃ before after, ordered = before ++ a :: after ∧
          ∀ b ∈ before, stepCheck q R C S b = false := by
  simpa only [findAction, Bool.not_eq_eq_eq_not, Bool.not_true] using
    (List.find?_eq_some_iff_append (xs := ordered) (p := stepCheck q R C S) (b := a))

/-- Complete action enumeration turns the existing existence theorem into
the actual first-match output. The fallback is not used on a winning support. -/
theorem selectedAction_step (ordered : List A) (fallback : A)
    (hcomplete : ∀ a : A, a ∈ ordered) (S : Finset X)
    (hS : (↑S : Set X) ∈ supportWinning q R C) :
    (∀ x ∈ (↑S : Set X), C x (selectedAction q R C ordered fallback S)) ∧
      ∀ y : Y,
        (relationSuccessor q R (↑S : Set X)
          (selectedAction q R C ordered fallback S) y).Nonempty →
        relationSuccessor q R (↑S : Set X)
          (selectedAction q R C ordered fallback S) y ∈ supportWinning q R C := by
  obtain ⟨a, hcert, hnext⟩ := supportWinning_step q R C (↑S : Set X) hS
  have hne : S.Nonempty := (supportWinning_subset_arena q R C hS).1
  have htest : stepCheck q R C S a = true :=
    (stepCheck_iff q R C S a).mpr ⟨hne, hcert, hnext⟩
  cases hfind : findAction q R C ordered S with
  | none =>
      have hnone := List.find?_eq_none.mp hfind
      exact False.elim ((hnone a (hcomplete a)) htest)
  | some b =>
      have hb : stepCheck q R C S b = true := List.find?_some hfind
      simpa only [selectedAction, hfind, Option.getD_some] using
        (stepCheck_iff q R C S b).mp hb |>.2

/-- Empty records have the declared fixed output even when the first listed
action differs from the fallback. -/
@[simp] theorem selectedAction_empty (ordered : List A) (fallback : A) :
    selectedAction q R C ordered fallback ∅ = fallback := by
  have hnone : findAction q R C ordered ∅ = none := by
    apply List.find?_eq_none.mpr
    intro a _
    simp [stepCheck]
  simp only [selectedAction, hnone, Option.getD_none]

/-- A successful synthesis returns exactly the executable program built from
the supplied data and has checked all three acceptance conditions. -/
theorem synthesize_eq_some_iff [DecidableEq A]
    (initial : Finset X) (ordered : List A) (fallback : A) (program : Program X Y A) :
    synthesize q R C initial ordered fallback = some program ↔
      initial.Nonempty ∧ (∀ a : A, a ∈ ordered) ∧
        finiteMemoryCheck q R C initial = true ∧
          program = buildProgram q R C initial ordered fallback := by
  by_cases hne : initial.Nonempty <;>
    by_cases hcomplete : ∀ a : A, a ∈ ordered <;>
      by_cases hcheck : finiteMemoryCheck q R C initial = true <;>
        simp [synthesize, hne, hcomplete, hcheck, eq_comm]

/-- The synthesis decision includes list coverage and a nonempty initial
support, instead of silently treating either as an unchecked runtime input. -/
theorem synthesize_isSome_iff [DecidableEq A]
    (initial : Finset X) (ordered : List A) (fallback : A) :
    (synthesize q R C initial ordered fallback).isSome = true ↔
      initial.Nonempty ∧ (∀ a : A, a ∈ ordered) ∧
        finiteMemoryCheck q R C initial = true := by
  by_cases hne : initial.Nonempty <;>
    by_cases hcomplete : ∀ a : A, a ∈ ordered <;>
      by_cases hcheck : finiteMemoryCheck q R C initial = true <;>
        simp [synthesize, hne, hcomplete, hcheck]

end FiniteSemantics

namespace Program

/-- Interpret a deterministic runtime action as a point-mass policy. The
noncomputability belongs to the PMF representation, not to the program. -/
noncomputable def toController {X Y A : Type u} (program : Program X Y A) :
    FiniteMemoryController (Finset X) Y A where
  initialMemory := program.initialMemory
  action := fun S => PMF.pure (program.action S)
  update := program.update

/-- The probability interpretation replays exactly the executable memory. -/
@[simp] theorem toController_memory {X Y A : Type u} (program : Program X Y A) :
    ∀ n (h : CausalHistory Y (A × Y) n),
      program.toController.memory n h = program.memory n h := by
  intro n
  induction n with
  | zero => intro h; rfl
  | succ n ih =>
      rintro ⟨h, a, y⟩
      change program.update (program.toController.memory n h) a y =
        program.update (program.memory n h) a y
      rw [ih]

end Program

/-- The actual stochastic-policy interpretation of the synthesized runtime. -/
noncomputable def semanticController
    {X Y A : Type u} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq Y]
    (q : X → Y) (R : X → A → X → Prop) (C : X → A → Prop)
    [∀ x a z, Decidable (R x a z)] [∀ x a, Decidable (C x a)]
    (initial : Finset X) (ordered : List A) (fallback : A) :
    FiniteMemoryController (Finset X) Y A :=
  (buildProgram q R C initial ordered fallback).toController

section ActualSource

variable {X Y A : Type u} [Fintype X] [Fintype A]
variable [DecidableEq X] [DecidableEq Y]
variable (q : X → Y) (R : X → A → X → Prop) (C : X → A → Prop)
variable [∀ x a z, Decidable (R x a z)] [∀ x a, Decidable (C x a)]
variable (initial : Finset X) (ordered : List A) (fallback : A)
variable (p₀ : PMF X) (P : ℕ → X → A → PMF X)

/-- Exact table/source agreement identifies executable memory with the
original source trace, including null records. No action selector is assumed. -/
theorem memory_eq_traceSupport
    (h0 : ∀ x, x ∈ initial ↔ x ∈ p₀.support)
    (hR : ∀ n x a z, z ∈ (P n x a).support ↔ R x a z) :
    ∀ n (h : CausalHistory Y (A × Y) n),
      (↑((semanticController q R C initial ordered fallback).memory n h) : Set X) =
        traceSupport p₀ q P n h := by
  intro n
  induction n with
  | zero =>
      intro y
      change (↑(initialMemory q initial y) : Set X) = initialSupport p₀ q y
      ext x
      simp [initialMemory, initialSupport, h0]
  | succ n ih =>
      rintro ⟨h, a, y⟩
      change (↑(nextMemory q R
        ((semanticController q R C initial ordered fallback).memory n h) a y) : Set X) =
          successorSupport q P n (traceSupport p₀ q P n h) a y
      rw [nextMemory, finiteRelationSuccessor_coe_eq_relationSuccessor, ih]
      exact (successorSupport_eq_relation_of_homogeneous q P R hR
        n (traceSupport p₀ q P n h) a y).symm

/-- The executable program's own replay has the same trace identity. -/
theorem program_memory_eq_traceSupport
    (h0 : ∀ x, x ∈ initial ↔ x ∈ p₀.support)
    (hR : ∀ n x a z, z ∈ (P n x a).support ↔ R x a z)
    (n : ℕ) (h : CausalHistory Y (A × Y) n) :
    (↑((buildProgram q R C initial ordered fallback).memory n h) : Set X) =
      traceSupport p₀ q P n h := by
  simpa only [semanticController, Program.toController_memory] using
    memory_eq_traceSupport q R C initial ordered fallback p₀ P h0 hR n h

/-- Winning membership is preserved on the supported histories of this
newly selected policy, not borrowed from the old classical selector. -/
theorem supported_histories_winning
    (hcomplete : ∀ a : A, a ∈ ordered)
    (h0 : ∀ x, x ∈ initial ↔ x ∈ p₀.support)
    (hR : ∀ n x a z, z ∈ (P n x a).support ↔ R x a z)
    (hcheck : finiteMemoryCheck q R C initial = true) :
    ∀ n, ∀ h ∈ (coarseLaw p₀ q P
      (semanticController q R C initial ordered fallback).policy n).support,
      traceSupport p₀ q P n h ∈ supportWinning q R C := by
  have hinit := (finiteMemoryCheck_iff_initial_winning
    q R C initial p₀ P h0 hR).mp hcheck
  intro n
  induction n with
  | zero =>
      intro y hy
      exact hinit y ((mem_coarseLaw_zero_support_iff p₀ q P
        (semanticController q R C initial ordered fallback).policy y).mp hy)
  | succ n ih =>
      rintro ⟨h, a, y⟩ hh
      have hparts := (mem_coarseLaw_succ_support_iff p₀ q P
        (semanticController q R C initial ordered fallback).policy n h a y).mp hh
      let S := (semanticController q R C initial ordered fallback).memory n h
      have hmem : (↑S : Set X) = traceSupport p₀ q P n h :=
        memory_eq_traceSupport q R C initial ordered fallback p₀ P h0 hR n h
      have hwin : (↑S : Set X) ∈ supportWinning q R C := by
        rw [hmem]
        exact ih h hparts.1
      have ha := hparts.2.1
      change a ∈ (PMF.pure (selectedAction q R C ordered fallback S)).support at ha
      have haeq : a = selectedAction q R C ordered fallback S := by
        simpa only [PMF.support_pure, Set.mem_singleton_iff] using ha
      have hstep := selectedAction_step q R C ordered fallback hcomplete S hwin
      change successorSupport q P n (traceSupport p₀ q P n h) a y ∈ supportWinning q R C
      rw [successorSupport_eq_relation_of_homogeneous q P R hR, haeq, ← hmem]
      apply hstep.2 y
      rw [hmem, ← haeq, ← successorSupport_eq_relation_of_homogeneous q P R hR n]
      exact hparts.2.2

variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace A] [MeasurableSingletonClass A]

/-- Every time has zero actual uncertified occupancy for the executable
controller's own deployment law. Numerical transition probabilities may vary. -/
theorem zero_uncovered
    (certified : ℕ → X → A → Prop)
    (hcomplete : ∀ a : A, a ∈ ordered)
    (h0 : ∀ x, x ∈ initial ↔ x ∈ p₀.support)
    (hR : ∀ n x a z, z ∈ (P n x a).support ↔ R x a z)
    (hC : ∀ n x a, certified n x a ↔ C x a)
    (hcheck : finiteMemoryCheck q R C initial = true) :
    ∀ n, (coverageDeploymentRowLaw p₀ q P
      (semanticController q R C initial ordered fallback).policy n).toMeasure.real
        {xa | ¬ certified n xa.1 xa.2} = 0 := by
  intro n
  apply (zero_uncovered_iff_support_certified p₀ q P
    (semanticController q R C initial ordered fallback).policy certified n).mpr
  intro h hh a ha x hx
  let S := (semanticController q R C initial ordered fallback).memory n h
  have hmem : (↑S : Set X) = traceSupport p₀ q P n h :=
    memory_eq_traceSupport q R C initial ordered fallback p₀ P h0 hR n h
  have hwin : (↑S : Set X) ∈ supportWinning q R C := by
    rw [hmem]
    exact supported_histories_winning q R C initial ordered fallback
      p₀ P hcomplete h0 hR hcheck n h hh
  change a ∈ (PMF.pure (selectedAction q R C ordered fallback S)).support at ha
  have haeq : a = selectedAction q R C ordered fallback S := by
    simpa only [PMF.support_pure, Set.mem_singleton_iff] using ha
  apply (hC n x a).mpr
  rw [haeq]
  apply (selectedAction_step q R C ordered fallback hcomplete S hwin).1 x
  rwa [hmem]

/-- For exact source representations and a complete action list, executable
synthesis succeeds exactly when some complete causal policy can certify all
times. Its empty-input guard adds no rejection of an actual initial PMF. -/
theorem synthesize_isSome_iff_exists_all_times_policy [DecidableEq A]
    (certified : ℕ → X → A → Prop)
    (hcomplete : ∀ a : A, a ∈ ordered)
    (h0 : ∀ x, x ∈ initial ↔ x ∈ p₀.support)
    (hR : ∀ n x a z, z ∈ (P n x a).support ↔ R x a z)
    (hC : ∀ n x a, certified n x a ↔ C x a) :
    (synthesize q R C initial ordered fallback).isSome = true ↔
      ∃ π : ∀ n, CausalHistory Y (A × Y) n → PMF A,
        ∀ n, (coverageDeploymentRowLaw p₀ q P π n).toMeasure.real
          {xa | ¬ certified n xa.1 xa.2} = 0 := by
  have hne : initial.Nonempty := by
    obtain ⟨x, hx⟩ := p₀.support_nonempty
    exact ⟨x, (h0 x).mpr hx⟩
  rw [synthesize_isSome_iff]
  have hiff := finiteMemoryCheck_iff_exists_all_times_policy q R C initial p₀ P
    certified (PMF.pure fallback) h0 hR hC
  exact ⟨fun h => hiff.mp h.2.2, fun h => ⟨hne, hcomplete, hiff.mpr h⟩⟩

/-- A returned runtime program carries the actual zero-occupancy guarantee;
list completeness and viability are extracted from successful synthesis. -/
theorem synthesize_some_zero_uncovered [DecidableEq A]
    (certified : ℕ → X → A → Prop) (program : Program X Y A)
    (hsynth : synthesize q R C initial ordered fallback = some program)
    (h0 : ∀ x, x ∈ initial ↔ x ∈ p₀.support)
    (hR : ∀ n x a z, z ∈ (P n x a).support ↔ R x a z)
    (hC : ∀ n x a, certified n x a ↔ C x a) :
    ∀ n, (coverageDeploymentRowLaw p₀ q P program.toController.policy n).toMeasure.real
      {xa | ¬ certified n xa.1 xa.2} = 0 := by
  obtain ⟨_, hcomplete, hcheck, rfl⟩ :=
    (synthesize_eq_some_iff q R C initial ordered fallback program).mp hsynth
  exact zero_uncovered q R C initial ordered fallback p₀ P
    certified hcomplete h0 hR hC hcheck

variable [MeasurableSpace (Finset X)] [MeasurableSingletonClass (Finset X)]

/-- The new controller is physically safe in its own infinite source law
when the independent initial-safety and certified-support conditions hold. -/
theorem all_times_physical_safe
    (certified : ℕ → X → A → Prop)
    (hcomplete : ∀ a : A, a ∈ ordered)
    (h0 : ∀ x, x ∈ initial ↔ x ∈ p₀.support)
    (hR : ∀ n x a z, z ∈ (P n x a).support ↔ R x a z)
    (hC : ∀ n x a, certified n x a ↔ C x a)
    (hcheck : finiteMemoryCheck q R C initial = true)
    (K : Set X) (hinit : ∀ x ∈ p₀.support, x ∈ K)
    (hclosed : ∀ x a, x ∈ K → C x a → ∀ z, R x a z → z ∈ K) :
    FiniteMemoryPhysicalSafety.stateTrajMeasure
      (semanticController q R C initial ordered fallback) p₀ q P
        {ω | ∀ n : ℕ, ω n ∈ K} = 1 := by
  apply FiniteMemoryPhysicalSafety.controller_all_times_physical_safe
    (semanticController q R C initial ordered fallback) p₀ q P certified K hinit
  · intro n x a hx hc z hz
    exact hclosed x a hx ((hC n x a).mp hc) z ((hR n x a z).mp hz)
  · exact zero_uncovered q R C initial ordered fallback p₀ P
      certified hcomplete h0 hR hC hcheck

/-- End-to-end safety of the actual executable output, with no externally
supplied winning selector and no identification with the old selected policy. -/
theorem synthesize_some_all_times_physical_safe [DecidableEq A]
    (certified : ℕ → X → A → Prop) (program : Program X Y A)
    (hsynth : synthesize q R C initial ordered fallback = some program)
    (h0 : ∀ x, x ∈ initial ↔ x ∈ p₀.support)
    (hR : ∀ n x a z, z ∈ (P n x a).support ↔ R x a z)
    (hC : ∀ n x a, certified n x a ↔ C x a)
    (K : Set X) (hinit : ∀ x ∈ p₀.support, x ∈ K)
    (hclosed : ∀ x a, x ∈ K → C x a → ∀ z, R x a z → z ∈ K) :
    FiniteMemoryPhysicalSafety.stateTrajMeasure program.toController p₀ q P
      {ω | ∀ n : ℕ, ω n ∈ K} = 1 := by
  obtain ⟨_, hcomplete, hcheck, rfl⟩ :=
    (synthesize_eq_some_iff q R C initial ordered fallback program).mp hsynth
  exact all_times_physical_safe q R C initial ordered fallback p₀ P
    certified hcomplete h0 hR hC hcheck K hinit hclosed

open UEOT.V3.FiniteDiscountedControl UEOT.V3.QSDPerron
open FiniteMemoryRealization SourcePolicyPathBridgeCheck SameSourceKilledPathCheck
open scoped Classical BigOperators

noncomputable local instance pairDecidableEq :
    DecidableEq (X × Finset X) := Classical.decEq _

/-- With one fixed numerical source, a successfully synthesized program has
unit killed mass at every finite time on its actual state-memory chain. Safety
is derived from synthesis, initial safety and certified relation closure. -/
theorem synthesize_some_killed_mass_one [DecidableEq A] [Nonempty A]
    (source : Model X (fun _ => A))
    (certified : ℕ → X → A → Prop) (program : Program X Y A)
    (hsynth : synthesize q R C initial ordered fallback = some program)
    (h0 : ∀ x, x ∈ initial ↔ x ∈ p₀.support)
    (hR : ∀ x a z, z ∈ (source.transitionPMF x a).support ↔ R x a z)
    (hC : ∀ n x a, certified n x a ↔ C x a)
    (K : Set X) (hinit : ∀ x ∈ p₀.support, x ∈ K)
    (hclosed : ∀ x a, x ∈ K → C x a → ∀ z, R x a z → z ∈ K)
    (n : ℕ) :
    ∑ v : (Prod.fst ⁻¹' K : Set (X × Finset X)),
      rowApply (safeInitialRow (augmentedInitial program.toController p₀ q)
        (Prod.fst ⁻¹' K))
        ((killedMatrix (HomogeneousMemorySurvival.augmentedModel source program.toController q)
          (liftedStationaryPolicy Prod.snd program.toController.action)
          (Prod.fst ⁻¹' K)) ^ n) v = 1 := by
  rw [← HomogeneousMemorySurvival.actual_finite_survival_eq_killed_mass
    source program.toController q p₀ K n]
  have hzero := synthesize_some_zero_uncovered q R C initial ordered fallback p₀
    (fun _ => source.transitionPMF) certified program hsynth h0 (fun _ => hR) hC
  have hsafety := FiniteMemoryPhysicalSafety.actual_finite_safety_one p₀ q
    (fun _ => source.transitionPMF) program.toController.policy certified K hinit
    (by
      intro m x a hx hc z hz
      exact hclosed x a hx ((hC m x a).mp hc) z ((hR x a z).mp hz)) hzero n
  simpa only [Measure.real, ENNReal.toReal_one] using congrArg ENNReal.toReal hsafety

end ActualSource

end ExecutableSupportSynthesis
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
