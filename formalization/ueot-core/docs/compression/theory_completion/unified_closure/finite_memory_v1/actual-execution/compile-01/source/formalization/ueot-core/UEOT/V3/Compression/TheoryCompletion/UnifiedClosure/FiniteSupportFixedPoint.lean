import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteSupportViabilityCheck
import Mathlib.Data.Fintype.Powerset

/-!
# A bounded greatest fixed point on observed supports

The arena consists of nonempty subsets contained in one observation fiber.
The transition input is a fixed support relation, not a fixed numerical PMF.
Backward refinement stabilizes after at most the number of arena supports,
and the resulting greatest fixed point is equivalent to every finite
remaining-horizon viability problem. The empty support is added only when
counting total-controller memory, including impossible observation records.

The existing finite relation checker remains the executable recursion.
This module does not assert that an arbitrary PMF supplies executable exact
support decisions, or that qualitative support homogeneity gives a fixed
numerical killed matrix.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
namespace SupportViabilityClosure

open scoped Classical

universe u

noncomputable section

/-- One observed successor for a fixed qualitative transition relation. -/
def relationSuccessor
    {X Y A : Type u} (q : X → Y) (R : X → A → X → Prop)
    (S : Set X) (a : A) (y : Y) : Set X :=
  {x' | q x' = y ∧ ∃ x ∈ S, R x a x'}

/-- The finite arena excludes both the empty set and sets mixing distinct
current observations. Finiteness of the ambient observation type is not needed. -/
def supportArena {X Y : Type u} (q : X → Y) : Set (Set X) :=
  {S | S.Nonempty ∧ ∃ y : Y, ∀ x ∈ S, q x = y}

/-- Every nonempty observed successor belongs to the observation arena. -/
theorem relationSuccessor_mem_arena
    {X Y A : Type u} (q : X → Y) (R : X → A → X → Prop)
    (S : Set X) (a : A) (y : Y)
    (hne : (relationSuccessor q R S a y).Nonempty) :
    relationSuccessor q R S a y ∈ supportArena q :=
  ⟨hne, y, fun _ hx => hx.1⟩

/-- Each nonempty initial observation fiber is an arena support of the
original initial law, without renormalizing or replacing that law. -/
theorem initialSupport_mem_arena
    {X Y : Type u} (p₀ : PMF X) (q : X → Y) (y : Y)
    (hne : (initialSupport p₀ q y).Nonempty) :
    initialSupport p₀ q y ∈ supportArena q :=
  ⟨hne, y, fun _ hx => hx.2⟩

/-- The existing executable successor computes this same set when supplied
the fixed relation. No new finite-horizon checker is introduced. -/
theorem finiteRelationSuccessor_coe_eq_relationSuccessor
    {X Y A : Type u} [Fintype X] [DecidableEq X] [DecidableEq Y]
    (q : X → Y) (R : X → A → X → Prop)
    [∀ x a z, Decidable (R x a z)]
    (n : ℕ) (S : Finset X) (a : A) (y : Y) :
    (↑(finiteRelationSuccessor q (fun _ => R) n S a y) : Set X) =
      relationSuccessor q R (↑S : Set X) a y := by
  ext z
  simp [finiteRelationSuccessor, relationSuccessor]

/-- An action must certify the entire current support and preserve the
candidate family after every nonempty observation branch. -/
def supportPre
    {X Y A : Type u} (q : X → Y) (R : X → A → X → Prop)
    (C : X → A → Prop) (W : Set (Set X)) : Set (Set X) :=
  {S | S ∈ supportArena q ∧ ∃ a : A,
    (∀ x ∈ S, C x a) ∧
      ∀ y : Y, (relationSuccessor q R S a y).Nonempty →
        relationSuccessor q R S a y ∈ W}

/-- Backward refinement is monotone in its candidate family. -/
theorem supportPre_mono
    {X Y A : Type u} (q : X → Y) (R : X → A → X → Prop)
    (C : X → A → Prop) {V W : Set (Set X)} (hVW : V ⊆ W) :
    supportPre q R C V ⊆ supportPre q R C W := by
  rintro S ⟨hS, a, hcert, hnext⟩
  exact ⟨hS, a, hcert, fun y hy => hVW (hnext y hy)⟩

/-- Start with all possible nonempty observation supports and repeatedly
remove those without a jointly certified continuation action. -/
def supportIterate
    {X Y A : Type u} (q : X → Y) (R : X → A → X → Prop)
    (C : X → A → Prop) : ℕ → Set (Set X)
  | 0 => supportArena q
  | k + 1 => supportPre q R C (supportIterate q R C k)

/-- Every refinement remains inside the observation arena. -/
theorem supportIterate_subset_arena
    {X Y A : Type u} (q : X → Y) (R : X → A → X → Prop)
    (C : X → A → Prop) (k : ℕ) :
    supportIterate q R C k ⊆ supportArena q := by
  cases k with
  | zero => exact fun _ h => h
  | succ k => exact fun _ h => h.1

/-- The candidate families form a decreasing chain. -/
theorem supportIterate_succ_subset
    {X Y A : Type u} (q : X → Y) (R : X → A → X → Prop)
    (C : X → A → Prop) (k : ℕ) :
    supportIterate q R C (k + 1) ⊆ supportIterate q R C k := by
  induction k with
  | zero => exact fun _ h => h.1
  | succ k ih => exact supportPre_mono q R C ih

/-- The exact finite-horizon recursion agrees with the support refinement.
The absolute time is arbitrary because both relation and certification here
are fixed; numerical transition weights do not enter this equivalence. -/
theorem mem_supportIterate_iff_viableWith
    {X Y A : Type u} (q : X → Y) (R : X → A → X → Prop)
    (C : X → A → Prop) :
    ∀ k n (S : Set X), S ∈ supportArena q →
      (S ∈ supportIterate q R C k ↔
        viableWith (fun _ => relationSuccessor q R) (fun _ => C) n k S) := by
  intro k
  induction k with
  | zero =>
      intro n S hS
      exact ⟨fun _ => trivial, fun _ => hS⟩
  | succ k ih =>
      intro n S hS
      constructor
      · rintro ⟨_, a, hcert, hnext⟩
        refine ⟨a, hcert, ?_⟩
        intro y hy
        exact (ih (n + 1) (relationSuccessor q R S a y)
          (relationSuccessor_mem_arena q R S a y hy)).mp (hnext y hy)
      · rintro ⟨a, hcert, hnext⟩
        refine ⟨hS, a, hcert, ?_⟩
        intro y hy
        exact (ih (n + 1) (relationSuccessor q R S a y)
          (relationSuccessor_mem_arena q R S a y hy)).mpr (hnext y hy)

/-- A finite mathematical enumeration of the arena. Deciding arbitrary
observation fibers may use classical choice; executable data have their own
explicit deciders in the existing finite relation checker. -/
def supportArenaFinset
    {X Y : Type u} [Fintype X] (q : X → Y) : Finset (Set X) :=
  Finset.univ.filter (fun S => S ∈ supportArena q)

/-- The refinement bound counts supports, not microscopic states. -/
def supportArenaCard
    {X Y : Type u} [Fintype X] (q : X → Y) : ℕ :=
  (supportArenaFinset q).card

private def supportIterateFinset
    {X Y A : Type u} [Fintype X] (q : X → Y)
    (R : X → A → X → Prop) (C : X → A → Prop) (k : ℕ) :
    Finset (Set X) :=
  Finset.univ.filter (fun S => S ∈ supportIterate q R C k)

private theorem exists_supportIterate_fixed
    {X Y A : Type u} [Fintype X] (q : X → Y)
    (R : X → A → X → Prop) (C : X → A → Prop) :
    ∃ k ≤ supportArenaCard q,
      supportIterate q R C (k + 1) = supportIterate q R C k := by
  let M := supportArenaCard q
  let B := supportIterateFinset q R C
  by_contra hnone
  have hdrop (k : ℕ) (hk : k ≤ M) : (B (k + 1)).card < (B k).card := by
    have hsub : B (k + 1) ⊆ B k := by
      intro S hS
      have hS' : S ∈ supportIterate q R C (k + 1) := by
        simpa [B, supportIterateFinset] using hS
      simpa [B, supportIterateFinset] using
        supportIterate_succ_subset q R C k hS'
    have hne : B (k + 1) ≠ B k := by
      intro heq
      apply hnone
      refine ⟨k, hk, ?_⟩
      ext S
      have hm : S ∈ B (k + 1) ↔ S ∈ B k := by rw [heq]
      simpa [B, supportIterateFinset] using hm
    exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
  have hcost : ∀ k, k ≤ M + 1 → (B k).card + k ≤ M := by
    intro k
    induction k with
    | zero =>
        intro _
        simp [B, M, supportIterateFinset, supportIterate,
          supportArenaCard, supportArenaFinset]
    | succ k ih =>
        intro hk
        have hprev := ih (by omega)
        have hstrict := hdrop k (by omega)
        omega
  have himpossible := hcost (M + 1) (by omega)
  omega

private theorem supportIterate_eq_add_of_fixed
    {X Y A : Type u} (q : X → Y) (R : X → A → X → Prop)
    (C : X → A → Prop) (k : ℕ)
    (hfix : supportIterate q R C (k + 1) = supportIterate q R C k) :
    ∀ t, supportIterate q R C (k + t) = supportIterate q R C k := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
      change supportPre q R C (supportIterate q R C (k + t)) = _
      rw [ih]
      exact hfix

private theorem supportIterate_at_card_fixed
    {X Y A : Type u} [Fintype X] (q : X → Y)
    (R : X → A → X → Prop) (C : X → A → Prop) :
    supportIterate q R C (supportArenaCard q + 1) =
      supportIterate q R C (supportArenaCard q) := by
  obtain ⟨k, hk, hfix⟩ := exists_supportIterate_fixed q R C
  have hsum : k + (supportArenaCard q - k) = supportArenaCard q := by omega
  have hnow := supportIterate_eq_add_of_fixed q R C k hfix (supportArenaCard q - k)
  have hnext := supportIterate_eq_add_of_fixed q R C k hfix
    (supportArenaCard q - k + 1)
  rw [← Nat.add_assoc, hsum] at hnext
  rw [hsum] at hnow
  exact hnext.trans hnow.symm

/-- The candidate family after the proven finite cutoff. -/
def supportWinning
    {X Y A : Type u} [Fintype X] (q : X → Y)
    (R : X → A → X → Prop) (C : X → A → Prop) : Set (Set X) :=
  supportIterate q R C (supportArenaCard q)

/-- At the arena-cardinality cutoff refinement has reached a fixed point.
This discharges fixed-point existence instead of assuming it in a package. -/
theorem supportWinning_fixed
    {X Y A : Type u} [Fintype X] (q : X → Y)
    (R : X → A → X → Prop) (C : X → A → Prop) :
    supportPre q R C (supportWinning q R C) = supportWinning q R C :=
  supportIterate_at_card_fixed q R C

/-- Every larger finite cutoff gives the same winning family. In particular,
an executable upper bound on the arena cardinal can replace its classical
enumeration when reusing the existing finite-horizon checker. -/
theorem supportIterate_eq_winning_of_card_le
    {X Y A : Type u} [Fintype X] (q : X → Y)
    (R : X → A → X → Prop) (C : X → A → Prop)
    (K : ℕ) (hK : supportArenaCard q ≤ K) :
    supportIterate q R C K = supportWinning q R C := by
  have hsum : supportArenaCard q + (K - supportArenaCard q) = K := by omega
  have hstable := supportIterate_eq_add_of_fixed q R C (supportArenaCard q)
    (supportIterate_at_card_fixed q R C) (K - supportArenaCard q)
  rw [hsum] at hstable
  exact hstable

/-- Winning supports are nonempty and have one current observation. -/
theorem supportWinning_subset_arena
    {X Y A : Type u} [Fintype X] (q : X → Y)
    (R : X → A → X → Prop) (C : X → A → Prop) :
    supportWinning q R C ⊆ supportArena q :=
  supportIterate_subset_arena q R C (supportArenaCard q)

/-- A winning support supplies a common certified action and preserves
winning membership on every nonempty observed successor. -/
theorem supportWinning_step
    {X Y A : Type u} [Fintype X] (q : X → Y)
    (R : X → A → X → Prop) (C : X → A → Prop)
    (S : Set X) (hS : S ∈ supportWinning q R C) :
    ∃ a : A, (∀ x ∈ S, C x a) ∧
      ∀ y : Y, (relationSuccessor q R S a y).Nonempty →
        relationSuccessor q R S a y ∈ supportWinning q R C := by
  have hpre : S ∈ supportPre q R C (supportWinning q R C) := by
    rw [supportWinning_fixed]
    exact hS
  exact hpre.2

private theorem postfixed_subset_every_supportIterate
    {X Y A : Type u} (q : X → Y) (R : X → A → X → Prop)
    (C : X → A → Prop) (W : Set (Set X))
    (hW : W ⊆ supportPre q R C W) :
    ∀ k, W ⊆ supportIterate q R C k := by
  intro k
  induction k with
  | zero => exact fun _ hS => (hW hS).1
  | succ k ih =>
      intro S hS
      exact supportPre_mono q R C ih (hW hS)

/-- The bounded result includes every family with a certified action
preserving all its nonempty observation branches: it is greatest. -/
theorem supportWinning_greatest_of_postfixed
    {X Y A : Type u} [Fintype X] (q : X → Y)
    (R : X → A → X → Prop) (C : X → A → Prop)
    (W : Set (Set X)) (hW : W ⊆ supportPre q R C W) :
    W ⊆ supportWinning q R C :=
  postfixed_subset_every_supportIterate q R C W hW (supportArenaCard q)

/-- Checking the single bounded horizon is equivalent to all horizons,
for every support in the observation arena and every starting time. -/
theorem supportWinning_iff_all_horizons
    {X Y A : Type u} [Fintype X] (q : X → Y)
    (R : X → A → X → Prop) (C : X → A → Prop)
    (n : ℕ) (S : Set X) (hS : S ∈ supportArena q) :
    S ∈ supportWinning q R C ↔
      ∀ k, viableWith (fun _ => relationSuccessor q R) (fun _ => C) n k S := by
  constructor
  · intro hwin k
    have hpost : supportWinning q R C ⊆
        supportPre q R C (supportWinning q R C) := by
      intro U hU
      rw [supportWinning_fixed]
      exact hU
    exact (mem_supportIterate_iff_viableWith q R C k n S hS).mp
      (postfixed_subset_every_supportIterate q R C
        (supportWinning q R C) hpost k hwin)
  · intro hV
    exact (mem_supportIterate_iff_viableWith q R C
      (supportArenaCard q) n S hS).mpr (hV (supportArenaCard q))

/-- Total support memory includes the empty record support as well as
all nonempty single-observation supports, including unreachable ones. -/
def SupportMemory {X Y : Type u} (q : X → Y) :=
  {S : Set X // S = ∅ ∨ S ∈ supportArena q}

noncomputable instance supportMemoryFintype
    {X Y : Type u} [Fintype X] (q : X → Y) : Fintype (SupportMemory q) :=
  Fintype.ofFinite _

/-- Exactly one additional memory value accounts for the empty support. -/
theorem supportMemory_card
    {X Y : Type u} [Fintype X] (q : X → Y) :
    Fintype.card (SupportMemory q) = supportArenaCard q + 1 := by
  let T : Finset (Set X) := insert ∅ (supportArenaFinset q)
  have hmem (S : Set X) : S ∈ T ↔ S = ∅ ∨ S ∈ supportArena q := by
    simp [T, supportArenaFinset]
  let e : SupportMemory q ≃ {S : Set X // S ∈ T} :=
    { toFun := fun S => ⟨S.1, (hmem S.1).mpr S.2⟩
      invFun := fun S => ⟨S.1, (hmem S.1).mp S.2⟩
      left_inv := by intro S; rfl
      right_inv := by intro S; rfl }
  have hnot : (∅ : Set X) ∉ supportArenaFinset q := by
    simp [supportArenaFinset, supportArena]
  have hcard := Fintype.card_congr e
  simpa [T, Finset.card_insert_of_notMem hnot, supportArenaCard] using hcard

/-- The whole total-controller memory, not just its reachable states, has
at most the number of subsets of the finite microscopic state space. -/
theorem supportArenaCard_add_one_le_pow
    {X Y : Type u} [Fintype X] (q : X → Y) :
    supportArenaCard q + 1 ≤ 2 ^ Fintype.card X := by
  rw [← supportMemory_card]
  have hcard := Fintype.card_le_of_injective
    (fun S : SupportMemory q => S.1) Subtype.val_injective
  simpa only [Fintype.card_set] using hcard

end
end SupportViabilityClosure
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
