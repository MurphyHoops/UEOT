import UEOT.V3.Compression.RecursiveSufficientState
import Mathlib.Tactic

/-!
# SISC N1 — exact finite controlled stochastic quotient

Deterministic future equivalence automatically supports an action update.
For a genuinely stochastic state kernel, **this implication is not free**:
the probabilities of moving into *every* observable equivalence class must
agree for equivalent source states. This is the strong-lumpability boundary.

All probability normalization and class masses use finite sums. No
measurable-space kernel or physical Objecthood result is inferred here.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

open UEOT.V3.Compression.RecursiveSufficientState

universe uX uA uQ

/-- A finite controlled stochastic transition law on registered microstates. -/
structure FiniteControlledStochasticKernel (X : Type uX) (A : Type uA)
    [Fintype X] where
  mass : X → A → X → ℝ
  nonneg : ∀ x a y, 0 ≤ mass x a y
  normalized : ∀ x a, ∑ y, mass x a y = 1

/-- Probability carried by one reachable quotient fibre. -/
noncomputable def massIntoClass {X : Type uX} {A : Type uA} {Q : Type uQ}
    [Fintype X] (K : FiniteControlledStochasticKernel X A) (q : X → Q)
    (x : X) (a : A) (c : ReachableState q) : ℝ :=
  by
    classical
    exact ∑ y, if q y = c.1 then K.mass x a y else 0

/-- Strong finite lumpability, phrased entirely in terms of the observable
candidate representation, one action and transition mass into *each* class. -/
def StrongLumpability {X : Type uX} {A : Type uA} {Q : Type uQ}
    [Fintype X] (K : FiniteControlledStochasticKernel X A) (q : X → Q) : Prop :=
  ∀ x y, q x = q y → ∀ a c,
    massIntoClass K q x a c = massIntoClass K q y a c

/-- Strong lumpability is precisely input-fibre compatibility of the
class-mass response. This bridge reuses the pre-existing M-RS theorem. -/
theorem strong_lumpability_iff_input_fiber_compatible
    {X : Type uX} {A : Type uA} {Q : Type uQ}
    [Fintype X] (K : FiniteControlledStochasticKernel X A) (q : X → Q) :
    StrongLumpability K q ↔
      InputFiberCompatible q (fun x a c => massIntoClass K q x a c) := by
  constructor
  · intro h x y hxy a
    funext c
    exact h x y hxy a c
  · intro h x y hxy a c
    exact congrFun (h hxy a) c

/-- THE EXACT QUOTIENT CRITERION:

For a finite controlled stochastic process, the chosen quotient supports an
action-dependent class-transition kernel on its **reachable** states iff the
source kernel is strongly lumpable relative to that quotient. When it exists,
the class kernel is unique. This removes an otherwise hidden bridge premise.
-/
theorem strong_lumpability_iff_existsUnique_class_kernel
    {X : Type uX} {A : Type uA} {Q : Type uQ}
    [Fintype X] (K : FiniteControlledStochasticKernel X A) (q : X → Q) :
    StrongLumpability K q ↔
      ∃! Kbar : ReachableState q → A → ReachableState q → ℝ,
        ∀ x a c, Kbar (toReachable q x) a c = massIntoClass K q x a c := by
  constructor
  · intro hlump
    obtain ⟨U, hU, huniq⟩ := existsUnique_reachableUpdate q
      (fun x a c => massIntoClass K q x a c)
      ((strong_lumpability_iff_input_fiber_compatible K q).mp hlump)
    refine ⟨U, ?_, ?_⟩
    · intro x a c
      exact congrFun (hU x a) c
    · intro V hV
      apply huniq V
      intro x a
      funext c
      exact hV x a c
  · rintro ⟨Kbar, hfactor, _⟩
    intro x y hxy a c
    have hc : toReachable q x = toReachable q y := Subtype.ext hxy
    calc
      massIntoClass K q x a c = Kbar (toReachable q x) a c := (hfactor x a c).symm
      _ = Kbar (toReachable q y) a c := by rw [hc]
      _ = massIntoClass K q y a c := hfactor y a c

/-- Fibre mass is nonnegative: quotienting cannot introduce negative
transition weights. -/
theorem massIntoClass_nonneg
    {X : Type uX} {A : Type uA} {Q : Type uQ}
    [Fintype X] (K : FiniteControlledStochasticKernel X A) (q : X → Q)
    (x : X) (a : A) (c : ReachableState q) :
    0 ≤ massIntoClass K q x a c := by
  classical
  unfold massIntoClass
  apply Finset.sum_nonneg
  intro y _
  by_cases h : q y = c.1
  · simpa [h] using K.nonneg x a y
  · simp [h]

/-- The class fibres partition the finite source, so their masses sum to 1.
No Fintype instance on the quotient is assumed: it is derived from finite X
and surjectivity of the reachable-image map. -/
theorem massIntoClass_sum_one
    {X : Type uX} {A : Type uA} {Q : Type uQ}
    [Fintype X] (K : FiniteControlledStochasticKernel X A) (q : X → Q)
    (x : X) (a : A) :
    letI : Fintype (ReachableState q) :=
      Fintype.ofFinite (ReachableState q)
    ∑ c : ReachableState q, massIntoClass K q x a c = 1 := by
  classical
  letI : Finite (ReachableState q) :=
    Finite.of_surjective (toReachable q) (toReachable_surjective q)
  letI : Fintype (ReachableState q) := Fintype.ofFinite _
  change (∑ c : ReachableState q, massIntoClass K q x a c) = 1
  calc
    (∑ c : ReachableState q, massIntoClass K q x a c) =
        ∑ y : X, ∑ c : ReachableState q,
          if q y = c.1 then K.mass x a y else 0 := by
      simp only [massIntoClass]
      rw [Finset.sum_comm]
    _ = ∑ y : X, K.mass x a y := by
      apply Finset.sum_congr rfl
      intro y _
      have h : ∀ c : ReachableState q,
          (q y = c.1) ↔ (c = toReachable q y) := by
        intro c
        constructor
        · intro h; apply Subtype.ext; exact h.symm
        · intro h; exact congrArg Subtype.val h |>.symm
      simp_rw [h]
      simp
    _ = 1 := K.normalized x a

/-- Strong lumpability is equivalent to existence **and uniqueness of a
normalized nonnegative** controlled stochastic kernel on reachable quotient
classes, not merely a real-valued factorization. -/
theorem strong_lumpability_iff_existsUnique_stochastic_quotient
    {X : Type uX} {A : Type uA} {Q : Type uQ}
    [Fintype X] (K : FiniteControlledStochasticKernel X A) (q : X → Q) :
    StrongLumpability K q ↔
      letI : Fintype (ReachableState q) := Fintype.ofFinite _
      ∃! Kbar : FiniteControlledStochasticKernel (ReachableState q) A,
        ∀ x a c, Kbar.mass (toReachable q x) a c =
          massIntoClass K q x a c := by
  classical
  letI : Finite (ReachableState q) :=
    Finite.of_surjective (toReachable q) (toReachable_surjective q)
  letI : Fintype (ReachableState q) := Fintype.ofFinite _
  constructor
  · intro hlump
    obtain ⟨U, hU, huniq⟩ :=
      (strong_lumpability_iff_existsUnique_class_kernel K q).mp hlump
    let QK : FiniteControlledStochasticKernel (ReachableState q) A := {
      mass := U
      nonneg := by
        intro c a d
        rcases c.property with ⟨x, hx⟩
        have hc : c = toReachable q x := Subtype.ext hx.symm
        rw [hc, hU x a d]
        exact massIntoClass_nonneg K q x a d
      normalized := by
        intro c a
        rcases c.property with ⟨x, hx⟩
        have hc : c = toReachable q x := Subtype.ext hx.symm
        rw [hc]
        have hpoint : ∀ d : ReachableState q,
            U (toReachable q x) a d = massIntoClass K q x a d := by
          intro d
          exact hU x a d
        simp_rw [hpoint]
        exact massIntoClass_sum_one K q x a
    }
    refine ⟨QK, ?_, ?_⟩
    · intro x a d
      exact hU x a d
    · intro other hother
      have heq : other.mass = QK.mass := by
        funext c a d
        rcases c.property with ⟨x, hx⟩
        have hc : c = toReachable q x := Subtype.ext hx.symm
        rw [hc]
        exact (hother x a d).trans ((hU x a d).symm)
      cases other with
      | mk mass nonneg normalized =>
          dsimp [QK] at heq ⊢
          cases heq
          rfl
  · rintro ⟨QK, hfactor, _⟩
    intro x y hxy a c
    have hc : toReachable q x = toReachable q y := Subtype.ext hxy
    calc
      massIntoClass K q x a c = QK.mass (toReachable q x) a c :=
        (hfactor x a c).symm
      _ = QK.mass (toReachable q y) a c := by rw [hc]
      _ = massIntoClass K q y a c := hfactor y a c

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
