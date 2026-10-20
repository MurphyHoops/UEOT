import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteSupportViability

/-!
# Exact finite support-viability checking

The executable entry point consumes a decidable finite support relation.
Its proved equivalence to the actual PMF support connects its Boolean result
to the existing exact viability predicate. The original actual-PMF checker
and its correctness theorem are retained as the reusable mathematical
bridge; arbitrary noncomputable PMFs are not executable input data.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
namespace SupportViabilityClosure

universe u

/-- Compute one complete observation-successor support as a finite set.
The source-support decider is required to decide the actual PMF support. -/
def finiteSuccessor
    {X Y A : Type u} [Fintype X] [DecidableEq X] [DecidableEq Y]
    (q : X → Y) (P : ℕ → X → A → PMF X)
    [∀ n x a z, Decidable (z ∈ (P n x a).support)]
    (n : ℕ) (S : Finset X) (a : A) (y : Y) : Finset X :=
  Finset.univ.filter fun z =>
    q z = y ∧ ∃ x ∈ S, z ∈ (P n x a).support

/-- The computed support is extensionally the already defined actual
support successor. No representation-correctness premise is assumed. -/
theorem finiteSuccessor_coe_eq
    {X Y A : Type u} [Fintype X] [DecidableEq X] [DecidableEq Y]
    (q : X → Y) (P : ℕ → X → A → PMF X)
    [∀ n x a z, Decidable (z ∈ (P n x a).support)]
    (n : ℕ) (S : Finset X) (a : A) (y : Y) :
    (↑(finiteSuccessor q P n S a y) : Set X) =
      successorSupport q P n (↑S : Set X) a y := by
  ext z
  simp [finiteSuccessor, successorSupport]

/-- A finite Boolean decision procedure for the whole backward viability
recursion. It enumerates X and A and needs no finite enumeration of Y. -/
def finiteViabilityCheck
    {X Y A : Type u} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq Y]
    (q : X → Y) (P : ℕ → X → A → PMF X)
    (certified : ℕ → X → A → Prop)
    [∀ n x a z, Decidable (z ∈ (P n x a).support)]
    [∀ n x a, Decidable (certified n x a)] :
    ℕ → ℕ → Finset X → Bool
  | _, 0, _ => true
  | n, k + 1, S =>
      decide (∃ a : A,
        (∀ x ∈ S, certified n x a) ∧
          ∀ z : X,
            (finiteSuccessor q P n S a (q z)).Nonempty →
              finiteViabilityCheck q P certified (n + 1) k
                (finiteSuccessor q P n S a (q z)) = true)

/-- Exact correctness of the finite checker. Nonempty observation branches
are enumerated via a witness z in their full successor set, rather than
turning indistinguishable microscopic states into separate control choices. -/
theorem finiteViabilityCheck_correct
    {X Y A : Type u} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq Y]
    (q : X → Y) (P : ℕ → X → A → PMF X)
    (certified : ℕ → X → A → Prop)
    [∀ n x a z, Decidable (z ∈ (P n x a).support)]
    [∀ n x a, Decidable (certified n x a)] :
    ∀ k n (S : Finset X),
      finiteViabilityCheck q P certified n k S = true ↔
        Viable q P certified n k (↑S : Set X) := by
  intro k
  induction k with
  | zero =>
      intro n S
      simp [finiteViabilityCheck, Viable, viableWith]
  | succ k ih =>
      intro n S
      simp only [finiteViabilityCheck, decide_eq_true_eq]
      constructor
      · rintro ⟨a, hcert, hnext⟩
        refine ⟨a, hcert, ?_⟩
        intro y hy
        obtain ⟨z, hz⟩ := hy
        have hobs : q z = y := hz.1
        have hfinite : (finiteSuccessor q P n S a y).Nonempty := by
          refine ⟨z, ?_⟩
          change z ∈ (↑(finiteSuccessor q P n S a y) : Set X)
          rw [finiteSuccessor_coe_eq]
          exact hz
        have hcheck := hnext z
        rw [hobs] at hcheck
        have hV := (ih (n + 1) (finiteSuccessor q P n S a y)).mp
          (hcheck hfinite)
        simpa only [finiteSuccessor_coe_eq] using hV
      · rintro ⟨a, hcert, hnext⟩
        refine ⟨a, hcert, ?_⟩
        intro z hfinite
        have hsupport :
            (successorSupport q P n (↑S : Set X) a (q z)).Nonempty := by
          obtain ⟨w, hw⟩ := hfinite
          refine ⟨w, ?_⟩
          have hmem : w ∈ (↑(finiteSuccessor q P n S a (q z)) : Set X) := hw
          rw [finiteSuccessor_coe_eq] at hmem
          exact hmem
        apply (ih (n + 1) (finiteSuccessor q P n S a (q z))).mpr
        simpa only [finiteSuccessor_coe_eq] using hnext (q z) hsupport


end SupportViabilityClosure
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
namespace SupportViabilityClosure

universe u

/-- Execute one full observation successor using an explicit support relation. -/
def finiteRelationSuccessor
    {X Y A : Type u} [Fintype X] [DecidableEq X] [DecidableEq Y]
    (q : X → Y) (R : ℕ → X → A → X → Prop)
    [∀ n x a z, Decidable (R n x a z)]
    (n : ℕ) (S : Finset X) (a : A) (y : Y) : Finset X :=
  Finset.univ.filter fun z => q z = y ∧ ∃ x ∈ S, R n x a z

/-- A finite executable check whose data are a decidable support relation,
observation map, and certification predicate. Correctness for an actual PMF
source additionally requires the proved representation equivalence below. -/
def finiteRelationViabilityCheck
    {X Y A : Type u} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq Y]
    (q : X → Y) (R : ℕ → X → A → X → Prop)
    (certified : ℕ → X → A → Prop)
    [∀ n x a z, Decidable (R n x a z)]
    [∀ n x a, Decidable (certified n x a)] :
    ℕ → ℕ → Finset X → Bool
  | _, 0, _ => true
  | n, k + 1, S =>
      decide (∃ a : A,
        (∀ x ∈ S, certified n x a) ∧
          ∀ z : X,
            (finiteRelationSuccessor q R n S a (q z)).Nonempty →
              finiteRelationViabilityCheck q R certified (n + 1) k
                (finiteRelationSuccessor q R n S a (q z)) = true)

/-- The represented successor is the original computed actual successor. -/
theorem finiteRelationSuccessor_eq
    {X Y A : Type u} [Fintype X] [DecidableEq X] [DecidableEq Y]
    (q : X → Y) (R : ℕ → X → A → X → Prop)
    (P : ℕ → X → A → PMF X)
    [∀ n x a z, Decidable (R n x a z)]
    [∀ n x a z, Decidable (z ∈ (P n x a).support)]
    (hR : ∀ n x a z, R n x a z ↔ z ∈ (P n x a).support)
    (n : ℕ) (S : Finset X) (a : A) (y : Y) :
    finiteRelationSuccessor q R n S a y = finiteSuccessor q P n S a y := by
  ext z
  simp [finiteRelationSuccessor, finiteSuccessor, hR]

/-- Representing the source changes only the executable data boundary:
the resulting Boolean is exactly the existing actual-PMF check. -/
theorem finiteRelationViabilityCheck_eq
    {X Y A : Type u} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq Y]
    (q : X → Y) (R : ℕ → X → A → X → Prop)
    (P : ℕ → X → A → PMF X) (certified : ℕ → X → A → Prop)
    [∀ n x a z, Decidable (R n x a z)]
    [∀ n x a z, Decidable (z ∈ (P n x a).support)]
    [∀ n x a, Decidable (certified n x a)]
    (hR : ∀ n x a z, R n x a z ↔ z ∈ (P n x a).support) :
    ∀ k n (S : Finset X),
      finiteRelationViabilityCheck q R certified n k S =
        finiteViabilityCheck q P certified n k S := by
  intro k
  induction k with
  | zero =>
      intro n S
      rfl
  | succ k ih =>
      intro n S
      have hiff :
          finiteRelationViabilityCheck q R certified n (k + 1) S = true ↔
            finiteViabilityCheck q P certified n (k + 1) S = true := by
        simp only [finiteRelationViabilityCheck, finiteViabilityCheck,
          decide_eq_true_eq, finiteRelationSuccessor_eq q R P hR, ih]
      cases hleft : finiteRelationViabilityCheck q R certified n (k + 1) S <;>
        cases hright : finiteViabilityCheck q P certified n (k + 1) S <;>
          simp_all

/-- Consume the previously checked actual-source theorem after proving
representation correctness. No empirical or unverified support table is used. -/
theorem finiteRelationViabilityCheck_correct
    {X Y A : Type u} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq Y]
    (q : X → Y) (R : ℕ → X → A → X → Prop)
    (P : ℕ → X → A → PMF X) (certified : ℕ → X → A → Prop)
    [∀ n x a z, Decidable (R n x a z)]
    [∀ n x a z, Decidable (z ∈ (P n x a).support)]
    [∀ n x a, Decidable (certified n x a)]
    (hR : ∀ n x a z, R n x a z ↔ z ∈ (P n x a).support)
    (k n : ℕ) (S : Finset X) :
    finiteRelationViabilityCheck q R certified n k S = true ↔
      Viable q P certified n k (↑S : Set X) := by
  rw [finiteRelationViabilityCheck_eq q R P certified hR k n S]
  exact finiteViabilityCheck_correct q P certified k n S


end SupportViabilityClosure
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
