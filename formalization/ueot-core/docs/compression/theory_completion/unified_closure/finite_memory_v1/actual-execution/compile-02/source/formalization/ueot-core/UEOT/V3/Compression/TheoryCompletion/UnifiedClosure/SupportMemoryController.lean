import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteMemoryPolicy
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteSupportFixedPoint
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.InfiniteSupportViability

/-!
# A finite support controller in its own source experiment

The actual transition sequence may change its numerical probabilities. Its
support relation and certification predicate must have the fixed versions
specified below. The controller has autonomous output and update and a
fixed fallback PMF, so its entire policy has at most `|B_q| + 1` memory values.
Its replayed memory is proved equal to the original source trace support at
every record. Winning membership and zero uncertified occupancy are then
proved in the actual deployment laws of this newly constructed policy.

The controller is selected noncomputably. A finite mathematical cutoff is
not a polynomial complexity claim or an executable exact PMF-support oracle.
No identity with a previous horizon-dependent policy, physical safety,
reference-process check budget reduction, or fixed numerical killed matrix
is asserted.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
namespace SupportViabilityClosure

open MeasureTheory UEOT.V3.PathError
open scoped Classical

universe u

noncomputable section

/-- Support homogeneity identifies the actual time-dependent successor
with the fixed relation successor on every set and every record. -/
theorem successorSupport_eq_relation_of_homogeneous
    {X Y A : Type u} (q : X → Y) (P : ℕ → X → A → PMF X)
    (R : X → A → X → Prop)
    (hR : ∀ n x a z, z ∈ (P n x a).support ↔ R x a z)
    (n : ℕ) (S : Set X) (a : A) (y : Y) :
    successorSupport q P n S a y = relationSuccessor q R S a y := by
  ext z
  simp only [successorSupport, relationSuccessor, Set.mem_setOf_eq, hR]

/-- The finite backward problem is unchanged by replacing actual supports
and certifications by their proved homogeneous representations. -/
theorem viable_iff_homogeneous_relation
    {X Y A : Type u} (q : X → Y) (P : ℕ → X → A → PMF X)
    (certified : ℕ → X → A → Prop)
    (R : X → A → X → Prop) (C : X → A → Prop)
    (hR : ∀ n x a z, z ∈ (P n x a).support ↔ R x a z)
    (hC : ∀ n x a, certified n x a ↔ C x a)
    (n k : ℕ) (S : Set X) :
    Viable q P certified n k S ↔
      viableWith (fun _ => relationSuccessor q R) (fun _ => C) n k S := by
  have hnext : successorSupport q P = fun _ => relationSuccessor q R := by
    funext n S a y
    exact successorSupport_eq_relation_of_homogeneous q P R hR n S a y
  have hcert : certified = fun _ => C := by
    funext n x a
    exact propext (hC n x a)
  simp only [Viable, hnext, hcert]

/-- Choose one certified continuation for each winning support. All other
supports use one fixed fallback distribution, with no history or clock. -/
def supportWinningAction
    {X Y A : Type u} [Fintype X]
    (q : X → Y) (R : X → A → X → Prop) (C : X → A → Prop)
    (fallback : PMF A) (S : Set X) : PMF A :=
  if hS : S ∈ supportWinning q R C then
    PMF.pure (Classical.choose (supportWinning_step q R C S hS))
  else fallback

/-- A positive action of the winning selector certifies every possible
state and preserves the winning family after each nonempty observation. -/
theorem supportWinningAction_support_step
    {X Y A : Type u} [Fintype X]
    (q : X → Y) (R : X → A → X → Prop) (C : X → A → Prop)
    (fallback : PMF A) (S : Set X) (a : A)
    (hS : S ∈ supportWinning q R C)
    (ha : a ∈ (supportWinningAction q R C fallback S).support) :
    (∀ x ∈ S, C x a) ∧
      ∀ y : Y, (relationSuccessor q R S a y).Nonempty →
        relationSuccessor q R S a y ∈ supportWinning q R C := by
  have haeq : a = Classical.choose (supportWinning_step q R C S hS) := by
    simpa only [supportWinningAction, dif_pos hS, PMF.support_pure,
      Set.mem_singleton_iff] using ha
  rw [haeq]
  exact Classical.choose_spec (supportWinning_step q R C S hS)

/-- A complete autonomous controller. Empty supports remain valid memory
values, so initialization and update are total even at impossible records. -/
def supportMemoryController
    {X Y A : Type u} [Fintype X]
    (p₀ : PMF X) (q : X → Y) (R : X → A → X → Prop)
    (C : X → A → Prop) (fallback : PMF A) :
    FiniteMemoryController (SupportMemory q) Y A where
  initialMemory := fun y => ⟨initialSupport p₀ q y, by
    by_cases hne : (initialSupport p₀ q y).Nonempty
    · exact Or.inr (initialSupport_mem_arena p₀ q y hne)
    · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp hne)⟩
  action := fun S => supportWinningAction q R C fallback S.1
  update := fun S a y => ⟨relationSuccessor q R S.1 a y, by
    by_cases hne : (relationSuccessor q R S.1 a y).Nonempty
    · exact Or.inr (relationSuccessor_mem_arena q R S.1 a y hne)
    · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp hne)⟩

/-- The replayed finite memory is exactly the original source trace
support at every full record, not only at positive-probability records. -/
theorem supportMemoryController_memory_eq_traceSupport
    {X Y A : Type u} [Fintype X]
    (p₀ : PMF X) (q : X → Y) (P : ℕ → X → A → PMF X)
    (R : X → A → X → Prop) (C : X → A → Prop) (fallback : PMF A)
    (hR : ∀ n x a z, z ∈ (P n x a).support ↔ R x a z) :
    ∀ n (h : CausalHistory Y (A × Y) n),
      ((supportMemoryController p₀ q R C fallback).memory n h).1 =
        traceSupport p₀ q P n h := by
  intro n
  induction n with
  | zero => intro h; rfl
  | succ n ih =>
      rintro ⟨h, a, y⟩
      change relationSuccessor q R
        (((supportMemoryController p₀ q R C fallback).memory n h).1) a y =
          successorSupport q P n (traceSupport p₀ q P n h) a y
      rw [ih, successorSupport_eq_relation_of_homogeneous q P R hR]

private theorem supportMemoryController_policy_eq
    {X Y A : Type u} [Fintype X]
    (p₀ : PMF X) (q : X → Y) (P : ℕ → X → A → PMF X)
    (R : X → A → X → Prop) (C : X → A → Prop) (fallback : PMF A)
    (hR : ∀ n x a z, z ∈ (P n x a).support ↔ R x a z)
    (n : ℕ) (h : CausalHistory Y (A × Y) n) :
    (supportMemoryController p₀ q R C fallback).policy n h =
      supportWinningAction q R C fallback (traceSupport p₀ q P n h) := by
  change supportWinningAction q R C fallback
    (((supportMemoryController p₀ q R C fallback).memory n h).1) = _
  rw [supportMemoryController_memory_eq_traceSupport p₀ q P R C fallback hR]

/-- The newly constructed policy preserves the winning invariant on its
own actual supported histories, retaining the original initial law. -/
theorem supportMemoryController_supported_histories_winning
    {X Y A : Type u} [Fintype X] [Fintype A]
    (p₀ : PMF X) (q : X → Y) (P : ℕ → X → A → PMF X)
    (R : X → A → X → Prop) (C : X → A → Prop) (fallback : PMF A)
    (hR : ∀ n x a z, z ∈ (P n x a).support ↔ R x a z)
    (hinit : ∀ y : Y, (initialSupport p₀ q y).Nonempty →
      initialSupport p₀ q y ∈ supportWinning q R C) :
    ∀ n, ∀ h ∈ (coarseLaw p₀ q P
      (supportMemoryController p₀ q R C fallback).policy n).support,
      traceSupport p₀ q P n h ∈ supportWinning q R C := by
  intro n
  induction n with
  | zero =>
      intro h hh
      exact hinit h ((mem_coarseLaw_zero_support_iff p₀ q P
        (supportMemoryController p₀ q R C fallback).policy h).mp hh)
  | succ n ih =>
      rintro ⟨h, a, y⟩ hh
      have hparts := (mem_coarseLaw_succ_support_iff p₀ q P
        (supportMemoryController p₀ q R C fallback).policy n h a y).mp hh
      have hwin := ih h hparts.1
      have ha := hparts.2.1
      rw [supportMemoryController_policy_eq p₀ q P R C fallback hR] at ha
      have hnext := (supportWinningAction_support_step
        q R C fallback (traceSupport p₀ q P n h) a hwin ha).2
      change successorSupport q P n (traceSupport p₀ q P n h) a y ∈ _
      rw [successorSupport_eq_relation_of_homogeneous q P R hR]
      apply hnext y
      rw [← successorSupport_eq_relation_of_homogeneous q P R hR]
      exact hparts.2.2

/-- Every actual deployment row of this finite-memory policy is certified.
Both the history law and action law belong to this same controller. -/
theorem supportMemoryController_zero_uncovered
    {X Y A : Type u} [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p₀ : PMF X) (q : X → Y) (P : ℕ → X → A → PMF X)
    (certified : ℕ → X → A → Prop)
    (R : X → A → X → Prop) (C : X → A → Prop) (fallback : PMF A)
    (hR : ∀ n x a z, z ∈ (P n x a).support ↔ R x a z)
    (hC : ∀ n x a, certified n x a ↔ C x a)
    (hinit : ∀ y : Y, (initialSupport p₀ q y).Nonempty →
      initialSupport p₀ q y ∈ supportWinning q R C) :
    ∀ n, (coverageDeploymentRowLaw p₀ q P
      (supportMemoryController p₀ q R C fallback).policy n).toMeasure.real
        {xa | ¬ certified n xa.1 xa.2} = 0 := by
  intro n
  apply (zero_uncovered_iff_support_certified p₀ q P
    (supportMemoryController p₀ q R C fallback).policy certified n).mpr
  intro h hh a ha x hx
  have hwin := supportMemoryController_supported_histories_winning
    p₀ q P R C fallback hR hinit n h hh
  rw [supportMemoryController_policy_eq p₀ q P R C fallback hR] at ha
  exact (hC n x a).mpr ((supportWinningAction_support_step
    q R C fallback (traceSupport p₀ q P n h) a hwin ha).1 x hx)

/-- One finite horizon, counting observation supports rather than states,
is enough to decide existence of an all-times zero-occupancy policy. -/
theorem bounded_horizon_iff_all_times_zero_uncovered
    {X Y A : Type u} [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p₀ : PMF X) (q : X → Y) (P : ℕ → X → A → PMF X)
    (certified : ℕ → X → A → Prop)
    (R : X → A → X → Prop) (C : X → A → Prop) (fallback : PMF A)
    (hR : ∀ n x a z, z ∈ (P n x a).support ↔ R x a z)
    (hC : ∀ n x a, certified n x a ↔ C x a) :
    (∃ π : ∀ n, CausalHistory Y (A × Y) n → PMF A,
      ∀ n, n < supportArenaCard q →
        (coverageDeploymentRowLaw p₀ q P π n).toMeasure.real
          {xa | ¬ certified n xa.1 xa.2} = 0) ↔
    ∀ n, (coverageDeploymentRowLaw p₀ q P
      (supportMemoryController p₀ q R C fallback).policy n).toMeasure.real
        {xa | ¬ certified n xa.1 xa.2} = 0 := by
  constructor
  · intro hfinite
    have hinit := (initial_viability_iff_exists_zero_uncovered_policy
      p₀ q P certified (supportArenaCard q) (fun _ _ => fallback)).mpr hfinite
    apply supportMemoryController_zero_uncovered
      p₀ q P certified R C fallback hR hC
    intro y hy
    apply (mem_supportIterate_iff_viableWith q R C (supportArenaCard q) 0
      (initialSupport p₀ q y) (initialSupport_mem_arena p₀ q y hy)).mpr
    exact (viable_iff_homogeneous_relation q P certified R C hR hC
      0 (supportArenaCard q) (initialSupport p₀ q y)).mp (hinit y hy)
  · intro hzero
    exact ⟨(supportMemoryController p₀ q R C fallback).policy,
      fun n _ => hzero n⟩

end
end SupportViabilityClosure
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
