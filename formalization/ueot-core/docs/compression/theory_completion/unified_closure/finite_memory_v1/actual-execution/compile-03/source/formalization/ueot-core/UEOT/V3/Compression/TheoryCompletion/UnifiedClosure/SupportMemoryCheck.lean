import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportMemoryController

/-!
# An executable finite check for all-times support certification

The program receives a finite initial support and decidable observation,
relation and certification data. It reuses the existing finite-horizon
relation checker at the explicit cutoff `2 ^ |X| - 1`. The program does not
receive an unknown winning policy, an actual PMF-support decider, or a
Classical selector. Exact agreement with an actual initial law and transition
support is a theorem premise, and is not silently inferred from a table.

The correctness endpoint certifies the actual deployment row laws of the
same autonomous support controller. Decision is executable; the existing
winning-action selection remains noncomputable and no runtime complexity
bound or approximate support-discovery guarantee is asserted.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
namespace SupportViabilityClosure

open MeasureTheory UEOT.V3.PathError

universe u

/-- Check every initially possible observation fiber at a computable bound
on the number of nonempty supports. Repeated observations may be checked
more than once, but no finite enumeration of the ambient observation type
is required. This definition uses only the supplied finite decidable data. -/
def finiteMemoryCheck
    {X Y A : Type u} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq Y]
    (q : X → Y) (R : X → A → X → Prop) (C : X → A → Prop)
    [∀ x a z, Decidable (R x a z)] [∀ x a, Decidable (C x a)]
    (initial : Finset X) : Bool :=
  decide (∀ x ∈ initial,
    finiteRelationViabilityCheck q (fun _ => R) (fun _ => C) 0
      (2 ^ Fintype.card X - 1) (initial.filter (fun z => q z = q x)) = true)

private theorem initial_filter_coe_eq
    {X Y : Type u} [DecidableEq Y]
    (p₀ : PMF X) (q : X → Y) (initial : Finset X)
    (h0 : ∀ x, x ∈ initial ↔ x ∈ p₀.support) (y : Y) :
    (↑(initial.filter (fun z => q z = y)) : Set X) = initialSupport p₀ q y := by
  ext x
  simp [initialSupport, h0]

/-- Exact initial-support and transition-support matching turns the
executable table check into membership of every actual initial observation
fiber in the greatest support fixed point. -/
theorem finiteMemoryCheck_iff_initial_winning
    {X Y A : Type u} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq Y]
    (q : X → Y) (R : X → A → X → Prop) (C : X → A → Prop)
    [∀ x a z, Decidable (R x a z)] [∀ x a, Decidable (C x a)]
    (initial : Finset X) (p₀ : PMF X) (P : ℕ → X → A → PMF X)
    (h0 : ∀ x, x ∈ initial ↔ x ∈ p₀.support)
    (hR : ∀ n x a z, z ∈ (P n x a).support ↔ R x a z) :
    finiteMemoryCheck q R C initial = true ↔
      ∀ y : Y, (initialSupport p₀ q y).Nonempty →
        initialSupport p₀ q y ∈ supportWinning q R C := by
  letI : ∀ n x a z, Decidable (z ∈ (P n x a).support) :=
    fun _ _ _ _ => Classical.propDecidable _
  let B : ℕ := 2 ^ Fintype.card X - 1
  have hB : supportArenaCard q ≤ B := by
    have hbound := supportArenaCard_add_one_le_pow q
    dsimp [B]
    omega
  have hcorrect (y : Y) (hy : (initialSupport p₀ q y).Nonempty) :
      finiteRelationViabilityCheck q (fun _ => R) (fun _ => C) 0 B
        (initial.filter (fun z => q z = y)) = true ↔
          initialSupport p₀ q y ∈ supportWinning q R C := by
    have hcheck := finiteRelationViabilityCheck_correct
      q (fun _ => R) P (fun _ => C) (fun n x a z => (hR n x a z).symm)
      B 0 (initial.filter (fun z => q z = y))
    rw [initial_filter_coe_eq p₀ q initial h0 y] at hcheck
    have hrelation := viable_iff_homogeneous_relation
      q P (fun _ => C) R C hR (fun _ _ _ => Iff.rfl)
      0 B (initialSupport p₀ q y)
    have hiterate := mem_supportIterate_iff_viableWith
      q R C B 0 (initialSupport p₀ q y) (initialSupport_mem_arena p₀ q y hy)
    exact hcheck.trans (hrelation.trans (hiterate.symm.trans (by
      rw [supportIterate_eq_winning_of_card_le q R C B hB])))
  unfold finiteMemoryCheck
  rw [decide_eq_true_eq]
  constructor
  · intro hcheck y hy
    obtain ⟨x, hx⟩ := hy
    have hxinitial : x ∈ initial := (h0 x).mpr hx.1
    have hchecked := hcheck x hxinitial
    have hchecked_y :
        finiteRelationViabilityCheck q (fun _ => R) (fun _ => C) 0 B
          (initial.filter (fun z => q z = y)) = true := by
      simpa only [hx.2] using hchecked
    exact (hcorrect y ⟨x, hx⟩).mp hchecked_y
  · intro hwin x hx
    have hy : (initialSupport p₀ q (q x)).Nonempty :=
      ⟨x, (h0 x).mp hx, rfl⟩
    exact (hcorrect (q x) hy).mpr (hwin (q x) hy)

/-- A positive Boolean result is equivalent to zero actual uncertified-row
occupancy at every time for this same constructed finite-memory controller.
Initial, transition and certification representations are all retained. -/
theorem finiteMemoryCheck_iff_controller_zero_uncovered
    {X Y A : Type u} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq Y]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (q : X → Y) (R : X → A → X → Prop) (C : X → A → Prop)
    [∀ x a z, Decidable (R x a z)] [∀ x a, Decidable (C x a)]
    (initial : Finset X) (p₀ : PMF X) (P : ℕ → X → A → PMF X)
    (certified : ℕ → X → A → Prop) (fallback : PMF A)
    (h0 : ∀ x, x ∈ initial ↔ x ∈ p₀.support)
    (hR : ∀ n x a z, z ∈ (P n x a).support ↔ R x a z)
    (hC : ∀ n x a, certified n x a ↔ C x a) :
    finiteMemoryCheck q R C initial = true ↔
      ∀ n, (coverageDeploymentRowLaw p₀ q P
        (supportMemoryController p₀ q R C fallback).policy n).toMeasure.real
          {xa | ¬ certified n xa.1 xa.2} = 0 := by
  constructor
  · intro hcheck
    exact supportMemoryController_zero_uncovered
      p₀ q P certified R C fallback hR hC
      ((finiteMemoryCheck_iff_initial_winning q R C initial p₀ P h0 hR).mp hcheck)
  · intro hzero
    apply (finiteMemoryCheck_iff_initial_winning q R C initial p₀ P h0 hR).mpr
    have hinit := (initial_viability_iff_exists_zero_uncovered_policy
      p₀ q P certified (supportArenaCard q) (fun _ _ => fallback)).mpr
        ⟨(supportMemoryController p₀ q R C fallback).policy, fun n _ => hzero n⟩
    intro y hy
    apply (mem_supportIterate_iff_viableWith q R C (supportArenaCard q) 0
      (initialSupport p₀ q y) (initialSupport_mem_arena p₀ q y hy)).mpr
    exact (viable_iff_homogeneous_relation q P certified R C hR hC
      0 (supportArenaCard q) (initialSupport p₀ q y)).mp (hinit y hy)

/-- The same finite decision also characterizes existence of any complete
causal policy with all-times zero actual uncertified occupancy. No unknown
policy is an input to the executable check. -/
theorem finiteMemoryCheck_iff_exists_all_times_policy
    {X Y A : Type u} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq Y]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (q : X → Y) (R : X → A → X → Prop) (C : X → A → Prop)
    [∀ x a z, Decidable (R x a z)] [∀ x a, Decidable (C x a)]
    (initial : Finset X) (p₀ : PMF X) (P : ℕ → X → A → PMF X)
    (certified : ℕ → X → A → Prop) (fallback : PMF A)
    (h0 : ∀ x, x ∈ initial ↔ x ∈ p₀.support)
    (hR : ∀ n x a z, z ∈ (P n x a).support ↔ R x a z)
    (hC : ∀ n x a, certified n x a ↔ C x a) :
    finiteMemoryCheck q R C initial = true ↔
      ∃ π : ∀ n, CausalHistory Y (A × Y) n → PMF A,
        ∀ n, (coverageDeploymentRowLaw p₀ q P π n).toMeasure.real
          {xa | ¬ certified n xa.1 xa.2} = 0 := by
  rw [finiteMemoryCheck_iff_controller_zero_uncovered
    q R C initial p₀ P certified fallback h0 hR hC]
  constructor
  · intro hzero
    exact ⟨(supportMemoryController p₀ q R C fallback).policy, hzero⟩
  · rintro ⟨π, hzero⟩
    apply (bounded_horizon_iff_all_times_zero_uncovered
      p₀ q P certified R C fallback hR hC).mp
    exact ⟨π, fun n _ => hzero n⟩

end SupportViabilityClosure
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
