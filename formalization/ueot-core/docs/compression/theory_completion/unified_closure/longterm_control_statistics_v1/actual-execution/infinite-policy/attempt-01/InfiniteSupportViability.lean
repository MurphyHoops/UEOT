import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteSupportViability

/-!
# One infinite policy from arbitrarily long actual-support viability

The initial law, observation, entire time-dependent transition sequence and
certification sequence are fixed before the horizon is quantified. Finite
actions turn nested nonempty continuation choices into one consistent choice.
The resulting complete causal policy has zero actual uncertified-row occupancy
at every time. Its invariant is proved on its own supported histories.

This is not a finite-memory realization theorem, a stationary-policy theorem,
or a physical-safety theorem. The explicit complete fallback is retained at
nonviable histories; neither it nor a reference process is rewritten.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
namespace SupportViabilityClosure

open MeasureTheory UEOT.V3.PathError
open scoped Classical

noncomputable section

universe u

/-- Removing the last required row preserves backward viability, including
for time-dependent transitions and certification. -/
theorem viableWith_horizon_pred
    {X Y A : Type u}
    (next : ℕ → Set X → A → Y → Set X)
    (certified : ℕ → X → A → Prop) :
    ∀ k n S, viableWith next certified n (k + 1) S →
      viableWith next certified n k S := by
  intro k
  induction k with
  | zero =>
      intro n S _
      trivial
  | succ k ih =>
      intro n S hV
      obtain ⟨a, hcert, hnext⟩ := hV
      refine ⟨a, hcert, ?_⟩
      intro y hy
      exact ih (n + 1) (next n S a y) (hnext y hy)

/-- All finite remaining horizons for the same time and the same source
support. This definition carries no policy or all-times occupancy conclusion. -/
abbrev InfiniteViable
    {X Y A : Type u} (q : X → Y) (P : ℕ → X → A → PMF X)
    (certified : ℕ → X → A → Prop) (n : ℕ) (S : Set X) : Prop :=
  ∀ k, Viable q P certified n k S

private theorem exists_forall_of_finite_nested
    {A : Type u} [Fintype A] (D : ℕ → A → Prop)
    (hstep : ∀ n a, D (n + 1) a → D n a)
    (hne : ∀ n, ∃ a, D n a) :
    ∃ a, ∀ n, D n a := by
  classical
  have hdown (i j : ℕ) (hij : i ≤ j) : ∀ a, D j a → D i a := by
    induction j, hij using Nat.le_induction with
    | base =>
        intro a ha
        exact ha
    | succ j hij ih =>
        intro a ha
        exact ih a (hstep j a ha)
  by_contra h
  have hfail : ∀ a, ∃ n, ¬ D n a := by
    intro a
    by_contra hh
    apply h
    refine ⟨a, ?_⟩
    intro n
    by_contra hn
    exact hh ⟨n, hn⟩
  choose k hk using hfail
  let K : ℕ := Finset.univ.sup k
  obtain ⟨a, ha⟩ := hne K
  have hle : k a ≤ K := Finset.le_sup (f := k) (Finset.mem_univ a)
  exact hk a (hdown (k a) K hle a ha)

/-- Finite actions yield one action that certifies the current support and
leaves every nonempty observed successor viable for all remaining horizons.
The action is chosen once, independently of any requested future horizon. -/
theorem infiniteViable_step
    {X Y A : Type u} [Fintype A]
    (q : X → Y) (P : ℕ → X → A → PMF X)
    (certified : ℕ → X → A → Prop) (n : ℕ) (S : Set X)
    (hV : InfiniteViable q P certified n S) :
    ∃ a : A,
      (∀ x ∈ S, certified n x a) ∧
        ∀ y : Y, (successorSupport q P n S a y).Nonempty →
          InfiniteViable q P certified (n + 1)
            (successorSupport q P n S a y) := by
  let D : ℕ → A → Prop := fun k a =>
    (∀ x ∈ S, certified n x a) ∧
      ∀ y : Y, (successorSupport q P n S a y).Nonempty →
        Viable q P certified (n + 1) k (successorSupport q P n S a y)
  have hstep : ∀ k a, D (k + 1) a → D k a := by
    intro k a ha
    refine ⟨ha.1, ?_⟩
    intro y hy
    exact viableWith_horizon_pred (successorSupport q P) certified k (n + 1)
      (successorSupport q P n S a y) (ha.2 y hy)
  have hne : ∀ k, ∃ a, D k a := by
    intro k
    exact hV (k + 1)
  obtain ⟨a, ha⟩ := exists_forall_of_finite_nested D hstep hne
  refine ⟨a, (ha 0).1, ?_⟩
  intro y hy k
  exact (ha k).2 y hy

/-- A complete causal policy using the consistent continuation choice on
all-horizon viable supports. At every other history it uses the supplied
complete fallback, without identifying that fallback with a memoryless rule. -/
def infiniteViablePolicy
    {X Y A : Type u} [Fintype A]
    (p₀ : PMF X) (q : X → Y) (P : ℕ → X → A → PMF X)
    (certified : ℕ → X → A → Prop)
    (πbase : ∀ n, CausalHistory Y (A × Y) n → PMF A) :
    ∀ n, CausalHistory Y (A × Y) n → PMF A :=
  fun n h =>
    if hV : InfiniteViable q P certified n (traceSupport p₀ q P n h) then
      PMF.pure (Classical.choose
        (infiniteViable_step q P certified n (traceSupport p₀ q P n h) hV))
    else πbase n h

/-- Every positive action of this policy at an all-horizon viable history
certifies the whole current support and preserves the same invariant. -/
theorem infiniteViablePolicy_support_step
    {X Y A : Type u} [Fintype A]
    (p₀ : PMF X) (q : X → Y) (P : ℕ → X → A → PMF X)
    (certified : ℕ → X → A → Prop)
    (πbase : ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (n : ℕ) (h : CausalHistory Y (A × Y) n) (a : A)
    (hV : InfiniteViable q P certified n (traceSupport p₀ q P n h))
    (ha : a ∈ (infiniteViablePolicy p₀ q P certified πbase n h).support) :
    (∀ x ∈ traceSupport p₀ q P n h, certified n x a) ∧
      ∀ y : Y,
        (successorSupport q P n (traceSupport p₀ q P n h) a y).Nonempty →
          InfiniteViable q P certified (n + 1)
            (successorSupport q P n (traceSupport p₀ q P n h) a y) := by
  let hstep := infiniteViable_step q P certified n (traceSupport p₀ q P n h) hV
  let chosen : A := Classical.choose hstep
  have hpure : infiniteViablePolicy p₀ q P certified πbase n h =
      PMF.pure chosen := by
    simp only [infiniteViablePolicy, dif_pos hV, chosen]
  have haeq : a = chosen := by
    have hnonzero : (infiniteViablePolicy p₀ q P certified πbase n h) a ≠ 0 :=
      (PMF.mem_support_iff _ _).mp ha
    rw [hpure] at hnonzero
    by_contra hne
    apply hnonzero
    simp [PMF.pure_apply]
    exact hne
  rw [haeq]
  exact Classical.choose_spec hstep

/-- Initial all-horizon viability is preserved along the actually supported
histories of this single synthesized policy for every time. -/
theorem infiniteViablePolicy_supported_histories_viable
    {X Y A : Type u} [Fintype X] [Fintype A]
    (p₀ : PMF X) (q : X → Y) (P : ℕ → X → A → PMF X)
    (certified : ℕ → X → A → Prop)
    (πbase : ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (hinit : ∀ y : Y, (initialSupport p₀ q y).Nonempty →
      InfiniteViable q P certified 0 (initialSupport p₀ q y)) :
    ∀ n, ∀ h ∈
        (coarseLaw p₀ q P (infiniteViablePolicy p₀ q P certified πbase) n).support,
      InfiniteViable q P certified n (traceSupport p₀ q P n h) := by
  intro n
  induction n with
  | zero =>
      intro h hh
      exact hinit h ((mem_coarseLaw_zero_support_iff
        p₀ q P (infiniteViablePolicy p₀ q P certified πbase) h).mp hh)
  | succ n ih =>
      intro hc hh
      rcases hc with ⟨h, a, y⟩
      have hparts := (mem_coarseLaw_succ_support_iff
        p₀ q P (infiniteViablePolicy p₀ q P certified πbase) n h a y).mp hh
      have hV := ih h hparts.1
      have hstep := infiniteViablePolicy_support_step
        p₀ q P certified πbase n h a hV hparts.2.1
      exact hstep.2 y hparts.2.2

/-- This one complete policy has zero actual uncertified-row occupancy at
every time. The row law is the original source experiment driven by this
policy; it is not a different law or a limit of horizon-dependent policies. -/
theorem infiniteViablePolicy_zero_uncovered
    {X Y A : Type u} [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p₀ : PMF X) (q : X → Y) (P : ℕ → X → A → PMF X)
    (certified : ℕ → X → A → Prop)
    (πbase : ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (hinit : ∀ y : Y, (initialSupport p₀ q y).Nonempty →
      InfiniteViable q P certified 0 (initialSupport p₀ q y)) :
    ∀ n,
      (coverageDeploymentRowLaw p₀ q P
        (infiniteViablePolicy p₀ q P certified πbase) n).toMeasure.real
          {xa | ¬ certified n xa.1 xa.2} = 0 := by
  intro n
  apply (zero_uncovered_iff_support_certified
    p₀ q P (infiniteViablePolicy p₀ q P certified πbase) certified n).mpr
  intro h hh a ha x hx
  have hV := infiniteViablePolicy_supported_histories_viable
    p₀ q P certified πbase hinit n h hh
  exact (infiniteViablePolicy_support_step
    p₀ q P certified πbase n h a hV ha).1 x hx

/-- Exact all-times characterization in the original source row laws,
with no stationarity or finiteness assumption on the observation type. -/
theorem initial_infiniteViability_iff_exists_all_times_zero_uncovered_policy
    {X Y A : Type u} [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p₀ : PMF X) (q : X → Y) (P : ℕ → X → A → PMF X)
    (certified : ℕ → X → A → Prop)
    (πbase : ∀ n, CausalHistory Y (A × Y) n → PMF A) :
    (∀ y : Y, (initialSupport p₀ q y).Nonempty →
      InfiniteViable q P certified 0 (initialSupport p₀ q y)) ↔
    ∃ π : ∀ n, CausalHistory Y (A × Y) n → PMF A,
      ∀ n, (coverageDeploymentRowLaw p₀ q P π n).toMeasure.real
        {xa | ¬ certified n xa.1 xa.2} = 0 := by
  constructor
  · intro hinit
    exact ⟨infiniteViablePolicy p₀ q P certified πbase,
      infiniteViablePolicy_zero_uncovered p₀ q P certified πbase hinit⟩
  · rintro ⟨π, hzero⟩ y hy T
    exact ((initial_viability_iff_exists_zero_uncovered_policy
      p₀ q P certified T πbase).mpr ⟨π, fun n _ => hzero n⟩) y hy

/-- With all source data fixed, arbitrarily long horizon-dependent causal
policies exist exactly when a single complete causal policy certifies every
actual row at all times. No consistency of the supplied finite witnesses is
assumed: the nested finite-action construction supplies a new witness. -/
theorem arbitrarily_long_zero_uncovered_iff_single_all_times_policy
    {X Y A : Type u} [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p₀ : PMF X) (q : X → Y) (P : ℕ → X → A → PMF X)
    (certified : ℕ → X → A → Prop)
    (πbase : ∀ n, CausalHistory Y (A × Y) n → PMF A) :
    (∀ T, ∃ π : ∀ n, CausalHistory Y (A × Y) n → PMF A,
      ∀ n, n < T →
        (coverageDeploymentRowLaw p₀ q P π n).toMeasure.real
          {xa | ¬ certified n xa.1 xa.2} = 0) ↔
    ∃ π : ∀ n, CausalHistory Y (A × Y) n → PMF A,
      ∀ n, (coverageDeploymentRowLaw p₀ q P π n).toMeasure.real
        {xa | ¬ certified n xa.1 xa.2} = 0 := by
  constructor
  · intro hfinite
    apply (initial_infiniteViability_iff_exists_all_times_zero_uncovered_policy
      p₀ q P certified πbase).mp
    intro y hy T
    exact ((initial_viability_iff_exists_zero_uncovered_policy
      p₀ q P certified T πbase).mpr (hfinite T)) y hy
  · rintro ⟨π, hzero⟩ T
    exact ⟨π, fun n _ => hzero n⟩

end
end SupportViabilityClosure
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
