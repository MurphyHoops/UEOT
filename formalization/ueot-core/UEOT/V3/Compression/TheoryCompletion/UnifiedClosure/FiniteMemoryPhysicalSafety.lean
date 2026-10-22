import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteMemoryRealization
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportMemoryController
import UEOT.V3.ViabilityPath

/-!
# Actual certification, memory realization and physical safety

Zero uncertified occupancy is converted to safety only with two physical
premises: the original initial support is safe, and every actually certified
transition from a safe state has safe successor support. The first proof works
for any complete causal policy and its own nonautonomous deployment row law.
The finite-memory specialization then uses the constructed state-memory
Ionescu--Tulcea law and its proved finite-prefix identity.

The original state path is the coordinatewise state projection of that same
infinite augmented process. It need not be Markov on states alone. Finally,
the existing winning-support controller discharges the zero-occupancy premise
under its exact source support/certification and initial-winning conditions.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
namespace FiniteMemoryPhysicalSafety

open MeasureTheory ProbabilityTheory Function
open UEOT.V3.PathError UEOT.V3.DynamicsKernel UEOT.V3.CoreOperationalAssembly
open SupportViabilityClosure SourcePolicyPathBridgeCheck SameSourceInfinitePrefixCheck
open FiniteMemoryRealization
open scoped Classical ENNReal ProbabilityTheory

noncomputable section

universe u

private theorem no_failure_last_mem
    {X A : Type u} (K : Set X) (n : ℕ) (h : CausalHistory X (A × X) n)
    (hs : ¬ riskEverFailure (fun x => x ∉ K) n h) : riskLastState n h ∈ K := by
  cases n with
  | zero => exact not_not.mp hs
  | succ n => exact not_not.mp ((not_or.mp hs).2)

/-- Initial safety and actual certified-support closure turn the given
policy's own zero occupancy into safety of every supported finite record. -/
theorem supported_micro_history_safe
    {X Y A : Type u} [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p₀ : PMF X) (q : X → Y) (P : ℕ → X → A → PMF X)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (certified : ℕ → X → A → Prop) (K : Set X)
    (hinit : ∀ x ∈ p₀.support, x ∈ K)
    (hclosed : ∀ n x a, x ∈ K → certified n x a →
      ∀ z ∈ (P n x a).support, z ∈ K)
    (hzero : ∀ n, (coverageDeploymentRowLaw p₀ q P π n).toMeasure.real
      {xa | ¬ certified n xa.1 xa.2} = 0) :
    ∀ n, ∀ h ∈ (microLaw p₀ q P π n).support,
      ¬ riskEverFailure (fun x => x ∉ K) n h := by
  intro n
  induction n with
  | zero =>
      intro x hx
      exact not_not.mpr (hinit x hx)
  | succ n ih =>
      rintro ⟨h, a, z⟩ hh
      have hs := (mem_microLaw_succ_support_iff p₀ q P π n h a z).mp hh
      have hsafe := ih h hs.1
      have hg : projectHistory q n h ∈ (coarseLaw p₀ q P π n).support :=
        (PMF.mem_support_map_iff _ _ _).mpr ⟨h, hs.1, rfl⟩
      have hx : riskLastState n h ∈ traceSupport p₀ q P n (projectHistory q n h) :=
        (mem_traceSupport_iff_realized p₀ q P π n _ hg _).mpr
          ⟨h, hs.1, rfl, rfl⟩
      have hc := (zero_uncovered_iff_support_certified p₀ q P π certified n).mp
        (hzero n) _ hg a hs.2.1 _ hx
      have hz := hclosed n (riskLastState n h) a
        (no_failure_last_mem K n h hsafe) hc z hs.2.2
      exact not_or.mpr ⟨hsafe, not_not.mpr hz⟩

/-- The physical no-failure event, including time zero, has probability one
in each original finite experiment of this same causal policy. -/
theorem actual_finite_safety_one
    {X Y A : Type u} [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p₀ : PMF X) (q : X → Y) (P : ℕ → X → A → PMF X)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (certified : ℕ → X → A → Prop) (K : Set X)
    (hinit : ∀ x ∈ p₀.support, x ∈ K)
    (hclosed : ∀ n x a, x ∈ K → certified n x a →
      ∀ z ∈ (P n x a).support, z ∈ K)
    (hzero : ∀ n, (coverageDeploymentRowLaw p₀ q P π n).toMeasure.real
      {xa | ¬ certified n xa.1 xa.2} = 0) (n : ℕ) :
    (microLaw p₀ q P π n).toMeasure
      {h | ¬ riskEverFailure (fun x => x ∉ K) n h} = 1 := by
  apply ((microLaw p₀ q P π n).toMeasure_apply_eq_one_iff
    (Set.toFinite _).measurableSet).mpr
  exact supported_micro_history_safe p₀ q P π certified K hinit hclosed hzero n

/-- A coordinatewise map commutes with the complete recursive-history
equivalence. This is an algebraic identity, not a lumpability assumption. -/
theorem stateHistoryEquiv_map
    {S T : Type u} [MeasurableSpace S] [MeasurableSpace T] (f : S → T) :
    ∀ n (h : CausalHistory S S n),
      stateHistoryEquiv n (riskHistoryMap f f n h) =
        mapHistory f n (stateHistoryEquiv n h) := by
  intro n
  induction n with
  | zero => intro h; rfl
  | succ n ih =>
      rintro ⟨h, x⟩
      change appendHistory n
          (stateHistoryEquiv n (riskHistoryMap f f n h), f x) =
        mapHistory f (n + 1) (appendHistory n (stateHistoryEquiv n h, x))
      rw [mapHistory_appendHistory, ih]

/-- The actual infinite state path is the state projection of the already
constructed state-memory law. No state-only Markov property is imposed. -/
def stateTrajMeasure
    {X M Y A : Type u} [Fintype X] [Fintype M]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    (controller : FiniteMemoryController M Y A) (p₀ : PMF X) (q : X → Y)
    (P : ℕ → X → A → PMF X) : Measure (ℕ → X) :=
  (augmentedTrajMeasure controller p₀ q P).map (mapPath Prod.fst)

instance stateTrajMeasure_isProbability
    {X M Y A : Type u} [Fintype X] [Fintype M]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    (controller : FiniteMemoryController M Y A) (p₀ : PMF X) (q : X → Y)
    (P : ℕ → X → A → PMF X) :
    IsProbabilityMeasure (stateTrajMeasure controller p₀ q P) := by
  unfold stateTrajMeasure
  exact Measure.isProbabilityMeasure_map
    (measurable_mapPath Prod.fst measurable_fst).aemeasurable

/-- Every state prefix of the projected infinite law is the corresponding
full state history of the original action/state experiment. -/
theorem actual_state_prefix_eq
    {X M Y A : Type u} [Fintype X] [Fintype M]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    (controller : FiniteMemoryController M Y A) (p₀ : PMF X) (q : X → Y)
    (P : ℕ → X → A → PMF X) (n : ℕ) :
    ((microLaw p₀ q P controller.policy n).map
      (stateHistoryEquiv n ∘ eraseActionHistory n)).toMeasure =
      (stateTrajMeasure controller p₀ q P).map (Preorder.frestrictLe n) := by
  rw [stateTrajMeasure, Measure.map_map (Preorder.measurable_frestrictLe n)
    (measurable_mapPath Prod.fst measurable_fst), frestrictLe_mapPath]
  rw [← Measure.map_map (measurable_mapHistory Prod.fst measurable_fst n)
    (Preorder.measurable_frestrictLe n), ← actual_augmented_prefix_eq]
  rw [PMF.toMeasure_map, PMF.map_comp]
  · congr 2
    funext h
    change stateHistoryEquiv n (eraseActionHistory n h) =
      mapHistory Prod.fst n (stateHistoryEquiv n (augmentHistory controller q n h))
    rw [← stateHistoryEquiv_map, eraseMemory_augmentHistory]
  · exact measurable_mapHistory Prod.fst measurable_fst n

/-- Any finite state-prefix event retains its actual policy-driven mass. -/
theorem actual_state_prefix_event_mass
    {X M Y A : Type u} [Fintype X] [Fintype M] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (controller : FiniteMemoryController M Y A) (p₀ : PMF X) (q : X → Y)
    (P : ℕ → X → A → PMF X) (n : ℕ) (B : Set ((i : Finset.Iic n) → X)) :
    (microLaw p₀ q P controller.policy n).toMeasure
      ((stateHistoryEquiv n ∘ eraseActionHistory n) ⁻¹' B) =
      stateTrajMeasure controller p₀ q P ((Preorder.frestrictLe n) ⁻¹' B) := by
  have hB : MeasurableSet B := (Set.toFinite B).measurableSet
  have h := congrArg (fun μ : Measure ((i : Finset.Iic n) → X) => μ B)
    (actual_state_prefix_eq controller p₀ q P n)
  rw [PMF.toMeasure_map_apply _ _ _ (measurable_of_finite _) hB,
    Measure.map_apply (Preorder.measurable_frestrictLe n) hB] at h
  exact h

private theorem currentState_erase
    {X A : Type u} (n : ℕ) (h : CausalHistory X (A × X) n) :
    currentState n (eraseActionHistory n h) = riskLastState n h := by
  cases n <;> rfl

/-- The projected infinite coordinate has exactly the original microscopic
terminal event mass; this also preserves the unmodified initial state law. -/
theorem stateTrajMeasure_coordinate_mass
    {X M Y A : Type u} [Fintype X] [Fintype M] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (controller : FiniteMemoryController M Y A) (p₀ : PMF X) (q : X → Y)
    (P : ℕ → X → A → PMF X) (n : ℕ) (K : Set X) :
    stateTrajMeasure controller p₀ q P {ω | ω n ∈ K} =
      (microLaw p₀ q P controller.policy n).toMeasure
        {h | riskLastState n h ∈ K} := by
  have h := actual_state_prefix_event_mass controller p₀ q P n
    {g | g (lastHistoryIndex n) ∈ K}
  have hlast (g : CausalHistory X (A × X) n) :
      stateHistoryEquiv n (eraseActionHistory n g) (lastHistoryIndex n) =
        riskLastState n g := by
    rw [stateHistoryEquiv_last, currentState_erase]
  have hprefix (ω : ℕ → X) :
      Preorder.frestrictLe n ω (lastHistoryIndex n) = ω n := rfl
  simpa only [Set.preimage_ofPred_eq, Function.comp_apply, hlast, hprefix] using h.symm

/-- Physical safety at every discrete time in the actual infinite law of
this finite-memory controller. Numerical time dependence remains allowed. -/
theorem controller_all_times_physical_safe
    {X M Y A : Type u} [Fintype X] [Fintype M] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (controller : FiniteMemoryController M Y A) (p₀ : PMF X) (q : X → Y)
    (P : ℕ → X → A → PMF X) (certified : ℕ → X → A → Prop) (K : Set X)
    (hinit : ∀ x ∈ p₀.support, x ∈ K)
    (hclosed : ∀ n x a, x ∈ K → certified n x a →
      ∀ z ∈ (P n x a).support, z ∈ K)
    (hzero : ∀ n, (coverageDeploymentRowLaw p₀ q P controller.policy n).toMeasure.real
      {xa | ¬ certified n xa.1 xa.2} = 0) :
    stateTrajMeasure controller p₀ q P {ω | ∀ n : ℕ, ω n ∈ K} = 1 := by
  apply UEOT.V3.ViabilityPath.all_times_safe_eq_one
    (stateTrajMeasure controller p₀ q P) (fun n ω => ω n) K
    (Set.toFinite K).measurableSet (fun n => measurable_pi_apply n)
  intro n
  rw [stateTrajMeasure_coordinate_mass]
  apply ((microLaw p₀ q P controller.policy n).toMeasure_apply_eq_one_iff
    (Set.toFinite _).measurableSet).mpr
  intro h hh
  exact no_failure_last_mem K n h (supported_micro_history_safe
    p₀ q P controller.policy certified K hinit hclosed hzero n h hh)

/-- The previously constructed winning-support controller is physically
safe in its own infinite process once the explicit physical premises hold.
Zero uncertified occupancy is discharged by its existing source theorem. -/
theorem supportMemoryController_all_times_physical_safe
    {X Y A : Type u} [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p₀ : PMF X) (q : X → Y)
    [MeasurableSpace (SupportMemory q)] [MeasurableSingletonClass (SupportMemory q)]
    (P : ℕ → X → A → PMF X) (certified : ℕ → X → A → Prop)
    (R : X → A → X → Prop) (C : X → A → Prop) (fallback : PMF A)
    (hR : ∀ n x a z, z ∈ (P n x a).support ↔ R x a z)
    (hC : ∀ n x a, certified n x a ↔ C x a)
    (hwinning : ∀ y : Y, (initialSupport p₀ q y).Nonempty →
      initialSupport p₀ q y ∈ supportWinning q R C)
    (K : Set X) (hinit : ∀ x ∈ p₀.support, x ∈ K)
    (hclosed : ∀ x a, x ∈ K → C x a → ∀ z, R x a z → z ∈ K) :
    stateTrajMeasure (supportMemoryController p₀ q R C fallback) p₀ q P
      {ω | ∀ n : ℕ, ω n ∈ K} = 1 := by
  apply controller_all_times_physical_safe
    (supportMemoryController p₀ q R C fallback) p₀ q P certified K hinit
  · intro n x a hx hc z hz
    exact hclosed x a hx ((hC n x a).mp hc) z ((hR n x a z).mp hz)
  · exact supportMemoryController_zero_uncovered
      p₀ q P certified R C fallback hR hC hwinning

end
end FiniteMemoryPhysicalSafety
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
