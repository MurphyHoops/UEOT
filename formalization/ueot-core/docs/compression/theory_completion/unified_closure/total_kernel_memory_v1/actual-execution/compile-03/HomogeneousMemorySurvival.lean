import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteMemoryPhysicalSafety
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceSurvivalTail

/-!
# The same homogeneous controlled source with its actual finite memory

The augmented controlled model keeps the original actions and rewards. Its
transition samples the original model's successor and computes the controller's
actual memory update from that action and successor observation. The stationary
policy on state-memory pairs reads precisely the stored memory.

Its closed-loop rows are proved equal to the rows already constructed from the
original controlled history experiment. Consequently its homogeneous trajectory
is the existing actual augmented trajectory, not an independent replacement.
The existing killed-matrix finite and infinite survival theorems then apply to
the actual controller's state path. State-only Markovity is not asserted.

Numerical homogeneity is supplied by one fixed original model. A time-independent
support relation alone does not meet this hypothesis. The inherited reward and
discount fields are unused by the survival results. No initial safety, positive
survival, nonempty safe set, certification or QSD assumption is imposed.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
namespace HomogeneousMemorySurvival

open MeasureTheory ProbabilityTheory Function Filter
open UEOT.V3.PathError UEOT.V3.DynamicsKernel UEOT.V3.CoreOperationalAssembly
open UEOT.V3.FiniteDiscountedControl UEOT.V3.QSDPerron
open UEOT.V3.RecoveryHittingNonnegative UEOT.V3.Compression.Objecthood
open SupportViabilityClosure SourcePolicyPathBridgeCheck SameSourceInfinitePrefixCheck
open SameSourceKilledPathCheck SameSourceSafePrefixCheck SameSourceSurvivalTailCheck
open FiniteMemoryRealization FiniteMemoryPhysicalSafety
open scoped Classical BigOperators ENNReal ProbabilityTheory

noncomputable section

universe u

variable {X Mem Y A : Type u} [Fintype X] [Fintype Mem] [Fintype A] [Nonempty A]

noncomputable local instance pairDecidableEq :
    DecidableEq (X × Mem) := Classical.decEq _

/-- Lift the original action-conditioned numerical source to state-memory
pairs, preserving the original reward and discount rather than adding a new
control objective. -/
def augmentedModel
    (source : Model X (fun _ => A))
    (controller : FiniteMemoryController Mem Y A) (q : X → Y) :
    Model (X × Mem) (fun _ => A) where
  transition := fun xm a zm =>
    ((source.transitionPMF xm.1 a).map
      (fun z => (z, controller.update xm.2 a (q z))) zm).toReal
  reward := fun xm a => source.reward xm.1 a
  rewardBound := source.rewardBound
  discount := source.discount
  transition_nonneg := fun _ _ _ => ENNReal.toReal_nonneg
  transition_sum_one := fun xm a => coverage_sum_toReal
    ((source.transitionPMF xm.1 a).map
      (fun z => (z, controller.update xm.2 a (q z))))
  reward_abs_le := fun xm a => source.reward_abs_le xm.1 a
  discount_pos := source.discount_pos
  discount_lt_one := source.discount_lt_one

/-- Every action-conditioned augmented PMF is exactly the original numerical
source followed by its recorded-action memory update. -/
theorem augmentedModel_transitionPMF
    (source : Model X (fun _ => A))
    (controller : FiniteMemoryController Mem Y A) (q : X → Y)
    (xm : X × Mem) (a : A) :
    (augmentedModel source controller q).transitionPMF xm a =
      (source.transitionPMF xm.1 a).map
        (fun z => (z, controller.update xm.2 a (q z))) := by
  apply PMF.ext
  intro zm
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [Model.transitionPMF_apply_toReal]
  rfl

/-- The stationary current-memory feedback and augmented model induce the
same numerical row as the original finite-memory controlled experiment. -/
theorem closed_loop_eq_augmentedRow
    (source : Model X (fun _ => A))
    (controller : FiniteMemoryController Mem Y A) (q : X → Y)
    (n : ℕ) (xm : X × Mem) :
    policyTransitionPMF (augmentedModel source controller q)
        (liftedStationaryPolicy Prod.snd controller.action) xm =
      augmentedRow controller q (fun _ => source.transitionPMF) n xm := by
  have hstationary := actual_next_state_eq_stationary_row
    (augmentedModel source controller q) Prod.snd controller.action 0 xm
  simp only [riskLastState] at hstationary
  rw [← hstationary]
  change (pmfExtend (controller.action xm.2)
    ((augmentedModel source controller q).transitionPMF xm)).map Prod.snd = _
  have hrows : (augmentedModel source controller q).transitionPMF xm =
      fun a => (source.transitionPMF xm.1 a).map
        (fun z => (z, controller.update xm.2 a (q z))) := by
    funext a
    exact augmentedModel_transitionPMF source controller q xm a
  rw [hrows]
  unfold augmentedRow pmfExtend
  simp only [PMF.map_bind, PMF.map_comp]
  rfl

variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace Mem] [MeasurableSingletonClass Mem]

/-- Identity of the full infinite measures, using the same initial law and
each of the same numerical rows. The imported finite-prefix theorem already
identifies the left side with the original controlled microscopic experiment. -/
theorem actual_augmentedTrajMeasure_eq_homogeneous
    (source : Model X (fun _ => A))
    (controller : FiniteMemoryController Mem Y A) (q : X → Y) (p₀ : PMF X) :
    augmentedTrajMeasure controller p₀ q (fun _ => source.transitionPMF) =
      homTrajMeasure (augmentedInitial controller p₀ q).toMeasure
        (pmfRowKernel (policyTransitionPMF (augmentedModel source controller q)
          (liftedStationaryPolicy Prod.snd controller.action))) := by
  have hrows : augmentedRow controller q (fun _ => source.transitionPMF) =
      fun _ => policyTransitionPMF (augmentedModel source controller q)
        (liftedStationaryPolicy Prod.snd controller.action) := by
    funext n xm
    exact (closed_loop_eq_augmentedRow source controller q n xm).symm
  rw [augmentedTrajMeasure, hrows]
  rfl

private theorem projected_survival_mass
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (source : Model X (fun _ => A))
    (controller : FiniteMemoryController Mem Y A) (q : X → Y) (p₀ : PMF X)
    (K : Set X) (n : ℕ) :
    (stateTrajMeasure controller p₀ q (fun _ => source.transitionPMF)).real
        (survivalSet Kᶜ n) =
      ∑ v : (Prod.fst ⁻¹' K : Set (X × Mem)),
        rowApply (safeInitialRow (augmentedInitial controller p₀ q) (Prod.fst ⁻¹' K))
          ((killedMatrix (augmentedModel source controller q)
            (liftedStationaryPolicy Prod.snd controller.action) (Prod.fst ⁻¹' K)) ^ n) v := by
  have hset : mapPath (Prod.fst : X × Mem → X) ⁻¹' survivalSet Kᶜ n =
      survivalSet (Prod.fst ⁻¹' K : Set (X × Mem))ᶜ n := by
    ext ω
    simp only [Set.mem_preimage, mem_survivalSet_iff]
    rfl
  rw [stateTrajMeasure, Measure.real,
    Measure.map_apply (measurable_mapPath Prod.fst measurable_fst)
      (measurableSet_survivalSet (Set.toFinite Kᶜ).measurableSet n),
    hset, actual_augmentedTrajMeasure_eq_homogeneous]
  exact homogeneous_survival_real_eq_killed_pow_sum
    (augmentedModel source controller q) Prod.snd controller.action
    (augmentedInitial controller p₀ q) (Prod.fst ⁻¹' K) n

/-- The original action/state experiment's finite survival probability is the
unnormalized killed mass on state-memory pairs. Time-zero failure, an empty
safe set and zero later survival are retained. -/
theorem actual_finite_survival_eq_killed_mass
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (source : Model X (fun _ => A))
    (controller : FiniteMemoryController Mem Y A) (q : X → Y) (p₀ : PMF X)
    (K : Set X) (n : ℕ) :
    (microLaw p₀ q (fun _ => source.transitionPMF) controller.policy n).toMeasure.real
        {h | ¬ riskEverFailure (fun x => x ∉ K) n h} =
      ∑ v : (Prod.fst ⁻¹' K : Set (X × Mem)),
        rowApply (safeInitialRow (augmentedInitial controller p₀ q) (Prod.fst ⁻¹' K))
          ((killedMatrix (augmentedModel source controller q)
            (liftedStationaryPolicy Prod.snd controller.action) (Prod.fst ⁻¹' K)) ^ n) v := by
  have hsource := FiniteMemoryPhysicalSafety.actual_state_prefix_event_mass
    controller p₀ q (fun _ => source.transitionPMF) n (historySurvivalSet Kᶜ n)
  rw [actual_safe_prefix_pullback] at hsource
  have hreal := congrArg ENNReal.toReal hsource
  exact hreal.trans (projected_survival_mass source controller q p₀ K n)

/-- The same killed masses converge to all-times survival of the original
controller's actual state trajectory. No Markov property of that state-only
projection, positive survival or QSD hypothesis is needed. -/
theorem killed_mass_tendsto_actual_infinite_survival
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (source : Model X (fun _ => A))
    (controller : FiniteMemoryController Mem Y A) (q : X → Y) (p₀ : PMF X)
    (K : Set X) :
    Tendsto
      (fun n : ℕ => ∑ v : (Prod.fst ⁻¹' K : Set (X × Mem)),
        rowApply (safeInitialRow (augmentedInitial controller p₀ q) (Prod.fst ⁻¹' K))
          ((killedMatrix (augmentedModel source controller q)
            (liftedStationaryPolicy Prod.snd controller.action) (Prod.fst ⁻¹' K)) ^ n) v)
      atTop
      (nhds ((stateTrajMeasure controller p₀ q (fun _ => source.transitionPMF)).real
        (neverHitSet Kᶜ))) := by
  have hE : MeasurableSet (neverHitSet Kᶜ) := by
    rw [neverHitSet_eq_iInter_survivalSet]
    exact MeasurableSet.iInter fun n =>
      measurableSet_survivalSet (Set.toFinite Kᶜ).measurableSet n
  have hlimit :
      (stateTrajMeasure controller p₀ q (fun _ => source.transitionPMF)).real
          (neverHitSet Kᶜ) =
        (homTrajMeasure (augmentedInitial controller p₀ q).toMeasure
          (pmfRowKernel (policyTransitionPMF (augmentedModel source controller q)
            (liftedStationaryPolicy Prod.snd controller.action)))).real
          (neverHitSet (Prod.fst ⁻¹' K : Set (X × Mem))ᶜ) := by
    rw [stateTrajMeasure, Measure.real,
      Measure.map_apply (measurable_mapPath Prod.fst measurable_fst) hE,
      actual_augmentedTrajMeasure_eq_homogeneous]
    rfl
  rw [hlimit]
  exact killed_survival_mass_tendsto_homogeneous_neverHit_real
    (augmentedModel source controller q) Prod.snd controller.action
    (augmentedInitial controller p₀ q) (Prod.fst ⁻¹' K)

end
end HomogeneousMemorySurvival
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
