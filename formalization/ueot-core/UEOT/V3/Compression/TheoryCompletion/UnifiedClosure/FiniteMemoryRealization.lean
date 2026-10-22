import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteMemoryPolicy
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceInfinitePrefix

/-!
# One finite-memory source on the actual state-memory space

The augmented initial law and transition rows are constructed from the
original initial PMF, source transitions, observation and controller. Replaying
the recorded actions computes the memory in every complete microscopic
history. Its exact pushforward is the Markov history law on state-memory pairs.
Erasing memory recovers the complete original state history.

The numerical source rows may depend on time. The infinite realization uses
that same sequence of rows in Ionescu--Tulcea; no homogeneous replacement,
support-matching certificate or path-law identity is assumed. Finiteness of
memory is needed only for the finite measurable infinite-law interface below.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
namespace FiniteMemoryRealization

open MeasureTheory ProbabilityTheory Function
open UEOT.V3.PathError UEOT.V3.DynamicsKernel UEOT.V3.CoreOperationalAssembly
open SupportViabilityClosure SourcePolicyPathBridgeCheck SameSourceInfinitePrefixCheck
open scoped Classical ENNReal ProbabilityTheory

noncomputable section

universe u

/-- The original state and the controller's actual initialized memory. -/
def augmentedInitial {X M Y A : Type u}
    (controller : FiniteMemoryController M Y A) (p₀ : PMF X) (q : X → Y) :
    PMF (X × M) :=
  p₀.map fun x => (x, controller.initialMemory (q x))

/-- Sample the actual action, sample its actual next state, then update
memory from that recorded action and the new observation. -/
def augmentedRow {X M Y A : Type u}
    (controller : FiniteMemoryController M Y A) (q : X → Y)
    (P : ℕ → X → A → PMF X) (n : ℕ) (xm : X × M) : PMF (X × M) :=
  (pmfExtend (controller.action xm.2) (P n xm.1)).map
    fun ax => (ax.2, controller.update xm.2 ax.1 (q ax.2))

/-- Replay every recorded action while retaining every state-memory pair. -/
def augmentHistory {X M Y A : Type u}
    (controller : FiniteMemoryController M Y A) (q : X → Y) :
    ∀ n, CausalHistory X (A × X) n → CausalHistory (X × M) (X × M) n
  | 0, x => (x, controller.initialMemory (q x))
  | n + 1, h => (augmentHistory controller q n h.1,
      (h.2.2, controller.memory (n + 1) (projectHistory q (n + 1) h)))

@[simp] theorem augmentHistory_last {X M Y A : Type u}
    (controller : FiniteMemoryController M Y A) (q : X → Y)
    (n : ℕ) (h : CausalHistory X (A × X) n) :
    currentState n (augmentHistory controller q n h) =
      (riskLastState n h, controller.memory n (projectHistory q n h)) := by
  cases n <;> rfl

/-- Memory erasure keeps the entire original state history, including time zero. -/
theorem eraseMemory_augmentHistory {X M Y A : Type u}
    (controller : FiniteMemoryController M Y A) (q : X → Y) :
    ∀ n (h : CausalHistory X (A × X) n),
      riskHistoryMap Prod.fst Prod.fst n (augmentHistory controller q n h) =
        eraseActionHistory n h := by
  intro n
  induction n with
  | zero => intro h; rfl
  | succ n ih =>
      rintro ⟨h, a, x⟩
      change (riskHistoryMap Prod.fst Prod.fst n
        (augmentHistory controller q n h), x) = (eraseActionHistory n h, x)
      rw [ih]

private theorem map_extend_dependent
    {H Z W V : Type u} (p : PMF H) (K : H → PMF Z)
    (F : H → W) (G : H → Z → V) (L : W → PMF V)
    (hrow : ∀ h, (K h).map (G h) = L (F h)) :
    (pmfExtend p K).map (fun hz => (F hz.1, G hz.1 hz.2)) =
      pmfExtend (p.map F) L := by
  unfold pmfExtend
  rw [PMF.map_bind, PMF.bind_map]
  congr 1
  funext h
  dsimp only [Function.comp_apply]
  rw [← hrow h, PMF.map_comp, PMF.map_comp]
  rfl

/-- The actual policy-driven microscopic history becomes the state-memory
Markov history of the constructed rows, for every finite horizon. -/
theorem actual_augmented_history_law
    {X M Y A : Type u}
    (controller : FiniteMemoryController M Y A) (p₀ : PMF X) (q : X → Y)
    (P : ℕ → X → A → PMF X) (n : ℕ) :
    (microLaw p₀ q P controller.policy n).map (augmentHistory controller q n) =
      causalLaw (augmentedInitial controller p₀ q)
        (fun k h => augmentedRow controller q P k (currentState k h)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hrow (h : CausalHistory X (A × X) n) :
          (riskMicroControlKernel q P controller.policy n h).map
            (fun ax => (ax.2,
              controller.update (controller.memory n (projectHistory q n h))
                ax.1 (q ax.2))) =
            augmentedRow controller q P n
              (currentState n (augmentHistory controller q n h)) := by
        rw [augmentHistory_last]
        rfl
      change (pmfExtend (microLaw p₀ q P controller.policy n)
        (riskMicroControlKernel q P controller.policy n)).map
          (fun hz => (augmentHistory controller q n hz.1,
            (hz.2.2, controller.update
              (controller.memory n (projectHistory q n hz.1)) hz.2.1 (q hz.2.2)))) =
        pmfExtend (causalLaw (augmentedInitial controller p₀ q)
          (fun k h => augmentedRow controller q P k (currentState k h)) n)
          (fun h => augmentedRow controller q P n (currentState n h))
      rw [map_extend_dependent _ _ (augmentHistory controller q n) _
        (fun h => augmentedRow controller q P n (currentState n h)) hrow, ih]

/-- Projection of the augmented path recovers the actual complete microscopic
state path. This does not claim that the state-only marginal is Markov. -/
theorem augmented_history_state_projection
    {X M Y A : Type u}
    (controller : FiniteMemoryController M Y A) (p₀ : PMF X) (q : X → Y)
    (P : ℕ → X → A → PMF X) (n : ℕ) :
    (causalLaw (augmentedInitial controller p₀ q)
      (fun k h => augmentedRow controller q P k (currentState k h)) n).map
        (riskHistoryMap Prod.fst Prod.fst n) =
      (microLaw p₀ q P controller.policy n).map (eraseActionHistory n) := by
  rw [← actual_augmented_history_law, PMF.map_comp]
  congr 1
  funext h
  exact eraseMemory_augmentHistory controller q n h

section InfiniteSequence

variable {S : Type u} [Fintype S]
variable [MeasurableSpace S] [MeasurableSingletonClass S]

/-- The time-n row reads the last state of the supplied prefix. -/
def sequenceHistoryKernel (J : ℕ → S → PMF S) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → S) S :=
  homHistoryKernel (pmfRowKernel (J n)) n

instance sequenceHistoryKernel_isMarkov (J : ℕ → S → PMF S) (n : ℕ) :
    IsMarkovKernel (sequenceHistoryKernel J n) :=
  isMarkovKernel_homHistoryKernel (pmfRowKernel (J n)) n

/-- The Ionescu--Tulcea law of the actual, possibly nonautonomous PMF rows. -/
def sequenceTrajMeasure (p₀ : PMF S) (J : ℕ → S → PMF S) : Measure (ℕ → S) :=
  ProbabilityTheory.Kernel.trajMeasure (X := fun _ : ℕ => S)
    p₀.toMeasure (sequenceHistoryKernel J)

instance sequenceTrajMeasure_isProbability (p₀ : PMF S) (J : ℕ → S → PMF S) :
    IsProbabilityMeasure (sequenceTrajMeasure p₀ J) := by
  unfold sequenceTrajMeasure
  infer_instance

private theorem sequence_prefix_zero (p₀ : PMF S) (J : ℕ → S → PMF S) :
    (sequenceTrajMeasure p₀ J).map (Preorder.frestrictLe 0) =
      p₀.toMeasure.map (stateHistoryEquiv 0) := by
  rw [sequenceTrajMeasure, ProbabilityTheory.Kernel.trajMeasure,
    Measure.map_comp _ _ (by fun_prop),
    ProbabilityTheory.Kernel.traj_map_frestrictLe,
    ProbabilityTheory.Kernel.partialTraj_self, Measure.id_comp]
  rfl

private theorem sequence_prefix_succ (p₀ : PMF S) (J : ℕ → S → PMF S)
    (n : ℕ) :
    (((sequenceTrajMeasure p₀ J).map (Preorder.frestrictLe n)) ⊗ₘ
        sequenceHistoryKernel J n).map (appendHistory n) =
      (sequenceTrajMeasure p₀ J).map (Preorder.frestrictLe (n + 1)) := by
  have hstep :=
    ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      (X := fun _ : ℕ => S) (μ₀ := p₀.toMeasure)
      (κ := sequenceHistoryKernel J) (a := n)
  have hstep' :
      ((sequenceTrajMeasure p₀ J).map (Preorder.frestrictLe n)) ⊗ₘ
          sequenceHistoryKernel J n =
        (sequenceTrajMeasure p₀ J).map
          (fun x => (Preorder.frestrictLe n x, x (n + 1))) := by
    simpa only [sequenceTrajMeasure] using hstep
  rw [hstep', Measure.map_map (measurable_appendHistory n) (by fun_prop)]
  congr 1
  funext x
  exact appendHistory_prefix_next n x

private theorem extend_toMeasure
    {H Z : Type u} [Fintype H]
    [MeasurableSpace H] [MeasurableSingletonClass H] [MeasurableSpace Z]
    (p : PMF H) (K : H → PMF Z) :
    (pmfExtend p K).toMeasure = p.toMeasure ⊗ₘ pmfRowKernel K := by
  ext E hE
  rw [pmfExtend, PMF.toMeasure_bind_apply _ _ _ hE,
    Measure.compProd_apply hE, lintegral_countable']
  apply tsum_congr
  intro h
  rw [PMF.toMeasure_map_apply _ _ _ measurable_prodMk_left hE,
    PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton h)]
  change p h * (K h).toMeasure (Prod.mk h ⁻¹' E) =
    (K h).toMeasure (Prod.mk h ⁻¹' E) * p h
  exact mul_comm _ _

private theorem compProd_comap_map
    {H W Z : Type u} [MeasurableSpace H] [MeasurableSpace W] [MeasurableSpace Z]
    (μ : Measure H) [IsFiniteMeasure μ]
    (R : Kernel W Z) [IsMarkovKernel R]
    (F : H → W) (hF : Measurable F) :
    (μ ⊗ₘ Kernel.comap R F hF).map (Prod.map F id) = (μ.map F) ⊗ₘ R := by
  ext E hE
  rw [Measure.map_apply (hF.prodMap measurable_id) hE,
    Measure.compProd_apply (hE.preimage (hF.prodMap measurable_id)),
    Measure.compProd_apply hE,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hE) hF]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Every full finite PMF history is the corresponding prefix of the same
nonautonomous infinite law. The initial PMF and every numerical row agree. -/
theorem state_history_eq_sequence_prefix
    (p₀ : PMF S) (J : ℕ → S → PMF S) (n : ℕ) :
    ((causalLaw p₀ (fun k h => J k (currentState k h)) n).map
      (stateHistoryEquiv n)).toMeasure =
      (sequenceTrajMeasure p₀ J).map (Preorder.frestrictLe n) := by
  rw [← PMF.toMeasure_map _ _ (stateHistoryEquiv n).measurable]
  induction n with
  | zero => exact (sequence_prefix_zero p₀ J).symm
  | succ n ih =>
      have hrow :
          pmfRowKernel (fun h : CausalHistory S S n => J n (currentState n h)) =
            Kernel.comap (sequenceHistoryKernel J n)
              (stateHistoryEquiv n) (stateHistoryEquiv n).measurable := by
        ext h E hE
        change (J n (currentState n h)).toMeasure E =
          (J n (stateHistoryEquiv n h (lastHistoryIndex n))).toMeasure E
        rw [stateHistoryEquiv_last]
      change (pmfExtend (causalLaw p₀ (fun k h => J k (currentState k h)) n)
        (fun h => J n (currentState n h))).toMeasure.map
          (stateHistoryEquiv (n + 1)) = _
      rw [extend_toMeasure, stateHistoryEquiv_succ]
      rw [← Measure.map_map (measurable_appendHistory n)
        ((stateHistoryEquiv n).measurable.prodMap measurable_id)]
      rw [hrow, compProd_comap_map, ih]
      exact sequence_prefix_succ p₀ J n

end InfiniteSequence

/-- Actual infinite state-memory law of the given controller and source. -/
def augmentedTrajMeasure
    {X M Y A : Type u} [Fintype X] [Fintype M]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    (controller : FiniteMemoryController M Y A) (p₀ : PMF X) (q : X → Y)
    (P : ℕ → X → A → PMF X) : Measure (ℕ → X × M) :=
  sequenceTrajMeasure (augmentedInitial controller p₀ q) (augmentedRow controller q P)

instance augmentedTrajMeasure_isProbability
    {X M Y A : Type u} [Fintype X] [Fintype M]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    (controller : FiniteMemoryController M Y A) (p₀ : PMF X) (q : X → Y)
    (P : ℕ → X → A → PMF X) :
    IsProbabilityMeasure (augmentedTrajMeasure controller p₀ q P) := by
  unfold augmentedTrajMeasure
  infer_instance

/-- The entire augmented prefix is the actual controller experiment's image,
not an independently stipulated path process. -/
theorem actual_augmented_prefix_eq
    {X M Y A : Type u} [Fintype X] [Fintype M]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    (controller : FiniteMemoryController M Y A) (p₀ : PMF X) (q : X → Y)
    (P : ℕ → X → A → PMF X) (n : ℕ) :
    ((microLaw p₀ q P controller.policy n).map
      (stateHistoryEquiv n ∘ augmentHistory controller q n)).toMeasure =
      (augmentedTrajMeasure controller p₀ q P).map (Preorder.frestrictLe n) := by
  rw [← PMF.map_comp, actual_augmented_history_law]
  exact state_history_eq_sequence_prefix
    (augmentedInitial controller p₀ q) (augmentedRow controller q P) n

/-- Every measurable finite state-memory event has exactly its original
policy-driven probability. Action-dependent events require their own retained map. -/
theorem actual_augmented_prefix_event_mass
    {X M Y A : Type u} [Fintype X] [Fintype M] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (controller : FiniteMemoryController M Y A) (p₀ : PMF X) (q : X → Y)
    (P : ℕ → X → A → PMF X) (n : ℕ)
    (B : Set ((i : Finset.Iic n) → X × M)) :
    (microLaw p₀ q P controller.policy n).toMeasure
      ((stateHistoryEquiv n ∘ augmentHistory controller q n) ⁻¹' B) =
      augmentedTrajMeasure controller p₀ q P ((Preorder.frestrictLe n) ⁻¹' B) := by
  have hB : MeasurableSet B := (Set.toFinite B).measurableSet
  have h := congrArg (fun μ : Measure ((i : Finset.Iic n) → X × M) => μ B)
    (actual_augmented_prefix_eq controller p₀ q P n)
  rw [PMF.toMeasure_map_apply _ _ _ (measurable_of_finite _) hB,
    Measure.map_apply (Preorder.measurable_frestrictLe n) hB] at h
  exact h

end
end FiniteMemoryRealization
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
