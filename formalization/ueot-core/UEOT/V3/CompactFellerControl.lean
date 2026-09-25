import UEOT.V3.CompactArgmaxSelector
import UEOT.V3.CompactCausalOptimalityCore
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Kernel.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic

/-!
# P-CTL-02 — compact Feller discounted control

Frozen Core 3 section 19.3 assumes compact metric state and action spaces, a
fixed nonempty action space, continuous reward, a Markov transition kernel
weakly continuous in state-action, and a discount 0 < beta < 1.

The conclusion proved here is source-strength:

* the Bellman operator is a self-map of C(X, R) and a beta-contraction;
* it has a unique continuous fixed point;
* a measurable stationary deterministic Bellman maximizer exists; and
* that stationary policy is optimal against arbitrary randomized
  history-dependent causal policies.

Model.transition_weakContinuous stores the standard compact-space
test-function characterization of weak continuity. The theorem
transitionPM_continuous derives literal continuity into Mathlib's weak
topology on ProbabilityMeasure X, so this representation does not discretize
or weaken the source transition object.
-/

namespace UEOT.V3.CompactFellerControl

open Filter Topology MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

universe uX uA

variable {X : Type uX} {A : Type uA}
variable [MetricSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X]
variable [MetricSpace A] [CompactSpace A] [Nonempty A]
variable [MeasurableSpace A] [BorelSpace A]

structure Model (X : Type uX) (A : Type uA)
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [MetricSpace A] [CompactSpace A] [Nonempty A]
    [MeasurableSpace A] [BorelSpace A] where
  transition : Kernel (X × A) X
  transition_markov : IsMarkovKernel transition
  transition_weakContinuous :
    ∀ v : C(X, ℝ), Continuous fun za : X × A =>
      ∫ y, v y ∂transition za
  reward : C(X × A, ℝ)
  discount : ℝ
  discount_pos : 0 < discount
  discount_lt_one : discount < 1

namespace Model

variable (M : Model X A)

noncomputable def transitionPM (za : X × A) : ProbabilityMeasure X :=
  ⟨M.transition za, M.transition_markov.isProbabilityMeasure za⟩

/-- The test-function formulation stored in the model is exactly continuity
in Mathlib's weak topology on probability measures. -/
lemma transitionPM_continuous : Continuous M.transitionPM := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuousMap_continuous_integral]
  intro v
  simpa [transitionPM] using M.transition_weakContinuous v

noncomputable def expect (v : C(X, ℝ)) (za : X × A) : ℝ :=
  ∫ y, v y ∂M.transition za

lemma expect_continuous (v : C(X, ℝ)) :
    Continuous (M.expect v) := by
  change Continuous fun za : X × A => ∫ y, v y ∂M.transition za
  exact M.transition_weakContinuous v

noncomputable def qValue (v : C(X, ℝ)) (x : X) (a : A) : ℝ :=
  M.reward (x, a) + M.discount * M.expect v (x, a)

lemma qValue_joint_continuous (v : C(X, ℝ)) :
    Continuous ↿(M.qValue v) := by
  change Continuous fun za : X × A =>
    M.reward za + M.discount * M.expect v za
  exact M.reward.continuous.add
    (continuous_const.mul (M.expect_continuous v))

noncomputable def bellman (v : C(X, ℝ)) : C(X, ℝ) where
  toFun x := UEOT.V3.CompactArgmaxSelector.globalMax (M.qValue v) x
  continuous_toFun :=
    UEOT.V3.CompactArgmaxSelector.continuous_globalMax (M.qValue_joint_continuous v)

@[simp] lemma bellman_apply (v : C(X, ℝ)) (x : X) :
    M.bellman v x = UEOT.V3.CompactArgmaxSelector.globalMax (M.qValue v) x := rfl

lemma continuous_integrable (v : C(X, ℝ)) (μ : Measure X) [IsFiniteMeasure μ] :
    Integrable v μ := by
  refine Integrable.of_bound v.measurable.aestronglyMeasurable ‖v‖ ?_
  exact Filter.Eventually.of_forall fun x =>
    ContinuousMap.norm_coe_le_norm v x

lemma abs_expect_sub_le_dist (v w : C(X, ℝ)) (za : X × A) :
    |M.expect v za - M.expect w za| ≤ dist v w := by
  letI : IsProbabilityMeasure (M.transition za) :=
    M.transition_markov.isProbabilityMeasure za
  have hv : Integrable v (M.transition za) := continuous_integrable v _
  have hw : Integrable w (M.transition za) := continuous_integrable w _
  rw [expect, expect, ← integral_sub hv hw]
  have hpoint : ∀ y : X, ‖v y - w y‖ ≤ dist v w := by
    intro y
    simpa [Real.norm_eq_abs, Real.dist_eq] using
      (ContinuousMap.dist_le (f := v) (g := w) dist_nonneg).1 le_rfl y
  have hbound :=
    norm_integral_le_of_norm_le_const
      (μ := M.transition za) (f := fun y => v y - w y)
      (C := dist v w) (Filter.Eventually.of_forall hpoint)
  simpa [Real.norm_eq_abs] using hbound

lemma abs_qValue_sub_le (v w : C(X, ℝ)) (x : X) (a : A) :
    |M.qValue v x a - M.qValue w x a| ≤
      M.discount * dist v w := by
  have h := M.abs_expect_sub_le_dist v w (x, a)
  have hβ : 0 ≤ M.discount := M.discount_pos.le
  calc
    |M.qValue v x a - M.qValue w x a|
        = M.discount * |M.expect v (x, a) - M.expect w (x, a)| := by
          simp only [qValue]
          rw [show M.reward (x, a) + M.discount * M.expect v (x, a) -
                (M.reward (x, a) + M.discount * M.expect w (x, a)) =
                M.discount * (M.expect v (x, a) - M.expect w (x, a)) by ring,
              abs_mul, abs_of_nonneg hβ]
    _ ≤ M.discount * dist v w := mul_le_mul_of_nonneg_left h hβ

lemma abs_bellman_apply_sub_le (v w : C(X, ℝ)) (x : X) :
    |M.bellman v x - M.bellman w x| ≤
      M.discount * dist v w := by
  obtain ⟨av, hvmax, hvge⟩ :=
    UEOT.V3.CompactArgmaxSelector.exists_global_argmax (M.qValue_joint_continuous v) x
  obtain ⟨aw, hwmax, hwge⟩ :=
    UEOT.V3.CompactArgmaxSelector.exists_global_argmax (M.qValue_joint_continuous w) x
  have hvw := M.abs_qValue_sub_le v w x av
  have hwv := M.abs_qValue_sub_le v w x aw
  have hw_at_av : M.qValue w x av ≤ M.qValue w x aw := hwge av
  have hv_at_aw : M.qValue v x aw ≤ M.qValue v x av := hvge aw
  rw [bellman_apply, bellman_apply, hvmax, hwmax, abs_le]
  constructor
  · have hlow := (abs_le.mp hwv).1
    linarith
  · have hupp := (abs_le.mp hvw).2
    linarith

def discountNN : NNReal := ⟨M.discount, M.discount_pos.le⟩

@[simp] lemma coe_discountNN : (M.discountNN : ℝ) = M.discount := rfl

lemma bellman_lipschitz : LipschitzWith M.discountNN M.bellman := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro v w
  apply (ContinuousMap.dist_le (f := M.bellman v) (g := M.bellman w)
    (mul_nonneg (by positivity) dist_nonneg)).2
  intro x
  simpa [Real.dist_eq] using M.abs_bellman_apply_sub_le v w x

lemma bellman_contracting : ContractingWith M.discountNN M.bellman := by
  refine ⟨?_, M.bellman_lipschitz⟩
  change M.discount < 1
  exact M.discount_lt_one

noncomputable def optimalValue : C(X, ℝ) :=
  ContractingWith.fixedPoint M.bellman M.bellman_contracting

lemma optimalValue_fixed :
    M.bellman M.optimalValue = M.optimalValue :=
  M.bellman_contracting.fixedPoint_isFixedPt

lemma fixedPoint_unique {v : C(X, ℝ)} (hv : M.bellman v = v) :
    v = M.optimalValue :=
  M.bellman_contracting.fixedPoint_unique hv

lemma valueIteration_tendsto (v₀ : C(X, ℝ)) :
    Tendsto (fun n => M.bellman^[n] v₀) atTop (𝓝 M.optimalValue) :=
  M.bellman_contracting.tendsto_iterate_fixedPoint v₀

lemma valueError_le_residual (v : C(X, ℝ)) :
    dist v M.optimalValue ≤ dist v (M.bellman v) / (1 - M.discount) := by
  simpa [optimalValue] using M.bellman_contracting.dist_fixedPoint_le v

theorem exists_measurable_greedy :
    ∃ π : X → A,
      Measurable π ∧
      ∀ x,
        M.qValue M.optimalValue x (π x) = M.optimalValue x ∧
        ∀ a, M.qValue M.optimalValue x a ≤ M.optimalValue x := by
  obtain ⟨π, hπmeas, hπ⟩ :=
    UEOT.V3.CompactArgmaxSelector.measurable_argmax_selector
      (M.qValue_joint_continuous M.optimalValue)
  refine ⟨π, hπmeas, ?_⟩
  intro x
  have hfixed := congrArg (fun f : C(X, ℝ) => f x) M.optimalValue_fixed
  have hBell :
      UEOT.V3.CompactArgmaxSelector.globalMax (M.qValue M.optimalValue) x =
        M.optimalValue x := by
    simpa using hfixed
  constructor
  · exact (hπ x).1.trans hBell
  · intro a
    calc
      M.qValue M.optimalValue x a
          ≤ M.qValue M.optimalValue x (π x) := (hπ x).2 a
      _ = UEOT.V3.CompactArgmaxSelector.globalMax (M.qValue M.optimalValue) x :=
        (hπ x).1
      _ = M.optimalValue x := hBell

end Model
end
end UEOT.V3.CompactFellerControl


namespace UEOT.V3.CompactFellerControl.Model

open Filter Topology MeasureTheory ProbabilityTheory
open UEOT.V3.FiniteHistory
open UEOT.V3.ReflexiveStateAugmentation

noncomputable section

universe uX uA

variable {X : Type uX} {A : Type uA}
variable [MetricSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X]
variable [MetricSpace A] [CompactSpace A] [Nonempty A]
variable [MeasurableSpace A] [BorelSpace A]

noncomputable def causalModel (M : UEOT.V3.CompactFellerControl.Model X A) :
    UEOT.V3.CompactCausalOptimalityCore.Model X A where
  transition := M.transition
  transition_markov := M.transition_markov
  reward := fun x a => M.reward (x, a)
  reward_measurable := by
    change Measurable fun p : X × A => M.reward p
    exact M.reward.measurable
  rewardBound := ‖M.reward‖
  rewardBound_nonneg := norm_nonneg _
  reward_abs_le := by
    intro x a
    simpa [Real.norm_eq_abs] using ContinuousMap.norm_coe_le_norm M.reward (x, a)
  discount := M.discount
  discount_nonneg := M.discount_pos.le
  discount_lt_one := M.discount_lt_one

noncomputable def greedySelector (M : UEOT.V3.CompactFellerControl.Model X A) : X → A :=
  Classical.choose M.exists_measurable_greedy

lemma greedySelector_measurable (M : UEOT.V3.CompactFellerControl.Model X A) :
    Measurable M.greedySelector :=
  (Classical.choose_spec M.exists_measurable_greedy).1

lemma greedySelector_spec (M : UEOT.V3.CompactFellerControl.Model X A) (x : X) :
    M.qValue M.optimalValue x (M.greedySelector x) = M.optimalValue x ∧
      ∀ a, M.qValue M.optimalValue x a ≤ M.optimalValue x :=
  (Classical.choose_spec M.exists_measurable_greedy).2 x

noncomputable def greedyCertificate (M : UEOT.V3.CompactFellerControl.Model X A) :
    UEOT.V3.CompactCausalOptimalityCore.Model.GreedyCertificate M.causalModel where
  value := M.optimalValue
  value_measurable := M.optimalValue.measurable
  valueBound := ‖M.optimalValue‖
  valueBound_nonneg := norm_nonneg _
  value_abs_le := by
    intro x
    simpa [Real.norm_eq_abs] using
      ContinuousMap.norm_coe_le_norm M.optimalValue x
  action_le := by
    intro x a
    simpa [causalModel, UEOT.V3.CompactFellerControl.Model.qValue,
      UEOT.V3.CompactFellerControl.Model.expect] using (M.greedySelector_spec x).2 a
  selector := M.greedySelector
  selector_measurable := M.greedySelector_measurable
  action_eq := by
    intro x
    simpa [causalModel, UEOT.V3.CompactFellerControl.Model.qValue,
      UEOT.V3.CompactFellerControl.Model.expect] using (M.greedySelector_spec x).1

noncomputable def stationaryPolicy (M : UEOT.V3.CompactFellerControl.Model X A) :
    CausalPolicy X A :=
  M.greedyCertificate.stationaryPolicy

instance stationaryPolicy_markov (M : UEOT.V3.CompactFellerControl.Model X A) (n : ℕ) :
    IsMarkovKernel (M.stationaryPolicy n) := by
  unfold stationaryPolicy
  infer_instance

/-- Source-facing compact Feller discounted-control conclusion, including
actual optimality against arbitrary randomized full-history causal policies. -/
theorem p_ctl_02 (M : UEOT.V3.CompactFellerControl.Model X A) :
    ContractingWith M.discountNN M.bellman ∧
    M.bellman M.optimalValue = M.optimalValue ∧
    (∀ v : C(X, ℝ), M.bellman v = v → v = M.optimalValue) ∧
    Measurable M.greedySelector ∧
    (∀ x,
      M.qValue M.optimalValue x (M.greedySelector x) = M.optimalValue x) ∧
    (∀ (π : CausalPolicy X A) [∀ n, IsMarkovKernel (π n)] (x : X),
      M.causalModel.infiniteValue π 0
        (UEOT.V3.CompactCausalOptimalityCore.initialHistory (A := A) x) ≤
          M.optimalValue x) ∧
    (∀ x : X,
      M.causalModel.infiniteValue M.stationaryPolicy 0
        (UEOT.V3.CompactCausalOptimalityCore.initialHistory (A := A) x) =
          M.optimalValue x) := by
  refine ⟨M.bellman_contracting, M.optimalValue_fixed, ?_,
    M.greedySelector_measurable, ?_, ?_, ?_⟩
  · intro v hv
    exact M.fixedPoint_unique hv
  · intro x
    exact (M.greedySelector_spec x).1
  · intro π hπ x
    exact M.greedyCertificate.toBellmanUpperCertificate.infiniteValue_le_value
      π 0 (UEOT.V3.CompactCausalOptimalityCore.initialHistory (A := A) x)
  · intro x
    change
      M.causalModel.infiniteValue M.greedyCertificate.stationaryPolicy 0
          (UEOT.V3.CompactCausalOptimalityCore.initialHistory (A := A) x) =
        M.greedyCertificate.value x
    exact M.greedyCertificate.stationary_infiniteValue_eq_value 0
      (UEOT.V3.CompactCausalOptimalityCore.initialHistory (A := A) x)

end
end UEOT.V3.CompactFellerControl.Model
