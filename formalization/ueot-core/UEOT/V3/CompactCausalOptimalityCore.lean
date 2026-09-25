import UEOT.V3.ReflexiveStateAugmentation
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.Integral
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Causal optimality verification for compact discounted control

This is the policy-verification layer used by P-CTL-02. It reuses UEOT's
full-history randomized CausalPolicy type and defines finite-horizon values
directly by nested action/transition kernel integration. Geometric tail bounds
give the infinite discounted value for every causal policy.

A Bellman upper certificate then dominates every randomized history-dependent
policy, while a measurable deterministic greedy certificate constructs a
stationary policy and proves that it attains the Bellman value. Thus the source
phrase "measurable stationary optimal selector" is backed by an actual
all-causal optimality theorem rather than by a pointwise argmax alone.
-/

namespace UEOT.V3.CompactCausalOptimalityCore

open Filter Topology MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
open UEOT.V3.FiniteHistory
open UEOT.V3.FiniteHistoryMeasurable
open UEOT.V3.ReflexiveStateAugmentation

noncomputable section

universe uX uA

variable {X : Type uX} {A : Type uA}
variable [MeasurableSpace X] [MeasurableSpace A]

/-- Fixed-time full-history extension. -/
def advanceFiber (n : ℕ) (h : HistoryFiber X A n) (a : A) (y : X) :
    HistoryFiber X A (n + 1) :=
  (Fin.snoc h.1 y, Fin.snoc h.2 a)

theorem measurable_advanceFiber (n : ℕ) :
    Measurable
      (fun p : (HistoryFiber X A n × A) × X =>
        advanceFiber n p.1.1 p.1.2 p.2) := by
  have hstates :
      Measurable
        (fun p : (HistoryFiber X A n × A) × X =>
          (Fin.snoc p.1.1.1 p.2 : Fin (n + 2) → X)) := by
    rw [measurable_pi_iff]
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using
        (measurable_snd :
          Measurable (fun p : (HistoryFiber X A n × A) × X => p.2))
    · have hh :
        Measurable (fun p : (HistoryFiber X A n × A) × X => p.1.1.1) :=
          (measurable_historyFiber_states (X := X) (A := A) n).comp
            (measurable_fst.comp measurable_fst)
      simpa only [Fin.snoc_castSucc, Function.comp_def] using
        (measurable_pi_apply j).comp hh
  have hactions :
      Measurable
        (fun p : (HistoryFiber X A n × A) × X =>
          (Fin.snoc p.1.1.2 p.1.2 : Fin (n + 1) → A)) := by
    rw [measurable_pi_iff]
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last, Function.comp_def] using
        (measurable_snd.comp measurable_fst :
          Measurable (fun p : (HistoryFiber X A n × A) × X => p.1.2))
    · have hh :
        Measurable (fun p : (HistoryFiber X A n × A) × X => p.1.1.2) :=
          (measurable_historyFiber_actions (X := X) (A := A) n).comp
            (measurable_fst.comp measurable_fst)
      simpa only [Fin.snoc_castSucc, Function.comp_def] using
        (measurable_pi_apply j).comp hh
  exact hstates.prodMk hactions

@[simp] theorem currentFiber_advanceFiber
    (n : ℕ) (h : HistoryFiber X A n) (a : A) (y : X) :
    currentFiber (n + 1) (advanceFiber n h a y) = y := by
  simp [currentFiber, advanceFiber, Fin.snoc_last]

@[simp] theorem carrier_advance_eq_advanceFiber
    (n : ℕ) (h : HistoryFiber X A n) (a : A) (y : X) :
    Carrier.advance (⟨n, h⟩ : Carrier X A) a y =
      (⟨n + 1, advanceFiber n h a y⟩ : Carrier X A) := rfl

/-- The exact time-zero full history associated with an initial state. -/
def initialHistory (x : X) : HistoryFiber X A 0 :=
  ((fun _ : Fin 1 => x), Fin.elim0)

@[simp] theorem currentFiber_initialHistory (x : X) :
    currentFiber 0 (initialHistory (A := A) x) = x := rfl

/-- Generic measurable discounted model used only for the causal-verification layer. -/
structure Model (X : Type uX) (A : Type uA)
    [MeasurableSpace X] [MeasurableSpace A] where
  transition : Kernel (X × A) X
  transition_markov : IsMarkovKernel transition
  reward : X → A → ℝ
  reward_measurable : Measurable (Function.uncurry reward)
  rewardBound : ℝ
  rewardBound_nonneg : 0 ≤ rewardBound
  reward_abs_le : ∀ x a, |reward x a| ≤ rewardBound
  discount : ℝ
  discount_nonneg : 0 ≤ discount
  discount_lt_one : discount < 1

namespace Model

/-- Exact finite-horizon discounted value of an arbitrary randomized causal policy. -/
noncomputable def truncatedValue (M : Model X A)
    (π : UEOT.V3.ReflexiveStateAugmentation.CausalPolicy X A) :
    (N : ℕ) → (t : ℕ) → HistoryFiber X A t → ℝ
  | 0, _, _ => 0
  | N + 1, t, h =>
      ∫ a,
        (M.reward (currentFiber t h) a +
          M.discount *
            ∫ y, truncatedValue M π N (t + 1) (advanceFiber t h a y)
              ∂M.transition (currentFiber t h, a))
        ∂π t h

@[simp] theorem truncatedValue_zero
    (M : Model X A)
    (π : UEOT.V3.ReflexiveStateAugmentation.CausalPolicy X A)
    (t : ℕ) (h : HistoryFiber X A t) :
    M.truncatedValue π 0 t h = 0 := rfl

@[simp] theorem truncatedValue_succ
    (M : Model X A)
    (π : UEOT.V3.ReflexiveStateAugmentation.CausalPolicy X A)
    (N t : ℕ) (h : HistoryFiber X A t) :
    M.truncatedValue π (N + 1) t h =
      ∫ a,
        (M.reward (currentFiber t h) a +
          M.discount *
            ∫ y, M.truncatedValue π N (t + 1) (advanceFiber t h a y)
              ∂M.transition (currentFiber t h, a))
        ∂π t h := rfl

theorem measurable_truncatedValue
    (M : Model X A)
    (π : UEOT.V3.ReflexiveStateAugmentation.CausalPolicy X A)
    [∀ n, IsMarkovKernel (π n)] :
    ∀ (N t : ℕ), Measurable (M.truncatedValue π N t) := by
  letI : IsMarkovKernel M.transition := M.transition_markov
  intro N
  induction N with
  | zero =>
      intro t
      simp [truncatedValue]
  | succ N ih =>
      intro t
      let K : Kernel (HistoryFiber X A t × A) X := controlledNext t M.transition
      have hcont :
          Measurable
            (fun p : (HistoryFiber X A t × A) × X =>
              M.truncatedValue π N (t + 1) (advanceFiber t p.1.1 p.1.2 p.2)) :=
        (ih (t + 1)).comp (measurable_advanceFiber (X := X) (A := A) t)
      have hinner :
          StronglyMeasurable
            (fun p : HistoryFiber X A t × A =>
              ∫ y, M.truncatedValue π N (t + 1) (advanceFiber t p.1 p.2 y)
                ∂M.transition (currentFiber t p.1, p.2)) := by
        have h := hcont.stronglyMeasurable.integral_kernel_prod_right' (κ := K)
        simpa [K, controlledNext] using h
      have hr :
          StronglyMeasurable
            (fun p : HistoryFiber X A t × A => M.reward (currentFiber t p.1) p.2) := by
        exact (M.reward_measurable.comp
          (((measurable_currentFiber (Z := X) (A := A) t).comp measurable_fst).prodMk
            measurable_snd)).stronglyMeasurable
      have hfull :
          StronglyMeasurable
            (fun p : HistoryFiber X A t × A =>
              M.reward (currentFiber t p.1) p.2 +
                M.discount *
                  ∫ y, M.truncatedValue π N (t + 1) (advanceFiber t p.1 p.2 y)
                    ∂M.transition (currentFiber t p.1, p.2)) := by
        exact hr.add (hinner.const_mul M.discount)
      have hout := hfull.integral_kernel_prod_right' (κ := π t)
      simpa [truncatedValue] using hout.measurable

/-- The one-step action integrand whose policy average is the next truncated value. -/
noncomputable def actionValue
    (M : Model X A)
    (π : UEOT.V3.ReflexiveStateAugmentation.CausalPolicy X A)
    (N t : ℕ) (h : HistoryFiber X A t) (a : A) : ℝ :=
  M.reward (currentFiber t h) a +
    M.discount *
      ∫ y, M.truncatedValue π N (t + 1) (advanceFiber t h a y)
        ∂M.transition (currentFiber t h, a)

theorem truncatedValue_succ_eq_integral_actionValue
    (M : Model X A)
    (π : UEOT.V3.ReflexiveStateAugmentation.CausalPolicy X A)
    (N t : ℕ) (h : HistoryFiber X A t) :
    M.truncatedValue π (N + 1) t h =
      ∫ a, M.actionValue π N t h a ∂π t h := rfl

theorem stronglyMeasurable_actionValue_pair
    (M : Model X A)
    (π : UEOT.V3.ReflexiveStateAugmentation.CausalPolicy X A)
    [∀ n, IsMarkovKernel (π n)]
    (N t : ℕ) :
    StronglyMeasurable
      (fun p : HistoryFiber X A t × A => M.actionValue π N t p.1 p.2) := by
  letI : IsMarkovKernel M.transition := M.transition_markov
  let K : Kernel (HistoryFiber X A t × A) X := controlledNext t M.transition
  have hcont :
      Measurable
        (fun p : (HistoryFiber X A t × A) × X =>
          M.truncatedValue π N (t + 1) (advanceFiber t p.1.1 p.1.2 p.2)) :=
    (M.measurable_truncatedValue π N (t + 1)).comp
      (measurable_advanceFiber (X := X) (A := A) t)
  have hinner :
      StronglyMeasurable
        (fun p : HistoryFiber X A t × A =>
          ∫ y, M.truncatedValue π N (t + 1) (advanceFiber t p.1 p.2 y)
            ∂M.transition (currentFiber t p.1, p.2)) := by
    have h := hcont.stronglyMeasurable.integral_kernel_prod_right' (κ := K)
    simpa [K, controlledNext] using h
  have hr :
      StronglyMeasurable
        (fun p : HistoryFiber X A t × A => M.reward (currentFiber t p.1) p.2) := by
    exact (M.reward_measurable.comp
      (((measurable_currentFiber (Z := X) (A := A) t).comp measurable_fst).prodMk
        measurable_snd)).stronglyMeasurable
  change StronglyMeasurable
    ((fun p : HistoryFiber X A t × A => M.reward (currentFiber t p.1) p.2) +
      (fun p : HistoryFiber X A t × A =>
        M.discount *
          ∫ y, M.truncatedValue π N (t + 1) (advanceFiber t p.1 p.2 y)
            ∂M.transition (currentFiber t p.1, p.2)))
  exact hr.add (hinner.const_mul M.discount)

theorem stronglyMeasurable_actionValue
    (M : Model X A)
    (π : UEOT.V3.ReflexiveStateAugmentation.CausalPolicy X A)
    [∀ n, IsMarkovKernel (π n)]
    (N t : ℕ) (h : HistoryFiber X A t) :
    StronglyMeasurable (M.actionValue π N t h) := by
  exact (M.stronglyMeasurable_actionValue_pair π N t).comp_measurable
    (measurable_prodMk_left : Measurable (fun a : A => (h, a)))

/-- Uniform finite-horizon envelope generated by the one-stage reward bound. -/
def envelope (M : Model X A) : ℕ → ℝ
  | 0 => 0
  | N + 1 => M.rewardBound + M.discount * M.envelope N

@[simp] theorem envelope_zero (M : Model X A) : M.envelope 0 = 0 := rfl

@[simp] theorem envelope_succ (M : Model X A) (N : ℕ) :
    M.envelope (N + 1) = M.rewardBound + M.discount * M.envelope N := rfl

theorem envelope_nonneg (M : Model X A) : ∀ N, 0 ≤ M.envelope N := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      simp only [envelope_succ]
      exact add_nonneg M.rewardBound_nonneg (mul_nonneg M.discount_nonneg ih)

theorem abs_truncatedValue_le_envelope
    (M : Model X A)
    (π : UEOT.V3.ReflexiveStateAugmentation.CausalPolicy X A)
    [∀ n, IsMarkovKernel (π n)] :
    ∀ (N t : ℕ) (h : HistoryFiber X A t),
      |M.truncatedValue π N t h| ≤ M.envelope N := by
  letI : IsMarkovKernel M.transition := M.transition_markov
  intro N
  induction N with
  | zero =>
      intro t h
      simp
  | succ N ih =>
      intro t h
      have hinner (a : A) :
          |∫ y, M.truncatedValue π N (t + 1) (advanceFiber t h a y)
              ∂M.transition (currentFiber t h, a)| ≤ M.envelope N := by
        have hbound :=
          norm_integral_le_of_norm_le_const
            (μ := M.transition (currentFiber t h, a))
            (f := fun y => M.truncatedValue π N (t + 1) (advanceFiber t h a y))
            (C := M.envelope N)
            (Filter.Eventually.of_forall fun y => by
              simpa [Real.norm_eq_abs] using ih (t + 1) (advanceFiber t h a y))
        simpa [Real.norm_eq_abs] using hbound
      have haction (a : A) :
          |M.reward (currentFiber t h) a +
              M.discount *
                ∫ y, M.truncatedValue π N (t + 1) (advanceFiber t h a y)
                  ∂M.transition (currentFiber t h, a)| ≤
            M.envelope (N + 1) := by
        calc
          |M.reward (currentFiber t h) a +
              M.discount *
                ∫ y, M.truncatedValue π N (t + 1) (advanceFiber t h a y)
              ∂M.transition (currentFiber t h, a)|
              ≤ |M.reward (currentFiber t h) a| +
                  |M.discount *
                    ∫ y, M.truncatedValue π N (t + 1) (advanceFiber t h a y)
                      ∂M.transition (currentFiber t h, a)| := abs_add_le _ _
          _ = |M.reward (currentFiber t h) a| +
                M.discount *
                  |∫ y, M.truncatedValue π N (t + 1) (advanceFiber t h a y)
                    ∂M.transition (currentFiber t h, a)| := by
              rw [abs_mul, abs_of_nonneg M.discount_nonneg]
          _ ≤ M.rewardBound + M.discount * M.envelope N :=
              add_le_add (M.reward_abs_le _ _)
                (mul_le_mul_of_nonneg_left (hinner a) M.discount_nonneg)
          _ = M.envelope (N + 1) := by rw [envelope_succ]
      have hout :=
        norm_integral_le_of_norm_le_const
          (μ := π t h)
          (f := fun a =>
            M.reward (currentFiber t h) a +
              M.discount *
                ∫ y, M.truncatedValue π N (t + 1) (advanceFiber t h a y)
                  ∂M.transition (currentFiber t h, a))
          (C := M.envelope (N + 1))
          (Filter.Eventually.of_forall fun a => by
            simpa [Real.norm_eq_abs] using haction a)
      simpa [truncatedValue, Real.norm_eq_abs] using hout

theorem abs_actionValue_le_envelope_succ
    (M : Model X A)
    (π : UEOT.V3.ReflexiveStateAugmentation.CausalPolicy X A)
    [∀ n, IsMarkovKernel (π n)]
    (N t : ℕ) (h : HistoryFiber X A t) (a : A) :
    |M.actionValue π N t h a| ≤ M.envelope (N + 1) := by
  letI : IsMarkovKernel M.transition := M.transition_markov
  have hinner :
      |∫ y, M.truncatedValue π N (t + 1) (advanceFiber t h a y)
          ∂M.transition (currentFiber t h, a)| ≤ M.envelope N := by
    have hbound :=
      norm_integral_le_of_norm_le_const
        (μ := M.transition (currentFiber t h, a))
        (f := fun y => M.truncatedValue π N (t + 1) (advanceFiber t h a y))
        (C := M.envelope N)
        (Filter.Eventually.of_forall fun y => by
          simpa [Real.norm_eq_abs] using
            M.abs_truncatedValue_le_envelope π N (t + 1) (advanceFiber t h a y))
    simpa [Real.norm_eq_abs] using hbound
  calc
    |M.actionValue π N t h a|
        ≤ |M.reward (currentFiber t h) a| +
            |M.discount *
              ∫ y, M.truncatedValue π N (t + 1) (advanceFiber t h a y)
                ∂M.transition (currentFiber t h, a)| := by
          simpa [actionValue] using
            (abs_add_le (M.reward (currentFiber t h) a)
              (M.discount *
                ∫ y, M.truncatedValue π N (t + 1) (advanceFiber t h a y)
                  ∂M.transition (currentFiber t h, a)))
    _ = |M.reward (currentFiber t h) a| +
          M.discount *
            |∫ y, M.truncatedValue π N (t + 1) (advanceFiber t h a y)
              ∂M.transition (currentFiber t h, a)| := by
        rw [abs_mul, abs_of_nonneg M.discount_nonneg]
    _ ≤ M.rewardBound + M.discount * M.envelope N :=
        add_le_add (M.reward_abs_le _ _)
          (mul_le_mul_of_nonneg_left hinner M.discount_nonneg)
    _ = M.envelope (N + 1) := by rw [envelope_succ]

theorem integrable_actionValue
    (M : Model X A)
    (π : UEOT.V3.ReflexiveStateAugmentation.CausalPolicy X A)
    [∀ n, IsMarkovKernel (π n)]
    (N t : ℕ) (h : HistoryFiber X A t) :
    Integrable (M.actionValue π N t h) (π t h) := by
  refine Integrable.of_bound
    (M.stronglyMeasurable_actionValue π N t h).aestronglyMeasurable
    (M.envelope (N + 1)) ?_
  exact Filter.Eventually.of_forall fun a => by
    simpa [Real.norm_eq_abs] using M.abs_actionValue_le_envelope_succ π N t h a

theorem integrable_truncatedValue
    (M : Model X A)
    (π : UEOT.V3.ReflexiveStateAugmentation.CausalPolicy X A)
    [∀ n, IsMarkovKernel (π n)]
    (N t : ℕ) (μ : Measure (HistoryFiber X A t)) [IsFiniteMeasure μ] :
    Integrable (M.truncatedValue π N t) μ := by
  refine Integrable.of_bound
    (M.measurable_truncatedValue π N t).stronglyMeasurable.aestronglyMeasurable
    (M.envelope N) ?_
  exact Filter.Eventually.of_forall fun h => by
    simpa [Real.norm_eq_abs] using M.abs_truncatedValue_le_envelope π N t h

theorem integrable_truncatedValue_after_advance
    (M : Model X A)
    (π : UEOT.V3.ReflexiveStateAugmentation.CausalPolicy X A)
    [∀ n, IsMarkovKernel (π n)]
    (N t : ℕ) (h : HistoryFiber X A t) (a : A) :
    Integrable
      (fun y => M.truncatedValue π N (t + 1) (advanceFiber t h a y))
      (M.transition (currentFiber t h, a)) := by
  letI : IsMarkovKernel M.transition := M.transition_markov
  have hmeas := (M.measurable_truncatedValue π N (t + 1)).comp
    (show Measurable (fun y : X => advanceFiber t h a y) by
      exact (measurable_advanceFiber (X := X) (A := A) t).comp
        ((measurable_const.prodMk measurable_const).prodMk measurable_id))
  refine Integrable.of_bound hmeas.stronglyMeasurable.aestronglyMeasurable
    (M.envelope N) ?_
  exact Filter.Eventually.of_forall fun y => by
    simpa [Real.norm_eq_abs] using
      M.abs_truncatedValue_le_envelope π N (t + 1) (advanceFiber t h a y)

/-- Successive finite-horizon values differ only by the newly exposed terminal reward. -/
theorem abs_truncatedValue_succ_sub_le
    (M : Model X A)
    (π : UEOT.V3.ReflexiveStateAugmentation.CausalPolicy X A)
    [∀ n, IsMarkovKernel (π n)] :
    ∀ (N t : ℕ) (h : HistoryFiber X A t),
      |M.truncatedValue π (N + 1) t h - M.truncatedValue π N t h| ≤
        M.rewardBound * M.discount ^ N := by
  letI : IsMarkovKernel M.transition := M.transition_markov
  intro N
  induction N with
  | zero =>
      intro t h
      have hout :=
        norm_integral_le_of_norm_le_const
          (μ := π t h)
          (f := M.actionValue π 0 t h)
          (C := M.rewardBound)
          (Filter.Eventually.of_forall fun a => by
            have ha := M.abs_actionValue_le_envelope_succ π 0 t h a
            simpa [envelope, Real.norm_eq_abs] using ha)
      simpa [M.truncatedValue_succ_eq_integral_actionValue π 0 t h,
        actionValue, truncatedValue, Real.norm_eq_abs] using hout
  | succ N ih =>
      intro t h
      have hinner (a : A) :
          |(∫ y, M.truncatedValue π (N + 1) (t + 1) (advanceFiber t h a y)
                ∂M.transition (currentFiber t h, a)) -
            (∫ y, M.truncatedValue π N (t + 1) (advanceFiber t h a y)
                ∂M.transition (currentFiber t h, a))| ≤
            M.rewardBound * M.discount ^ N := by
        have hf : Integrable
            (fun y => M.truncatedValue π (N + 1) (t + 1) (advanceFiber t h a y))
            (M.transition (currentFiber t h, a)) := by
          have hmeas := (M.measurable_truncatedValue π (N + 1) (t + 1)).comp
            (show Measurable (fun y : X => advanceFiber t h a y) by
              exact (measurable_advanceFiber (X := X) (A := A) t).comp
                ((measurable_const.prodMk measurable_const).prodMk measurable_id))
          refine Integrable.of_bound hmeas.stronglyMeasurable.aestronglyMeasurable
            (M.envelope (N + 1)) ?_
          exact Filter.Eventually.of_forall fun y => by
            simpa [Real.norm_eq_abs] using
              M.abs_truncatedValue_le_envelope π (N + 1) (t + 1) (advanceFiber t h a y)
        have hg : Integrable
            (fun y => M.truncatedValue π N (t + 1) (advanceFiber t h a y))
            (M.transition (currentFiber t h, a)) := by
          have hmeas := (M.measurable_truncatedValue π N (t + 1)).comp
            (show Measurable (fun y : X => advanceFiber t h a y) by
              exact (measurable_advanceFiber (X := X) (A := A) t).comp
                ((measurable_const.prodMk measurable_const).prodMk measurable_id))
          refine Integrable.of_bound hmeas.stronglyMeasurable.aestronglyMeasurable
            (M.envelope N) ?_
          exact Filter.Eventually.of_forall fun y => by
            simpa [Real.norm_eq_abs] using
              M.abs_truncatedValue_le_envelope π N (t + 1) (advanceFiber t h a y)
        rw [← integral_sub hf hg]
        have hbound :=
          norm_integral_le_of_norm_le_const
            (μ := M.transition (currentFiber t h, a))
            (f := fun y =>
              M.truncatedValue π (N + 1) (t + 1) (advanceFiber t h a y) -
                M.truncatedValue π N (t + 1) (advanceFiber t h a y))
            (C := M.rewardBound * M.discount ^ N)
            (Filter.Eventually.of_forall fun y => by
              simpa [Real.norm_eq_abs] using ih (t + 1) (advanceFiber t h a y))
        simpa [Real.norm_eq_abs] using hbound
      have haction (a : A) :
          |M.actionValue π (N + 1) t h a - M.actionValue π N t h a| ≤
            M.rewardBound * M.discount ^ (N + 1) := by
        rw [actionValue, actionValue]
        have hβ := M.discount_nonneg
        rw [show
          M.reward (currentFiber t h) a +
                M.discount *
                  (∫ y, M.truncatedValue π (N + 1) (t + 1) (advanceFiber t h a y)
                    ∂M.transition (currentFiber t h, a)) -
              (M.reward (currentFiber t h) a +
                M.discount *
                  ∫ y, M.truncatedValue π N (t + 1) (advanceFiber t h a y)
                    ∂M.transition (currentFiber t h, a)) =
            M.discount *
              ((∫ y, M.truncatedValue π (N + 1) (t + 1) (advanceFiber t h a y)
                  ∂M.transition (currentFiber t h, a)) -
                (∫ y, M.truncatedValue π N (t + 1) (advanceFiber t h a y)
                  ∂M.transition (currentFiber t h, a))) by ring,
          abs_mul, abs_of_nonneg hβ]
        calc
          M.discount *
              |(∫ y, M.truncatedValue π (N + 1) (t + 1) (advanceFiber t h a y)
                    ∂M.transition (currentFiber t h, a)) -
                (∫ y, M.truncatedValue π N (t + 1) (advanceFiber t h a y)
                    ∂M.transition (currentFiber t h, a))|
              ≤ M.discount * (M.rewardBound * M.discount ^ N) :=
                mul_le_mul_of_nonneg_left (hinner a) M.discount_nonneg
          _ = M.rewardBound * M.discount ^ (N + 1) := by
                rw [pow_succ]
                ring
      have hf := M.integrable_actionValue π (N + 1) t h
      have hg := M.integrable_actionValue π N t h
      rw [M.truncatedValue_succ_eq_integral_actionValue π (N + 1) t h,
        M.truncatedValue_succ_eq_integral_actionValue π N t h,
        ← integral_sub hf hg]
      have hout :=
        norm_integral_le_of_norm_le_const
          (μ := π t h)
          (f := fun a => M.actionValue π (N + 1) t h a - M.actionValue π N t h a)
          (C := M.rewardBound * M.discount ^ (N + 1))
          (Filter.Eventually.of_forall fun a => by
            simpa [Real.norm_eq_abs] using haction a)
      simpa [Real.norm_eq_abs] using hout

theorem truncatedValue_cauchy
    (M : Model X A)
    (π : UEOT.V3.ReflexiveStateAugmentation.CausalPolicy X A)
    [∀ n, IsMarkovKernel (π n)]
    (t : ℕ) (h : HistoryFiber X A t) :
    CauchySeq (fun N => M.truncatedValue π N t h) := by
  refine cauchySeq_of_le_geometric M.discount M.rewardBound M.discount_lt_one ?_
  intro N
  simpa [Real.dist_eq, abs_sub_comm] using
    M.abs_truncatedValue_succ_sub_le π N t h

noncomputable def infiniteValue
    (M : Model X A)
    (π : UEOT.V3.ReflexiveStateAugmentation.CausalPolicy X A)
    [∀ n, IsMarkovKernel (π n)]
    (t : ℕ) (h : HistoryFiber X A t) : ℝ :=
  limUnder atTop (fun N => M.truncatedValue π N t h)

theorem truncatedValue_tendsto_infiniteValue
    (M : Model X A)
    (π : UEOT.V3.ReflexiveStateAugmentation.CausalPolicy X A)
    [∀ n, IsMarkovKernel (π n)]
    (t : ℕ) (h : HistoryFiber X A t) :
    Tendsto (fun N => M.truncatedValue π N t h) atTop
      (𝓝 (M.infiniteValue π t h)) := by
  simpa [infiniteValue] using (M.truncatedValue_cauchy π t h).tendsto_limUnder

/-- The only Bellman facts needed by the all-causal verification layer. -/
structure BellmanUpperCertificate (M : Model X A) where
  value : X → ℝ
  value_measurable : Measurable value
  valueBound : ℝ
  valueBound_nonneg : 0 ≤ valueBound
  value_abs_le : ∀ x, |value x| ≤ valueBound
  action_le : ∀ x a,
    M.reward x a + M.discount * (∫ y, value y ∂M.transition (x, a)) ≤ value x

namespace BellmanUpperCertificate

variable {M : Model X A}

theorem integrable_value
    (B : BellmanUpperCertificate M)
    (μ : Measure X) [IsFiniteMeasure μ] :
    Integrable B.value μ := by
  refine Integrable.of_bound B.value_measurable.stronglyMeasurable.aestronglyMeasurable
    B.valueBound ?_
  exact Filter.Eventually.of_forall fun x => by
    simpa [Real.norm_eq_abs] using B.value_abs_le x

theorem truncatedValue_le_value_add_tail
    (B : BellmanUpperCertificate M)
    (π : UEOT.V3.ReflexiveStateAugmentation.CausalPolicy X A)
    [∀ n, IsMarkovKernel (π n)] :
    ∀ (N t : ℕ) (h : HistoryFiber X A t),
      M.truncatedValue π N t h ≤
        B.value (currentFiber t h) + M.discount ^ N * B.valueBound := by
  letI : IsMarkovKernel M.transition := M.transition_markov
  intro N
  induction N with
  | zero =>
      intro t h
      have hneg : -B.value (currentFiber t h) ≤ B.valueBound :=
        (neg_le_abs (B.value (currentFiber t h))).trans (B.value_abs_le _)
      simp only [Model.truncatedValue_zero, pow_zero, one_mul]
      linarith
  | succ N ih =>
      intro t h
      have hinner (a : A) :
          (∫ y, M.truncatedValue π N (t + 1) (advanceFiber t h a y)
              ∂M.transition (currentFiber t h, a)) ≤
            (∫ y, B.value y ∂M.transition (currentFiber t h, a)) +
              M.discount ^ N * B.valueBound := by
        have hf := M.integrable_truncatedValue_after_advance π N t h a
        have hv := B.integrable_value (M.transition (currentFiber t h, a))
        have hc : Integrable
            (fun _ : X => M.discount ^ N * B.valueBound)
            (M.transition (currentFiber t h, a)) := integrable_const _
        have hsum : Integrable
            (fun y : X => B.value y + M.discount ^ N * B.valueBound)
            (M.transition (currentFiber t h, a)) := hv.add hc
        calc
          (∫ y, M.truncatedValue π N (t + 1) (advanceFiber t h a y)
              ∂M.transition (currentFiber t h, a))
              ≤ ∫ y, (B.value y + M.discount ^ N * B.valueBound)
                  ∂M.transition (currentFiber t h, a) := by
                exact integral_mono hf hsum fun y => by
                  simpa [currentFiber_advanceFiber] using
                    ih (t + 1) (advanceFiber t h a y)
          _ = (∫ y, B.value y ∂M.transition (currentFiber t h, a)) +
                M.discount ^ N * B.valueBound := by
              rw [integral_add hv hc, integral_const]
              simp
      have haction (a : A) :
          M.actionValue π N t h a ≤
            B.value (currentFiber t h) + M.discount ^ (N + 1) * B.valueBound := by
        calc
          M.actionValue π N t h a
              = M.reward (currentFiber t h) a +
                  M.discount *
                    ∫ y, M.truncatedValue π N (t + 1) (advanceFiber t h a y)
                      ∂M.transition (currentFiber t h, a) := rfl
          _ ≤ M.reward (currentFiber t h) a +
                M.discount *
                  ((∫ y, B.value y ∂M.transition (currentFiber t h, a)) +
                    M.discount ^ N * B.valueBound) := by
              exact add_le_add le_rfl
                (mul_le_mul_of_nonneg_left (hinner a) M.discount_nonneg)
          _ = (M.reward (currentFiber t h) a +
                M.discount * ∫ y, B.value y ∂M.transition (currentFiber t h, a)) +
                M.discount ^ (N + 1) * B.valueBound := by
              rw [pow_succ]
              ring
          _ ≤ B.value (currentFiber t h) +
                M.discount ^ (N + 1) * B.valueBound :=
              add_le_add (B.action_le _ a) le_rfl
      have hf := M.integrable_actionValue π N t h
      have hc : Integrable
          (fun _ : A => B.value (currentFiber t h) +
            M.discount ^ (N + 1) * B.valueBound) (π t h) := integrable_const _
      rw [M.truncatedValue_succ_eq_integral_actionValue π N t h]
      calc
        (∫ a, M.actionValue π N t h a ∂π t h)
            ≤ ∫ _ : A, (B.value (currentFiber t h) +
                M.discount ^ (N + 1) * B.valueBound) ∂π t h :=
              integral_mono hf hc haction
        _ = B.value (currentFiber t h) +
              M.discount ^ (N + 1) * B.valueBound := by
            rw [integral_const]
            simp

theorem infiniteValue_le_value
    (B : BellmanUpperCertificate M)
    (π : UEOT.V3.ReflexiveStateAugmentation.CausalPolicy X A)
    [∀ n, IsMarkovKernel (π n)]
    (t : ℕ) (h : HistoryFiber X A t) :
    M.infiniteValue π t h ≤ B.value (currentFiber t h) := by
  have hleft := M.truncatedValue_tendsto_infiniteValue π t h
  have hpow : Tendsto (fun N : ℕ => M.discount ^ N) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one M.discount_nonneg M.discount_lt_one
  have htail :
      Tendsto (fun N : ℕ => M.discount ^ N * B.valueBound) atTop (𝓝 0) := by
    simpa using hpow.mul_const B.valueBound
  have hright :
      Tendsto
        (fun N : ℕ => B.value (currentFiber t h) + M.discount ^ N * B.valueBound)
        atTop (𝓝 (B.value (currentFiber t h))) := by
    simpa using tendsto_const_nhds.add htail
  exact le_of_tendsto_of_tendsto' hleft hright
    (fun N => B.truncatedValue_le_value_add_tail π N t h)

end BellmanUpperCertificate

/-- A measurable deterministic Bellman maximizer together with its exact one-step equality. -/
structure GreedyCertificate (M : Model X A) extends BellmanUpperCertificate M where
  selector : X → A
  selector_measurable : Measurable selector
  action_eq : ∀ x,
    M.reward x (selector x) +
      M.discount * (∫ y, value y ∂M.transition (x, selector x)) = value x

namespace GreedyCertificate

variable {M : Model X A}

/-- The measurable stationary deterministic policy induced by the greedy selector. -/
noncomputable def stationaryPolicy
    (G : GreedyCertificate M) :
    UEOT.V3.ReflexiveStateAugmentation.CausalPolicy X A :=
  fun n =>
    Kernel.deterministic
      (fun h : HistoryFiber X A n => G.selector (currentFiber n h))
      (G.selector_measurable.comp (measurable_currentFiber (Z := X) (A := A) n))

instance stationaryPolicy_markov
    (G : GreedyCertificate M) (n : ℕ) :
    IsMarkovKernel (G.stationaryPolicy n) := by
  unfold stationaryPolicy
  infer_instance

theorem truncatedValue_stationary_succ
    (G : GreedyCertificate M)
    (N t : ℕ) (h : HistoryFiber X A t) :
    M.truncatedValue G.stationaryPolicy (N + 1) t h =
      M.actionValue G.stationaryPolicy N t h (G.selector (currentFiber t h)) := by
  rw [M.truncatedValue_succ_eq_integral_actionValue G.stationaryPolicy N t h]
  unfold stationaryPolicy
  exact Kernel.integral_deterministic'
    (G.selector_measurable.comp (measurable_currentFiber (Z := X) (A := A) t))
    (M.stronglyMeasurable_actionValue G.stationaryPolicy N t h)

theorem value_sub_tail_le_truncatedValue_stationary
    (G : GreedyCertificate M) :
    ∀ (N t : ℕ) (h : HistoryFiber X A t),
      G.value (currentFiber t h) - M.discount ^ N * G.valueBound ≤
        M.truncatedValue G.stationaryPolicy N t h := by
  letI : IsMarkovKernel M.transition := M.transition_markov
  intro N
  induction N with
  | zero =>
      intro t h
      have hpos : G.value (currentFiber t h) ≤ G.valueBound :=
        (le_abs_self (G.value (currentFiber t h))).trans (G.value_abs_le _)
      simp only [Model.truncatedValue_zero, pow_zero, one_mul]
      linarith
  | succ N ih =>
      intro t h
      let a : A := G.selector (currentFiber t h)
      have hinner :
          (∫ y, G.value y ∂M.transition (currentFiber t h, a)) -
              M.discount ^ N * G.valueBound ≤
            ∫ y, M.truncatedValue G.stationaryPolicy N (t + 1)
                (advanceFiber t h a y)
              ∂M.transition (currentFiber t h, a) := by
        have hv := G.toBellmanUpperCertificate.integrable_value
          (M.transition (currentFiber t h, a))
        have hc : Integrable
            (fun _ : X => M.discount ^ N * G.valueBound)
            (M.transition (currentFiber t h, a)) := integrable_const _
        have hleft : Integrable
            (fun y : X => G.value y - M.discount ^ N * G.valueBound)
            (M.transition (currentFiber t h, a)) := hv.sub hc
        have hright :=
          M.integrable_truncatedValue_after_advance G.stationaryPolicy N t h a
        calc
          (∫ y, G.value y ∂M.transition (currentFiber t h, a)) -
                M.discount ^ N * G.valueBound
              = ∫ y, (G.value y - M.discount ^ N * G.valueBound)
                  ∂M.transition (currentFiber t h, a) := by
                rw [integral_sub hv hc, integral_const]
                simp
          _ ≤ ∫ y, M.truncatedValue G.stationaryPolicy N (t + 1)
                  (advanceFiber t h a y)
                ∂M.transition (currentFiber t h, a) := by
              exact integral_mono hleft hright fun y => by
                simpa [currentFiber_advanceFiber] using
                  ih (t + 1) (advanceFiber t h a y)
      have haction :
          G.value (currentFiber t h) - M.discount ^ (N + 1) * G.valueBound ≤
            M.actionValue G.stationaryPolicy N t h a := by
        calc
          G.value (currentFiber t h) - M.discount ^ (N + 1) * G.valueBound
              = (M.reward (currentFiber t h) a +
                  M.discount *
                    ∫ y, G.value y ∂M.transition (currentFiber t h, a)) -
                    M.discount ^ (N + 1) * G.valueBound := by
                rw [G.action_eq (currentFiber t h)]
          _ = M.reward (currentFiber t h) a +
                M.discount *
                  ((∫ y, G.value y ∂M.transition (currentFiber t h, a)) -
                    M.discount ^ N * G.valueBound) := by
              rw [pow_succ]
              ring
          _ ≤ M.reward (currentFiber t h) a +
                M.discount *
                  ∫ y, M.truncatedValue G.stationaryPolicy N (t + 1)
                    (advanceFiber t h a y)
                    ∂M.transition (currentFiber t h, a) := by
              exact add_le_add le_rfl
                (mul_le_mul_of_nonneg_left hinner M.discount_nonneg)
          _ = M.actionValue G.stationaryPolicy N t h a := rfl
      rw [G.truncatedValue_stationary_succ N t h]
      simpa [a] using haction

theorem truncatedValue_stationary_tendsto_value
    (G : GreedyCertificate M)
    (t : ℕ) (h : HistoryFiber X A t) :
    Tendsto (fun N => M.truncatedValue G.stationaryPolicy N t h) atTop
      (𝓝 (G.value (currentFiber t h))) := by
  have hupper (N : ℕ) :=
    G.toBellmanUpperCertificate.truncatedValue_le_value_add_tail
      G.stationaryPolicy N t h
  have hlower (N : ℕ) :=
    G.value_sub_tail_le_truncatedValue_stationary N t h
  have herr (N : ℕ) :
      dist (M.truncatedValue G.stationaryPolicy N t h)
          (G.value (currentFiber t h)) ≤
        M.discount ^ N * G.valueBound := by
    rw [Real.dist_eq, abs_le]
    constructor
    · have hl := hlower N
      linarith
    · have hu := hupper N
      linarith
  have hpow : Tendsto (fun N : ℕ => M.discount ^ N) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one M.discount_nonneg M.discount_lt_one
  have htail :
      Tendsto (fun N : ℕ => M.discount ^ N * G.valueBound) atTop (𝓝 0) := by
    simpa using hpow.mul_const G.valueBound
  exact tendsto_iff_dist_tendsto_zero.2
    (squeeze_zero (fun _ => dist_nonneg) herr htail)

theorem stationary_infiniteValue_eq_value
    (G : GreedyCertificate M)
    (t : ℕ) (h : HistoryFiber X A t) :
    M.infiniteValue G.stationaryPolicy t h = G.value (currentFiber t h) := by
  exact tendsto_nhds_unique
    (M.truncatedValue_tendsto_infiniteValue G.stationaryPolicy t h)
    (G.truncatedValue_stationary_tendsto_value t h)

/-- Full all-causal verification: every randomized history-dependent policy is dominated,
and the measurable stationary deterministic greedy policy attains the Bellman value. -/
theorem optimal_against_all_causal
    (G : GreedyCertificate M) :
    (∀ (π : UEOT.V3.ReflexiveStateAugmentation.CausalPolicy X A)
        [∀ n, IsMarkovKernel (π n)]
        (t : ℕ) (h : HistoryFiber X A t),
      M.infiniteValue π t h ≤ G.value (currentFiber t h)) ∧
    (∀ (t : ℕ) (h : HistoryFiber X A t),
      M.infiniteValue G.stationaryPolicy t h = G.value (currentFiber t h)) := by
  constructor
  · intro π hπ t h
    exact G.toBellmanUpperCertificate.infiniteValue_le_value π t h
  · intro t h
    exact G.stationary_infiniteValue_eq_value t h

/-- Source-facing initial-state form of all-causal optimality. -/
theorem optimal_against_all_causal_from_state
    (G : GreedyCertificate M) :
    (∀ (π : UEOT.V3.ReflexiveStateAugmentation.CausalPolicy X A)
        [∀ n, IsMarkovKernel (π n)] (x : X),
      M.infiniteValue π 0 (initialHistory (A := A) x) ≤ G.value x) ∧
    (∀ x : X,
      M.infiniteValue G.stationaryPolicy 0 (initialHistory (A := A) x) = G.value x) := by
  constructor
  · intro π hπ x
    simpa using G.toBellmanUpperCertificate.infiniteValue_le_value
      π 0 (initialHistory (A := A) x)
  · intro x
    simpa using G.stationary_infiniteValue_eq_value 0 (initialHistory (A := A) x)

end GreedyCertificate

end Model
end
end UEOT.V3.CompactCausalOptimalityCore
