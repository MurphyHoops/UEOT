import UEOT.V3.Compression.Objecthood.AbsorbedRepairHittingSemantics
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Track O / GCR2 — exact path-law discounted hitting transform

This stage identifies the nested complete-history discounted value of GCR1 with
an exact normalized target occupation of the absorbed physical Ionescu--Tulcea
path law.  The normalized occupation is the Route-A hitting transform
representation used by GCR3; no beta-to-one or undiscounted completeness claim
is made here.
-/

namespace UEOT.V3.Compression.Objecthood

open Set Finset MeasureTheory ProbabilityTheory
open UEOT.V3.FiniteHistory
open UEOT.V3.FiniteHistoryMeasurable
open UEOT.V3.ReflexiveStateAugmentation
open UEOT.V3.ReflexiveStatePathLaw
open UEOT.V3.CompactCausalOptimalityCore
open UEOT.V3.DynamicsKernel
open scoped ENNReal ProbabilityTheory

universe uX uA uZ
noncomputable section

variable {X : Type uX} {A : Type uA}
variable [Fintype X] [Fintype A]
variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace A] [MeasurableSingletonClass A]

private theorem integral_fixedPolicyAugmented
    (n : ℕ) (pi : Kernel (HistoryFiber X A n) A) [IsMarkovKernel pi]
    (K : Kernel (X × A) X) [IsMarkovKernel K]
    (h : HistoryFiber X A n)
    (f : Carrier X A → ℝ) (hf : StronglyMeasurable f)
    (C : ℝ) (hC : ∀ z, ‖f z‖ ≤ C) :
    (∫ z, f z ∂fixedPolicyAugmented n pi K h) =
      ∫ a, ∫ y, f (Carrier.advance (⟨n,h⟩ : Carrier X A) a y)
        ∂K (currentFiber n h, a) ∂pi h := by
  let B : Kernel (HistoryFiber X A n) (HistoryFiber X A n × A) := Kernel.id ×ₖ pi
  let Cnext : Kernel (HistoryFiber X A n × A) X := controlledNext n K
  have hpre_meas : StronglyMeasurable
      (fun p : (HistoryFiber X A n × A) × X =>
        f (Carrier.advance (⟨n,p.1.1⟩ : Carrier X A) p.1.2 p.2)) :=
    hf.comp_measurable (measurable_advance_fixed n)
  have hpre_int : Integrable
      (fun p : (HistoryFiber X A n × A) × X =>
        f (Carrier.advance (⟨n,p.1.1⟩ : Carrier X A) p.1.2 p.2))
      ((B ⊗ₖ Cnext.comap Prod.snd measurable_snd) h) := by
    refine Integrable.of_bound hpre_meas.aestronglyMeasurable C ?_
    exact Filter.Eventually.of_forall fun p => hC _
  unfold fixedPolicyAugmented
  rw [Kernel.map_apply _ (measurable_advance_fixed n)]
  rw [integral_map_of_stronglyMeasurable (measurable_advance_fixed n) hf]
  rw [ProbabilityTheory.integral_compProd hpre_int]
  change
    (∫ p : HistoryFiber X A n × A,
      ∫ y, f (Carrier.advance (⟨n,p.1⟩ : Carrier X A) p.2 y)
        ∂K (currentFiber n p.1, p.2) ∂B h) = _
  have houter_int_B : Integrable
      (fun p : HistoryFiber X A n × A =>
        ∫ y, f (Carrier.advance (⟨n,p.1⟩ : Carrier X A) p.2 y)
          ∂K (currentFiber n p.1, p.2)) (B h) := by
    simpa [Cnext, controlledNext, Kernel.comap_apply] using hpre_int.integral_compProd
  have hB : B h = (Measure.dirac h).prod (pi h) := by
    simp [B, Kernel.prod_apply, Kernel.id_apply]
  have houter_int : Integrable
      (fun p : HistoryFiber X A n × A =>
        ∫ y, f (Carrier.advance (⟨n,p.1⟩ : Carrier X A) p.2 y)
          ∂K (currentFiber n p.1, p.2))
      ((Measure.dirac h).prod (pi h)) := by
    rwa [← hB]
  rw [hB, MeasureTheory.integral_prod _ houter_int]
  have hinner_strong : StronglyMeasurable
      (fun p : HistoryFiber X A n × A =>
        ∫ y, f (Carrier.advance (⟨n,p.1⟩ : Carrier X A) p.2 y)
          ∂K (currentFiber n p.1, p.2)) := by
    have hpre_meas' := hpre_meas.integral_kernel_prod_right'
      (κ := controlledNext n K)
    simpa [controlledNext] using hpre_meas'
  have houter_strong : StronglyMeasurable
      (fun h' : HistoryFiber X A n =>
        ∫ a, ∫ y, f (Carrier.advance (⟨n,h'⟩ : Carrier X A) a y)
          ∂K (currentFiber n h', a) ∂pi h) := by
    exact hinner_strong.integral_prod_right'
  rw [MeasureTheory.integral_dirac' _ _ houter_strong]

/-- Carrier-level stage reward of the normalized absorbed repair model. -/
noncomputable def carrierRepairReward (K : Set X) (beta : ℝ) (z : Carrier X A) : ℝ := by
  classical
  exact if Carrier.current z ∈ K then 1 - beta else 0

private theorem stronglyMeasurable_carrierRepairReward
    (K : Set X) (beta : ℝ) :
    StronglyMeasurable (carrierRepairReward (X := X) (A := A) K beta) := by
  classical
  have hstate : Measurable (fun x : X => if x ∈ K then (1 - beta : ℝ) else 0) :=
    measurable_of_finite _
  exact (hstate.comp measurable_current).stronglyMeasurable

/-- Ordinary Markov discounted recursion on the time-tagged complete-history carrier. -/
noncomputable def carrierRepairTruncatedValue
    (P : X → A → PMF X) (K : Set X) (beta : ℝ)
    (pi : CausalPolicy X A) : ℕ → Carrier X A → ℝ
  | 0, _ => 0
  | N + 1, z =>
      carrierRepairReward K beta z + beta *
        ∫ z', carrierRepairTruncatedValue P K beta pi N z'
          ∂historyKernel (pmfControlledKernel (absorbedRepairPMF P K)) pi z

@[simp] theorem carrierRepairTruncatedValue_zero
    (P : X → A → PMF X) (K : Set X) (beta : ℝ) (pi : CausalPolicy X A) (z : Carrier X A) :
    carrierRepairTruncatedValue P K beta pi 0 z = 0 := rfl

@[simp] theorem carrierRepairTruncatedValue_succ
    (P : X → A → PMF X) (K : Set X) (beta : ℝ) (pi : CausalPolicy X A)
    (N : ℕ) (z : Carrier X A) :
    carrierRepairTruncatedValue P K beta pi (N+1) z =
      carrierRepairReward K beta z + beta *
        ∫ z', carrierRepairTruncatedValue P K beta pi N z'
          ∂historyKernel (pmfControlledKernel (absorbedRepairPMF P K)) pi z := rfl

theorem stronglyMeasurable_carrierRepairTruncatedValue
    (P : X → A → PMF X) (K : Set X) (beta : ℝ)
    (pi : CausalPolicy X A) [∀ n, IsMarkovKernel (pi n)] :
    ∀ N, StronglyMeasurable (carrierRepairTruncatedValue P K beta pi N) := by
  intro N
  induction N with
  | zero => exact stronglyMeasurable_const
  | succ N ih =>
      have hint : StronglyMeasurable
          (fun z => ∫ z', carrierRepairTruncatedValue P K beta pi N z'
            ∂historyKernel (pmfControlledKernel (absorbedRepairPMF P K)) pi z) :=
        ih.integral_kernel
      exact (stronglyMeasurable_carrierRepairReward (X := X) (A := A) K beta).add
        (hint.const_mul beta)

theorem norm_carrierRepairTruncatedValue_le
    (P : X → A → PMF X) (K : Set X) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1)
    (pi : CausalPolicy X A) [∀ n, IsMarkovKernel (pi n)] :
    ∀ (N : ℕ) (z : Carrier X A),
      ‖carrierRepairTruncatedValue P K beta pi N z‖ ≤ N := by
  intro N
  induction N with
  | zero => intro z; simp [carrierRepairTruncatedValue]
  | succ N ih =>
      intro z
      have hint :
          ‖∫ z', carrierRepairTruncatedValue P K beta pi N z'
              ∂historyKernel (pmfControlledKernel (absorbedRepairPMF P K)) pi z‖ ≤ N := by
        have hb := norm_integral_le_of_norm_le_const
          (μ := historyKernel (pmfControlledKernel (absorbedRepairPMF P K)) pi z)
          (f := carrierRepairTruncatedValue P K beta pi N)
          (C := (N : ℝ))
          (Filter.Eventually.of_forall fun z' => by simpa using ih z')
        simpa using hb
      have hr : ‖carrierRepairReward (X := X) (A := A) K beta z‖ ≤ 1 := by
        classical
        rw [carrierRepairReward]
        by_cases hz : Carrier.current z ∈ K
        · simp [hz, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hbeta1)]
          linarith
        · simp [hz]
      rw [carrierRepairTruncatedValue_succ]
      calc
        ‖carrierRepairReward K beta z + beta *
            ∫ z', carrierRepairTruncatedValue P K beta pi N z'
              ∂historyKernel (pmfControlledKernel (absorbedRepairPMF P K)) pi z‖
            ≤ ‖carrierRepairReward K beta z‖ +
                ‖beta * ∫ z', carrierRepairTruncatedValue P K beta pi N z'
                  ∂historyKernel (pmfControlledKernel (absorbedRepairPMF P K)) pi z‖ :=
              norm_add_le _ _
        _ = ‖carrierRepairReward K beta z‖ + beta *
              ‖∫ z', carrierRepairTruncatedValue P K beta pi N z'
                ∂historyKernel (pmfControlledKernel (absorbedRepairPMF P K)) pi z‖ := by
              simp [norm_mul, Real.norm_eq_abs, abs_of_nonneg hbeta0]
        _ ≤ 1 + beta * N := add_le_add hr (mul_le_mul_of_nonneg_left hint hbeta0)
        _ ≤ 1 + N := by
              have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
              nlinarith
        _ = (N + 1 : ℕ) := by simp [Nat.cast_add, add_comm]

/-- The nested causal finite-horizon value is exactly the ordinary Markov recursion
on the complete-history carrier. -/
theorem truncatedValue_eq_carrierRepairTruncatedValue
    (P : X → A → PMF X) (K : Set X)
    (beta : ℝ) (hbeta0 : 0 < beta) (hbeta1 : beta < 1)
    (pi : CausalPolicy X A) [∀ n, IsMarkovKernel (pi n)] :
    ∀ (N t : ℕ) (h : HistoryFiber X A t),
      (causalNormalizedRepairModel P K beta hbeta0.le hbeta1).truncatedValue pi N t h =
        carrierRepairTruncatedValue P K beta pi N (⟨t,h⟩ : Carrier X A) := by
  classical
  intro N
  induction N with
  | zero => intro t h; rfl
  | succ N ih =>
      intro t h
      let M := causalNormalizedRepairModel P K beta hbeta0.le hbeta1
      let Q := pmfControlledKernel (absorbedRepairPMF P K)
      let f := carrierRepairTruncatedValue P K beta pi N
      have hf : StronglyMeasurable f := stronglyMeasurable_carrierRepairTruncatedValue P K beta pi N
      have hbound : ∀ z, ‖f z‖ ≤ (N : ℝ) := by
        intro z
        simpa [f] using norm_carrierRepairTruncatedValue_le P K beta hbeta0.le hbeta1.le pi N z
      have hstep := integral_fixedPolicyAugmented t (pi t) Q h f hf (N : ℝ) hbound
      rw [M.truncatedValue_succ_eq_integral_actionValue]
      unfold UEOT.V3.CompactCausalOptimalityCore.Model.actionValue
      change
        (∫ a,
          ((if currentFiber t h ∈ K then 1 - beta else 0) +
            beta * ∫ y,
              (causalNormalizedRepairModel P K beta hbeta0.le hbeta1).truncatedValue
                pi N (t + 1) (advanceFiber t h a y)
              ∂Q (currentFiber t h, a)) ∂pi t h) = _
      simp_rw [ih (t + 1)]
      change
        (∫ a,
          ((if currentFiber t h ∈ K then 1 - beta else 0) +
            beta * ∫ y, f (Carrier.advance (⟨t,h⟩ : Carrier X A) a y)
              ∂Q (currentFiber t h, a)) ∂pi t h) = _
      have hinner_meas : StronglyMeasurable
          (fun a : A => ∫ y, f (Carrier.advance (⟨t,h⟩ : Carrier X A) a y)
            ∂Q (currentFiber t h, a)) :=
        (measurable_of_countable _).stronglyMeasurable
      have hinner_int : Integrable
          (fun a : A => ∫ y, f (Carrier.advance (⟨t,h⟩ : Carrier X A) a y)
            ∂Q (currentFiber t h, a)) (pi t h) := by
        refine Integrable.of_bound hinner_meas.aestronglyMeasurable (N : ℝ) ?_
        refine Filter.Eventually.of_forall fun a => ?_
        have hb := norm_integral_le_of_norm_le_const
          (μ := Q (currentFiber t h, a))
          (f := fun y => f (Carrier.advance (⟨t,h⟩ : Carrier X A) a y))
          (C := (N : ℝ))
          (Filter.Eventually.of_forall fun y => hbound _)
        simpa using hb
      have hconst_int : Integrable
          (fun _ : A => (if currentFiber t h ∈ K then 1 - beta else 0)) (pi t h) :=
        integrable_const _
      rw [integral_add hconst_int (hinner_int.const_mul beta)]
      rw [integral_const, integral_const_mul]
      simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
      rw [← hstep]
      rw [carrierRepairTruncatedValue_succ]
      have hreward :
          carrierRepairReward K beta (⟨t, h⟩ : Carrier X A) =
            (if currentFiber t h ∈ K then 1 - beta else 0) := by
        classical
        unfold carrierRepairReward
        rfl
      rw [hreward]
      change
        (if currentFiber t h ∈ K then 1 - beta else 0) +
            beta * ∫ z, f z ∂fixedPolicyAugmented t (pi t) Q h =
          (if currentFiber t h ∈ K then 1 - beta else 0) +
            beta * ∫ z, f z ∂fixedPolicyAugmented t (pi t) Q h
      rfl



private theorem iterateKernel_isMarkov
    (Q : Kernel (Carrier X A) (Carrier X A)) [IsMarkovKernel Q] :
    ∀ n : ℕ, IsMarkovKernel (iterateKernel Q n) := by
  intro n
  induction n with
  | zero =>
      rw [iterateKernel_zero]
      infer_instance
  | succ n ih =>
      rw [iterateKernel_succ]
      letI : IsMarkovKernel (iterateKernel Q n) := ih
      infer_instance

private theorem iterateKernel_comm_right
    (Q : Kernel (Carrier X A) (Carrier X A)) :
    ∀ n : ℕ, iterateKernel Q n ∘ₖ Q = Q ∘ₖ iterateKernel Q n := by
  intro n
  induction n with
  | zero => simp [iterateKernel_zero]
  | succ n ih =>
      rw [iterateKernel_succ]
      rw [Kernel.comp_assoc]
      rw [ih]

private theorem iterateKernel_succ_right
    (Q : Kernel (Carrier X A) (Carrier X A)) (n : ℕ) :
    iterateKernel Q (n + 1) = iterateKernel Q n ∘ₖ Q := by
  rw [iterateKernel_succ, iterateKernel_comm_right Q n]


variable {Z : Type uZ} [MeasurableSpace Z]

/-- General last-coordinate marginal bridge for homogeneous history kernels. -/
theorem homHistoryKernel_comp_eq_last_marginal_general
    (Q : Kernel Z Z) [IsMarkovKernel Q]
    (n : ℕ) (nu : Measure ((i : Finset.Iic n) → Z)) [SFinite nu] :
    homHistoryKernel Q n ∘ₘ nu =
      Q ∘ₘ nu.map (fun h => h (lastHistoryIndex n)) := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
  unfold homHistoryKernel
  simp_rw [Kernel.comap_apply']
  rw [lintegral_map (Kernel.measurable_coe Q hs)
    (measurable_pi_apply (lastHistoryIndex n))]

/-- Successive coordinate marginals of a homogeneous Ionescu--Tulcea law,
without finite-state assumptions. -/
theorem homTrajMeasure_time_succ_general
    (mu : Measure Z) [IsProbabilityMeasure mu]
    (Q : Kernel Z Z) [IsMarkovKernel Q] (n : ℕ) :
    (homTrajMeasure mu Q).map (fun z : ℕ → Z => z (n + 1)) =
      Q ∘ₘ (homTrajMeasure mu Q).map (fun z : ℕ → Z => z n) := by
  letI : ∀ k, IsMarkovKernel (homHistoryKernel Q k) :=
    fun k => isMarkovKernel_homHistoryKernel Q k
  let muPath := homTrajMeasure mu Q
  have hstep :=
    ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      (X := fun _ : ℕ => Z) (μ₀ := mu) (κ := homHistoryKernel Q) (a := n)
  have hstep' :
      (muPath.map (Preorder.frestrictLe n)) ⊗ₘ homHistoryKernel Q n =
        muPath.map
          (fun x => (Preorder.frestrictLe n x, x (n + 1))) := by
    simpa [muPath, homTrajMeasure] using hstep
  have hnext :
      muPath.map (fun z : ℕ → Z => z (n + 1)) =
        homHistoryKernel Q n ∘ₘ muPath.map (Preorder.frestrictLe n) := by
    calc
      muPath.map (fun z : ℕ → Z => z (n + 1)) =
          (muPath.map
            (fun x => (Preorder.frestrictLe n x, x (n + 1)))).map
            Prod.snd := by
        symm
        rw [Measure.map_map measurable_snd (by fun_prop)]
        rfl
      _ =
          ((muPath.map (Preorder.frestrictLe n)) ⊗ₘ
            homHistoryKernel Q n).map Prod.snd := by
        rw [hstep']
      _ = homHistoryKernel Q n ∘ₘ
          muPath.map (Preorder.frestrictLe n) := by
        simpa [Measure.snd] using
          (Measure.snd_compProd
            (muPath.map (Preorder.frestrictLe n))
            (homHistoryKernel Q n))
  rw [hnext]
  rw [homHistoryKernel_comp_eq_last_marginal_general]
  congr 1
  rw [Measure.map_map
    (μ := muPath)
    (measurable_pi_apply (lastHistoryIndex n))
    (Preorder.measurable_frestrictLe n)]
  rfl


/-- Exact n-step target probability from a complete-history state. -/
noncomputable def carrierTargetProbability
    (Q : Kernel (Carrier X A) (Carrier X A))
    (K : Set X) (z : Carrier X A) (n : ℕ) : ℝ :=
  (iterateKernel Q n z).real (historyRepairTarget (A := A) K)

theorem normalized_carrierTargetProbability_zero
    (Q : Kernel (Carrier X A) (Carrier X A)) [IsMarkovKernel Q]
    (K : Set X) (beta : ℝ) (z : Carrier X A) :
    (1 - beta) * carrierTargetProbability Q K z 0 =
      carrierRepairReward K beta z := by
  classical
  unfold carrierTargetProbability historyRepairTarget
  rw [iterateKernel_zero, Kernel.id_apply, measureReal_def]
  rw [Measure.dirac_apply' z ((Set.toFinite K).measurableSet.preimage measurable_current)]
  unfold carrierRepairReward
  by_cases hz : Carrier.current z ∈ K <;> simp [Set.indicator, hz]

/-- Chapman--Kolmogorov recursion for the real target probability. -/
theorem carrierTargetProbability_succ
    (Q : Kernel (Carrier X A) (Carrier X A)) [IsMarkovKernel Q]
    (K : Set X) (z : Carrier X A) (n : ℕ) :
    carrierTargetProbability Q K z (n + 1) =
      ∫ y, carrierTargetProbability Q K y n ∂Q z := by
  letI : IsMarkovKernel (iterateKernel Q n) := iterateKernel_isMarkov Q n
  letI : IsMarkovKernel (iterateKernel Q (n+1)) := iterateKernel_isMarkov Q (n+1)
  have hS : MeasurableSet (historyRepairTarget (A := A) K) :=
    measurableSet_historyRepairTarget (A := A) K
  unfold carrierTargetProbability
  rw [iterateKernel_succ_right Q n]
  have hInt : Integrable
      ((historyRepairTarget (A := A) K).indicator (fun _ => (1 : ℝ)))
      ((iterateKernel Q n ∘ₖ Q) z) := by
    letI : IsProbabilityMeasure ((iterateKernel Q n ∘ₖ Q) z) := by infer_instance
    exact (integrable_const (1 : ℝ)).indicator hS
  rw [← integral_indicator_one hS]
  calc
    (∫ x, (historyRepairTarget (A := A) K).indicator
        (fun _ => (1 : ℝ)) x ∂(iterateKernel Q n ∘ₖ Q) z) =
        ∫ y, ∫ x, (historyRepairTarget (A := A) K).indicator
          (fun _ => (1 : ℝ)) x ∂iterateKernel Q n y ∂Q z :=
      ProbabilityTheory.Kernel.integral_comp hInt
    _ = ∫ y, (iterateKernel Q n y).real
          (historyRepairTarget (A := A) K) ∂Q z := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => integral_indicator_one hS


/-- Exact finite normalized discounted target occupation from a complete-history
state, expressed in terms of the homogeneous history-kernel n-step target
probabilities. -/
noncomputable def carrierNormalizedOccupationPartial
    (Q : Kernel (Carrier X A) (Carrier X A))
    (K : Set X) (beta : ℝ) (N : ℕ) (z : Carrier X A) : ℝ :=
  ∑ n ∈ Finset.range N,
    beta ^ n * (1 - beta) * carrierTargetProbability Q K z n

@[simp] theorem carrierNormalizedOccupationPartial_zero
    (Q : Kernel (Carrier X A) (Carrier X A))
    (K : Set X) (beta : ℝ) (z : Carrier X A) :
    carrierNormalizedOccupationPartial Q K beta 0 z = 0 := by
  simp [carrierNormalizedOccupationPartial]

private theorem measurable_carrierTargetProbability
    (Q : Kernel (Carrier X A) (Carrier X A)) [IsMarkovKernel Q]
    (K : Set X) (n : ℕ) :
    Measurable (fun z => carrierTargetProbability Q K z n) := by
  unfold carrierTargetProbability
  exact (iterateKernel Q n).measurable_coe
    (measurableSet_historyRepairTarget (A := A) K) |>.ennreal_toReal

private theorem integrable_carrierTargetProbability
    (Q : Kernel (Carrier X A) (Carrier X A)) [IsMarkovKernel Q]
    (K : Set X) (n : ℕ) (z : Carrier X A) :
    Integrable (fun y => carrierTargetProbability Q K y n) (Q z) := by
  letI : IsProbabilityMeasure (Q z) := by infer_instance
  have hm := (measurable_carrierTargetProbability Q K n).stronglyMeasurable
  refine Integrable.of_bound hm.aestronglyMeasurable 1 ?_
  refine Filter.Eventually.of_forall fun y => ?_
  letI : IsMarkovKernel (iterateKernel Q n) := iterateKernel_isMarkov Q n
  unfold carrierTargetProbability
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  letI : IsProbabilityMeasure (iterateKernel Q n y) := by infer_instance
  exact measureReal_le_one

/-- The exact normalized occupation partial sum obeys the same one-step Bellman
recursion as the carrier repair value. -/
theorem carrierNormalizedOccupationPartial_succ
    (Q : Kernel (Carrier X A) (Carrier X A)) [IsMarkovKernel Q]
    (K : Set X) (beta : ℝ) (z : Carrier X A) (N : ℕ) :
    carrierNormalizedOccupationPartial Q K beta (N + 1) z =
      carrierRepairReward K beta z +
        beta * ∫ y, carrierNormalizedOccupationPartial Q K beta N y ∂Q z := by
  classical
  rw [carrierNormalizedOccupationPartial]
  rw [Finset.sum_range_succ']
  simp only [pow_zero, one_mul]
  rw [normalized_carrierTargetProbability_zero Q K beta z]
  have hint_each : ∀ n ∈ Finset.range N,
      Integrable
        (fun y => beta ^ n * (1 - beta) * carrierTargetProbability Q K y n)
        (Q z) := by
    intro n hn
    exact (integrable_carrierTargetProbability Q K n z).const_mul
      (beta ^ n * (1 - beta))
  have hsum_int : Integrable
      (fun y => ∑ n ∈ Finset.range N,
        beta ^ n * (1 - beta) * carrierTargetProbability Q K y n) (Q z) := by
    exact MeasureTheory.integrable_finsetSum _ hint_each
  change
    (∑ k ∈ Finset.range N,
        beta ^ (k + 1) * (1 - beta) * carrierTargetProbability Q K z (k + 1)) +
        carrierRepairReward K beta z =
      carrierRepairReward K beta z +
        beta * ∫ y, (∑ n ∈ Finset.range N,
          beta ^ n * (1 - beta) * carrierTargetProbability Q K y n) ∂Q z
  rw [MeasureTheory.integral_finsetSum _ hint_each]
  simp_rw [integral_const_mul]
  simp_rw [← carrierTargetProbability_succ Q K z]
  have hp : ∀ n : ℕ, beta * (beta ^ n * (1 - beta)) = beta ^ (n + 1) * (1 - beta) := by
    intro n
    rw [pow_succ]
    ring
  rw [mul_sum]
  have hsum :
      (∑ i ∈ Finset.range N,
        beta * (beta ^ i * (1 - beta) * carrierTargetProbability Q K z (i + 1))) =
      ∑ i ∈ Finset.range N,
        beta ^ (i + 1) * (1 - beta) * carrierTargetProbability Q K z (i + 1) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← hp i]
    ring
  rw [hsum]
  ring

/-- The nested causal finite-horizon value is exactly the finite normalized
occupation of the complete-history Markovized path. -/
theorem truncatedValue_eq_carrierNormalizedOccupationPartial
    (P : X → A → PMF X) (K : Set X)
    (beta : ℝ) (hbeta0 : 0 < beta) (hbeta1 : beta < 1)
    (pi : CausalPolicy X A) [∀ n, IsMarkovKernel (pi n)] :
    ∀ (N t : ℕ) (h : HistoryFiber X A t),
      (causalNormalizedRepairModel P K beta hbeta0.le hbeta1).truncatedValue pi N t h =
        carrierNormalizedOccupationPartial
          (historyKernel (pmfControlledKernel (absorbedRepairPMF P K)) pi)
          K beta N (⟨t,h⟩ : Carrier X A) := by
  intro N t h
  rw [truncatedValue_eq_carrierRepairTruncatedValue P K beta hbeta0 hbeta1 pi N t h]
  induction N generalizing t with
  | zero => simp [carrierRepairTruncatedValue, carrierNormalizedOccupationPartial]
  | succ N ih =>
      rw [carrierRepairTruncatedValue_succ]
      rw [carrierNormalizedOccupationPartial_succ]
      have hQ :
          historyKernel (pmfControlledKernel (absorbedRepairPMF P K)) pi (⟨t,h⟩ : Carrier X A) =
            fixedPolicyAugmented t (pi t)
              (pmfControlledKernel (absorbedRepairPMF P K)) h := rfl
      rw [hQ]
      apply congrArg (fun r : ℝ => carrierRepairReward K beta (⟨t,h⟩ : Carrier X A) + beta * r)
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        rcases z with ⟨t', h'⟩
        exact ih t' h'


/-- Every coordinate marginal of a homogeneous trajectory started at a Dirac
history is the corresponding iterate kernel. -/
theorem homTrajMeasure_dirac_coordinate_eq_iterateKernel
    (Q : Kernel (Carrier X A) (Carrier X A)) [IsMarkovKernel Q]
    (z : Carrier X A) :
    ∀ n : ℕ,
      (homTrajMeasure (Measure.dirac z) Q).map
          (fun omega : ℕ → Carrier X A => omega n) =
        iterateKernel Q n z := by
  intro n
  induction n with
  | zero =>
      rw [homTrajMeasure_time_zero_general, iterateKernel_zero, Kernel.id_apply]
  | succ n ih =>
      rw [homTrajMeasure_time_succ_general]
      rw [ih]
      rw [iterateKernel_succ]
      rfl


/-- Exact coordinate target probability of the absorbed physical causal path law
is the corresponding `n`-step target probability of the homogeneous
complete-history kernel. -/
theorem causalRepairPathLaw_targetProbability_eq_carrier
    (P : X → A → PMF X) (K : Set X) (x : X)
    (pi : AdmissibleCausalRepairPolicy X A) (n : ℕ) :
    (causalRepairPathLaw (absorbedRepairPMF P K) x pi).real
        {omega | omega n ∈ K} =
      carrierTargetProbability
        (historyKernel (pmfControlledKernel (absorbedRepairPMF P K)) pi.policy)
        K (Carrier.singleton (A := A) x) n := by
  letI : ∀ m, IsMarkovKernel (pi.policy m) := pi.markov
  let Q := historyKernel (pmfControlledKernel (absorbedRepairPMF P K)) pi.policy
  have hK : MeasurableSet K := (Set.toFinite K).measurableSet
  have hEvent : MeasurableSet {omega : ℕ → X | omega n ∈ K} :=
    hK.preimage (measurable_pi_apply n)
  have hCarrier : MeasurableSet (historyRepairTarget (A := A) K) :=
    measurableSet_historyRepairTarget (A := A) K
  unfold causalRepairPathLaw reflexivePathLaw
  rw [measureReal_def, Measure.map_apply measurable_statePathReadout hEvent]
  change
    ((historyPathLaw
        (Measure.dirac x) (pmfControlledKernel (absorbedRepairPMF P K)) pi.policy)
      {omega | Carrier.current (omega n) ∈ K}).toReal = _
  rw [historyPathLaw_dirac_eq_homTrajMeasure
    (pmfControlledKernel (absorbedRepairPMF P K)) pi.policy x]
  have hcoord := homTrajMeasure_dirac_coordinate_eq_iterateKernel Q
    (Carrier.singleton (A := A) x) n
  have hmap :
      (homTrajMeasure (Measure.dirac (Carrier.singleton (A := A) x)) Q)
          {omega | Carrier.current (omega n) ∈ K} =
        (iterateKernel Q n (Carrier.singleton (A := A) x))
          (historyRepairTarget (A := A) K) := by
    have hm := congrArg
      (fun mu : Measure (Carrier X A) =>
        mu (historyRepairTarget (A := A) K)) hcoord
    rw [Measure.map_apply (measurable_pi_apply n) hCarrier] at hm
    exact hm
  rw [hmap]
  rfl

/-- Exact finite normalized discounted target occupation, written directly in
terms of coordinate-event probabilities of the absorbed physical
Ionescu--Tulcea path law. -/
noncomputable def causalNormalizedOccupationPartial
    (P : X → A → PMF X) (K : Set X) (x : X)
    (pi : AdmissibleCausalRepairPolicy X A)
    (beta : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N,
    beta ^ n * (1 - beta) *
      (causalRepairPathLaw (absorbedRepairPMF P K) x pi).real
        {omega | omega n ∈ K}

/-- Pathwise finite normalized target occupation. -/
noncomputable def pathNormalizedOccupationPartial
    (K : Set X) (beta : ℝ) (N : ℕ) (omega : ℕ → X) : ℝ :=
  ∑ n ∈ Finset.range N,
    ({omega' : ℕ → X | omega' n ∈ K}).indicator
      (fun _ => beta ^ n * (1 - beta)) omega

/-- The finite coordinate-probability formula is literally the Bochner
expectation of the pathwise normalized target occupation under the exact
absorbed physical causal path law. -/
theorem causalNormalizedOccupationPartial_eq_integral
    (P : X → A → PMF X) (K : Set X) (x : X)
    (pi : AdmissibleCausalRepairPolicy X A)
    (beta : ℝ) (N : ℕ) :
    causalNormalizedOccupationPartial P K x pi beta N =
      ∫ omega, pathNormalizedOccupationPartial K beta N omega
        ∂causalRepairPathLaw (absorbedRepairPMF P K) x pi := by
  let mu := causalRepairPathLaw (absorbedRepairPMF P K) x pi
  letI : IsProbabilityMeasure mu := by
    dsimp [mu, causalRepairPathLaw]
    infer_instance
  have hK : MeasurableSet K := (Set.toFinite K).measurableSet
  have hE (n : ℕ) : MeasurableSet {omega : ℕ → X | omega n ∈ K} :=
    hK.preimage (measurable_pi_apply n)
  have hint : ∀ n ∈ Finset.range N,
      Integrable
        (({omega : ℕ → X | omega n ∈ K}).indicator
          (fun _ => beta ^ n * (1 - beta))) mu := by
    intro n hn
    exact (integrable_const (beta ^ n * (1 - beta))).indicator (hE n)
  unfold causalNormalizedOccupationPartial pathNormalizedOccupationPartial
  change
    (∑ n ∈ Finset.range N,
      beta ^ n * (1 - beta) * mu.real {omega | omega n ∈ K}) =
      ∫ omega,
        (∑ n ∈ Finset.range N,
          ({omega' : ℕ → X | omega' n ∈ K}).indicator
            (fun _ => beta ^ n * (1 - beta)) omega) ∂mu
  rw [MeasureTheory.integral_finsetSum _ hint]
  apply Finset.sum_congr rfl
  intro n hn
  rw [MeasureTheory.integral_indicator_const _ (hE n)]
  simp [smul_eq_mul, mul_comm]

/-- **GCR2 finite exact path-law bridge.**  The nested causal discounted value
at a deterministic initial state equals the finite normalized target occupation
of the exact absorbed physical Ionescu--Tulcea law. -/
theorem truncatedValue_eq_causalNormalizedOccupationPartial
    (P : X → A → PMF X) (K : Set X) (x : X)
    (pi : AdmissibleCausalRepairPolicy X A)
    (beta : ℝ) (hbeta0 : 0 < beta) (hbeta1 : beta < 1)
    (N : ℕ) :
    (causalNormalizedRepairModel P K beta hbeta0.le hbeta1).truncatedValue
        pi.policy N 0 (initialHistory (A := A) x) =
      causalNormalizedOccupationPartial P K x pi beta N := by
  letI : ∀ m, IsMarkovKernel (pi.policy m) := pi.markov
  rw [truncatedValue_eq_carrierNormalizedOccupationPartial
    P K beta hbeta0 hbeta1 pi.policy N 0 (initialHistory (A := A) x)]
  unfold carrierNormalizedOccupationPartial causalNormalizedOccupationPartial
  apply Finset.sum_congr rfl
  intro n hn
  rw [causalRepairPathLaw_targetProbability_eq_carrier P K x pi n]
  rfl

/-- Exact-path-law normalized discounted repair surrogate: the limit of finite
normalized occupations of the absorbed physical causal path law. -/
noncomputable def causalNormalizedOccupation
    (P : X → A → PMF X) (K : Set X) (x : X)
    (pi : AdmissibleCausalRepairPolicy X A)
    (beta : ℝ) : ℝ :=
  Filter.limUnder Filter.atTop (fun N =>
    causalNormalizedOccupationPartial P K x pi beta N)

/-- `infiniteValue` packaged with the Markov witness already carried by an
`AdmissibleCausalRepairPolicy`. -/
noncomputable def admissibleCausalNormalizedInfiniteValue
    (P : X → A → PMF X) (K : Set X) (x : X)
    (pi : AdmissibleCausalRepairPolicy X A)
    (beta : ℝ) (hbeta0 : 0 < beta) (hbeta1 : beta < 1) : ℝ := by
  letI : ∀ m, IsMarkovKernel (pi.policy m) := pi.markov
  exact (causalNormalizedRepairModel P K beta hbeta0.le hbeta1).infiniteValue
    pi.policy 0 (initialHistory (A := A) x)

/-- **GCR2 infinite exact path-law bridge.**  The complete-history discounted
value is exactly the exact-path-law normalized target-occupation limit.  This is
still a fixed-`beta` identity, not an undiscounted reachability theorem. -/
theorem admissibleCausalNormalizedInfiniteValue_eq_occupation
    (P : X → A → PMF X) (K : Set X) (x : X)
    (pi : AdmissibleCausalRepairPolicy X A)
    (beta : ℝ) (hbeta0 : 0 < beta) (hbeta1 : beta < 1) :
    admissibleCausalNormalizedInfiniteValue P K x pi beta hbeta0 hbeta1 =
      causalNormalizedOccupation P K x pi beta := by
  letI : ∀ m, IsMarkovKernel (pi.policy m) := pi.markov
  unfold admissibleCausalNormalizedInfiniteValue
    UEOT.V3.CompactCausalOptimalityCore.Model.infiniteValue
    causalNormalizedOccupation
  apply congrArg (Filter.limUnder Filter.atTop)
  funext N
  exact truncatedValue_eq_causalNormalizedOccupationPartial
    P K x pi beta hbeta0 hbeta1 N

/-- The finite exact path-law occupations converge to the canonical GCR2
surrogate.  Thus `causalNormalizedOccupation` is not an arbitrary `limUnder`
choice: it is the actual limit inherited from the already-proved discounted
value Cauchy theorem. -/
theorem causalNormalizedOccupationPartial_tendsto
    (P : X → A → PMF X) (K : Set X) (x : X)
    (pi : AdmissibleCausalRepairPolicy X A)
    (beta : ℝ) (hbeta0 : 0 < beta) (hbeta1 : beta < 1) :
    Filter.Tendsto
      (fun N => causalNormalizedOccupationPartial P K x pi beta N)
      Filter.atTop (nhds (causalNormalizedOccupation P K x pi beta)) := by
  letI : ∀ m, IsMarkovKernel (pi.policy m) := pi.markov
  have ht :=
    UEOT.V3.CompactCausalOptimalityCore.Model.truncatedValue_tendsto_infiniteValue
      (causalNormalizedRepairModel P K beta hbeta0.le hbeta1)
      pi.policy 0 (initialHistory (A := A) x)
  have hfinite :
      (fun N =>
        (causalNormalizedRepairModel P K beta hbeta0.le hbeta1).truncatedValue
          pi.policy N 0 (initialHistory (A := A) x)) =
        (fun N => causalNormalizedOccupationPartial P K x pi beta N) := by
    funext N
    exact truncatedValue_eq_causalNormalizedOccupationPartial
      P K x pi beta hbeta0 hbeta1 N
  rw [hfinite] at ht
  have hinf := admissibleCausalNormalizedInfiniteValue_eq_occupation
    P K x pi beta hbeta0 hbeta1
  have hlim :
      (causalNormalizedRepairModel P K beta hbeta0.le hbeta1).infiniteValue
          pi.policy 0 (initialHistory (A := A) x) =
        causalNormalizedOccupation P K x pi beta := by
    simpa [admissibleCausalNormalizedInfiniteValue] using hinf
  rw [hlim] at ht
  exact ht

end
end UEOT.V3.Compression.Objecthood
