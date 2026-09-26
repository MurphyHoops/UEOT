/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
Modified for UEOT Core v3 integration in 2026: module import paths only.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Measure-theoretic Crooks–Jarzynski infrastructure

This module contains the state-space-independent core of the development. A
Crooks relation is expressed as an equality of measures on an arbitrary
measurable trajectory space. Evaluating that equality on the whole space gives
the Jarzynski equality as a Lebesgue integral. Pushing the equality through a
measurable observable gives the corresponding fluctuation relation for its
probability law.

For one Markov step, the module derives the Crooks relation from two
measure-theoretic hypotheses: equilibrium reweighting under the quench and local
detailed balance as an equality of composition-product measures. Both results
hold on arbitrary measurable state spaces.

The module also adapts an ordinary time-inhomogeneous family of Mathlib Markov
kernels `K t : Kernel Ω Ω` to the history-dependent kernels expected by
Mathlib's Ionescu–Tulcea construction. Thus `trajectoryMeasure μ₀ K` is the law
of the full trajectory on `ℕ → Ω` for an arbitrary measurable state space.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace CrooksJarzynski

universe u

namespace MeasureProtocol

variable {Γ : Type u} [MeasurableSpace Γ]

/-- A division-free Crooks relation on an arbitrary measurable trajectory
space. `workWeight` is the exponential work factor and `freeEnergyWeight` is
the corresponding equilibrium factor. -/
def CrooksRelation (forward reverse : Measure Γ)
    (workWeight : Γ → ℝ≥0∞) (freeEnergyWeight : ℝ≥0∞) : Prop :=
  forward.withDensity workWeight = freeEnergyWeight • reverse

/-- Mapping a measure by a measurable observable commutes with a density that
depends only on the observable. -/
theorem map_withDensity
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (observable : α → β) (q : β → ℝ≥0∞)
    (hObservable : Measurable observable) (hq : Measurable q) :
    (μ.map observable).withDensity q =
      (μ.withDensity (q ∘ observable)).map observable := by
  ext s hs
  rw [withDensity_apply _ hs, setLIntegral_map hs hq hObservable,
    Measure.map_apply hObservable hs,
    withDensity_apply _ (hObservable hs)]
  rfl

/-- A Crooks relation descends along every measurable observable. This is the
measure-theoretic coarse-graining step used to obtain work-distribution
fluctuation relations without assuming densities or atoms. -/
theorem CrooksRelation.map
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (forward reverse : Measure α) (observable : α → β)
    (q : β → ℝ≥0∞) (freeEnergyWeight : ℝ≥0∞)
    (hObservable : Measurable observable) (hq : Measurable q)
    (h : CrooksRelation forward reverse (q ∘ observable) freeEnergyWeight) :
    CrooksRelation (forward.map observable) (reverse.map observable)
      q freeEnergyWeight := by
  unfold CrooksRelation at h ⊢
  rw [map_withDensity forward observable q hObservable hq, h,
    Measure.map_smul]

/-- The measure-theoretic Jarzynski equality follows by evaluating the Crooks
measure identity on the whole trajectory space. -/
theorem jarzynski_lintegral
    (forward reverse : Measure Γ) (workWeight : Γ → ℝ≥0∞)
    (freeEnergyWeight : ℝ≥0∞) [IsProbabilityMeasure reverse]
    (h : CrooksRelation forward reverse workWeight freeEnergyWeight) :
    ∫⁻ γ, workWeight γ ∂forward = freeEnergyWeight := by
  have h_univ := congrArg (fun μ : Measure Γ => μ Set.univ) h
  simpa [CrooksRelation, withDensity_apply] using h_univ

/-- The real-valued integral form of `jarzynski_lintegral`.  Note that the
integrand is the exponential work weight `exp (-β W)` and the right-hand side
is the exponential free-energy weight `exp (-β ΔF)`, not the work `W` or the
free-energy difference `ΔF` themselves; the forward measure is not assumed to
be normalized. -/
theorem jarzynski_toReal_integral
    (forward reverse : Measure Γ) (workWeight : Γ → ℝ≥0∞)
    (freeEnergyWeight : ℝ≥0∞) [IsProbabilityMeasure reverse]
    (hwork : Measurable workWeight) (hfreeEnergy : freeEnergyWeight ≠ ∞)
    (h : CrooksRelation forward reverse workWeight freeEnergyWeight) :
    ∫ γ, (workWeight γ).toReal ∂forward = freeEnergyWeight.toReal := by
  have hjarzynski :=
    jarzynski_lintegral forward reverse workWeight freeEnergyWeight h
  rw [integral_toReal hwork.aemeasurable
    (ae_lt_top hwork (hjarzynski.trans_ne hfreeEnergy))]
  exact congrArg ENNReal.toReal hjarzynski

/-- The physical exponential form of `jarzynski_lintegral`. -/
theorem jarzynski_exponential
    (forward reverse : Measure Γ) (β ΔF : ℝ) (work : Γ → ℝ)
    [IsProbabilityMeasure reverse]
    (h : CrooksRelation forward reverse
      (fun γ => ENNReal.ofReal (Real.exp (-β * work γ)))
      (ENNReal.ofReal (Real.exp (-β * ΔF)))) :
    ∫⁻ γ, ENNReal.ofReal (Real.exp (-β * work γ)) ∂forward =
      ENNReal.ofReal (Real.exp (-β * ΔF)) :=
  jarzynski_lintegral forward reverse _ _ h

/-- The usual real-valued expectation form of the Jarzynski equality. -/
theorem jarzynski_integral
    (forward reverse : Measure Γ) (β ΔF : ℝ) (work : Γ → ℝ)
    [IsProbabilityMeasure reverse]
    (hwork : Measurable work)
    (h : CrooksRelation forward reverse
      (fun γ => ENNReal.ofReal (Real.exp (-β * work γ)))
      (ENNReal.ofReal (Real.exp (-β * ΔF)))) :
    ∫ γ, Real.exp (-β * work γ) ∂forward = Real.exp (-β * ΔF) := by
  have hmeas : AEStronglyMeasurable
      (fun γ => Real.exp (-β * work γ)) forward :=
    (by fun_prop : Measurable (fun γ => Real.exp (-β * work γ))).aestronglyMeasurable
  calc
    ∫ γ, Real.exp (-β * work γ) ∂forward =
        ENNReal.toReal
          (∫⁻ γ, ENNReal.ofReal (Real.exp (-β * work γ)) ∂forward) :=
      integral_eq_lintegral_of_nonneg_ae
        (ae_of_all _ fun γ => (Real.exp_pos (-β * work γ)).le) hmeas
    _ = ENNReal.toReal (ENNReal.ofReal (Real.exp (-β * ΔF))) :=
      congrArg ENNReal.toReal
        (jarzynski_exponential forward reverse β ΔF work h)
    _ = Real.exp (-β * ΔF) :=
      ENNReal.toReal_ofReal (Real.exp_pos (-β * ΔF)).le

/-- The Crooks relation for the pushforward law of a real-valued work
observable. -/
theorem work_distribution_crooks
    (forward reverse : Measure Γ) (β ΔF : ℝ) (work : Γ → ℝ)
    (hwork : Measurable work)
    (h : CrooksRelation forward reverse
      (fun γ => ENNReal.ofReal (Real.exp (-β * work γ)))
      (ENNReal.ofReal (Real.exp (-β * ΔF)))) :
    CrooksRelation (forward.map work) (reverse.map work)
      (fun w => ENNReal.ofReal (Real.exp (-β * w)))
      (ENNReal.ofReal (Real.exp (-β * ΔF))) := by
  have hq : Measurable
      (fun w : ℝ => ENNReal.ofReal (Real.exp (-β * w))) := by
    fun_prop
  apply CrooksRelation.map forward reverse work
    (fun w => ENNReal.ofReal (Real.exp (-β * w)))
    (ENNReal.ofReal (Real.exp (-β * ΔF))) hwork hq
  simpa [Function.comp_def] using h

namespace Markov

/-- Reweighting the first marginal before composing with a kernel is the same
as reweighting the resulting one-step path measure by the first coordinate. -/
theorem compProd_withDensity_fst
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (κ : Kernel α β) [SFinite μ] [IsSFiniteKernel κ]
    (q : α → ℝ≥0∞) (hq : Measurable q) :
    (μ ⊗ₘ κ).withDensity (fun p => q p.1) = μ.withDensity q ⊗ₘ κ := by
  ext s hs
  rw [withDensity_apply _ hs, Measure.compProd_apply hs]
  rw [← lintegral_indicator hs]
  have hqfst : Measurable (fun p : α × β => q p.1) :=
    hq.comp measurable_fst
  rw [Measure.lintegral_compProd (hqfst.indicator hs)]
  rw [lintegral_withDensity_eq_lintegral_mul μ hq
    (Kernel.measurable_kernel_prodMk_left hs)]
  apply lintegral_congr
  intro a
  simp only [Pi.mul_apply]
  have hsection : MeasurableSet (Prod.mk a ⁻¹' s) :=
    measurable_prodMk_left hs
  have hindicator :
      (fun b => s.indicator (fun p => q p.1) (a, b)) =
        (Prod.mk a ⁻¹' s).indicator (fun _ => q a) := by
    funext b
    rfl
  rw [hindicator, lintegral_indicator hsection]
  simp [MeasureTheory.lintegral_const]

variable {Ω : Type u} [MeasurableSpace Ω]

/-- A one-step Crooks relation on an arbitrary measurable state space. The
first hypothesis is the Gibbs reweighting identity for the quench. The second
is local detailed balance, stated without point masses as equality between the
forward equilibrium step measure and the swapped reverse equilibrium step
measure. -/
theorem oneStep_crooks
    (initial final : Measure Ω) (forward reverse : Kernel Ω Ω)
    [IsProbabilityMeasure initial] [IsProbabilityMeasure final]
    [IsMarkovKernel forward] [IsMarkovKernel reverse]
    (workWeight : Ω → ℝ≥0∞) (freeEnergyWeight : ℝ≥0∞)
    (hwork : Measurable workWeight)
    (hreweight : initial.withDensity workWeight = freeEnergyWeight • final)
    (hbalance :
      final ⊗ₘ forward = (final ⊗ₘ reverse).map Prod.swap) :
    CrooksRelation (initial ⊗ₘ forward)
      ((final ⊗ₘ reverse).map Prod.swap)
      (fun p => workWeight p.1) freeEnergyWeight := by
  unfold CrooksRelation
  rw [compProd_withDensity_fst initial forward workWeight hwork, hreweight,
    Measure.compProd_smul_left, hbalance]

/-- The one-step Jarzynski equality on an arbitrary measurable state space. -/
theorem oneStep_jarzynski
    (initial final : Measure Ω) (forward reverse : Kernel Ω Ω)
    [IsProbabilityMeasure initial] [IsProbabilityMeasure final]
    [IsMarkovKernel forward] [IsMarkovKernel reverse]
    (workWeight : Ω → ℝ≥0∞) (freeEnergyWeight : ℝ≥0∞)
    (hwork : Measurable workWeight)
    (hreweight : initial.withDensity workWeight = freeEnergyWeight • final)
    (hbalance :
      final ⊗ₘ forward = (final ⊗ₘ reverse).map Prod.swap) :
    ∫⁻ p, workWeight p.1 ∂(initial ⊗ₘ forward) = freeEnergyWeight := by
  letI : IsProbabilityMeasure ((final ⊗ₘ reverse).map Prod.swap) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  exact jarzynski_lintegral _ _ _ _
    (oneStep_crooks initial final forward reverse workWeight freeEnergyWeight
      hwork hreweight hbalance)

/-- The last state in a history indexed by `Finset.Iic t`. -/
def historyLast (t : ℕ) (x : (i : Finset.Iic t) → Ω) : Ω :=
  x ⟨t, Finset.mem_Iic.mpr le_rfl⟩

@[fun_prop]
theorem measurable_historyLast (t : ℕ) :
    Measurable (historyLast (Ω := Ω) t) :=
  measurable_pi_apply _

/-- Regard an ordinary Markov kernel as a history-dependent kernel by reading
only the most recent state. This is the adapter required by Ionescu–Tulcea. -/
def historyKernel (K : ℕ → Kernel Ω Ω) (t : ℕ) :
    Kernel ((i : Finset.Iic t) → Ω) Ω :=
  (K t).comap (historyLast t) (measurable_historyLast t)

instance instIsMarkovKernelHistoryKernel
    (K : ℕ → Kernel Ω Ω) [∀ t, IsMarkovKernel (K t)] (t : ℕ) :
    IsMarkovKernel (historyKernel K t) := by
  unfold historyKernel
  infer_instance

/-- The Ionescu–Tulcea trajectory law of a time-inhomogeneous Markov chain on
an arbitrary measurable state space. -/
noncomputable def trajectoryMeasure
    (μ₀ : Measure Ω) (K : ℕ → Kernel Ω Ω)
    [∀ t, IsMarkovKernel (K t)] : Measure (ℕ → Ω) :=
  Kernel.trajMeasure μ₀ (historyKernel K)

noncomputable instance instIsProbabilityMeasureTrajectoryMeasure
    (μ₀ : Measure Ω) (K : ℕ → Kernel Ω Ω)
    [IsProbabilityMeasure μ₀] [∀ t, IsMarkovKernel (K t)] :
    IsProbabilityMeasure (trajectoryMeasure μ₀ K) := by
  unfold trajectoryMeasure
  infer_instance

/-- Every finite prefix of `trajectoryMeasure` is extended by the prescribed
next-step Markov kernel. -/
theorem trajectoryMeasure_step
    (μ₀ : Measure Ω) (K : ℕ → Kernel Ω Ω)
    [IsProbabilityMeasure μ₀] [∀ t, IsMarkovKernel (K t)] (t : ℕ) :
    (trajectoryMeasure μ₀ K).map (Preorder.frestrictLe t) ⊗ₘ historyKernel K t =
      (trajectoryMeasure μ₀ K).map
        (fun x => (Preorder.frestrictLe t x, x (t + 1))) := by
  exact Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure

end Markov

end MeasureProtocol

end CrooksJarzynski
