/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
Modified for UEOT Core v3 integration in 2026: module import paths only.
-/
import UEOT.V3.ThirdParty.CrooksJarzynski.ContinuousTimeJumpHorizon
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Local balance for continuous-time jump path densities

This module turns local, factor-by-factor balance identities into the pathwise
Radon--Nikodym identity required by the continuous-time Crooks scaffold.  It
also instantiates holding and jump factors for a piecewise-constant-rate jump
model.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump

universe u

namespace JumpPath

variable {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}

/-- The reverse-experiment density after pulling it back to forward-oriented
coordinates.  Reverse holding factors are already indexed in forward time,
and reverse jump factors act from the next forward state back to the current
state. -/
noncomputable def alignedReverseDensity
    (finalWeight : Ω → ℝ≥0∞)
    (reverseHolding : Fin (n + 1) → Ω → NNReal → ℝ≥0∞)
    (reverseJump : Fin n → Ω → Ω → ℝ≥0∞)
    (γ : JumpPath Ω n) : ℝ≥0∞ :=
  finalWeight (γ.1 (Fin.last n)) *
      (∏ i : Fin n,
        reverseHolding i.castSucc (γ.1 i.castSucc) (γ.2 i.castSucc) *
          reverseJump i (γ.1 i.succ) (γ.1 i.castSucc)) *
    reverseHolding (Fin.last n) (γ.1 (Fin.last n)) (γ.2 (Fin.last n))

/-- A factorized path work weight, with endpoint, holding-interval, and jump
contributions. -/
noncomputable def factorizedWorkWeight
    (boundaryWork : Ω → Ω → ℝ≥0∞)
    (holdingWork : Fin (n + 1) → Ω → NNReal → ℝ≥0∞)
    (jumpWork : Fin n → Ω → Ω → ℝ≥0∞)
    (γ : JumpPath Ω n) : ℝ≥0∞ :=
  boundaryWork (γ.1 0) (γ.1 (Fin.last n)) *
      (∏ i : Fin n,
        holdingWork i.castSucc (γ.1 i.castSucc) (γ.2 i.castSucc) *
          jumpWork i (γ.1 i.castSucc) (γ.1 i.succ)) *
    holdingWork (Fin.last n) (γ.1 (Fin.last n)) (γ.2 (Fin.last n))

/-- The reverse density in the reverse experiment's own chronological
coordinates. -/
noncomputable def reverseExperimentDensity
    (finalWeight : Ω → ℝ≥0∞)
    (reverseHolding : Fin (n + 1) → Ω → NNReal → ℝ≥0∞)
    (reverseJump : Fin n → Ω → Ω → ℝ≥0∞) :
    JumpPath Ω n → ℝ≥0∞ :=
  alignedReverseDensity finalWeight reverseHolding reverseJump ∘ reverse

omit [MeasurableSpace Ω] in
/-- Pulling the reverse-experiment density back by reversal recovers the
forward-oriented reverse density. -/
@[simp]
theorem reverseExperimentDensity_reverse
    (finalWeight : Ω → ℝ≥0∞)
    (reverseHolding : Fin (n + 1) → Ω → NNReal → ℝ≥0∞)
    (reverseJump : Fin n → Ω → Ω → ℝ≥0∞)
    (γ : JumpPath Ω n) :
    reverseExperimentDensity finalWeight reverseHolding reverseJump (reverse γ) =
      alignedReverseDensity finalWeight reverseHolding reverseJump γ := by
  simp [reverseExperimentDensity]

omit [MeasurableSpace Ω] in
/-- Local endpoint, holding, and jump identities multiply into the complete
path-density identity.  This is the division-free local-detailed-balance step. -/
theorem density_mul_factorizedWorkWeight
    (initialWeight finalWeight : Ω → ℝ≥0∞)
    (forwardHolding reverseHolding holdingWork :
      Fin (n + 1) → Ω → NNReal → ℝ≥0∞)
    (forwardJump reverseJump jumpWork : Fin n → Ω → Ω → ℝ≥0∞)
    (boundaryWork : Ω → Ω → ℝ≥0∞)
    (freeEnergyWeight : ℝ≥0∞)
    (hboundary : ∀ x y,
      initialWeight x * boundaryWork x y =
        freeEnergyWeight * finalWeight y)
    (hholding : ∀ i x τ,
      forwardHolding i x τ * holdingWork i x τ =
        reverseHolding i x τ)
    (hjump : ∀ i x y,
      forwardJump i x y * jumpWork i x y =
        reverseJump i y x)
    (γ : JumpPath Ω n) :
    density initialWeight forwardHolding forwardJump γ *
        factorizedWorkWeight boundaryWork holdingWork jumpWork γ =
      freeEnergyWeight *
        alignedReverseDensity finalWeight reverseHolding reverseJump γ := by
  have hprod :
      (∏ i : Fin n,
        forwardHolding i.castSucc (γ.1 i.castSucc) (γ.2 i.castSucc) *
          forwardJump i (γ.1 i.castSucc) (γ.1 i.succ)) *
        (∏ i : Fin n,
          holdingWork i.castSucc (γ.1 i.castSucc) (γ.2 i.castSucc) *
            jumpWork i (γ.1 i.castSucc) (γ.1 i.succ)) =
      ∏ i : Fin n,
        reverseHolding i.castSucc (γ.1 i.castSucc) (γ.2 i.castSucc) *
          reverseJump i (γ.1 i.succ) (γ.1 i.castSucc) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    calc
      (forwardHolding i.castSucc (γ.1 i.castSucc) (γ.2 i.castSucc) *
          forwardJump i (γ.1 i.castSucc) (γ.1 i.succ)) *
          (holdingWork i.castSucc (γ.1 i.castSucc) (γ.2 i.castSucc) *
            jumpWork i (γ.1 i.castSucc) (γ.1 i.succ)) =
        (forwardHolding i.castSucc (γ.1 i.castSucc) (γ.2 i.castSucc) *
          holdingWork i.castSucc (γ.1 i.castSucc) (γ.2 i.castSucc)) *
        (forwardJump i (γ.1 i.castSucc) (γ.1 i.succ) *
          jumpWork i (γ.1 i.castSucc) (γ.1 i.succ)) := by
            ac_rfl
      _ = reverseHolding i.castSucc (γ.1 i.castSucc) (γ.2 i.castSucc) *
          reverseJump i (γ.1 i.succ) (γ.1 i.castSucc) := by
            rw [hholding, hjump]
  unfold density factorizedWorkWeight alignedReverseDensity
  calc
    initialWeight (γ.1 0) *
          (∏ i : Fin n,
            forwardHolding i.castSucc (γ.1 i.castSucc) (γ.2 i.castSucc) *
              forwardJump i (γ.1 i.castSucc) (γ.1 i.succ)) *
        forwardHolding (Fin.last n) (γ.1 (Fin.last n)) (γ.2 (Fin.last n)) *
      (boundaryWork (γ.1 0) (γ.1 (Fin.last n)) *
          (∏ i : Fin n,
            holdingWork i.castSucc (γ.1 i.castSucc) (γ.2 i.castSucc) *
              jumpWork i (γ.1 i.castSucc) (γ.1 i.succ)) *
        holdingWork (Fin.last n) (γ.1 (Fin.last n)) (γ.2 (Fin.last n))) =
      (initialWeight (γ.1 0) *
          boundaryWork (γ.1 0) (γ.1 (Fin.last n))) *
        ((∏ i : Fin n,
            forwardHolding i.castSucc (γ.1 i.castSucc) (γ.2 i.castSucc) *
              forwardJump i (γ.1 i.castSucc) (γ.1 i.succ)) *
          (∏ i : Fin n,
            holdingWork i.castSucc (γ.1 i.castSucc) (γ.2 i.castSucc) *
              jumpWork i (γ.1 i.castSucc) (γ.1 i.succ))) *
        (forwardHolding (Fin.last n) (γ.1 (Fin.last n)) (γ.2 (Fin.last n)) *
          holdingWork (Fin.last n) (γ.1 (Fin.last n)) (γ.2 (Fin.last n))) := by
            ac_rfl
    _ = (freeEnergyWeight * finalWeight (γ.1 (Fin.last n))) *
        (∏ i : Fin n,
          reverseHolding i.castSucc (γ.1 i.castSucc) (γ.2 i.castSucc) *
            reverseJump i (γ.1 i.succ) (γ.1 i.castSucc)) *
        reverseHolding (Fin.last n) (γ.1 (Fin.last n)) (γ.2 (Fin.last n)) := by
      rw [hboundary, hprod, hholding]
    _ = freeEnergyWeight *
        (finalWeight (γ.1 (Fin.last n)) *
          (∏ i : Fin n,
            reverseHolding i.castSucc (γ.1 i.castSucc) (γ.2 i.castSucc) *
              reverseJump i (γ.1 i.succ) (γ.1 i.castSucc)) *
          reverseHolding (Fin.last n) (γ.1 (Fin.last n)) (γ.2 (Fin.last n))) := by
      ac_rfl

/-- Crooks' relation obtained from local factor balance. -/
theorem crooks_of_local_factor_balance
    (reference : Measure (JumpPath Ω n))
    (initialWeight finalWeight : Ω → ℝ≥0∞)
    (forwardHolding reverseHolding holdingWork :
      Fin (n + 1) → Ω → NNReal → ℝ≥0∞)
    (forwardJump reverseJump jumpWork : Fin n → Ω → Ω → ℝ≥0∞)
    (boundaryWork : Ω → Ω → ℝ≥0∞)
    (freeEnergyWeight : ℝ≥0∞)
    (hreference : reference.map reverse = reference)
    (hforward : Measurable (density initialWeight forwardHolding forwardJump))
    (halignedReverse :
      Measurable (alignedReverseDensity finalWeight reverseHolding reverseJump))
    (hwork :
      Measurable (factorizedWorkWeight boundaryWork holdingWork jumpWork))
    (hboundary : ∀ x y,
      initialWeight x * boundaryWork x y =
        freeEnergyWeight * finalWeight y)
    (hholding : ∀ i x τ,
      forwardHolding i x τ * holdingWork i x τ = reverseHolding i x τ)
    (hjump : ∀ i x y,
      forwardJump i x y * jumpWork i x y = reverseJump i y x) :
    CrooksRelation
      (pathMeasure reference
        (density initialWeight forwardHolding forwardJump))
      (timeReversedMeasure
        (pathMeasure reference
          (reverseExperimentDensity finalWeight reverseHolding reverseJump)))
      (factorizedWorkWeight boundaryWork holdingWork jumpWork)
      freeEnergyWeight := by
  apply crooks_of_density_identity reference
    (density initialWeight forwardHolding forwardJump)
    (reverseExperimentDensity finalWeight reverseHolding reverseJump)
    (factorizedWorkWeight boundaryWork holdingWork jumpWork)
    freeEnergyWeight hreference hforward
    (halignedReverse.comp measurable_reverse) hwork
  refine ae_of_all reference fun γ => ?_
  rw [reverseExperimentDensity_reverse]
  exact density_mul_factorizedWorkWeight initialWeight finalWeight
    forwardHolding reverseHolding holdingWork
    forwardJump reverseJump jumpWork boundaryWork freeEnergyWeight
    hboundary hholding hjump γ

/-- Exponential survival weight for a segment with a constant escape rate. -/
noncomputable def holdingWeightOfEscapeRate
    (escapeRate : Fin (n + 1) → Ω → NNReal)
    (i : Fin (n + 1)) (x : Ω) (τ : NNReal) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-((escapeRate i x : ℝ) * (τ : ℝ))))

/-- Jump-rate factor embedded in `ℝ≥0∞`. -/
def jumpWeightOfRate
    (jumpRate : Fin n → Ω → Ω → NNReal)
    (i : Fin n) (x y : Ω) : ℝ≥0∞ :=
  jumpRate i x y

/-- Fixed-jump-count likelihood for segmentwise constant escape and jump rates. -/
noncomputable def rateDensity
    (initialWeight : Ω → ℝ≥0∞)
    (escapeRate : Fin (n + 1) → Ω → NNReal)
    (jumpRate : Fin n → Ω → Ω → NNReal) : JumpPath Ω n → ℝ≥0∞ :=
  density initialWeight (holdingWeightOfEscapeRate escapeRate)
    (jumpWeightOfRate jumpRate)

/-- Reverse-rate likelihood pulled back to forward path coordinates. -/
noncomputable def alignedReverseRateDensity
    (finalWeight : Ω → ℝ≥0∞)
    (escapeRate : Fin (n + 1) → Ω → NNReal)
    (jumpRate : Fin n → Ω → Ω → NNReal) : JumpPath Ω n → ℝ≥0∞ :=
  alignedReverseDensity finalWeight (holdingWeightOfEscapeRate escapeRate)
    (jumpWeightOfRate jumpRate)

/-- Work factor for a rate model when waiting-time factors cancel. -/
noncomputable def rateWorkWeight
    (boundaryWork : Ω → Ω → ℝ≥0∞)
    (jumpWork : Fin n → Ω → Ω → ℝ≥0∞) : JumpPath Ω n → ℝ≥0∞ :=
  factorizedWorkWeight boundaryWork (fun _ _ _ => 1) jumpWork

omit [MeasurableSpace Ω] in
/-- Equal forward and time-reversal-aligned escape rates cancel all survival
factors.  Boundary reweighting and local jump balance then imply the complete
rate-density identity. -/
theorem rateDensity_mul_rateWorkWeight
    (initialWeight finalWeight : Ω → ℝ≥0∞)
    (forwardEscape reverseEscape : Fin (n + 1) → Ω → NNReal)
    (forwardJump reverseJump : Fin n → Ω → Ω → NNReal)
    (boundaryWork : Ω → Ω → ℝ≥0∞)
    (jumpWork : Fin n → Ω → Ω → ℝ≥0∞)
    (freeEnergyWeight : ℝ≥0∞)
    (hboundary : ∀ x y,
      initialWeight x * boundaryWork x y =
        freeEnergyWeight * finalWeight y)
    (hescape : ∀ i x, forwardEscape i x = reverseEscape i x)
    (hjump : ∀ i x y,
      jumpWeightOfRate forwardJump i x y * jumpWork i x y =
        jumpWeightOfRate reverseJump i y x)
    (γ : JumpPath Ω n) :
    rateDensity initialWeight forwardEscape forwardJump γ *
        rateWorkWeight boundaryWork jumpWork γ =
      freeEnergyWeight *
        alignedReverseRateDensity finalWeight reverseEscape reverseJump γ := by
  unfold rateDensity rateWorkWeight alignedReverseRateDensity
  apply density_mul_factorizedWorkWeight
    initialWeight finalWeight
    (holdingWeightOfEscapeRate forwardEscape)
    (holdingWeightOfEscapeRate reverseEscape)
    (fun _ _ _ => 1)
    (jumpWeightOfRate forwardJump)
    (jumpWeightOfRate reverseJump)
    jumpWork boundaryWork freeEnergyWeight hboundary
  · intro i x τ
    simp [holdingWeightOfEscapeRate, hescape i x]
  · exact hjump

end JumpPath
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
