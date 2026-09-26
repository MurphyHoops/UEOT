/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
Modified for UEOT Core v3 integration in 2026: module import paths only.
-/
import UEOT.V3.ThirdParty.CrooksJarzynski.MeasureProtocol
import Mathlib.Data.Fin.Rev
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Continuous-time jump-process Crooks infrastructure

This module isolates the measure-theoretic step needed to extend the existing
finite-horizon Crooks development to continuous-time processes.

A continuous-time path law is represented by a density with respect to a common
reference measure on path space. If the forward density, the reverse density
pulled back by time reversal, and the work factor satisfy the pointwise
Radon--Nikodym identity, then the abstract `MeasureProtocol.CrooksRelation`
follows. This is the part of a jump-process proof that is independent of the
specific construction of the continuous-time Markov law.

For Markov jump processes, a fixed-jump-count path is represented by its states
and holding times. The module defines measurable path reversal, a generic
factorized jump-path density, and Crooks/Jarzynski wrappers on that path space.
The remaining process-specific obligation is to prove the density identity from
escape-rate and local-detailed-balance hypotheses, and then to sum over the
number of jumps.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump

universe u

variable {Γ : Type u} [MeasurableSpace Γ]

/-- A path law described by a density with respect to a common reference
measure. This representation is convenient for both jump-process likelihoods
and Girsanov-type diffusion likelihoods. -/
noncomputable def pathMeasure
    (reference : Measure Γ) (density : Γ → ℝ≥0∞) : Measure Γ :=
  reference.withDensity density

/-- A common-reference-density identity implies the abstract Crooks relation.

The hypothesis is the division-free path-density form
`p_forward * workWeight = freeEnergyWeight * p_reverse`. -/
theorem crooks_of_reference_density
    (reference : Measure Γ)
    (forwardDensity reverseDensity workWeight : Γ → ℝ≥0∞)
    (freeEnergyWeight : ℝ≥0∞)
    (hforward : Measurable forwardDensity)
    (hreverse : Measurable reverseDensity)
    (hwork : Measurable workWeight)
    (hdensity : ∀ᵐ γ ∂reference,
      forwardDensity γ * workWeight γ =
        freeEnergyWeight * reverseDensity γ) :
    CrooksRelation
      (pathMeasure reference forwardDensity)
      (pathMeasure reference reverseDensity)
      workWeight freeEnergyWeight := by
  unfold CrooksRelation pathMeasure
  calc
    (reference.withDensity forwardDensity).withDensity workWeight =
        reference.withDensity (forwardDensity * workWeight) :=
      (MeasureTheory.withDensity_mul reference hforward hwork).symm
    _ = reference.withDensity
        (fun γ => freeEnergyWeight * reverseDensity γ) :=
      MeasureTheory.withDensity_congr_ae hdensity
    _ = reference.withDensity
        (reverseDensity * fun _ : Γ => freeEnergyWeight) := by
      apply MeasureTheory.withDensity_congr_ae
      filter_upwards with γ
      simp [mul_comm]
    _ = (reference.withDensity reverseDensity).withDensity
        (fun _ : Γ => freeEnergyWeight) :=
      MeasureTheory.withDensity_mul reference hreverse measurable_const
    _ = freeEnergyWeight • reference.withDensity reverseDensity := by
      simp

/-- Mapping a density-defined path law by a measurable involution amounts to
composing its density with that involution, provided the reference measure is
invariant. -/
theorem map_pathMeasure_involution
    (reference : Measure Γ) (timeReverse : Γ → Γ)
    (density : Γ → ℝ≥0∞)
    (hmeasReverse : Measurable timeReverse)
    (hinvolution : Function.Involutive timeReverse)
    (hreference : reference.map timeReverse = reference)
    (hdensity : Measurable density) :
    (pathMeasure reference density).map timeReverse =
      pathMeasure reference (density ∘ timeReverse) := by
  unfold pathMeasure
  have hmap := CrooksJarzynski.MeasureProtocol.map_withDensity
    reference timeReverse (density ∘ timeReverse)
    hmeasReverse (hdensity.comp hmeasReverse)
  rw [hreference] at hmap
  have hcomp : (density ∘ timeReverse) ∘ timeReverse = density := by
    funext γ
    simpa [Function.comp_def] using congrArg density (hinvolution γ)
  rw [hcomp] at hmap
  exact hmap.symm

/-- A path-density identity against the time-reversed reverse experiment implies
Crooks' relation between the forward law and the time reversal of the reverse
law. -/
theorem crooks_of_reversal_density
    (reference : Measure Γ) (timeReverse : Γ → Γ)
    (forwardDensity reverseDensity workWeight : Γ → ℝ≥0∞)
    (freeEnergyWeight : ℝ≥0∞)
    (hmeasReverse : Measurable timeReverse)
    (hinvolution : Function.Involutive timeReverse)
    (hreference : reference.map timeReverse = reference)
    (hforward : Measurable forwardDensity)
    (hreverse : Measurable reverseDensity)
    (hwork : Measurable workWeight)
    (hdensity : ∀ᵐ γ ∂reference,
      forwardDensity γ * workWeight γ =
        freeEnergyWeight * reverseDensity (timeReverse γ)) :
    CrooksRelation
      (pathMeasure reference forwardDensity)
      ((pathMeasure reference reverseDensity).map timeReverse)
      workWeight freeEnergyWeight := by
  rw [map_pathMeasure_involution reference timeReverse reverseDensity
    hmeasReverse hinvolution hreference hreverse]
  exact crooks_of_reference_density reference forwardDensity
    (reverseDensity ∘ timeReverse) workWeight freeEnergyWeight
    hforward (hreverse.comp hmeasReverse) hwork
    (by simpa [Function.comp_def] using hdensity)

/-- A fixed-jump-count continuous-time path. `states i` is the state occupied
for the holding interval `holdingTimes i`. For `n` jumps there are `n + 1`
states and holding intervals, including the terminal no-jump interval. -/
abbrev JumpPath (Ω : Type u) (n : ℕ) :=
  (Fin (n + 1) → Ω) × (Fin (n + 1) → NNReal)

/-- The canonical product σ-algebra on fixed-jump-count paths.

Mathlib's measurable structure on a function space expects a function-valued
family of measurable structures. For the constant state and holding-time
families, these instances are supplied explicitly here. -/
@[instance_reducible]
instance instMeasurableSpaceJumpPath
    (Ω : Type u) [MeasurableSpace Ω] (n : ℕ) :
    MeasurableSpace (JumpPath Ω n) := by
  letI : (i : Fin (n + 1)) → MeasurableSpace Ω :=
    fun _ => inferInstance
  letI : (i : Fin (n + 1)) → MeasurableSpace NNReal :=
    fun _ => inferInstance
  exact Prod.instMeasurableSpace

namespace JumpPath

variable {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}

/-- Reverse both the state sequence and the holding-time sequence. -/
def reverse (γ : JumpPath Ω n) : JumpPath Ω n :=
  (fun i => γ.1 i.rev, fun i => γ.2 i.rev)

@[fun_prop]
theorem measurable_reverse :
    Measurable (reverse (Ω := Ω) (n := n)) := by
  apply Measurable.prodMk
  · rw [measurable_pi_iff]
    intro i
    exact (measurable_pi_apply i.rev).comp measurable_fst
  · rw [measurable_pi_iff]
    intro i
    exact (measurable_pi_apply i.rev).comp measurable_snd

omit [MeasurableSpace Ω] in
@[simp]
theorem reverse_reverse (γ : JumpPath Ω n) :
    reverse (reverse γ) = γ := by
  rcases γ with ⟨states, holdingTimes⟩
  apply Prod.ext
  · funext i
    simp [reverse]
  · funext i
    simp [reverse]

omit [MeasurableSpace Ω] in
/-- Path reversal is an involution. -/
theorem reverse_involutive :
    Function.Involutive (reverse (Ω := Ω) (n := n)) :=
  fun γ => reverse_reverse γ

/-- A generic factorized density for a jump path with exactly `n` jumps.

`holdingWeight` is indexed by the jump sector `Fin (n + 1)` and sees only the
state and the holding duration of its own segment, so it encodes a survival
factor `exp (-λᵢ(x) τᵢ)` whose rate is constant along that segment;
`jumpWeight` likewise encodes a segment-indexed jump rate. Calendar-time
dependence, where the hazard on a segment is an integral `∫ λ_s ds` over the
absolute times swept by that segment, is outside this parametrization: no
argument carries the absolute start time. This definition deliberately
separates the path-space measure theory from the later choice of
piecewise-constant rate factors. -/
noncomputable def density
    (initialWeight : Ω → ℝ≥0∞)
    (holdingWeight : Fin (n + 1) → Ω → NNReal → ℝ≥0∞)
    (jumpWeight : Fin n → Ω → Ω → ℝ≥0∞)
    (γ : JumpPath Ω n) : ℝ≥0∞ :=
  initialWeight (γ.1 0) *
      (∏ i : Fin n,
        holdingWeight i.castSucc (γ.1 i.castSucc) (γ.2 i.castSucc) *
          jumpWeight i (γ.1 i.castSucc) (γ.1 i.succ)) *
    holdingWeight (Fin.last n) (γ.1 (Fin.last n)) (γ.2 (Fin.last n))

/-- Time-reverse a measure on fixed-jump-count paths. -/
noncomputable def timeReversedMeasure
    (μ : Measure (JumpPath Ω n)) : Measure (JumpPath Ω n) :=
  μ.map reverse

/-- Fixed-jump-count Crooks relation from a path-density identity. -/
theorem crooks_of_density_identity
    (reference : Measure (JumpPath Ω n))
    (forwardDensity reverseDensity workWeight : JumpPath Ω n → ℝ≥0∞)
    (freeEnergyWeight : ℝ≥0∞)
    (hreference : reference.map reverse = reference)
    (hforward : Measurable forwardDensity)
    (hreverse : Measurable reverseDensity)
    (hwork : Measurable workWeight)
    (hdensity : ∀ᵐ γ ∂reference,
      forwardDensity γ * workWeight γ =
        freeEnergyWeight * reverseDensity (reverse γ)) :
    CrooksRelation
      (pathMeasure reference forwardDensity)
      (timeReversedMeasure (pathMeasure reference reverseDensity))
      workWeight freeEnergyWeight := by
  unfold timeReversedMeasure
  exact crooks_of_reversal_density reference reverse
    forwardDensity reverseDensity workWeight freeEnergyWeight
    measurable_reverse reverse_involutive hreference
    hforward hreverse hwork hdensity

/-- The fixed-jump-count Jarzynski equality obtained from the density-level
Crooks identity. -/
theorem jarzynski_of_density_identity
    (reference : Measure (JumpPath Ω n))
    (forwardDensity reverseDensity workWeight : JumpPath Ω n → ℝ≥0∞)
    (freeEnergyWeight : ℝ≥0∞)
    [IsProbabilityMeasure (pathMeasure reference reverseDensity)]
    (hreference : reference.map reverse = reference)
    (hforward : Measurable forwardDensity)
    (hreverse : Measurable reverseDensity)
    (hwork : Measurable workWeight)
    (hdensity : ∀ᵐ γ ∂reference,
      forwardDensity γ * workWeight γ =
        freeEnergyWeight * reverseDensity (reverse γ)) :
    ∫⁻ γ, workWeight γ ∂(pathMeasure reference forwardDensity) =
      freeEnergyWeight := by
  letI : IsProbabilityMeasure
      (timeReversedMeasure (pathMeasure reference reverseDensity)) := by
    unfold timeReversedMeasure
    exact Measure.isProbabilityMeasure_map measurable_reverse.aemeasurable
  exact jarzynski_lintegral _ _ _ _
    (crooks_of_density_identity reference forwardDensity reverseDensity
      workWeight freeEnergyWeight hreference hforward hreverse hwork hdensity)

/-- Equality with the time-reversed law is the zero-work, zero-free-energy
special case of the fixed-jump-count Crooks relation. -/
theorem eq_timeReversedMeasure_of_density_identity
    (reference : Measure (JumpPath Ω n))
    (forwardDensity reverseDensity : JumpPath Ω n → ℝ≥0∞)
    (hreference : reference.map reverse = reference)
    (hforward : Measurable forwardDensity)
    (hreverse : Measurable reverseDensity)
    (hdensity : ∀ᵐ γ ∂reference,
      forwardDensity γ = reverseDensity (reverse γ)) :
    pathMeasure reference forwardDensity =
      timeReversedMeasure (pathMeasure reference reverseDensity) := by
  have hcrooks := crooks_of_density_identity reference
    forwardDensity reverseDensity (fun _ => 1) 1
    hreference hforward hreverse measurable_const
    (by simpa using hdensity)
  simpa [CrooksRelation] using hcrooks

end JumpPath
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
