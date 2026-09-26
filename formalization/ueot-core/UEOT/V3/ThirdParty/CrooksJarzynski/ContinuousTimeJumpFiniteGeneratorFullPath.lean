/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
Modified for UEOT Core v3 integration in 2026: module import paths only.
-/
import UEOT.V3.ThirdParty.CrooksJarzynski.ContinuousTimeJumpFiniteGeneratorPathLaw
import UEOT.V3.ThirdParty.CrooksJarzynski.ContinuousTimeJumpFull

/-!
# The fixed-initial full path law of a general finite jump generator

The sector masses of a `FiniteJumpGenerator` sum to one, so the fixed-initial
sector laws assemble into an honest probability measure on the disjoint union of
all jump-count sectors.  This module builds that measure and identifies the
pushforward of its actual terminal coordinate.

The point of doing this at the measure level is fidelity: the transition mass
was defined as a sector sum, which is convenient for the arithmetic but is not
by itself a statement about the constructed path law.  Everything downstream is
phrased against `pathLawFrom`, so the sector sum only ever appears as an
intermediate evaluation.
-/

open MeasureTheory
open scoped ENNReal BigOperators unitInterval

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump

universe u

namespace FullPath

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The terminal state recorded by a complete finite-jump path, for an arbitrary
state space. -/
def terminalState : FullPath Ω → Ω
  | ⟨n, γ⟩ => γ.1 (Fin.last n)

@[fun_prop]
theorem measurable_terminalState :
    Measurable (terminalState : FullPath Ω → Ω) := by
  intro s hs
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro n
  change MeasurableSet ((fun γ : JumpPath Ω n => γ.1 (Fin.last n)) ⁻¹' s)
  exact ((measurable_pi_apply (Fin.last n)).comp measurable_fst) hs

end FullPath

namespace FiniteJumpGenerator

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-! ### Evaluating the sector law -/

/-- Integrating a function of the terminal state against the fixed-initial
sector law reduces to the finite sum over state sequences.  Taking `q = 1`
recovers the sector mass and taking `q` an indicator recovers the terminal
sector mass, so this is the single bridge between the measure-level law and the
arithmetic developed on state sequences. -/
theorem lintegral_terminal_sectorLawFrom
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x : Ω) (n : ℕ)
    (q : Ω → ℝ≥0∞) (hq : ∀ z, q z ≠ ∞) :
    ∫⁻ γ, q (γ.1 (Fin.last n)) ∂(G.sectorLawFrom T x n) =
      ∑ states : Fin (n + 1) → Ω,
        q (states (Fin.last n)) *
          (fixedInitialWeight x (states 0) * G.sequenceMass T states) := by
  have hdensity := G.measurable_rateDensity (fixedInitialWeight x) n
  have hterm : Measurable fun γ : JumpPath Ω n => q (γ.1 (Fin.last n)) :=
    (Measurable.of_discrete (f := q)).comp
      ((measurable_pi_apply (Fin.last n)).comp measurable_fst)
  have hjoint : Measurable fun γ : JumpPath Ω n =>
      JumpPath.rateDensity (fixedInitialWeight x) G.pathEscapeRate
          G.pathJumpRate γ *
        q (γ.1 (Fin.last n)) := hdensity.mul hterm
  unfold sectorLawFrom pathMeasure
  rw [lintegral_withDensity_eq_lintegral_mul _ hdensity hterm]
  simp only [Pi.mul_apply]
  have hpull : Measurable fun p : (Fin (n + 1) → Ω) × (Fin n → I) =>
      JumpPath.rateDensity (fixedInitialWeight x) G.pathEscapeRate
          G.pathJumpRate (Simplex.assemblePath T p) *
        q ((Simplex.assemblePath T p).1 (Fin.last n)) :=
    hjoint.comp (Simplex.measurable_assemblePath T)
  rw [G.rawCountingReference_eq T n,
    lintegral_map' hjoint.aemeasurable
      (Simplex.measurable_assemblePath T).aemeasurable,
    lintegral_prod _ hpull.aemeasurable, lintegral_fintype]
  refine Finset.sum_congr rfl fun states _ => ?_
  have hinner :
      (∫⁻ u, JumpPath.rateDensity (fixedInitialWeight x) G.pathEscapeRate
            G.pathJumpRate (Simplex.assemblePath T (states, u)) *
          q ((Simplex.assemblePath T (states, u)).1 (Fin.last n))
        ∂((T : ℝ≥0∞) ^ n •
          (volume : Measure (Fin n → I)).restrict
            (Simplex.freeSimplexSet n))) =
        (fixedInitialWeight x (states 0) * G.sequenceMass T states) *
          q (states (Fin.last n)) := by
    have hfst : ∀ u : Fin n → I,
        (Simplex.assemblePath T (states, u)).1 = states := fun _ => rfl
    simp only [hfst]
    rw [lintegral_mul_const' _ _ (hq (states (Fin.last n)))]
    rw [G.lintegral_rateDensity_assemblePath (fixedInitialWeight x) T states
      (by
        simp only [fixedInitialWeight]
        split <;> simp)]
  rw [hinner, G.stateSequenceCountingReference_singleton n states, mul_one]
  ring

/-- The fixed-initial sector law carries exactly the sector mass. -/
theorem sectorLawFrom_univ
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x : Ω) (n : ℕ) :
    G.sectorLawFrom T x n Set.univ = G.sectorMassFrom T x n := by
  rw [← lintegral_one, G.lintegral_terminal_sectorLawFrom T x n (fun _ => 1)
    fun _ => ENNReal.one_ne_top]
  simp [sectorMassFrom]

/-- The mass the `n`-jump sector actually sends to `y` is the terminal sector
mass. -/
theorem sectorLawFrom_terminal_singleton
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x y : Ω) (n : ℕ) :
    ∫⁻ γ, (if γ.1 (Fin.last n) = y then 1 else 0)
        ∂(G.sectorLawFrom T x n) =
      G.sectorTerminalMassFrom T x y n := by
  have hq : ∀ z : Ω, (if z = y then (1 : ℝ≥0∞) else 0) ≠ ∞ := by
    intro z
    split <;> simp
  rw [G.lintegral_terminal_sectorLawFrom T x n (fun z => if z = y then 1 else 0) hq]
  unfold sectorTerminalMassFrom
  refine Finset.sum_congr rfl fun states _ => ?_
  simp only [fixedInitialWeight]
  ring

/-! ### The full path law -/

/-- The normalized full finite-jump path law of a general finite jump generator
started from the prescribed state `x`. -/
noncomputable def pathLawFrom
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x : Ω) :
    Measure (FullPath Ω) :=
  FullPath.measure (G.sectorLawFrom T x)

/-- **The fixed-initial path law is a probability measure.**  This is
non-explosion at the measure level: no mass escapes to infinitely many jumps
inside the horizon. -/
instance instIsProbabilityMeasurePathLawFrom
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x : Ω) :
    IsProbabilityMeasure (G.pathLawFrom T x) := by
  refine FullPath.isProbabilityMeasure_measure (G.sectorLawFrom T x) ?_
  simp only [G.sectorLawFrom_univ T x]
  exact G.tsum_sectorMassFrom T x

/-- **The terminal marginal of the constructed path law.**  The pushforward of
the actual terminal coordinate assigns to each state exactly the transition
mass, so the sector sum used in the arithmetic is a genuine marginal of the
path law and not a separately defined quantity. -/
theorem pathLawFrom_terminalState_singleton
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x y : Ω) :
    (G.pathLawFrom T x).map FullPath.terminalState {y} = G.transitionMass T x y := by
  have hy : MeasurableSet ({y} : Set Ω) := measurableSet_singleton y
  have hmeas : ∀ n : ℕ,
      MeasurableSet {γ : JumpPath Ω n | γ.1 (Fin.last n) = y} := by
    intro n
    have h : MeasurableSet
        ((fun γ : JumpPath Ω n => γ.1 (Fin.last n)) ⁻¹' ({y} : Set Ω)) :=
      ((measurable_pi_apply (Fin.last n)).comp measurable_fst) hy
    exact h
  rw [Measure.map_apply FullPath.measurable_terminalState hy]
  unfold pathLawFrom FullPath.measure
  rw [Measure.sum_apply _ (FullPath.measurable_terminalState hy)]
  unfold transitionMass
  refine tsum_congr fun n => ?_
  rw [FullPath.liftMeasure, Measure.map_apply (FullPath.measurable_mk n)
    (FullPath.measurable_terminalState hy)]
  have hset : (Sigma.mk n ⁻¹' (FullPath.terminalState ⁻¹' ({y} : Set Ω))) =
      {γ : JumpPath Ω n | γ.1 (Fin.last n) = y} := rfl
  rw [hset, ← G.sectorLawFrom_terminal_singleton T x y n,
    ← lintegral_indicator_one (hmeas n)]
  refine lintegral_congr fun γ => ?_
  by_cases hγ : γ.1 (Fin.last n) = y <;> simp [hγ]

end FiniteJumpGenerator
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
