import UEOT.V3.Compression.FiniteRecurrentGaugeBridge
import UEOT.V3.Compression.MetricGaugeInvariance

/-!
# Approximate recurrent GOA stability modulo exact state gauge

Frozen P-GOA-03 compares two recurrent decompositions only after they have been
written in one common transient/recurrent coordinate system and one common
recurrent-class partition.  That is the correct place to measure genuine
dynamical perturbation, but the physical target may subsequently use different
state labels.

This module separates those two effects cleanly:

1. choose a gauge-aligned target representative `Mhat` and apply frozen
   P-GOA-03 to `M` versus `Mhat`;
2. allow an arbitrary exact state equivalence taking `Mhat.P` to the physical
   target kernel;
3. transport recurrent carriers and class laws exactly through that gauge;
4. transport the recurrent-mixture TV bound without charging any extra error
   for pure relabeling.

Thus only the aligned `Q/R/classLaw` defects contribute to the perturbation
radius.  Exact state gauge contributes zero physical error.
-/

namespace UEOT.V3.Compression.ApproximateRecurrentGaugeStability

open Filter Topology
open UEOT.V3
open UEOT.V3.FiniteDobrushin
open UEOT.V3.FiniteCesaroInvariant
open UEOT.V3.FiniteRecurrentDecompositionStability
open UEOT.V3.Compression.GoaGaugeInvariance
open UEOT.V3.Compression.MetricGaugeInvariance
open UEOT.V3.Compression.RecurrentClassGaugeInvariance
open UEOT.V3.Compression.FiniteRecurrentGaugeBridge
open scoped BigOperators Matrix.Norms.Operator

universe uT uR uC

noncomputable section

variable {T : Type uT} [Fintype T] [DecidableEq T]
variable {R : Type uR} [Fintype R] [DecidableEq R]
variable {C : Type uC} [Fintype C] [DecidableEq C]

/-- **P-GOA-03 modulo exact state gauge.**

`Mhat` is a gauge-aligned representative of the physical target: it shares the
same transient type and recurrent partition as `M`, so frozen P-GOA-03 can
measure only genuine perturbation.  `Ptarget` may then use any exact relabeling
of `Mhat.P`.

The conclusion preserves the original absorption-matrix bound and both aligned
Cesaro-limit certificates, transports every recurrent class/class-law pair to
the physical target, and gives the same recurrent-mixture TV radius in target
coordinates. -/
theorem p_goa_03_mod_state_gauge
    (K : RecurrentPartition R C)
    (M Mhat : FiniteRecurrentDecomposition (T := T) K)
    (Ptarget : Matrix (FullState T R) (FullState T R) ℝ)
    (hPtarget : Ptarget ∈ Matrix.rowStochastic ℝ (FullState T R))
    (e : FullState T R ≃ FullState T R)
    (hconj : ∀ s t, Mhat.P s t = Ptarget (e s) (e t))
    (epsQ epsR : ℝ)
    (hQ : ‖Mhat.block.Q - M.block.Q‖ ≤ epsQ)
    (hR : ‖Mhat.block.R - M.block.R‖ ≤ epsR)
    (hsmall : ‖M.block.N‖ * epsQ < 1)
    (x0 : FullState T R)
    (epsStat : C → ℝ)
    (hstat : ∀ j,
      lawTV (M.classLaw j) (Mhat.classLaw j) ≤ epsStat j) :
    let nu := recurrentMixture (initialClassWeights K M.block x0) M.classLaw
    let nuhat :=
      recurrentMixture (initialClassWeights K Mhat.block x0) Mhat.classLaw
    let targetMixture :=
      recurrentMixture
        (initialClassWeights K Mhat.block x0)
        (fun c => relabelSimplex e (Mhat.classLaw c))
    ‖Mhat.block.H - M.block.H‖ ≤
        (‖M.block.N‖ ^ 2 * epsQ + ‖M.block.N‖ * epsR) /
          (1 - ‖M.block.N‖ * epsQ) ∧
      Tendsto
        (cesaroRow M.P M.stochastic
          (FiniteRecurrentDecomposition.pureFullLaw x0))
        atTop (𝓝 nu) ∧
      Tendsto
        (cesaroRow Mhat.P Mhat.stochastic
          (FiniteRecurrentDecomposition.pureFullLaw x0))
        atTop (𝓝 nuhat) ∧
      (∀ c,
        RecurrentCarrier Ptarget (e '' classCarrier (T := T) K c) ∧
          relabelSimplex e (Mhat.classLaw c) ∈
            carrierInvariantLawSet Ptarget hPtarget
              (e '' classCarrier (T := T) K c)) ∧
      lawTV (relabelSimplex e nu) targetMixture ≤
        (1 / 2 : ℝ) *
            ((‖M.block.N‖ ^ 2 * epsQ + ‖M.block.N‖ * epsR) /
              (1 - ‖M.block.N‖ * epsQ)) +
          ∑ j, (initialClassWeights K Mhat.block x0).1 j * epsStat j := by
  letI : Nonempty (FullState T R) := ⟨x0⟩
  dsimp only
  rcases p_goa_03 K M Mhat epsQ epsR hQ hR hsmall x0 epsStat hstat with
    ⟨hH, hcesM, hcesHat, hTV⟩
  refine ⟨hH, hcesM, hcesHat, ?_, ?_⟩
  · intro c
    exact decomposition_class_transport Mhat Ptarget hPtarget e hconj c
  · have hmix := recurrentMixture_relabel e
      (initialClassWeights K Mhat.block x0) Mhat.classLaw
    rw [← hmix]
    rw [lawTV_relabel e]
    exact hTV

/-- Pure state gauge contributes no class-law TV defect.  This isolates the
classwise `epsStat` term in P-GOA-03 as a genuine semantic perturbation rather
than a labeling artifact. -/
theorem classLaw_tv_relabel_both
    (K : RecurrentPartition R C)
    (M Mhat : FiniteRecurrentDecomposition (T := T) K)
    (e : FullState T R ≃ FullState T R)
    (c : C) :
    lawTV (relabelSimplex e (M.classLaw c))
        (relabelSimplex e (Mhat.classLaw c)) =
      lawTV (M.classLaw c) (Mhat.classLaw c) := by
  let r0 : R := Classical.choose (K.class_nonempty c)
  letI : Nonempty (FullState T R) := ⟨Sum.inr r0⟩
  exact lawTV_relabel e (M.classLaw c) (Mhat.classLaw c)

end


end UEOT.V3.Compression.ApproximateRecurrentGaugeStability
