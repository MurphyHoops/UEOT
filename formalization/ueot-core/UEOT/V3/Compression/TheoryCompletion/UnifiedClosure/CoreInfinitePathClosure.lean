import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CorePMFViabilityReconciliation
import UEOT.V3.ViabilityTrajectory
import Mathlib.Tactic

/-!
# Frozen P-PER-03 actual infinite-path-law completion of UMC V4

V4 proved finite positive-support-path safety from exact stochastic control
quotients. The frozen Core already contains a much STRONGER theorem: the
Ionescu--Tulcea law of a genuine stationary controlled Markov process stays
inside a fixed viable kernel at ALL countably many discrete times with
probability one. We do not duplicate that construction.

The new work below proves the V4 real-mass viable fixedpoint is also a fixed
point of P-PER-03's PMF deletion operator on the original MICRO source.
Hence its all-times path theorem applies, with no duplicate stochastic process
and no independently supplied trajectory law.

A maximal region may be empty. A legal initial PMF supported on it is
required, and physical matter/program repair is not derived.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.ViabilityKernel
open UEOT.V3.ViabilityTrajectory

universe uX uY uA

/-- Exact quotient and fixed-point viability imply a genuine fixed point
of the original MICRO PMF viability operator at the identical viability set.
The controller need not have been supplied in advance. -/
theorem micro_pmf_viability_fixed_of_macro_real_fixed
    {X : Type uX} {Y : Type uY} {A : Type uA}
    [Fintype X] [Fintype Y] [Fintype A] [Nonempty A]
    (Q : ExactControlQuotient X Y (fun _ => A))
    (safe : Y → Prop) (n : ℕ)
    (hfix : ∀ c : Y, macroViable Q safe n c ↔
      macroViable Q safe (n+1) c) :
    let P : X → A → PMF X := fun x a => Q.micro.transitionPMF x a
    let K : Set X := {x | macroViable Q safe n (Q.f x)}
    viabilityStep P K = K := by
  classical
  let P : X → A → PMF X := fun x a => Q.micro.transitionPMF x a
  let K : Set X := {x | macroViable Q safe n (Q.f x)}
  change viabilityStep P K = K
  apply Set.Subset.antisymm (viabilityStep_subset P K)
  intro x hx
  change x ∈ K ∧ ∃ a : A, StaysIn (P x a) K
  refine ⟨hx, ?_⟩
  obtain ⟨a, ha⟩ :=
    macro_viable_fixedpoint_has_safe_action Q safe n hfix (Q.f x) hx
  refine ⟨a, ?_⟩
  apply (frozen_pmf_staysIn_iff_real_zero_outside Q.micro
    (fun z => macroViable Q safe n (Q.f z)) x a).2
  have hs := (macro_zero_outside_iff_micro_zero_outside
    Q (macroViable Q safe n) x a).1 ha
  exact hs

/-- Under ANY exact finite controlled quotient, the synthesized viable
micro region inherits P-PER's genuine infinite Ionescu--Tulcea trajectory
guarantee. No externally asserted micro controlled invariance or existing
controller is a premise. -/
theorem exists_source_micro_all_times_viable_path_law
    {X : Type uX} {Y : Type uY} {A : Type uA}
    [Fintype X] [Fintype Y] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (Q : ExactControlQuotient X Y (fun _ => A))
    (safe : Y → Prop) :
    ∃ n : ℕ, n ≤ Fintype.card Y ∧
      ∀ μ : PMF X,
        StaysIn μ {x | macroViable Q safe n (Q.f x)} →
        ∃ pi : X → A,
          stationaryTrajMeasure
            (fun x a => Q.micro.transitionPMF x a) pi μ
            {ω | ∀ t : ℕ, macroViable Q safe n (Q.f (ω t))} = 1 := by
  obtain ⟨n, hn, hfix⟩ := exists_finite_viability_fixedpoint Q safe
  refine ⟨n, hn, ?_⟩
  intro μ hμ
  let P : X → A → PMF X := fun x a => Q.micro.transitionPMF x a
  let K : Set X := {x | macroViable Q safe n (Q.f x)}
  have hK : MeasurableSet K := (Set.toFinite K).measurableSet
  have hPfix : viabilityStep P K = K :=
    micro_pmf_viability_fixed_of_macro_real_fixed Q safe n hfix
  exact exists_stationary_policy_all_times_of_fixed P hPfix μ hμ hK

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
