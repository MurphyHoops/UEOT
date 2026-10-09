import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.TwoStageFormationTransport
import UEOT.V3.CoreOperationalAssembly
import Mathlib.Tactic

/-!
# UMC-03/06 — shared-source two-step formation with dependent certificates

Two stochastic *certification events* may be arbitrarily dependent. The
existing P-CORE finite-event bound (which requires NO independence between
events) is composed with UMC-03 derived two-step response-channel formation.
The event assumptions are about separately checkable world residuals,
NOT the final desired formed certificate. Marginal concentration under
correlated time samples remains a separate open theorem.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open MeasureTheory
open UEOT.V3.CoreOperationalAssembly
open UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

universe uOmega uX0 uX1 uX2 uP0 uP1 uP2 uO0 uO1 uO2

/-- P-CORE's actual dependent-event bound gives a high-probability
derived formation certificate across two registered noisy transports.
No event independence or preselected final-forming model is assumed. -/
theorem dependent_two_stage_formation_high_probability
    {Ω : Type uOmega} [MeasurableSpace Ω]
    {X0 : Type uX0} {X1 : Type uX1} {X2 : Type uX2}
    {P0 : Type uP0} {P1 : Type uP1} {P2 : Type uP2}
    {O0 : Type uO0} {O1 : Type uO1} {O2 : Type uO2}
    [Fintype O0] [Fintype O1]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (events : Bool → Set Ω) (α : Bool → ℝ)
    (hevents : ∀ b, MeasurableSet (events b))
    (hfail : ∀ b, μ.real (events b)ᶜ ≤ α b)
    (K01 : FiniteResponseChannel O0 O1)
    (K12 : FiniteResponseChannel O1 O2)
    (actual0 : X0 → O0 → ℝ)
    (actual1 : Ω → X1 → O1 → ℝ)
    (actual2 : Ω → X2 → O2 → ℝ)
    (predict0 : P0 → O0 → ℝ)
    (predict1 : P1 → O1 → ℝ)
    (predict2 : P2 → O2 → ℝ)
    (tx01 : X0 → X1) (tx12 : X1 → X2)
    (tp01 : P0 → P1) (tp12 : P1 → P2)
    (tau dw01 dp01 dw12 dp12 : ℝ)
    (hWorld01 : ∀ ω, ω ∈ events false → ∀ x j,
      |actual1 ω (tx01 x) j -
        ∑ i, K01.weight j i * actual0 x i| ≤ dw01)
    (hParent01 : ∀ p j,
      |predict1 (tp01 p) j -
        ∑ i, K01.weight j i * predict0 p i| ≤ dp01)
    (hWorld12 : ∀ ω, ω ∈ events true → ∀ x j,
      |actual2 ω (tx12 x) j -
        ∑ i, K12.weight j i * actual1 ω x i| ≤ dw12)
    (hParent12 : ∀ p j,
      |predict2 (tp12 p) j -
        ∑ i, K12.weight j i * predict1 p i| ≤ dp12)
    (x : X0) (p : P0)
    (hformed0 : FormedByResponse actual0 predict0 tau x p) :
    1 - ∑ b : Bool, α b ≤
      μ.real {ω | FormedByResponse (actual2 ω) predict2
        (dw12 + (dw01 + tau + dp01) + dp12)
        (tx12 (tx01 x)) (tp12 (tp01 p))} := by
  have hprob : 1 - ∑ b : Bool, α b ≤
      μ.real (commonGoodEvent events) :=
    commonGoodEvent_measureReal_lower μ events α hevents hfail
  have hsubset : commonGoodEvent events ⊆
      {ω | FormedByResponse (actual2 ω) predict2
        (dw12 + (dw01 + tau + dp01) + dp12)
        (tx12 (tx01 x)) (tp12 (tp01 p))} := by
    intro ω hω
    have hfirst : ω ∈ events false :=
      Set.mem_iInter.mp hω false
    have hsecond : ω ∈ events true :=
      Set.mem_iInter.mp hω true
    exact two_stage_formation_budget
      K01 K12 actual0 (actual1 ω) (actual2 ω)
      predict0 predict1 predict2
      tx01 tx12 tp01 tp12 tau dw01 dp01 dw12 dp12
      (hWorld01 ω hfirst) hParent01
      (hWorld12 ω hsecond) hParent12 x p hformed0
  exact hprob.trans (measureReal_mono hsubset)

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
