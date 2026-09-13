import UEOT.V3.TotalVariation
import Mathlib.Tactic.Linarith

/-!
# P-API-01 — composition of exact and approximate process interfaces

This file formalizes only the process-interface contract from frozen Core 3
§28.3.  A process interface has a protocol lift and a measurable path readout.
Control actions, policy lifts, rewards, and constraints deliberately do not
belong to this layer.
-/

namespace UEOT.V3.ProcessInterface

open MeasureTheory
open UEOT.V3.TotalVariation

universe uUA uUB uUC uOA uOB uOC

/-- A typed process interface `A → B`: protocols are lifted from `B` to `A`,
while realized paths are read out from `A` to `B`. -/
structure Interface
    (UA : Type uUA) (UB : Type uUB)
    (ΩA : Type uOA) (ΩB : Type uOB)
    [MeasurableSpace ΩA] [MeasurableSpace ΩB] where
  protocol : UB → UA
  readout : ΩA → ΩB
  measurable_readout : Measurable readout

variable {UA : Type uUA} {UB : Type uUB} {UC : Type uUC}
variable {ΩA : Type uOA} {ΩB : Type uOB} {ΩC : Type uOC}
variable [MeasurableSpace ΩA] [MeasurableSpace ΩB] [MeasurableSpace ΩC]

/-- Composition has the contravariant protocol map and covariant path map
specified in the frozen source. -/
def Interface.comp
    (AB : Interface UA UB ΩA ΩB)
    (BC : Interface UB UC ΩB ΩC) :
    Interface UA UC ΩA ΩC where
  protocol := AB.protocol ∘ BC.protocol
  readout := BC.readout ∘ AB.readout
  measurable_readout := BC.measurable_readout.comp AB.measurable_readout

@[simp] theorem comp_protocol
    (AB : Interface UA UB ΩA ΩB)
    (BC : Interface UB UC ΩB ΩC) :
    (AB.comp BC).protocol = AB.protocol ∘ BC.protocol := rfl

@[simp] theorem comp_readout
    (AB : Interface UA UB ΩA ΩB)
    (BC : Interface UB UC ΩB ΩC) :
    (AB.comp BC).readout = BC.readout ∘ AB.readout := rfl

/-- Exact naturality for all declared protocols. -/
def ExactNatural
    (I : Interface UA UB ΩA ΩB)
    (PA : UA → Measure ΩA) (PB : UB → Measure ΩB) : Prop :=
  ∀ u, (PA (I.protocol u)).map I.readout = PB u

/-- The event-supremum total variation used by UEOT obeys the ordinary
triangle inequality on probability laws. -/
theorem tvDist_triangle
    (μ ν ξ : Measure ΩA)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ] :
    tvDist μ ξ ≤ tvDist μ ν + tvDist ν ξ := by
  unfold tvDist
  refine csSup_le (tvEventSet_nonempty μ ξ) ?_
  intro r hr
  rcases hr with ⟨A, hA, rfl⟩
  calc
    |μ.real A - ξ.real A| ≤
        |μ.real A - ν.real A| + |ν.real A - ξ.real A| :=
      abs_sub_le _ _ _
    _ ≤ tvDist μ ν + tvDist ν ξ :=
      add_le_add (tvEvent_le μ ν A hA) (tvEvent_le ν ξ A hA)

/-- **P-API-01, exact clause.**  Exact process interfaces compose exactly,
with `J_AC = J_AB ∘ J_BC` and `C_AC = C_BC ∘ C_AB`. -/
theorem p_api_01_exact
    (AB : Interface UA UB ΩA ΩB)
    (BC : Interface UB UC ΩB ΩC)
    (PA : UA → Measure ΩA)
    (PB : UB → Measure ΩB)
    (PC : UC → Measure ΩC)
    (hAB : ExactNatural AB PA PB)
    (hBC : ExactNatural BC PB PC) :
    (AB.comp BC).protocol = AB.protocol ∘ BC.protocol ∧
    (AB.comp BC).readout = BC.readout ∘ AB.readout ∧
    ExactNatural (AB.comp BC) PA PC := by
  refine ⟨rfl, rfl, ?_⟩
  intro u
  change
    (PA (AB.protocol (BC.protocol u))).map
        (BC.readout ∘ AB.readout) = PC u
  rw [← Measure.map_map BC.measurable_readout AB.measurable_readout]
  rw [hAB (BC.protocol u), hBC u]

/-- **P-API-01, approximate clause.**  If the two interface defects are at most
`εAB` and `εBC` uniformly over their declared protocols, the composite defect
is at most `min 1 (εAB + εBC)`. -/
theorem p_api_01_approx
    (AB : Interface UA UB ΩA ΩB)
    (BC : Interface UB UC ΩB ΩC)
    (PA : UA → Measure ΩA)
    (PB : UB → Measure ΩB)
    (PC : UC → Measure ΩC)
    (hPA : ∀ u, IsProbabilityMeasure (PA u))
    (hPB : ∀ u, IsProbabilityMeasure (PB u))
    (hPC : ∀ u, IsProbabilityMeasure (PC u))
    (εAB εBC : ℝ)
    (hAB : ∀ u,
      tvDist ((PA (AB.protocol u)).map AB.readout) (PB u) ≤ εAB)
    (hBC : ∀ u,
      tvDist ((PB (BC.protocol u)).map BC.readout) (PC u) ≤ εBC) :
    ∀ u,
      tvDist
          ((PA ((AB.comp BC).protocol u)).map (AB.comp BC).readout)
          (PC u) ≤
        min 1 (εAB + εBC) := by
  intro u
  let μA : Measure ΩA := PA (AB.protocol (BC.protocol u))
  let μB : Measure ΩB := PB (BC.protocol u)
  let μC : Measure ΩC := PC u
  letI : IsProbabilityMeasure μA := hPA _
  letI : IsProbabilityMeasure μB := hPB _
  letI : IsProbabilityMeasure μC := hPC _
  letI : IsProbabilityMeasure (μA.map AB.readout) :=
    Measure.isProbabilityMeasure_map AB.measurable_readout.aemeasurable
  letI : IsProbabilityMeasure ((μA.map AB.readout).map BC.readout) :=
    Measure.isProbabilityMeasure_map BC.measurable_readout.aemeasurable
  letI : IsProbabilityMeasure (μB.map BC.readout) :=
    Measure.isProbabilityMeasure_map BC.measurable_readout.aemeasurable
  have hpush :
      tvDist ((μA.map AB.readout).map BC.readout)
          (μB.map BC.readout) ≤ εAB := by
    exact le_trans
      (tvDist_map_le (μA.map AB.readout) μB BC.readout BC.measurable_readout)
      (hAB (BC.protocol u))
  have hsecond : tvDist (μB.map BC.readout) μC ≤ εBC :=
    hBC u
  have hsum :
      tvDist ((μA.map AB.readout).map BC.readout) μC ≤ εAB + εBC := by
    exact le_trans
      (tvDist_triangle
        ((μA.map AB.readout).map BC.readout)
        (μB.map BC.readout) μC)
      (add_le_add hpush hsecond)
  have hone :
      tvDist ((μA.map AB.readout).map BC.readout) μC ≤ 1 :=
    tvDist_le_one _ _
  have hmin :
      tvDist ((μA.map AB.readout).map BC.readout) μC ≤
        min 1 (εAB + εBC) :=
    le_min hone hsum
  change
    tvDist
        ((PA (AB.protocol (BC.protocol u))).map
          (BC.readout ∘ AB.readout))
        (PC u) ≤ min 1 (εAB + εBC)
  rw [← Measure.map_map BC.measurable_readout AB.measurable_readout]
  exact hmin

end UEOT.V3.ProcessInterface
