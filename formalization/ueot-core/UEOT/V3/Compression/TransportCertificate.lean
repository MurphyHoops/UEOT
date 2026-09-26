import UEOT.V3.ProcessInterface
import UEOT.V3.TransportDefect

/-!
# UEOT Core compression — transport/certificate calculus

This module isolates a second repeated skeleton from the frozen 106-theorem
Core: an error certificate is transported through a map that is
non-expansive, then combined with a fresh local defect by a triangle
inequality.

The abstract theorem below knows nothing about probability, total variation,
or process interfaces.  The first specialization reconstructs the approximate
clause of P-API-01 from exactly those two laws.  This is the first
machine-checked compression witness: a source-facing theorem family is an
instance of a smaller transport/certificate schema.
-/

namespace UEOT.V3.Compression.TransportCertificate

/-- Generic two-stage error transport.

`dA` measures the old-stage defect, `F` transports old-stage objects to the
new stage, and `dB` measures the new-stage defect.  If transport is
non-expansive and `dB` satisfies the needed triangle inequality, an old defect
plus a fresh local defect bounds the composite defect. -/
theorem twoStage_bound
    {A B : Type*}
    (dA : A → A → ℝ) (dB : B → B → ℝ) (F : A → B)
    {x y : A} {z : B} {εold εnew : ℝ}
    (hcontract : dB (F x) (F y) ≤ dA x y)
    (htriangle : dB (F x) z ≤ dB (F x) (F y) + dB (F y) z)
    (hold : dA x y ≤ εold)
    (hnew : dB (F y) z ≤ εnew) :
    dB (F x) z ≤ εold + εnew := by
  calc
    dB (F x) z ≤ dB (F x) (F y) + dB (F y) z := htriangle
    _ ≤ dA x y + dB (F y) z := add_le_add hcontract (le_refl _)
    _ ≤ εold + εnew := add_le_add hold hnew

/-- Exact commuting diagrams compose.  This is the zero-defect/equality
counterpart of `twoStage_bound`. -/
theorem twoStage_exact
    {A B C : Type*}
    (F : A → B) (G : B → C)
    {a : A} {b : B} {c : C}
    (h₁ : F a = b) (h₂ : G b = c) :
    G (F a) = c := by
  rw [h₁, h₂]

open scoped BigOperators

/-- Heterogeneous finite-chain accumulation.

The objects may live in a different type at every stage.  The theorem assumes
only the *local* contraction/transport inequality needed for the actual
ideal/realized pair, a local triangle split, and a fresh local defect bound.
It therefore does not hide probability, measurability, topology, or other
domain-specific assumptions inside the meta layer.  Those obligations must be
discharged by each specialization. -/
theorem chain_bound
    {A : ℕ → Type*}
    (defect : ∀ n, A n → A n → ℝ)
    (ideal actual : (n : ℕ) → A n)
    (step : ∀ n, A n → A (n + 1))
    (ε : ℕ → ℝ)
    (hbase : defect 0 (ideal 0) (actual 0) ≤ 0)
    (hcontract : ∀ n,
      defect (n + 1) (ideal (n + 1)) (step n (actual n)) ≤
        defect n (ideal n) (actual n))
    (htriangle : ∀ n,
      defect (n + 1) (ideal (n + 1)) (actual (n + 1)) ≤
        defect (n + 1) (ideal (n + 1)) (step n (actual n)) +
        defect (n + 1) (step n (actual n)) (actual (n + 1)))
    (hlocal : ∀ n,
      defect (n + 1) (step n (actual n)) (actual (n + 1)) ≤ ε n) :
    ∀ n,
      defect n (ideal n) (actual n) ≤
        ∑ i ∈ Finset.range n, ε i := by
  intro n
  induction n with
  | zero =>
      simpa using hbase
  | succ n ih =>
      calc
        defect (n + 1) (ideal (n + 1)) (actual (n + 1)) ≤
            defect (n + 1) (ideal (n + 1)) (step n (actual n)) +
              defect (n + 1) (step n (actual n)) (actual (n + 1)) :=
          htriangle n
        _ ≤ defect n (ideal n) (actual n) + ε n :=
          add_le_add (hcontract n) (hlocal n)
        _ ≤ (∑ i ∈ Finset.range n, ε i) + ε n :=
          add_le_add ih (le_refl _)
        _ = ∑ i ∈ Finset.range (n + 1), ε i := by
          rw [Finset.sum_range_succ]

open MeasureTheory
open UEOT.V3.TotalVariation
open UEOT.V3.ProcessInterface

universe uUA uUB uUC uOA uOB uOC

/-- P-API-01's approximate composition bound, reconstructed through the
generic transport/certificate theorem rather than by a bespoke triangle
argument.

Keeping this theorem separate from the frozen source-facing theorem lets the
compression project test the abstraction without rewriting the already
FULL-GREEN P-ID. -/
theorem processInterface_approx_via_twoStage
    {UA : Type uUA} {UB : Type uUB} {UC : Type uUC}
    {ΩA : Type uOA} {ΩB : Type uOB} {ΩC : Type uOC}
    [MeasurableSpace ΩA] [MeasurableSpace ΩB] [MeasurableSpace ΩC]
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
  have hsum :
      tvDist ((μA.map AB.readout).map BC.readout) μC ≤ εAB + εBC := by
    exact twoStage_bound
      (dA := fun μ ν : Measure ΩB => tvDist μ ν)
      (dB := fun μ ν : Measure ΩC => tvDist μ ν)
      (F := fun μ : Measure ΩB => μ.map BC.readout)
      (tvDist_map_le (μA.map AB.readout) μB BC.readout BC.measurable_readout)
      (UEOT.V3.ProcessInterface.tvDist_triangle
        ((μA.map AB.readout).map BC.readout)
        (μB.map BC.readout) μC)
      (hAB (BC.protocol u))
      (hBC u)
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

/-- Exact P-API-01 naturality is the equality-valued form of the same
composition pattern. -/
theorem processInterface_exact_via_twoStage
    {UA : Type uUA} {UB : Type uUB} {UC : Type uUC}
    {ΩA : Type uOA} {ΩB : Type uOB} {ΩC : Type uOC}
    [MeasurableSpace ΩA] [MeasurableSpace ΩB] [MeasurableSpace ΩC]
    (AB : Interface UA UB ΩA ΩB)
    (BC : Interface UB UC ΩB ΩC)
    (PA : UA → Measure ΩA)
    (PB : UB → Measure ΩB)
    (PC : UC → Measure ΩC)
    (hAB : ExactNatural AB PA PB)
    (hBC : ExactNatural BC PB PC) :
    ExactNatural (AB.comp BC) PA PC := by
  intro u
  change
    (PA (AB.protocol (BC.protocol u))).map
        (BC.readout ∘ AB.readout) = PC u
  rw [← Measure.map_map BC.measurable_readout AB.measurable_readout]
  exact twoStage_exact
    (fun μ : Measure ΩA => μ.map AB.readout)
    (fun μ : Measure ΩB => μ.map BC.readout)
    (hAB (BC.protocol u))
    (hBC u)

open UEOT.V3.TransportDefect

universe uM

/-- P-ID-01's pointwise transport-defect accumulation reconstructed as an
instance of `chain_bound`.

This theorem deliberately has the same mathematical conclusion as the
already-FULL-GREEN pointwise lemma, but the proof factors the source-specific
measure theory (TV data processing, triangle inequality, coherent measurable
transport) from the generic additive accumulation argument. -/
theorem transportDefect_pointwise_via_chain
    {M : ℕ → Type uM} [∀ n, MeasurableSpace (M n)]
    (S : FrozenTransportSystem M) (ε : ℕ → ℝ)
    (hadj : S.AdjacentBound ε) :
    ∀ n (m : M 0),
      tvDist ((S.K 0 m).map (S.Γ 0 n))
        (S.K n (S.Γ 0 n m)) ≤
        ∑ i ∈ Finset.range n, ε i := by
  intro n m
  let A : ℕ → Type uM := fun k => Measure (M k)
  let defect : ∀ k, A k → A k → ℝ :=
    fun _ μ ν => tvDist μ ν
  let ideal : (k : ℕ) → A k :=
    fun k => (S.K 0 m).map (S.Γ 0 k)
  let actual : (k : ℕ) → A k :=
    fun k => S.K k (S.Γ 0 k m)
  let step : ∀ k, A k → A (k + 1) :=
    fun k μ => μ.map (S.Γ k (k + 1))
  apply chain_bound defect ideal actual step ε
  · have hΓ0 : S.Γ 0 0 = id := by
      funext x
      exact S.Γ_id 0 x
    letI : IsProbabilityMeasure (S.K 0 m) := S.isProbability_K 0 m
    simp [defect, ideal, actual, hΓ0, UEOT.V3.TransportDefect.tvDist_self]
  · intro k
    have h0k : Measurable (S.Γ 0 k) := S.measurable_Γ 0 k
    have hk : Measurable (S.Γ k (k + 1)) := S.measurable_Γ k (k + 1)
    have hcomp :
        S.Γ 0 (k + 1) = S.Γ k (k + 1) ∘ S.Γ 0 k := by
      funext x
      exact S.Γ_comp 0 k (k + 1) x
    letI : IsProbabilityMeasure (S.K 0 m) := S.isProbability_K 0 m
    letI : IsProbabilityMeasure ((S.K 0 m).map (S.Γ 0 k)) :=
      Measure.isProbabilityMeasure_map h0k.aemeasurable
    letI : IsProbabilityMeasure (S.K k (S.Γ 0 k m)) :=
      S.isProbability_K k (S.Γ 0 k m)
    change
      tvDist ((S.K 0 m).map (S.Γ 0 (k + 1)))
          ((S.K k (S.Γ 0 k m)).map (S.Γ k (k + 1))) ≤
        tvDist ((S.K 0 m).map (S.Γ 0 k))
          (S.K k (S.Γ 0 k m))
    rw [hcomp, ← Measure.map_map hk h0k]
    exact tvDist_map_le
      ((S.K 0 m).map (S.Γ 0 k))
      (S.K k (S.Γ 0 k m))
      (S.Γ k (k + 1)) hk
  · intro k
    have h0next : Measurable (S.Γ 0 (k + 1)) :=
      S.measurable_Γ 0 (k + 1)
    have hk : Measurable (S.Γ k (k + 1)) := S.measurable_Γ k (k + 1)
    letI : IsProbabilityMeasure (S.K 0 m) := S.isProbability_K 0 m
    letI : IsProbabilityMeasure ((S.K 0 m).map (S.Γ 0 (k + 1))) :=
      Measure.isProbabilityMeasure_map h0next.aemeasurable
    letI : IsProbabilityMeasure (S.K k (S.Γ 0 k m)) :=
      S.isProbability_K k (S.Γ 0 k m)
    letI : IsProbabilityMeasure
        ((S.K k (S.Γ 0 k m)).map (S.Γ k (k + 1))) :=
      Measure.isProbabilityMeasure_map hk.aemeasurable
    letI : IsProbabilityMeasure (S.K (k + 1) (S.Γ 0 (k + 1) m)) :=
      S.isProbability_K (k + 1) (S.Γ 0 (k + 1) m)
    exact UEOT.V3.TransportDefect.tvDist_triangle _ _ _
  · intro k
    have hcomp_pt :
        S.Γ 0 (k + 1) m = S.Γ k (k + 1) (S.Γ 0 k m) :=
      S.Γ_comp 0 k (k + 1) m
    simpa [defect, actual, step, hcomp_pt] using hadj k (S.Γ 0 k m)


end UEOT.V3.Compression.TransportCertificate
