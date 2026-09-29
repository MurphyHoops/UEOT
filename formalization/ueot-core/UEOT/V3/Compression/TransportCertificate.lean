import UEOT.V3.ProcessInterface
import UEOT.V3.TransportDefect
import UEOT.V3.InformationPacking
import Mathlib.Analysis.ODE.DiscreteGronwall

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

/-- Exact transport through a commuting factorization triangle.

This is the exact counterpart needed when two representations are both
obtained from one common source and one factors through the other.  The theorem
is deliberately set-level: measurability or other domain structure belongs to
the specialization that establishes `hcomm`. -/
theorem factorRoute_exact
    {A B C : Type*}
    (F : A → B) (G : A → C) (H : B → C)
    {a : A} {b : B} {c : C}
    (hF : F a = b) (hG : G a = c) (hcomm : H (F a) = G a) :
    H b = c := by
  rw [← hF, hcomm, hG]

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

/-- Heterogeneous weighted finite-chain accumulation.

This is the discrete-Gronwall extension of `chain_bound`.  The stage types may
still vary with time, but transport is now allowed to amplify the incoming
defect by a nonnegative factor `L n`.  Local defects `ε n` are injected after
transport, yielding the exact finite-horizon product/sum formula used by the
frozen development-pipeline theorem P-ID-02. -/
theorem weighted_chain_bound
    {A : ℕ → Type*}
    (defect : ∀ n, A n → A n → ℝ)
    (ideal actual : (n : ℕ) → A n)
    (step : ∀ n, A n → A (n + 1))
    (L ε : ℕ → ℝ)
    (hcontract : ∀ n,
      defect (n + 1) (ideal (n + 1)) (step n (actual n)) ≤
        L n * defect n (ideal n) (actual n))
    (htriangle : ∀ n,
      defect (n + 1) (ideal (n + 1)) (actual (n + 1)) ≤
        defect (n + 1) (ideal (n + 1)) (step n (actual n)) +
        defect (n + 1) (step n (actual n)) (actual (n + 1)))
    (hlocal : ∀ n,
      defect (n + 1) (step n (actual n)) (actual (n + 1)) ≤ ε n)
    (hL0 : ∀ n, 0 ≤ L n)
    (n : ℕ) :
    defect n (ideal n) (actual n) ≤
      (∏ j ∈ Finset.range n, L j) * defect 0 (ideal 0) (actual 0) +
        ∑ k ∈ Finset.range n,
          ε k * ∏ j ∈ Finset.Ico (k + 1) n, L j := by
  have hrec : ∀ t,
      defect (t + 1) (ideal (t + 1)) (actual (t + 1)) ≤
        L t * defect t (ideal t) (actual t) + ε t := by
    intro t
    calc
      defect (t + 1) (ideal (t + 1)) (actual (t + 1)) ≤
          defect (t + 1) (ideal (t + 1)) (step t (actual t)) +
          defect (t + 1) (step t (actual t)) (actual (t + 1)) :=
        htriangle t
      _ ≤ L t * defect t (ideal t) (actual t) + ε t :=
        add_le_add (hcontract t) (hlocal t)
  have hgr :=
    discrete_gronwall_prod_general
      (u := fun t => defect t (ideal t) (actual t))
      (b := ε)
      (c := L)
      (n₀ := 0)
      (fun t _ => hrec t)
      (fun t _ => hL0 t)
      (Nat.zero_le n)
  rw [Nat.Ico_zero_eq_range] at hgr
  calc
    defect n (ideal n) (actual n) ≤
        defect 0 (ideal 0) (actual 0) * (∏ j ∈ Finset.range n, L j) +
          ∑ k ∈ Finset.range n,
            ε k * ∏ j ∈ Finset.Ico (k + 1) n, L j := hgr
    _ = (∏ j ∈ Finset.range n, L j) *
          defect 0 (ideal 0) (actual 0) +
          ∑ k ∈ Finset.range n,
            ε k * ∏ j ∈ Finset.Ico (k + 1) n, L j := by
      rw [mul_comm (defect 0 (ideal 0) (actual 0))]

/-- Generic multiplicative certificate accumulation.

If a nonnegative one-step factor `factor n` preserves at least that fraction of
the current certificate `survival n`, then the certificate at time `n`
dominates the product of all preceding factors.  Probability, coupling, and
path-law semantics are deliberately absent from this meta theorem and must be
supplied by a specialization. -/
theorem multiplicative_chain_lower_bound
    (factor survival : ℕ → ℝ)
    (hfactor : ∀ n, 0 ≤ factor n)
    (hbase : 1 ≤ survival 0)
    (hstep : ∀ n, survival n * factor n ≤ survival (n + 1)) :
    ∀ n, (∏ i ∈ Finset.range n, factor i) ≤ survival n := by
  intro n
  induction n with
  | zero =>
      simpa using hbase
  | succ n ih =>
      rw [Finset.prod_range_succ]
      exact
        (mul_le_mul_of_nonneg_right ih (hfactor n)).trans
          (hstep n)

universe uDev

/-- Full source-facing P-ID-02 finite-horizon development bound reconstructed
through `weighted_chain_bound`.

The assumptions and conclusion coincide with
`UEOT.V3.DevelopmentTransport.development_pipeline`: a declared reference
trajectory, one-step residual bounds, stagewise Lipschitz propagation, and
nonnegative Lipschitz constants.  The compression layer contributes only the
generic weighted transport recurrence. -/
theorem development_pipeline_via_weighted_chain
    {X : Type uDev} [PseudoMetricSpace X]
    (θ θbar : ℕ → X)
    (Ψ : ℕ → X → X)
    (L ε : ℕ → ℝ)
    (href : ∀ t, θbar (t + 1) = Ψ t (θbar t))
    (hres : ∀ t, dist (θ (t + 1)) (Ψ t (θ t)) ≤ ε t)
    (hlip : ∀ t x y, dist (Ψ t x) (Ψ t y) ≤ L t * dist x y)
    (hL0 : ∀ t, 0 ≤ L t)
    (n : ℕ) :
    dist (θ n) (θbar n) ≤
      (∏ j ∈ Finset.range n, L j) * dist (θ 0) (θbar 0) +
        ∑ k ∈ Finset.range n,
          ε k * ∏ j ∈ Finset.Ico (k + 1) n, L j := by
  let A : ℕ → Type uDev := fun _ => X
  let defect : ∀ k, A k → A k → ℝ := fun _ x y => dist y x
  let ideal : (k : ℕ) → A k := fun k => θbar k
  let actual : (k : ℕ) → A k := fun k => θ k
  let step : ∀ k, A k → A (k + 1) := fun k x => Ψ k x
  apply weighted_chain_bound defect ideal actual step L ε
  · intro k
    dsimp [defect, ideal, actual, step]
    rw [href k]
    exact hlip k (θ k) (θbar k)
  · intro k
    dsimp [defect, ideal, actual, step]
    calc
      dist (θ (k + 1)) (θbar (k + 1)) ≤
          dist (θ (k + 1)) (Ψ k (θ k)) +
            dist (Ψ k (θ k)) (θbar (k + 1)) := dist_triangle _ _ _
      _ = dist (Ψ k (θ k)) (θbar (k + 1)) +
          dist (θ (k + 1)) (Ψ k (θ k)) := add_comm _ _
  · intro k
    dsimp [defect, actual, step]
    exact hres k
  · exact hL0

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

/-- Full source-facing exact P-API-01 shape reconstructed through the
compression calculus. -/
theorem processInterface_exact_source_via_twoStage
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
    (AB.comp BC).protocol = AB.protocol ∘ BC.protocol ∧
    (AB.comp BC).readout = BC.readout ∘ AB.readout ∧
    ExactNatural (AB.comp BC) PA PC := by
  exact ⟨rfl, rfl, processInterface_exact_via_twoStage AB BC PA PB PC hAB hBC⟩

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

/-- Full source-facing P-ID-01 supremum statement reconstructed through the
generic chain theorem. -/
theorem transportDefect_source_via_chain
    {M : ℕ → Type uM} [∀ n, MeasurableSpace (M n)]
    (S : FrozenTransportSystem M) (ε : ℕ → ℝ)
    [Nonempty (M 0)] (hadj : S.AdjacentBound ε) (n : ℕ) :
    sSup (Set.range fun m : M 0 =>
      tvDist ((S.K 0 m).map (S.Γ 0 n))
        (S.K n (S.Γ 0 n m))) ≤
      ∑ i ∈ Finset.range n, ε i := by
  refine csSup_le (Set.range_nonempty _) ?_
  intro d hd
  rcases hd with ⟨m, rfl⟩
  exact transportDefect_pointwise_via_chain S ε hadj n m

universe uX uMs uMr uA

/-- P-DYN-04's reachable-image approximate cross-scale bound reconstructed
through the generic two-stage transport certificate.

The domain-specific work is exactly the source obligation: both macro kernels
approximate pushforwards of one microscopic transition law, the coarse readout
factors through the fine readout, and total variation contracts under the
measurable coarse map.  The error addition itself is delegated to
`twoStage_bound`. -/
theorem dynamicsCrossScale_approx_via_twoStage
    {X : Type uX} {Ms : Type uMs} {Mr : Type uMr} {A : Type uA}
    [MeasurableSpace X] [MeasurableSpace Ms] [MeasurableSpace Mr]
    (P : X → A → Measure X)
    (Ps : Ms → A → Measure Ms)
    (Pr : Mr → A → Measure Mr)
    (fs : X → Ms) (fr : X → Mr) (c : Ms → Mr)
    (hfs : Measurable fs) (hfr : Measurable fr) (hc : Measurable c)
    (hcomp : ∀ x, fr x = c (fs x))
    (hP : ∀ x a, IsProbabilityMeasure (P x a))
    (hPs : ∀ m a, IsProbabilityMeasure (Ps m a))
    (hPr : ∀ m a, IsProbabilityMeasure (Pr m a))
    (εs εr : ℝ)
    (hs : ∀ x a,
      tvDist ((P x a).map fs) (Ps (fs x) a) ≤ εs)
    (hr : ∀ x a,
      tvDist ((P x a).map fr) (Pr (fr x) a) ≤ εr) :
    ∀ m ∈ Set.range fs, ∀ a,
      tvDist ((Ps m a).map c) (Pr (c m) a) ≤ εs + εr := by
  rintro m ⟨x, rfl⟩ a
  letI : IsProbabilityMeasure (P x a) := hP x a
  letI : IsProbabilityMeasure (Ps (fs x) a) := hPs (fs x) a
  letI : IsProbabilityMeasure (Pr (c (fs x)) a) := hPr (c (fs x)) a
  letI : IsProbabilityMeasure ((P x a).map fs) :=
    (Measure.isProbabilityMeasure_map_iff hfs.aemeasurable).2 inferInstance
  letI : IsProbabilityMeasure ((P x a).map fr) :=
    (Measure.isProbabilityMeasure_map_iff hfr.aemeasurable).2 inferInstance
  letI : IsProbabilityMeasure ((Ps (fs x) a).map c) :=
    (Measure.isProbabilityMeasure_map_iff hc.aemeasurable).2 inferInstance
  letI : IsProbabilityMeasure (((P x a).map fs).map c) :=
    (Measure.isProbabilityMeasure_map_iff hc.aemeasurable).2 inferInstance

  have hmapEq :
      ((P x a).map fs).map c = (P x a).map fr := by
    rw [Measure.map_map hc hfs]
    congr 1
    funext y
    exact (hcomp y).symm

  have hcontract :
      tvDist ((Ps (fs x) a).map c) (((P x a).map fs).map c) ≤
        tvDist (Ps (fs x) a) ((P x a).map fs) :=
    tvDist_map_le (Ps (fs x) a) ((P x a).map fs) c hc

  have hold :
      tvDist (Ps (fs x) a) ((P x a).map fs) ≤ εs := by
    rw [UEOT.V3.InformationPacking.tvDist_symm]
    exact hs x a

  have hnew :
      tvDist (((P x a).map fs).map c) (Pr (c (fs x)) a) ≤ εr := by
    rw [hmapEq]
    simpa [hcomp x] using hr x a

  exact twoStage_bound
    (dA := fun μ ν : Measure Ms => tvDist μ ν)
    (dB := fun μ ν : Measure Mr => tvDist μ ν)
    (F := fun μ : Measure Ms => μ.map c)
    hcontract
    (UEOT.V3.ProcessInterface.tvDist_triangle
      ((Ps (fs x) a).map c)
      (((P x a).map fs).map c)
      (Pr (c (fs x)) a))
    hold hnew

/-- Exact P-DYN-04 reachable-image intertwining reconstructed from the generic
commuting-factor transport law.  No assumption is stronger than the frozen
source-facing exact clause. -/
theorem dynamicsCrossScale_exact_via_factor
    {X : Type uX} {Ms : Type uMs} {Mr : Type uMr} {A : Type uA}
    [MeasurableSpace X] [MeasurableSpace Ms] [MeasurableSpace Mr]
    (P : X → A → Measure X)
    (Ps : Ms → A → Measure Ms)
    (Pr : Mr → A → Measure Mr)
    (fs : X → Ms) (fr : X → Mr) (c : Ms → Mr)
    (hfs : Measurable fs) (hc : Measurable c)
    (hcomp : ∀ x, fr x = c (fs x))
    (hs : ∀ x a, (P x a).map fs = Ps (fs x) a)
    (hr : ∀ x a, (P x a).map fr = Pr (fr x) a) :
    ∀ m ∈ Set.range fs, ∀ a,
      (Ps m a).map c = Pr (c m) a := by
  rintro m ⟨x, rfl⟩ a
  have hmapEq :
      ((P x a).map fs).map c = (P x a).map fr := by
    rw [Measure.map_map hc hfs]
    congr 1
    funext y
    exact (hcomp y).symm
  have hr' : (P x a).map fr = Pr (c (fs x)) a := by
    simpa [hcomp x] using hr x a
  exact factorRoute_exact
    (fun μ : Measure X => μ.map fs)
    (fun μ : Measure X => μ.map fr)
    (fun μ : Measure Ms => μ.map c)
    (hs x a) hr' hmapEq


end UEOT.V3.Compression.TransportCertificate
