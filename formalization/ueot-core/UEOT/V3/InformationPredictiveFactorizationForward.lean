import UEOT.V3.InformationPredictiveFactorizationCanonical

/-!
# P-INT-01 — predictive factorization implies conditional independence

After canonicalizing the factorization witness to `q₀ = P(Y | z(H))`, the
forward direction is a graph-transport identity followed by Mathlib's standard
conditional-independence characterization in terms of regular conditional
probabilities.
-/

namespace UEOT.V3.InformationPredictiveFactorization

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

universe uH uY uZ

variable {H : Type uH} {Y : Type uY} {Z : Type uZ}
variable [MeasurableSpace H] [MeasurableSpace Y] [MeasurableSpace Z]
variable [StandardBorelSpace H] [StandardBorelSpace Y]
variable [Nonempty H] [Nonempty Y]

/-- Source condition (i), in the generic statistic form: the future and the
full history are conditionally independent given `z(H)`. -/
def PredictiveConditionalIndependence
    (μ : Measure (H × Y)) [IsProbabilityMeasure μ]
    (z : H → Z) (hz : Measurable z) : Prop :=
  futureVar (H := H) (Y := Y) ⟂ᵢ[
    statisticVar (Y := Y) z,
    measurable_statisticVar (Y := Y) z hz;
    μ] historyVar (H := H) (Y := Y)

/-- The graph law of `(z(H),H)` is the pushforward of the history marginal by
`h ↦ (z h,h)`. -/
theorem historyGraph_map_eq_fst_map
    (μ : Measure (H × Y))
    (z : H → Z) (hz : Measurable z) :
    μ.map (fun p : H × Y => (z p.1, p.1)) =
      μ.fst.map (fun h : H => (z h, h)) := by
  have he : Measurable (fun h : H => (z h, h)) := hz.prodMk measurable_id
  unfold Measure.fst
  exact (Measure.map_map he measurable_fst).symm

/-- If the history-conditional future law is `q(z(h))`, then after adjoining the
statistic to the history coordinate the conditional kernel is simply `q`
indexed by the first coordinate and ignoring the history coordinate. -/
theorem compProd_map_factorizedHistoryGraph
    (ν : Measure H) [SFinite ν]
    (q : Kernel Z Y) [IsSFiniteKernel q]
    (z : H → Z) (hz : Measurable z) :
    (ν ⊗ₘ q.comap z hz).map
        (fun p : H × Y => ((z p.1, p.1), p.2)) =
      (ν.map (fun h : H => (z h, h))) ⊗ₘ Kernel.prodMkRight H q := by
  let e : H → Z × H := fun h => (z h, h)
  have he : Measurable e := hz.prodMk measurable_id
  have hF : Measurable (fun p : H × Y => (e p.1, p.2)) :=
    (he.comp measurable_fst).prodMk measurable_snd
  ext s hs
  rw [Measure.map_apply hF hs]
  rw [Measure.compProd_apply (hF hs), Measure.compProd_apply hs]
  rw [lintegral_map
    (Kernel.measurable_kernel_prodMk_left hs) he]
  congr with h

/-- A predictive factorization makes the canonical statistic-conditional kernel
`q₀=P(Y|z(H))` a conditional law of `Y` given the enlarged conditioning variable
`(z(H),H)`, with the history coordinate ignored. -/
theorem hasCondDistrib_future_historyGraph_of_factorization
    (μ : Measure (H × Y)) [IsProbabilityMeasure μ]
    (z : H → Z) (hz : Measurable z)
    (hfac : PredictiveFactorization μ z hz) :
    HasCondDistrib
      (futureVar (H := H) (Y := Y))
      (fun p : H × Y => (z p.1, p.1))
      (Kernel.prodMkRight H
        (condDistrib
          (futureVar (H := H) (Y := Y))
          (statisticVar (Y := Y) z) μ))
      μ := by
  let q0 : Kernel Z Y :=
    condDistrib
      (futureVar (H := H) (Y := Y))
      (statisticVar (Y := Y) z) μ
  letI : IsMarkovKernel q0 := by
    dsimp [q0]
    infer_instance
  have hcanon :
      μ.condKernel =ᵐ[μ.fst] q0.comap z hz := by
    dsimp [q0]
    exact canonicalFactorization_of_factorization μ z hz hfac
  have hdis : μ.fst ⊗ₘ μ.condKernel = μ :=
    Measure.disintegrate μ μ.condKernel
  have hcomp :
      μ.fst ⊗ₘ μ.condKernel = μ.fst ⊗ₘ q0.comap z hz :=
    Measure.compProd_congr hcanon
  have hgraph : Measurable (fun p : H × Y => (z p.1, p.1)) :=
    (measurable_statisticVar (Y := Y) z hz).prodMk measurable_historyVar
  refine ⟨hgraph.aemeasurable.prodMk measurable_futureVar.aemeasurable, ?_⟩
  calc
    μ.map (fun p : H × Y => ((z p.1, p.1), p.2)) =
        (μ.fst ⊗ₘ μ.condKernel).map
          (fun p : H × Y => ((z p.1, p.1), p.2)) := by
      rw [hdis]
    _ = (μ.fst ⊗ₘ q0.comap z hz).map
          (fun p : H × Y => ((z p.1, p.1), p.2)) := by
      rw [hcomp]
    _ = μ.fst.map (fun h : H => (z h, h)) ⊗ₘ Kernel.prodMkRight H q0 :=
      compProd_map_factorizedHistoryGraph μ.fst q0 z hz
    _ = μ.map (fun p : H × Y => (z p.1, p.1)) ⊗ₘ Kernel.prodMkRight H q0 := by
      rw [historyGraph_map_eq_fst_map μ z hz]

/-- Generic forward half of the source Predictive Factorization
Characterization Theorem. -/
theorem predictiveConditionalIndependence_of_factorization
    (μ : Measure (H × Y)) [IsProbabilityMeasure μ]
    (z : H → Z) (hz : Measurable z)
    (hfac : PredictiveFactorization μ z hz) :
    PredictiveConditionalIndependence μ z hz := by
  let q0 : Kernel Z Y :=
    condDistrib
      (futureVar (H := H) (Y := Y))
      (statisticVar (Y := Y) z) μ
  have hcd := hasCondDistrib_future_historyGraph_of_factorization μ z hz hfac
  have hgraph :
      condDistrib
          (futureVar (H := H) (Y := Y))
          (fun p : H × Y => (z p.1, p.1)) μ
        =ᵐ[μ.map (fun p : H × Y => (z p.1, p.1))]
          Kernel.prodMkRight H q0 := by
    dsimp [q0]
    exact condDistrib_ae_eq_of_measure_eq_compProd
      (μ := μ)
      (Y := futureVar (H := H) (Y := Y))
      (fun p : H × Y => (z p.1, p.1))
      measurable_futureVar.aemeasurable
      (κ := Kernel.prodMkRight H q0)
      hcd.map_eq
  have hiff :=
    condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight
      (μ := μ)
      (f := futureVar (H := H) (Y := Y))
      (g := historyVar (H := H) (Y := Y))
      measurable_futureVar measurable_historyVar
      (k := statisticVar (Y := Y) z)
      (measurable_statisticVar (Y := Y) z hz)
  have hhistoryFirst :
      historyVar (H := H) (Y := Y) ⟂ᵢ[
        statisticVar (Y := Y) z,
        measurable_statisticVar (Y := Y) z hz;
        μ] futureVar (H := H) (Y := Y) := by
    apply hiff.mpr
    simpa [q0, statisticVar, historyVar] using hgraph
  exact hhistoryFirst.symm

end

end UEOT.V3.InformationPredictiveFactorization
