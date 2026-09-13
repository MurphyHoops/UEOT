import UEOT.V3.InformationPredictiveFactorizationForward

/-!
# P-INT-01 — conditional independence implies predictive factorization

The reverse direction compares two versions of `P(Y | z(H), H)` on the graph
law of `(z(H),H)`: one obtained from conditional independence and one obtained
by the fact that adding a measurable function of `H` does not refine the
history-conditional law.  Pulling the resulting equality back along the graph
map gives `P(Y|H)=P(Y|z(H))∘z` almost surely.
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

/-- Generic reverse half of the source Predictive Factorization
Characterization Theorem. -/
theorem factorization_of_predictiveConditionalIndependence
    (μ : Measure (H × Y)) [IsProbabilityMeasure μ]
    (z : H → Z) (hz : Measurable z)
    (hci : PredictiveConditionalIndependence μ z hz) :
    PredictiveFactorization μ z hz := by
  let q0 : Kernel Z Y :=
    condDistrib
      (futureVar (H := H) (Y := Y))
      (statisticVar (Y := Y) z) μ
  let e : H → Z × H := fun h => (z h, h)
  have he : Measurable e := hz.prodMk measurable_id
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
    exact hci.symm
  have hind :
      condDistrib
          (futureVar (H := H) (Y := Y))
          (fun p : H × Y =>
            (statisticVar (Y := Y) z p, historyVar (H := H) (Y := Y) p)) μ
        =ᵐ[μ.map (fun p : H × Y =>
          (statisticVar (Y := Y) z p, historyVar (H := H) (Y := Y) p))]
          Kernel.prodMkRight H q0 := by
    dsimp [q0]
    exact hiff.mp hhistoryFirst
  have href := condDistrib_future_historyGraph_ae_eq_condKernel_comap μ z hz
  have hgraph :
      μ.condKernel.comap Prod.snd
          (measurable_snd : Measurable (Prod.snd : Z × H → H))
        =ᵐ[μ.map (fun p : H × Y => (z p.1, p.1))]
          Kernel.prodMkRight H q0 := by
    filter_upwards [href, hind] with zh href_zh hind_zh
    exact href_zh.symm.trans hind_zh
  have hgraphLaw := historyGraph_map_eq_fst_map μ z hz
  rw [hgraphLaw] at hgraph
  have hpull :
      ∀ᵐ h ∂μ.fst,
        (μ.condKernel.comap Prod.snd
            (measurable_snd : Measurable (Prod.snd : Z × H → H))) (e h) =
          (Kernel.prodMkRight H q0) (e h) :=
    ae_of_ae_map he.aemeasurable hgraph
  refine ⟨q0, inferInstance, ?_⟩
  filter_upwards [hpull] with h hh
  simpa [e, Kernel.comap_apply, Kernel.prodMkRight_apply] using hh

/-- **Generic P-INT-01 characterization.**  For a measurable history statistic
`z`, future/history conditional independence given `z(H)` is equivalent to the
canonical predictive kernel factoring measurably through `z`. -/
theorem predictiveConditionalIndependence_iff_factorization
    (μ : Measure (H × Y)) [IsProbabilityMeasure μ]
    (z : H → Z) (hz : Measurable z) :
    PredictiveConditionalIndependence μ z hz ↔
      PredictiveFactorization μ z hz := by
  constructor
  · exact factorization_of_predictiveConditionalIndependence μ z hz
  · exact predictiveConditionalIndependence_of_factorization μ z hz

end

end UEOT.V3.InformationPredictiveFactorization
