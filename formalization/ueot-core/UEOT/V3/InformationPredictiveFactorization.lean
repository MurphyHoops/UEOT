import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.HasCondDistrib
import Mathlib.Probability.Kernel.Disintegration.Unique

/-!
# P-INT-01 — general predictive factorization interface

This module develops the source-faithful Standard-Borel formulation of the
Predictive Factorization Characterization Theorem.  The canonical future law
is the regular conditional kernel `P(Y|H)`.  Exact factorization through a
measurable statistic `z : H → Z` means that this kernel is almost surely the
pullback of a Markov kernel on `Z`.

No countability assumption is imposed on the canonical predictive state here;
that restriction belongs to P-INFO-03, not to the general P-INT-01 theorem.
-/

namespace UEOT.V3.InformationPredictiveFactorization

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

universe uH uY uZ uΩ

variable {H : Type uH} {Y : Type uY} {Z : Type uZ}
variable [MeasurableSpace H] [MeasurableSpace Y] [MeasurableSpace Z]
variable [StandardBorelSpace H] [StandardBorelSpace Y]
variable [Nonempty Y]

/-- History coordinate on the joint sample space `H × Y`. -/
def historyVar : H × Y → H := Prod.fst

/-- Future coordinate on the joint sample space. -/
def futureVar : H × Y → Y := Prod.snd

/-- Lift a history statistic to the joint sample space. -/
def statisticVar (z : H → Z) : H × Y → Z := fun p => z p.1

lemma measurable_historyVar : Measurable (historyVar : H × Y → H) :=
  measurable_fst

lemma measurable_futureVar : Measurable (futureVar : H × Y → Y) :=
  measurable_snd

lemma measurable_statisticVar
    (z : H → Z) (hz : Measurable z) :
    Measurable (statisticVar (Y := Y) z) :=
  hz.comp measurable_fst

/-- Source condition (ii): the canonical future kernel `P(Y|H)` factors through
`z`.  A Markov kernel `q : Kernel Z Y` is the Lean form of the source's
measurable map `Ψ : Z → P(Y)`. -/
def PredictiveFactorization
    (μ : Measure (H × Y)) [IsProbabilityMeasure μ]
    (z : H → Z) (hz : Measurable z) : Prop :=
  ∃ q : Kernel Z Y, IsMarkovKernel q ∧
    μ.condKernel =ᵐ[μ.fst] q.comap z hz

/-- The canonical conditional distribution of the future given the history is
exactly the standard `condKernel` of the joint law, up to the unavoidable
`P_H`-a.e. choice of regular conditional versions. -/
theorem condDistrib_future_history_ae_eq_condKernel
    (μ : Measure (H × Y)) [IsProbabilityMeasure μ] :
    condDistrib (futureVar (H := H) (Y := Y))
        (historyVar (H := H) (Y := Y)) μ =ᵐ[μ.fst]
      μ.condKernel := by
  have hdis : μ.fst ⊗ₘ μ.condKernel = μ :=
    Measure.disintegrate μ μ.condKernel
  have hpair :
      (fun p : H × Y => (p.1, p.2)) = id := by
    funext p
    exact Prod.eta p
  have hjoint :
      μ.map (fun p : H × Y => (p.1, p.2)) =
        μ.map (fun p : H × Y => p.1) ⊗ₘ μ.condKernel := by
    rw [hpair, Measure.map_id]
    change μ = μ.fst ⊗ₘ μ.condKernel
    exact hdis.symm
  have h := condDistrib_ae_eq_of_measure_eq_compProd
    (μ := μ)
    (Y := futureVar (H := H) (Y := Y))
    (historyVar (H := H) (Y := Y))
    measurable_futureVar.aemeasurable
    (κ := μ.condKernel)
    hjoint
  simpa [Measure.fst, historyVar] using h

/-- Transport a composition-product along the graph embedding
`h ↦ (z h, h)` in its first coordinate.  The output kernel depends on the graph
point only through its history coordinate.  This is the measure-theoretic core
of the fact that adding a measurable function of a conditioning variable does
not change a conditional law. -/
theorem compProd_map_historyGraph
    (ν : Measure H) [SFinite ν]
    (κ : Kernel H Y) [IsSFiniteKernel κ]
    (z : H → Z) (hz : Measurable z) :
    (ν ⊗ₘ κ).map
        (fun p : H × Y => ((z p.1, p.1), p.2)) =
      (ν.map (fun h : H => (z h, h))) ⊗ₘ
        (κ.comap Prod.snd (measurable_snd : Measurable (Prod.snd : Z × H → H))) := by
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

/-- If `κ` is a conditional law of `Y` given `X`, then the same law pulled back
through the history projection is a conditional law given `(z(X), X)`. -/
theorem hasCondDistrib_historyGraph
    {Ω : Type uΩ} [MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P]
    (X : Ω → H) (Yv : Ω → Y)
    (κ : Kernel H Y) [IsSFiniteKernel κ]
    (h : HasCondDistrib Yv X κ P)
    (z : H → Z) (hz : Measurable z) :
    HasCondDistrib Yv (fun ω => (z (X ω), X ω))
      (κ.comap Prod.snd (measurable_snd : Measurable (Prod.snd : Z × H → H))) P := by
  let e : H → Z × H := fun x => (z x, x)
  have he : Measurable e := hz.prodMk measurable_id
  have hF : Measurable (fun p : H × Y => (e p.1, p.2)) :=
    (he.comp measurable_fst).prodMk measurable_snd
  refine ⟨?_, ?_⟩
  · exact (he.comp_aemeasurable h.aemeasurable_fst).prodMk h.aemeasurable_snd
  · calc
      P.map (fun ω => ((z (X ω), X ω), Yv ω)) =
          (P.map (fun ω => (X ω, Yv ω))).map
            (fun p : H × Y => ((z p.1, p.1), p.2)) := by
        rw [AEMeasurable.map_map_of_aemeasurable
          hF.aemeasurable h.aemeasurable]
        rfl
      _ = (P.map X ⊗ₘ κ).map
            (fun p : H × Y => ((z p.1, p.1), p.2)) := by
        rw [h.map_eq]
      _ = (P.map X).map (fun x : H => (z x, x)) ⊗ₘ
            (κ.comap Prod.snd
              (measurable_snd : Measurable (Prod.snd : Z × H → H))) := by
        exact compProd_map_historyGraph (P.map X) κ z hz
      _ = P.map (fun ω => (z (X ω), X ω)) ⊗ₘ
            (κ.comap Prod.snd
              (measurable_snd : Measurable (Prod.snd : Z × H → H))) := by
        rw [AEMeasurable.map_map_of_aemeasurable he.aemeasurable h.aemeasurable_fst]
        rfl

/-- The joint law `μ` itself witnesses that `μ.condKernel` is a conditional law
of the future coordinate given the history coordinate. -/
theorem hasCondDistrib_future_history_condKernel
    (μ : Measure (H × Y)) [IsProbabilityMeasure μ] :
    HasCondDistrib
      (futureVar (H := H) (Y := Y))
      (historyVar (H := H) (Y := Y))
      μ.condKernel μ := by
  refine ⟨measurable_historyVar.aemeasurable.prodMk measurable_futureVar.aemeasurable, ?_⟩
  have hpair :
      (fun p : H × Y =>
        (historyVar (H := H) (Y := Y) p, futureVar (H := H) (Y := Y) p)) = id := by
    funext p
    exact Prod.eta p
  rw [hpair, Measure.map_id]
  change μ = μ.fst ⊗ₘ μ.condKernel
  exact (Measure.disintegrate μ μ.condKernel).symm

/-- Adding the measurable statistic `z(H)` to the conditioning variable does
not change the future law beyond reindexing by the history projection. -/
theorem condDistrib_future_historyGraph_ae_eq_condKernel_comap
    (μ : Measure (H × Y)) [IsProbabilityMeasure μ]
    (z : H → Z) (hz : Measurable z) :
    condDistrib
        (futureVar (H := H) (Y := Y))
        (fun p : H × Y => (z p.1, p.1)) μ
      =ᵐ[μ.map (fun p : H × Y => (z p.1, p.1))]
        μ.condKernel.comap Prod.snd
          (measurable_snd : Measurable (Prod.snd : Z × H → H)) := by
  have hcd := hasCondDistrib_historyGraph
    (P := μ)
    (X := historyVar (H := H) (Y := Y))
    (Yv := futureVar (H := H) (Y := Y))
    (κ := μ.condKernel)
    (hasCondDistrib_future_history_condKernel μ)
    z hz
  exact condDistrib_ae_eq_of_measure_eq_compProd
    (μ := μ)
    (Y := futureVar (H := H) (Y := Y))
    (fun p : H × Y => (z p.1, p.1))
    measurable_futureVar.aemeasurable
    (κ := μ.condKernel.comap Prod.snd
      (measurable_snd : Measurable (Prod.snd : Z × H → H)))
    hcd.map_eq

/-- Push a composition-product through the statistic on its first coordinate
when the conditional kernel already factors through that statistic. -/
theorem compProd_map_statistic
    (ν : Measure H) [SFinite ν]
    (q : Kernel Z Y) [IsSFiniteKernel q]
    (z : H → Z) (hz : Measurable z) :
    (ν ⊗ₘ q.comap z hz).map (fun p : H × Y => (z p.1, p.2)) =
      (ν.map z) ⊗ₘ q := by
  have hF : Measurable (fun p : H × Y => (z p.1, p.2)) :=
    (hz.comp measurable_fst).prodMk measurable_snd
  ext s hs
  rw [Measure.map_apply hF hs]
  rw [Measure.compProd_apply (hF hs), Measure.compProd_apply hs]
  rw [lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hz]
  congr with h

/-- Under a predictive factorization witness `q`, that same kernel is a
conditional distribution of the future given the statistic `z(H)`. -/
theorem hasCondDistrib_future_statistic_of_factorization
    (μ : Measure (H × Y)) [IsProbabilityMeasure μ]
    (z : H → Z) (hz : Measurable z)
    (q : Kernel Z Y) [IsMarkovKernel q]
    (hfac : μ.condKernel =ᵐ[μ.fst] q.comap z hz) :
    HasCondDistrib
      (futureVar (H := H) (Y := Y))
      (statisticVar (Y := Y) z)
      q μ := by
  refine ⟨(measurable_statisticVar (Y := Y) z hz).aemeasurable.prodMk
    measurable_futureVar.aemeasurable, ?_⟩
  have hdis : μ.fst ⊗ₘ μ.condKernel = μ :=
    Measure.disintegrate μ μ.condKernel
  have hcomp :
      μ.fst ⊗ₘ μ.condKernel = μ.fst ⊗ₘ q.comap z hz :=
    Measure.compProd_congr hfac
  calc
    μ.map (fun p : H × Y =>
        (statisticVar (Y := Y) z p, futureVar (H := H) (Y := Y) p)) =
        μ.map (fun p : H × Y => (z p.1, p.2)) := by rfl
    _ = (μ.fst ⊗ₘ μ.condKernel).map
          (fun p : H × Y => (z p.1, p.2)) := by rw [hdis]
    _ = (μ.fst ⊗ₘ q.comap z hz).map
          (fun p : H × Y => (z p.1, p.2)) := by rw [hcomp]
    _ = μ.fst.map z ⊗ₘ q := compProd_map_statistic μ.fst q z hz
    _ = μ.map (statisticVar (Y := Y) z) ⊗ₘ q := by
      unfold statisticVar Measure.fst
      rw [Measure.map_map hz measurable_fst]
      rfl

/-- Consequently the regular conditional distribution `P(Y|z(H))` is the
factorization kernel `q`, up to the usual almost-sure version choice. -/
theorem condDistrib_future_statistic_ae_eq_of_factorization
    (μ : Measure (H × Y)) [IsProbabilityMeasure μ]
    (z : H → Z) (hz : Measurable z)
    (q : Kernel Z Y) [IsMarkovKernel q]
    (hfac : μ.condKernel =ᵐ[μ.fst] q.comap z hz) :
    condDistrib
      (futureVar (H := H) (Y := Y))
      (statisticVar (Y := Y) z) μ
      =ᵐ[μ.map (statisticVar (Y := Y) z)] q := by
  have hcd := hasCondDistrib_future_statistic_of_factorization
    μ z hz q hfac
  exact condDistrib_ae_eq_of_measure_eq_compProd
    (μ := μ)
    (Y := futureVar (H := H) (Y := Y))
    (statisticVar (Y := Y) z)
    measurable_futureVar.aemeasurable
    (κ := q)
    hcd.map_eq

end

end UEOT.V3.InformationPredictiveFactorization
