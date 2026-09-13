import UEOT.V3.InformationPredictiveFactorizationReverse

/-!
# P-INT-01 — single-protocol structured factorization core

This module specializes the generic factorization theorem to the UEOT Core 3.0
structured decomposition

`H = (Hˢ,Hᵉ)`, `M=f(Hˢ)`, `U=g(Hᵉ)`, `Z=(M,U)`.

It proves the single-protocol kernel equivalence underlying P-INT-01.  The full
Core 3.0 P-INT-01 additionally requires the countable intervention-family
common-version clause; that layer is formalized separately before promotion.
-/

namespace UEOT.V3.InformationPInt01

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open UEOT.V3.InformationPredictiveFactorization

universe uHS uHE uM uU uY

variable {HS : Type uHS} {HE : Type uHE}
variable {M : Type uM} {U : Type uU} {Y : Type uY}
variable [MeasurableSpace HS] [MeasurableSpace HE]
variable [MeasurableSpace M] [MeasurableSpace U] [MeasurableSpace Y]
variable [StandardBorelSpace HS] [StandardBorelSpace HE]
variable [StandardBorelSpace M] [StandardBorelSpace U]
variable [StandardBorelSpace Y]
variable [Nonempty HS] [Nonempty HE] [Nonempty Y]

/-- The Core 3.0 statistic `Z=(M,U)` built from internal and environmental
history summaries. -/
def structuredStatistic
    (f : HS → M) (g : HE → U) : HS × HE → M × U :=
  fun h => (f h.1, g h.2)

lemma measurable_structuredStatistic
    (f : HS → M) (g : HE → U)
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (structuredStatistic f g) :=
  (hf.comp measurable_fst).prodMk (hg.comp measurable_snd)

/-- Single-protocol condition (i): `Y ⟂ H | (M,U)`. -/
def StructuredPredictiveClosure
    (μ : Measure ((HS × HE) × Y)) [IsProbabilityMeasure μ]
    (f : HS → M) (g : HE → U)
    (hf : Measurable f) (hg : Measurable g) : Prop :=
  PredictiveConditionalIndependence μ
    (structuredStatistic f g)
    (measurable_structuredStatistic f g hf hg)

/-- Single-protocol condition (ii): the canonical predictive state
`C⋆=Law(Y|H)` factors measurably through `(M,U)`. -/
def StructuredPredictiveFactorization
    (μ : Measure ((HS × HE) × Y)) [IsProbabilityMeasure μ]
    (f : HS → M) (g : HE → U)
    (hf : Measurable f) (hg : Measurable g) : Prop :=
  ∃ ψ : Kernel (M × U) Y, IsMarkovKernel ψ ∧
    μ.condKernel =ᵐ[μ.fst]
      ψ.comap (structuredStatistic f g)
        (measurable_structuredStatistic f g hf hg)

/-- **Single-protocol core lemma for P-INT-01.**

For standard-Borel variables with `H=(Hˢ,Hᵉ)`, `M=f(Hˢ)`, `U=g(Hᵉ)`, the
structured predictive-closure condition `Y ⟂ H | (M,U)` holds iff the canonical
predictive law `C⋆=Law(Y|H)` factors measurably through `(M,U)`.

This theorem alone is not the full counted Core 3.0 P-INT-01: the latter also
requires the common-version statement for every protocol in a countable
intervention family. -/
theorem p_int_01_single_protocol
    (μ : Measure ((HS × HE) × Y)) [IsProbabilityMeasure μ]
    (f : HS → M) (g : HE → U)
    (hf : Measurable f) (hg : Measurable g) :
    StructuredPredictiveClosure μ f g hf hg ↔
      StructuredPredictiveFactorization μ f g hf hg := by
  unfold StructuredPredictiveClosure StructuredPredictiveFactorization
  exact predictiveConditionalIndependence_iff_factorization
    μ (structuredStatistic f g) (measurable_structuredStatistic f g hf hg)

end

end UEOT.V3.InformationPInt01
