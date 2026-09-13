import UEOT.V3.InformationPInt01
import UEOT.V3.PredictionAE
import Mathlib.Probability.Kernel.Disintegration.Unique

/-!
# P-INT-01 — countable intervention family and common versions

This module adds the Core 3.0 common-protocol clause to the single-protocol
predictive-factorization equivalence. Protocols share a history law `ν` and
have response kernels `K i : Kernel H Y`; the protocol joint law is
`ν ⊗ₘ K i`. For a countable protocol family, protocolwise almost-sure
factorizations are put on one common conull set and assembled into the
canonical protocol predictive state already formalized in `PredictionAE`.
-/

namespace UEOT.V3.InformationPInt01Common

noncomputable section

open MeasureTheory ProbabilityTheory
open UEOT.V3.InformationPredictiveFactorization
open UEOT.V3.InformationPInt01
open UEOT.V3.PredictionAE

universe uH uY uZ uI uHS uHE uM uU

variable {H : Type uH} {Y : Type uY} {Z : Type uZ} {I : Type uI}
variable [MeasurableSpace H] [MeasurableSpace Y] [MeasurableSpace Z]
variable [StandardBorelSpace H] [StandardBorelSpace Y]
variable [Nonempty H] [Nonempty Y]

/-- Conditional-independence closure for one protocol whose response kernel is
`κ` and whose history marginal is the common reference law `ν`. -/
def ProtocolClosureAt
    (ν : Measure H) [IsProbabilityMeasure ν]
    (κ : Kernel H Y) (hκ : IsMarkovKernel κ)
    (z : H → Z) (hz : Measurable z) : Prop := by
  letI : IsMarkovKernel κ := hκ
  exact PredictiveConditionalIndependence (ν ⊗ₘ κ) z hz

/-- Kernel factorization for one protocol under the common history law. -/
def ProtocolFactorizationAt
    (ν : Measure H)
    (κ : Kernel H Y)
    (z : H → Z) (hz : Measurable z) : Prop :=
  ∃ q : Kernel Z Y, IsMarkovKernel q ∧
    κ =ᵐ[ν] q.comap z hz

/-- The joint-law single-protocol theorem is exactly the response-kernel
factorization theorem when the joint law is `ν ⊗ₘ κ`. -/
theorem protocolClosureAt_iff_factorization
    (ν : Measure H) [IsProbabilityMeasure ν]
    (κ : Kernel H Y) (hκ : IsMarkovKernel κ)
    (z : H → Z) (hz : Measurable z) :
    ProtocolClosureAt ν κ hκ z hz ↔
      ProtocolFactorizationAt ν κ z hz := by
  letI : IsMarkovKernel κ := hκ
  let ρ : Measure (H × Y) := ν ⊗ₘ κ
  letI : IsProbabilityMeasure ρ := by
    dsimp [ρ]
    infer_instance
  have hfst : ρ.fst = ν := by
    dsimp [ρ]
    exact Measure.fst_compProd ν κ
  have hmeasure : ρ = ρ.fst ⊗ₘ κ := by
    calc
      ρ = ν ⊗ₘ κ := by rfl
      _ = ρ.fst ⊗ₘ κ := by rw [hfst]
  have hkcond : κ =ᵐ[ρ.fst] ρ.condKernel :=
    ProbabilityTheory.eq_condKernel_of_measure_eq_compProd
      (ρ := ρ) κ hmeasure
  rw [hfst] at hkcond
  have hcond : ρ.condKernel =ᵐ[ν] κ := hkcond.symm
  have hsingle := predictiveConditionalIndependence_iff_factorization ρ z hz
  constructor
  · intro hclose
    have hρclose : PredictiveConditionalIndependence ρ z hz := by
      simpa [ProtocolClosureAt, ρ] using hclose
    rcases hsingle.mp hρclose with ⟨q, hq, hfac⟩
    have hfacν : ρ.condKernel =ᵐ[ν] q.comap z hz := by
      simpa [hfst] using hfac
    exact ⟨q, hq, hcond.symm.trans hfacν⟩
  · rintro ⟨q, hq, hfac⟩
    have hρfacν : ρ.condKernel =ᵐ[ν] q.comap z hz :=
      hcond.trans hfac
    have hρfac : ρ.condKernel =ᵐ[ρ.fst] q.comap z hz := by
      simpa [hfst] using hρfacν
    have hρclose : PredictiveConditionalIndependence ρ z hz :=
      hsingle.mpr ⟨q, hq, hρfac⟩
    simpa [ProtocolClosureAt, ρ] using hρclose

/-- All protocols satisfy the conditional-independence closure condition. -/
def CommonProtocolClosure
    (ν : Measure H) [IsProbabilityMeasure ν]
    (K : I → Kernel H Y)
    (hK : ∀ i, IsMarkovKernel (K i))
    (z : H → Z) (hz : Measurable z) : Prop :=
  ∀ i, ProtocolClosureAt ν (K i) (hK i) z hz

/-- Protocolwise factorization through the same statistic, before the countable
family is placed on one common conull set. -/
def CommonProtocolFactorization
    (ν : Measure H)
    (K : I → Kernel H Y)
    (z : H → Z) (hz : Measurable z) : Prop :=
  ∃ L : I → Kernel Z Y,
    (∀ i, IsMarkovKernel (L i)) ∧
    ∀ i, K i =ᵐ[ν] (L i).comap z hz

/-- Core 3.0 common-version factorization: the same protocol decoder family
works simultaneously outside one null set. -/
def CommonVersionFactorization
    (ν : Measure H)
    (K : I → Kernel H Y)
    (z : H → Z) : Prop :=
  ∃ L : I → Kernel Z Y,
    (∀ i, IsMarkovKernel (L i)) ∧
    ∀ᵐ h ∂ν, ∀ i, K i h = L i (z h)

/-- Protocolwise closure is equivalent to protocolwise kernel factorization.
Countability is not needed for this logical equivalence. -/
theorem commonProtocolClosure_iff_factorization
    (ν : Measure H) [IsProbabilityMeasure ν]
    (K : I → Kernel H Y)
    (hK : ∀ i, IsMarkovKernel (K i))
    (z : H → Z) (hz : Measurable z) :
    CommonProtocolClosure ν K hK z hz ↔
      CommonProtocolFactorization ν K z hz := by
  constructor
  · intro hclose
    have hi : ∀ i, ProtocolFactorizationAt ν (K i) z hz := by
      intro i
      exact (protocolClosureAt_iff_factorization ν (K i) (hK i) z hz).mp (hclose i)
    choose L hLmarkov hLfac using hi
    exact ⟨L, hLmarkov, hLfac⟩
  · rintro ⟨L, hLmarkov, hLfac⟩ i
    exact (protocolClosureAt_iff_factorization ν (K i) (hK i) z hz).mpr
      ⟨L i, hLmarkov i, hLfac i⟩

/-- For a countable family, protocolwise factorization is equivalent to one
common almost-sure version valid for every protocol simultaneously. -/
theorem commonProtocolFactorization_iff_commonVersion
    [Countable I]
    (ν : Measure H)
    (K : I → Kernel H Y)
    (z : H → Z) (hz : Measurable z) :
    CommonProtocolFactorization ν K z hz ↔
      CommonVersionFactorization ν K z := by
  constructor
  · rintro ⟨L, hLmarkov, hLfac⟩
    have hL : ∀ i, ∀ᵐ h ∂ν, K i h = L i (z h) := by
      intro i
      filter_upwards [hLfac i] with h hh
      simpa [Kernel.comap_apply] using hh
    exact ⟨L, hLmarkov, ae_all_iff.mpr hL⟩
  · rintro ⟨L, hLmarkov, hcommon⟩
    refine ⟨L, hLmarkov, ?_⟩
    intro i
    filter_upwards [hcommon] with h hh
    simpa [Kernel.comap_apply] using hh i

/-- **Core 3.0 common-protocol characterization.** For a countable protocol
family, conditional independence for every protocol is equivalent to one
protocol decoder family that represents all response kernels on a single
common conull set. -/
theorem commonProtocolClosure_iff_commonVersion
    [Countable I]
    (ν : Measure H) [IsProbabilityMeasure ν]
    (K : I → Kernel H Y)
    (hK : ∀ i, IsMarkovKernel (K i))
    (z : H → Z) (hz : Measurable z) :
    CommonProtocolClosure ν K hK z hz ↔
      CommonVersionFactorization ν K z := by
  exact (commonProtocolClosure_iff_factorization ν K hK z hz).trans
    (commonProtocolFactorization_iff_commonVersion ν K z hz)

/-- The common factorization can be packaged as one measurable decoder into the
full canonical intervention predictive state `h ↦ (i ↦ K i h)`. -/
theorem commonProtocolClosure_common_decoder
    [Countable I]
    (ν : Measure H) [IsProbabilityMeasure ν]
    (K : I → Kernel H Y)
    (hK : ∀ i, IsMarkovKernel (K i))
    (z : H → Z) (hz : Measurable z)
    (hclose : CommonProtocolClosure ν K hK z hz) :
    ∃ decoder : Z → (I → Measure Y), Measurable decoder ∧
      ∀ᵐ h ∂ν, (fun i => K i h) = decoder (z h) := by
  rcases (commonProtocolClosure_iff_factorization ν K hK z hz).mp hclose with
    ⟨L, hLmarkov, hLfac⟩
  have hL : ∀ i, ∀ᵐ h ∂ν, K i h = L i (z h) := by
    intro i
    filter_upwards [hLfac i] with h hh
    simpa [Kernel.comap_apply] using hh
  exact PredictionAE.common_factorization ν K z L hL

section Structured

variable {HS : Type uHS} {HE : Type uHE} {M : Type uM} {U : Type uU}
variable [MeasurableSpace HS] [MeasurableSpace HE]
variable [MeasurableSpace M] [MeasurableSpace U]
variable [StandardBorelSpace HS] [StandardBorelSpace HE]
variable [StandardBorelSpace M] [StandardBorelSpace U]
variable [Nonempty HS] [Nonempty HE]

/-- Core 3.0 structured common-protocol closure with
`H=(H^S,H^E)` and statistic `(M,U)=(f(H^S),g(H^E))`. -/
def StructuredCommonProtocolClosure
    (ν : Measure (HS × HE)) [IsProbabilityMeasure ν]
    (K : I → Kernel (HS × HE) Y)
    (hK : ∀ i, IsMarkovKernel (K i))
    (f : HS → M) (hf : Measurable f)
    (g : HE → U) (hg : Measurable g) : Prop :=
  CommonProtocolClosure ν K hK (structuredStatistic f g)
    (measurable_structuredStatistic f g hf hg)

/-- Structured Core 3.0 common-version factorization through `(M,U)`. -/
def StructuredCommonVersionFactorization
    (ν : Measure (HS × HE))
    (K : I → Kernel (HS × HE) Y)
    (f : HS → M) (g : HE → U) : Prop :=
  ∃ L : I → Kernel (M × U) Y,
    (∀ i, IsMarkovKernel (L i)) ∧
    ∀ᵐ h ∂ν, ∀ i, K i h = L i (f h.1, g h.2)

/-- **Core 3.0 P-INT-01 — countable common-version theorem.**
For `H=(H^S,H^E)`, `M=f(H^S)`, `U=g(H^E)`, and a finite/countable protocol
family, protocolwise `Y_i ⟂ H | (M,U)` holds iff all canonical future-law
coordinates factor through `(M,U)` on one common conull set. -/
theorem p_int_01
    [Countable I]
    (ν : Measure (HS × HE)) [IsProbabilityMeasure ν]
    (K : I → Kernel (HS × HE) Y)
    (hK : ∀ i, IsMarkovKernel (K i))
    (f : HS → M) (hf : Measurable f)
    (g : HE → U) (hg : Measurable g) :
    StructuredCommonProtocolClosure ν K hK f hf g hg ↔
      StructuredCommonVersionFactorization ν K f g := by
  unfold StructuredCommonProtocolClosure StructuredCommonVersionFactorization
  exact commonProtocolClosure_iff_commonVersion
    ν K hK (structuredStatistic f g) (measurable_structuredStatistic f g hf hg)

/-- State-valued form of the right-hand side of Core 3.0 P-INT-01. -/
theorem p_int_01_common_decoder
    [Countable I]
    (ν : Measure (HS × HE)) [IsProbabilityMeasure ν]
    (K : I → Kernel (HS × HE) Y)
    (hK : ∀ i, IsMarkovKernel (K i))
    (f : HS → M) (hf : Measurable f)
    (g : HE → U) (hg : Measurable g)
    (hclose : StructuredCommonProtocolClosure ν K hK f hf g hg) :
    ∃ decoder : (M × U) → (I → Measure Y), Measurable decoder ∧
      ∀ᵐ h ∂ν, (fun i => K i h) = decoder (f h.1, g h.2) := by
  exact commonProtocolClosure_common_decoder
    ν K hK (structuredStatistic f g) (measurable_structuredStatistic f g hf hg) hclose

end Structured

end

end UEOT.V3.InformationPInt01Common
