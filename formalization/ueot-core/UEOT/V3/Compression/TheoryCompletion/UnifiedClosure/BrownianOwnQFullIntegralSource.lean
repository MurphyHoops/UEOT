import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQPredictableDensity

/-!
Original commitment: every genuine original-Fs own-Q predictable L2 input needs its actual returned integral/process/energy without closure membership hypotheses.
Existing result: native full predictable Q-L2 is proved exactly equal to actual elementary closure, with existing own-Q isometry and originalFs conditional process.
Premise reduced: exact same native-class inclusion composes the existing returned integral and process for arbitrary genuine full inputs.
Model/witness: SAME Q_A/W, original Fs, arbitrary horizon U incl U>A/U0; no law transport, alternate output or natural-filtration equality.
Consumer/boundary: arbitrary full Q input actual martingale/cutoff energy and literal finite agreement; no continuous modification asserted here.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQFullIntegralSource
open MeasureTheory ProbabilityTheory Set Filter
open BrownianTimeIntegrand BrownianPredictableInputs BrownianIntegralClosure BrownianMartingaleSource
open BrownianBoundedExponentialLimitSource BrownianOwnQTimeInput BrownianOwnQPredictableDensity
open BrownianOwnQIntegralClosure BrownianOwnQTimeTruncation
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
variable (A : ℝ≥0) (f : fullPredictableL2 A) (K : ℝ) (hK : 0≤K)
    (hF : ∀ᵐ p ∂inputLaw A, |(f : Lp ℝ 2 (inputLaw A)) p|≤K)

/-- Identity on the actual dtU×Q native class; only the PROVED membership changes. -/
def domainIsometry (U : ℝ≥0) : fullPredictableL2Q A f U→ₗᵢ[ℝ] integralDomain A f K hK hF U where
  toFun g:=⟨g.val,fullPredictableL2Q_le_domain A f K hK hF U g.property⟩
  map_add' _ _:=rfl
  map_smul' _ _:=rfl
  norm_map' _:=rfl

def fullIntegral (U : ℝ≥0) : fullPredictableL2Q A f U→L[ℝ] Lp ℝ 2 (fullLaw A f) :=
  (integral A f K hK hF U).comp (domainIsometry A f K hK hF U).toContinuousLinearMap

theorem fullIntegral_norm (U : ℝ≥0) (g : fullPredictableL2Q A f U) : ‖fullIntegral A f K hK hF U g‖=‖g‖ :=
  integral_norm A f K hK hF U (domainIsometry A f K hK hF U g)

def fullIntegralProcess (U : ℝ≥0) (g : fullPredictableL2Q A f U) : ℝ≥0→(ℝ≥0→ℝ)→ℝ :=
  BrownianOwnQIntegralMartingale.integralProcess A f K hK hF U (domainIsometry A f K hK hF U g)

theorem fullIntegralProcess_martingale (U : ℝ≥0) (g : fullPredictableL2Q A f U) :
    Martingale (fullIntegralProcess A f K hK hF U g) naturalFiltration (fullLaw A f) :=
  BrownianOwnQIntegralMartingale.integralProcess_martingale A f K hK hF U (domainIsometry A f K hK hF U g)

theorem fullIntegralProcess_stronglyAdapted (U : ℝ≥0) (g : fullPredictableL2Q A f U) :
    StronglyAdapted naturalFiltration (fullIntegralProcess A f K hK hF U g) :=
  (fullIntegralProcess_martingale A f K hK hF U g).stronglyAdapted

theorem fullIntegralProcess_energy (U u : ℝ≥0) (g : fullPredictableL2Q A f U) :
    (∫ ω,fullIntegralProcess A f K hK hF U g u ω^2 ∂fullLaw A f)=
      ∫ p in BrownianIntegralTimeTruncation.timeSet U u,(g : Lp ℝ 2 (inputLawQ A f U)) p^2 ∂inputLawQ A f U :=
  BrownianOwnQIntegralMartingale.integralProcess_energy A f K hK hF U u (domainIsometry A f K hK hF U g)

theorem fullIntegralProcess_horizon (U : ℝ≥0) (g : fullPredictableL2Q A f U) :
    fullIntegralProcess A f K hK hF U g U=ᵐ[fullLaw A f] fullIntegral A f K hK hF U g :=
  BrownianOwnQIntegralMartingale.integralProcess_horizon A f K hK hF U (domainIsometry A f K hK hF U g)

theorem fullIntegralProcess_zero (U : ℝ≥0) (g : fullPredictableL2Q A f U) :
    fullIntegralProcess A f K hK hF U g 0=ᵐ[fullLaw A f] 0 :=
  BrownianOwnQIntegralMartingale.integralProcess_zero A f K hK hF U (domainIsometry A f K hK hF U g)

/-- Actual full-domain integral still returns each ORIGINAL literal table output. -/
def elementaryInputQ {U : ℝ≥0} (r : ElementaryInput U) : fullPredictableL2Q A f U :=
  ⟨inputValueQ A f K hK hF r,elementary_input_predictable_Q A f K hK hF r⟩

theorem fullIntegral_returns_literal {U : ℝ≥0} (r : ElementaryInput U) :
    fullIntegral A f K hK hF U (elementaryInputQ A f K hK hF r)=outputValueQ A f K hK hF r := by
  change integral A f K hK hF U (domainIsometry A f K hK hF U (elementaryInputQ A f K hK hF r))=_
  have he : domainIsometry A f K hK hF U (elementaryInputQ A f K hK hF r)=representedInput A f K hK hF r := Subtype.ext rfl
  rw[he,BrownianOwnQIntegralClosure.integral_returns_literal]

theorem fullIntegralProcess_conditional (U u : ℝ≥0) (g : fullPredictableL2Q A f U) :
    fullIntegralProcess A f K hK hF U g u=(fullLaw A f)[fullIntegral A f K hK hF U g|naturalFiltration u] := rfl

/-- Zero horizon needs no division/nondegeneracy exception. -/
theorem fullIntegral_zero_horizon (g : fullPredictableL2Q A f 0) : fullIntegral A f K hK hF 0 g=0 := by
  apply Lp.ext
  exact (fullIntegralProcess_horizon A f K hK hF 0 g).symm.trans
    ((fullIntegralProcess_zero A f K hK hF 0 g).trans (Lp.coeFn_zero ℝ 2 (fullLaw A f)).symm)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQFullIntegralSource
