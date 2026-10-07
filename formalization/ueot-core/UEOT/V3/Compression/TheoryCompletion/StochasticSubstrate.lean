import UEOT.V3.FiniteCTMCPathKL
import UEOT.V3.GirsanovPathKL
import UEOT.V3.DiffusionHJBVerification
import UEOT.V3.RecoveryDynkin

/-!
# Theory Completion P11 — stochastic-calculus substrate boundary

P11 does not rebuild an SDE library for its own sake.  It exposes, in one typed
surface, the exact division already present in Core v3:

* the finite CTMC path-KL theorem is internally derived from the concrete jump
  path law and support inclusion;
* Girsanov KL consumes a `TerminalGirsanovData` process theorem;
* diffusion HJB verification consumes a `ControlFamily` whose runs already
  contain the process-specific Itô/localization output.

The wrappers below preserve these assumptions visibly.  No adapter conclusion
is inserted into a structure by P11.
-/

namespace UEOT.V3.Compression.TheoryCompletion

open MeasureTheory ProbabilityTheory InformationTheory
open UEOT.V3.FiniteCTMCPathKL
open UEOT.V3.GirsanovPathKL
open UEOT.V3.DiffusionHJBVerification
open CrooksJarzynski.MeasureProtocol.ContinuousTimeJump
open CrooksJarzynski.MeasureProtocol.ContinuousTimeJump.FiniteJumpGenerator

open scoped ENNReal

universe uX uΩ uΓ uE uA

/-- Internal finite-jump stochastic-analysis branch.  The only scientific
interface premise here is support inclusion between the two concrete finite
jump generators. -/
theorem p11_finiteCTMC_internal_pathKL
    {X : Type uX} [Fintype X] [DecidableEq X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (Gu G0 : FiniteJumpGenerator X) (T : NNReal) (x : X)
    (hsupport : SupportIncluded Gu G0) :
    klDiv (Gu.pathLawFrom T x) (G0.pathLawFrom T x) =
      ENNReal.ofReal
        (∫ γ,
          (∫ t : ℝ in (0 : ℝ)..(T : ℝ),
            ∑ j : X,
              ((Gu.jumpRate (FullPath.trajectory γ t) j : ℝ) *
                    jumpLogRatio Gu G0 (FullPath.trajectory γ t) j -
                (Gu.jumpRate (FullPath.trajectory γ t) j : ℝ) +
                (G0.jumpRate (FullPath.trajectory γ t) j : ℝ)))
          ∂Gu.pathLawFrom T x) :=
  p_kl_04 Gu G0 T x hsupport

/-- Girsanov branch with its process-specific terminal stochastic-calculus
certificate kept explicit. -/
theorem p11_girsanov_terminal_adapter
    {Ω : Type uΩ} [MeasurableSpace Ω]
    {Γ : Type uΓ} [MeasurableSpace Γ]
    {E : Type uE} [NormedAddCommGroup E] [MeasurableSpace E]
    {P0 Q : Measure Ω} {T : NNReal} {u : ℝ → Ω → E}
    [IsProbabilityMeasure P0] [IsProbabilityMeasure Q]
    (h : TerminalGirsanovData P0 Q T u)
    (statePath : Ω → Γ) (hstate : Measurable statePath) :
    klDiv Q P0 =
        ENNReal.ofReal
          ((2 : ℝ)⁻¹ * ∫ ω, controlEnergy T u ω ∂Q) ∧
      klDiv (Q.map statePath) (P0.map statePath) ≤
        ENNReal.ofReal
          ((2 : ℝ)⁻¹ * ∫ ω, controlEnergy T u ω ∂Q) :=
  h.p_kl_05 statePath hstate

/-- Diffusion HJB branch with the process-specific `ItoRun` family visible in
`F : M.ControlFamily Policy`.  P11 adds no claim that a symbolic generator alone
constructs those runs. -/
theorem p11_diffusionHJB_terminal_adapter
    {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [MeasurableSpace X] [BorelSpace X]
    {A : Type uA} [MeasurableSpace A]
    (M : DiffusionHJBVerification.Model X A)
    {Policy : Type*} (F : M.ControlFamily Policy) :
    F.IsOptimalValue :=
  DiffusionHJBVerification.p_ctl_03 M F

/-- **P11 terminal surface.**  It intentionally combines one internally derived
finite-jump formula with one terminal-adapter Girsanov result.  The theorem's
premises make the remaining lower-level stochastic obligation impossible to
hide behind the P11 label. -/
theorem p11_terminal_stochastic_substrate
    {X : Type uX} [Fintype X] [DecidableEq X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (Gu G0 : FiniteJumpGenerator X) (Tjump : NNReal) (x : X)
    (hsupport : SupportIncluded Gu G0)
    {Ω : Type uΩ} [MeasurableSpace Ω]
    {Γ : Type uΓ} [MeasurableSpace Γ]
    {E : Type uE} [NormedAddCommGroup E] [MeasurableSpace E]
    {P0 Q : Measure Ω} {Tdiff : NNReal} {u : ℝ → Ω → E}
    [IsProbabilityMeasure P0] [IsProbabilityMeasure Q]
    (hG : TerminalGirsanovData P0 Q Tdiff u)
    (statePath : Ω → Γ) (hstate : Measurable statePath) :
    (klDiv (Gu.pathLawFrom Tjump x) (G0.pathLawFrom Tjump x) =
      ENNReal.ofReal
        (∫ γ,
          (∫ t : ℝ in (0 : ℝ)..(Tjump : ℝ),
            ∑ j : X,
              ((Gu.jumpRate (FullPath.trajectory γ t) j : ℝ) *
                    jumpLogRatio Gu G0 (FullPath.trajectory γ t) j -
                (Gu.jumpRate (FullPath.trajectory γ t) j : ℝ) +
                (G0.jumpRate (FullPath.trajectory γ t) j : ℝ)))
          ∂Gu.pathLawFrom Tjump x)) ∧
    (klDiv Q P0 =
        ENNReal.ofReal
          ((2 : ℝ)⁻¹ * ∫ ω, controlEnergy Tdiff u ω ∂Q) ∧
      klDiv (Q.map statePath) (P0.map statePath) ≤
        ENNReal.ofReal
          ((2 : ℝ)⁻¹ * ∫ ω, controlEnergy Tdiff u ω ∂Q)) := by
  exact ⟨p11_finiteCTMC_internal_pathKL Gu G0 Tjump x hsupport,
    p11_girsanov_terminal_adapter hG statePath hstate⟩

end UEOT.V3.Compression.TheoryCompletion
