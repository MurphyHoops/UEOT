import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianContinuousAdaptedInputs
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianLiteralGridLimit

/-!
Original commitment: actual continuous integral QV needs a SAME-input limit, not only changing literal-record error arrays.
Existing result: actual bounded continuous-adapted left inputs, literal grid/dt energy limit, and grid-uniform L1 input stability.
Premise reduced: derive actual UNIFORM-clock QV limit for the constructed original bounded continuous-adapted input.
Model/witness: SAME sourceLaw/inputLaw T/naturalFiltration, actual joint measurable AE-continuous H with true all-time bound K.
Consumer: scalar Ito and full predictable L2 density extension; arbitrary caller partition/general-input limits remain separate.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedContinuousQV
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianMartingaleSource BrownianIntegralClosure BrownianPredictableDensity
open BrownianIntegralContinuousVersion BrownianIntegralTimeEnergy BrownianIntegralEnergyL1 BrownianIntegralGridL1
open BrownianQuadraticVariation BrownianContinuousAdaptedInputs BrownianLiteralGridLimit
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- True SAME-input QV, in native source L1, on the actually constructed
uniformClock family. It is derived by original finite data and genuine L2/L1
stability, with no additional QV or compensator hypothesis. -/
theorem boundedContinuous_uniform_QV (T : ℝ≥0) (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ)
    (hjoint : Measurable (Function.uncurry H)) (hadapt : StronglyAdapted naturalFiltration H)
    (hcont : ∀ᵐ ω ∂sourceLaw, Continuous (fun u => H u ω))
    (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ u ω, ‖H u ω‖ ≤ K) :
    Tendsto (fun n => gridSquares T (uniformClock T n)
      (continuousPredictableInput T H hjoint hadapt hcont K hK hbound)) atTop
      (𝓝 (energyClass T T (continuousPredictableInput T H hjoint hadapt hcont K hK hbound))) := by
  let r := leftRecord T H hadapt K hbound
  let f := continuousPredictableInput T H hjoint hadapt hcont K hK hbound
  let g (n : ℕ) := literalPredictableInput (r n)
  have hg : Tendsto g atTop (𝓝 f) :=
    tendsto_subtype_rng.mpr (left_inputClass_tendsto T H hjoint hadapt hcont K hK hbound)
  have hrow : ∀ n i, ∀ᵐ ω ∂sourceLaw, |(r n).coefficient i ω| ≤ K := by
    intro n i
    apply Eventually.of_forall
    intro ω
    exact (Real.norm_eq_abs _).symm ▸ hbound (uniformClock T n i.castSucc) ω
  have hrowMesh : Tendsto (fun n => (mesh (r n).clock : ℝ)) atTop (𝓝 0) := uniformClock_mesh_tendsto T
  have hL := literal_grid_error_tendsto T r K hK hrow hrowMesh
  change Tendsto (fun n => gridSquares T (uniformClock T n) (g n)-energyClass T T (g n)) atTop (𝓝 0) at hL
  have hbound0 : Tendsto (fun n => ‖f-g n‖*(‖f‖+‖g n‖)) atTop (𝓝 0) := by
    have hd : Tendsto (fun n => ‖f-g n‖) atTop (𝓝 0) := by
      simpa only [sub_self,norm_zero] using ((tendsto_const_nhds (x := f)).sub hg).norm
    simpa only [zero_mul] using hd.mul ((tendsto_const_nhds (x := ‖f‖)).add hg.norm)
  have hD : Tendsto (fun n => gridSquares T (uniformClock T n) f-gridSquares T (uniformClock T n) (g n))
      atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    exact squeeze_zero (fun _ => norm_nonneg _)
      (fun n => gridSquares_sub_norm_le T (uniformClock T n) (uniformClock_mono T n)
        (uniformClock_zero T n) (uniformClock_end T n) f (g n)) hbound0
  have hA : Tendsto (fun n => energyClass T T (g n)-energyClass T T f) atTop (𝓝 0) := by
    simpa only [sub_self] using (energyClass_tendsto T T hg).sub (tendsto_const_nhds (x := energyClass T T f))
  have hE : Tendsto (fun n => gridSquares T (uniformClock T n) f-energyClass T T f) atTop (𝓝 0) := by
    have h := (hD.add hL).add hA
    have he (n : ℕ) :
        (gridSquares T (uniformClock T n) f-gridSquares T (uniformClock T n) (g n)+
          (gridSquares T (uniformClock T n) (g n)-energyClass T T (g n)))+
            (energyClass T T (g n)-energyClass T T f) =
              gridSquares T (uniformClock T n) f-energyClass T T f := by abel
    have h' := (tendsto_congr' (Eventually.of_forall he)).mp h
    simpa only [add_zero] using h'
  simpa only [sub_add_cancel,zero_add] using hE.add_const (energyClass T T f)

/-- The limit just derived is the actual finite path-square sum of the SAME
continuousIntegralProcess, converging in measure to its SAME actual dt energy. -/
theorem boundedContinuous_uniform_QV_inMeasure (T : ℝ≥0) (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ)
    (hjoint : Measurable (Function.uncurry H)) (hadapt : StronglyAdapted naturalFiltration H)
    (hcont : ∀ᵐ ω ∂sourceLaw, Continuous (fun u => H u ω))
    (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ u ω, ‖H u ω‖ ≤ K) :
    TendstoInMeasure sourceLaw (fun n ω => ∑ i : Fin (n+1),
      (continuousIntegralProcess T (continuousPredictableInput T H hjoint hadapt hcont K hK hbound)
          (uniformClock T n i.succ) ω-
        continuousIntegralProcess T (continuousPredictableInput T H hjoint hadapt hcont K hK hbound)
          (uniformClock T n i.castSucc) ω)^2) atTop
      (timeEnergy T (continuousPredictableInput T H hjoint hadapt hcont K hK hbound) T) :=
  TendstoInMeasure.congr (fun n => gridSquares_coe T (uniformClock T n) _)
    (energyClass_coe T T _) (tendstoInMeasure_of_tendsto_Lp
      (boundedContinuous_uniform_QV T H hjoint hadapt hcont K hK hbound))

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedContinuousQV
