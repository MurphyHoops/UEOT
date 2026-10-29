import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteSpanLeftInputs
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianLiteralGridLimit

/-!
Original commitment: actual same-input QV must cover ORIGINAL full predictable L2, not only bounded continuous inputs.
Existing result: native finite-span density, same-input causal left approximants, exact literal QV and grid/energy L1 stability.
Premise reduced: derive uniform-clock QV for EVERY original fullPredictableL2 input without L4 or extra regularity.
Model/witness: SAME inputLaw T/sourceLaw/naturalFiltration and same continuousIntegralProcess/timeEnergy, including T=0.
Consumer: actual scalar Ito source; arbitrary caller partitions and general C2 Ito remain separate subsequent obligations.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFullInputQV
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianMartingaleSource BrownianIntegralClosure BrownianPredictableDensity BrownianPredictableInputs
open BrownianIntegralFinitePaths BrownianFiniteSpanLeftInputs BrownianIntegralContinuousVersion
open BrownianIntegralTimeEnergy BrownianIntegralEnergyL1 BrownianIntegralGridL1 BrownianQuadraticVariation
open BrownianContinuousAdaptedInputs BrownianLiteralGridLimit
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- Same ORIGINAL finite span, not merely a changing array of literal inputs. -/
theorem finiteSpan_uniform_QV (T : ℝ≥0) (a : ElementaryInput T →₀ ℝ) :
    Tendsto (fun n => gridSquares T (uniformClock T n) (spanInput T a)) atTop
      (𝓝 (energyClass T T (spanInput T a))) := by
  let K := spanBound T a
  let r := leftRecord T (clippedTrace T a) (clippedTrace_adapted T a) K (clippedTrace_bound T a)
  let f := spanInput T a
  let g (n : ℕ) := literalPredictableInput (r n)
  have hg : Tendsto g atTop (𝓝 f) :=
    tendsto_subtype_rng.mpr (finiteSpan_left_inputClass_tendsto T a)
  have hrow : ∀ n i, ∀ᵐ ω ∂sourceLaw, |(r n).coefficient i ω| ≤ K := by
    intro n i
    apply Eventually.of_forall
    intro ω
    exact (Real.norm_eq_abs _).symm ▸ clippedTrace_bound T a (uniformClock T n i.castSucc) ω
  have hrowMesh : Tendsto (fun n => (mesh (r n).clock : ℝ)) atTop (𝓝 0) := uniformClock_mesh_tendsto T
  have hL := literal_grid_error_tendsto T r K (spanBound_nonneg T a) hrow hrowMesh
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

/-- Uniform-clock error is uniformly stable in its original L2 input, in
L1 natural scale; generic inputs never acquire an L4 hypothesis. -/
theorem uniform_error_sub_norm_le (T : ℝ≥0) (n : ℕ) (f g : fullPredictableL2 T) :
    ‖(gridSquares T (uniformClock T n) f-energyClass T T f)-
      (gridSquares T (uniformClock T n) g-energyClass T T g)‖ ≤
      2*‖f-g‖*(‖f‖+‖g‖) := by
  have he : (gridSquares T (uniformClock T n) f-energyClass T T f)-
      (gridSquares T (uniformClock T n) g-energyClass T T g) =
      (gridSquares T (uniformClock T n) f-gridSquares T (uniformClock T n) g)-
        (energyClass T T f-energyClass T T g) := by abel
  rw [he]
  exact (norm_sub_le _ _).trans (by
    have hq := gridSquares_sub_norm_le T (uniformClock T n) (uniformClock_mono T n)
      (uniformClock_zero T n) (uniformClock_end T n) f g
    have ha := energyClass_sub_norm_le T T f g
    linarith)

/-- Every SAME original full predictable L2 input has actual uniform-clock QV
converging to its actual time integral energy, in native source L1. -/
theorem fullInput_uniform_QV (T : ℝ≥0) (f : fullPredictableL2 T) :
    Tendsto (fun n => gridSquares T (uniformClock T n) f) atTop (𝓝 (energyClass T T f)) := by
  have he : Tendsto (fun n => gridSquares T (uniformClock T n) f-energyClass T T f) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    let C := 2*‖f‖+1
    have hC : 0 < C := by dsimp [C]; positivity
    let δ := min 1 (ε/(4*C))
    have hδ : 0 < δ := lt_min zero_lt_one (div_pos hε (by positivity))
    obtain ⟨a,ha⟩ := exists_spanInput_dist_lt T f δ hδ
    let g := spanInput T a
    have hfg : ‖f-g‖ < δ := by simpa only [dist_eq_norm,norm_sub_rev] using ha
    have hg : ‖g‖ ≤ ‖f‖+1 := by
      have hdist : ‖g-f‖ < 1 := by simpa only [norm_sub_rev] using hfg.trans_le (min_le_left _ _)
      have hn := norm_sub_le g f
      have hx : ‖g‖ ≤ ‖g-f‖+‖f‖ := by simpa only [sub_add_cancel] using norm_add_le (g-f) f
      linarith
    have hsmall : 2*‖f-g‖*(‖f‖+‖g‖) < ε/2 := by
      have hd : ‖f-g‖ < ε/(4*C) := hfg.trans_le (min_le_right _ _)
      have hmul : ‖f-g‖*(4*C) < ε := (lt_div_iff₀ (by positivity : 0 < 4*C)).mp hd
      have hh : ‖f‖+‖g‖ ≤ C := calc
        _ ≤ ‖f‖+(‖f‖+1) := add_le_add (le_refl ‖f‖) hg
        _ = C := by dsimp [C]; ring
      have hm := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 2*‖f-g‖)
      nlinarith
    have hlim : Tendsto (fun n => gridSquares T (uniformClock T n) g-energyClass T T g) atTop (𝓝 0) := by
      change Tendsto (fun n => gridSquares T (uniformClock T n) (spanInput T a)-energyClass T T (spanInput T a)) atTop (𝓝 0)
      simpa only [sub_self] using (finiteSpan_uniform_QV T a).sub (tendsto_const_nhds (x := energyClass T T (spanInput T a)))
    obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hlim (ε/2) (by positivity)
    refine ⟨N,fun n hn => ?_⟩
    have hng : ‖gridSquares T (uniformClock T n) g-energyClass T T g‖ < ε/2 := by
      simpa only [dist_zero_right] using hN n hn
    have hd := uniform_error_sub_norm_le T n f g
    have ht : ‖gridSquares T (uniformClock T n) f-energyClass T T f‖ ≤
        ‖(gridSquares T (uniformClock T n) f-energyClass T T f)-
          (gridSquares T (uniformClock T n) g-energyClass T T g)‖+
        ‖gridSquares T (uniformClock T n) g-energyClass T T g‖ := by
      simpa only [sub_add_cancel] using norm_add_le
        ((gridSquares T (uniformClock T n) f-energyClass T T f)-
          (gridSquares T (uniformClock T n) g-energyClass T T g))
        (gridSquares T (uniformClock T n) g-energyClass T T g)
    simp only [dist_zero_right]
    linarith
  simpa only [sub_add_cancel,zero_add] using he.add_const (energyClass T T f)

/-- Literal finite path-square sums of the SAME actual continuous integral
converge in measure to its SAME actual dt energy, for every full input. -/
theorem fullInput_uniform_QV_inMeasure (T : ℝ≥0) (f : fullPredictableL2 T) :
    TendstoInMeasure sourceLaw (fun n ω => ∑ i : Fin (n+1),
      (continuousIntegralProcess T f (uniformClock T n i.succ) ω-
        continuousIntegralProcess T f (uniformClock T n i.castSucc) ω)^2) atTop (timeEnergy T f T) :=
  TendstoInMeasure.congr (fun n => gridSquares_coe T (uniformClock T n) f)
    (energyClass_coe T T f) (tendstoInMeasure_of_tendsto_Lp (fullInput_uniform_QV T f))

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFullInputQV
