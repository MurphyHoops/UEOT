import UEOT
open MeasureTheory ProbabilityTheory Set Filter
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource
open BrownianTimeIntegrand BrownianPredictableInputs BrownianPredictableDensity BrownianIntegralClosure
open BrownianIntegralFinitePaths BrownianIntegralContinuousVersion BrownianIntegralTimeEnergy BrownianIntegralCompensator
open BrownianIntegralGridL1 BrownianIntegralEnergyL1 BrownianQuadraticVariation
open BrownianLiteralGridBinding BrownianFiniteSpanLeftInputs BrownianFullInputQV
open BrownianContinuousAdaptedInputs BrownianBoundedContinuousQV
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

-- One arbitrary original input, with no L4, path-regularity or QV premise,
-- binds the native QV limit, literal path-square sums and actual time energy.
example (T : ℝ≥0) (f : fullPredictableL2 T) :
    Tendsto (fun n => gridSquares T (uniformClock T n) f) atTop (𝓝 (energyClass T T f)) ∧
    TendstoInMeasure sourceLaw (fun n ω => ∑ i : Fin (n+1),
      (continuousIntegralProcess T f (uniformClock T n i.succ) ω-
        continuousIntegralProcess T f (uniformClock T n i.castSucc) ω)^2)
      atTop (timeEnergy T f T) ∧
    ((energyClass T T f : (ℝ≥0 → ℝ) → ℝ) =ᵐ[sourceLaw] timeEnergy T f T) ∧
    Martingale (compensatedIntegral T f) naturalFiltration sourceLaw :=
  ⟨fullInput_uniform_QV T f,fullInput_uniform_QV_inMeasure T f,energyClass_coe T T f,
    compensatedIntegral_martingale T f⟩

-- The bounded clipped trace changes only an original source-null set; its
-- sampled classes converge to the ORIGINAL finite span used in the QV limit.
example (T : ℝ≥0) (a : ElementaryInput T →₀ ℝ) :
    (∀ᵐ ω ∂sourceLaw, ∀ u, clippedTrace T a u ω = spanTrace T a u ω) ∧
    (continuousInputClass T (clippedTrace T a) (clippedTrace_measurable T a)
      (spanBound T a) (clippedTrace_bound T a) = (spanInput T a : Lp ℝ 2 (inputLaw T))) ∧
    Tendsto (fun n => inputValue (leftRecord T (clippedTrace T a) (clippedTrace_adapted T a)
      (spanBound T a) (clippedTrace_bound T a) n)) atTop
      (𝓝 (spanInput T a : Lp ℝ 2 (inputLaw T))) ∧
    Tendsto (fun n => gridSquares T (uniformClock T n) (spanInput T a)) atTop
      (𝓝 (energyClass T T (spanInput T a))) :=
  ⟨clippedTrace_eq_ae T a,clippedTrace_inputClass T a,finiteSpan_left_inputClass_tendsto T a,
    finiteSpan_uniform_QV T a⟩

example (T : ℝ≥0) (r : ElementaryInput T) (i : Fin r.n) :
    ((incrementAt T (r.clock i.castSucc) (r.clock i.succ) (literalPredictableInput r) :
      (ℝ≥0 → ℝ) → ℝ) =ᵐ[sourceLaw]
      BrownianOneStepIntegral.oneStep (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ)) ∧
    ((gridSquares T r.clock (literalPredictableInput r)-energyClass T T (literalPredictableInput r) :
      Lp ℝ 1 sourceLaw) =ᵐ[sourceLaw] errorSum r.clock (fun j ω => r.coefficient j ω^2)) :=
  ⟨integral_literal_increment_coe r i,literal_grid_error_coe r⟩

-- A concrete real source-dependent adapted input consumes the bounded branch.
def sineSource (u : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ := Real.sin (process u ω)

theorem sineSource_joint : Measurable (Function.uncurry sineSource) :=
  Real.continuous_sin.measurable.comp measurable_joint_process

theorem sineSource_adapted : StronglyAdapted naturalFiltration sineSource :=
  fun u => Real.continuous_sin.comp_stronglyMeasurable (process_stronglyAdapted u)

theorem sineSource_continuous : ∀ᵐ ω ∂sourceLaw, Continuous (fun u => sineSource u ω) :=
  ae_of_all _ (fun ω => Real.continuous_sin.comp (process_continuous ω))

theorem sineSource_bound : ∀ u ω, ‖sineSource u ω‖ ≤ 1 := by
  intro u ω
  exact Real.abs_sin_le_one _

example (T : ℝ≥0) :
    Tendsto (fun n => gridSquares T (uniformClock T n)
      (continuousPredictableInput T sineSource sineSource_joint sineSource_adapted sineSource_continuous
        1 (by norm_num) sineSource_bound)) atTop
      (𝓝 (energyClass T T (continuousPredictableInput T sineSource sineSource_joint sineSource_adapted
        sineSource_continuous 1 (by norm_num) sineSource_bound))) :=
  boundedContinuous_uniform_QV T sineSource sineSource_joint sineSource_adapted sineSource_continuous
    1 (by norm_num) sineSource_bound

-- The left endpoint has the old value; the right endpoint retains H, as
-- required by the Ioc trace. There is no right-continuity assumption here.
example (H : (ℝ≥0 → ℝ) → ℝ) (ω : ℝ≥0 → ℝ) :
    rowTrace H 1 2 1 ω = 0 ∧ rowTrace H 1 2 2 ω = H ω := by
  norm_num [rowTrace]

-- Horizon zero and empty native grids retain all original inputs.
example (f : fullPredictableL2 0) (n : ℕ) :
    gridSquares 0 (uniformClock 0 n) f = 0 := by
  simp [gridSquares,uniformClock,incrementAt,BrownianIntegralSquareL1.squareClass]

example (f : fullPredictableL2 0) : energyClass 0 0 f = 0 := by
  apply Lp.ext
  filter_upwards [energyClass_coe 0 0 f,Lp.coeFn_zero ℝ 1 sourceLaw] with ω he hz
  rw [he,timeEnergy_zero]
  exact hz.symm

example (T : ℝ≥0) (τ : Fin 1 → ℝ≥0) (f : fullPredictableL2 T) :
    gridSquares T τ f = 0 := by simp [gridSquares]

-- Positive unit-input energy is the SAME literal time integral; the final
-- full-input theorem is thus a source path-square limit toward actual one.
theorem unit_energy : timeEnergy 1 (literalPredictableInput (unitInput 1)) 1 =ᵐ[sourceLaw] fun _ => (1 : ℝ) := by
  apply (timeEnergy_literal_horizon (unitInput 1)).trans
  apply ae_of_all
  intro ω
  change (∑ i : Fin 1, (((unitInput 1).clock i.succ : ℝ)-((unitInput 1).clock i.castSucc : ℝ))*
    (unitInput 1).coefficient i ω^2) = 1
  rw [Fin.sum_univ_one]
  change ((1 : ℝ)-0)*1^2 = 1
  norm_num


example : TendstoInMeasure sourceLaw (fun n ω => ∑ i : Fin (n+1),
    (continuousIntegralProcess 1 (literalPredictableInput (unitInput 1)) (uniformClock 1 n i.succ) ω-
      continuousIntegralProcess 1 (literalPredictableInput (unitInput 1)) (uniformClock 1 n i.castSucc) ω)^2)
    atTop (fun _ => (1 : ℝ)) :=
  TendstoInMeasure.congr_right unit_energy (fullInput_uniform_QV_inMeasure 1 (literalPredictableInput (unitInput 1)))
