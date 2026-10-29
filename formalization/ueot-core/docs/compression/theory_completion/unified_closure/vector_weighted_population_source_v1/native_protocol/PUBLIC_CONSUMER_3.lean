import UEOT
open MeasureTheory ProbabilityTheory Set Filter
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianFiniteProductSource BrownianVectorOneStepIntegral BrownianVectorSimplePredictableIntegral
open BrownianVectorTimeInput BrownianVectorIntegralClosure
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

-- A common consumer binds the actual extension, the SAME literal output,
-- its actual raw function and the original Euclidean input norm.
example {d : ℕ} {T : ℝ≥0} (r : ElementaryInput d T) :
    integral d T (representedInput r) = outputValue r ∧
    ((integral d T (representedInput r) : Sample d → ℝ) =ᵐ[productLaw d]
      simpleIntegral d r.clock r.coefficient) ∧
    ‖integral d T (representedInput r)‖ = ‖(representedInput r : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T))‖ := by
  refine ⟨integral_returns_literal r,?_,integral_norm d T _⟩
  rw [integral_returns_literal]
  exact (simpleIntegral_memLp_two r.clock r.coefficient r.coefficient_bounded).coeFn_toLp

-- Native finite combination really returns the corresponding original
-- output, before/after completion; no independent output field was assumed.
example {d : ℕ} {T : ℝ≥0} (r : ElementaryInput d T) (c : ℝ) :
    integral d T (inclusionIsometry d T ⟨inputLinear d T (Finsupp.single r c),⟨Finsupp.single r c,rfl⟩⟩) =
      c • outputValue r := by
  rw [integral_agrees_elementary,elementaryIntegral_image]
  simp [outputLinear]

-- A genuinely changing native input converges; its actual returned source
-- outputs converge, using extension continuity and literal return together.
example {d : ℕ} {T : ℝ≥0} (r : ElementaryInput d T) :
    Tendsto (fun n : ℕ => (1/((n+1 : ℕ) : ℝ)) • outputValue r) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hc : Tendsto (fun n : ℕ => 1/((n+1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp hn
  have hx : Tendsto (fun n : ℕ => (1/((n+1 : ℕ) : ℝ)) • representedInput r) atTop (𝓝 0) := by
    simpa only [zero_smul] using hc.smul (tendsto_const_nhds (x := representedInput r))
  have h := integral_tendsto d T hx
  simpa only [map_smul,integral_returns_literal,map_zero] using h

-- No native Lp Subsingleton instance is assumed for d0.
example (T : ℝ≥0) (x : integralDomain 0 T) : integral 0 T x = 0 := by
  have he : (x : Lp (EuclideanSpace ℝ (Fin 0)) 2 (inputLaw 0 T)) = 0 := by
    apply Lp.ext
    exact ae_of_all _ (fun _ => Subsingleton.elim _ _)
  have hx : ‖x‖ = 0 := by
    change ‖(x : Lp (EuclideanSpace ℝ (Fin 0)) 2 (inputLaw 0 T))‖ = 0
    rw [he,norm_zero]
  apply norm_eq_zero.mp
  rw [integral_norm,hx]

def emptyInput (d : ℕ) : ElementaryInput d 0 where
  n := 0
  clock := fun _ => 0
  coefficient := fun i => Fin.elim0 i
  clock_mono := fun _ _ _ => le_rfl
  clock_zero := rfl
  clock_end := rfl
  coefficient_past := fun i => Fin.elim0 i
  coefficient_bounded := fun i => Fin.elim0 i

example (d : ℕ) : integral d 0 (representedInput (emptyInput d)) = 0 := by
  rw [integral_returns_literal]
  apply Lp.ext
  filter_upwards [(simpleIntegral_memLp_two (emptyInput d).clock (emptyInput d).coefficient
    (emptyInput d).coefficient_bounded).coeFn_toLp,Lp.coeFn_zero ℝ 2 (productLaw d)] with ω h hz
  change outputValue (emptyInput d) ω = _ at h
  have he : simpleIntegral d (emptyInput d).clock (emptyInput d).coefficient ω = 0 := by
    change (∑ i : Fin 0, oneStep d (Fin.elim0 i) 0 0 ω) = 0
    exact Finset.sum_eq_zero (fun i _ => Fin.elim0 i)
  exact h.trans (he.trans hz.symm)

namespace IndependentVectorClosure
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorIntegralClosure
example (d : ℕ) (T : ℝ≥0) (f g : integralDomain d T) :
    dist (integral d T f) (integral d T g) = dist f g :=
  (integralIsometry d T).isometry.dist_eq f g
#print axioms integral_returns_literal
#print axioms integral_norm
#print axioms literal_outputs_tendsto
end IndependentVectorClosure
