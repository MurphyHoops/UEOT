import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteStateDriftSource

/-!
Original commitment: the actual predictable drift is its ordinary Lebesgue time integral.
Existing result: bounded genuine predictable drifts produce adapted continuous finite-variation primitives on the original source.
Premise boundary: bounded predictability alone does not justify replacing actual primitive increments by point-sampled drift rates.
Model/witness: deterministic rational-time indicator, original source, horizon one and the original rational uniform caller clocks.
Consumer: actual drift Ito must integrate its continuous-state weights against actual beta dt, not assume false left-rate Riemann convergence.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PredictableDriftPointSamplingCounterexample
open MeasureTheory ProbabilityTheory Set Filter
open BrownianFiniteProductSource BrownianVectorPredictableInputs BrownianQuadraticVariation
open scoped NNReal ENNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- The time pullback makes the permission valid also on negative raw real
coordinates; on nonnegative time it is precisely the rational indicator. -/
def rate (t : ℝ) : ℝ := (range (fun q : ℚ => (q : ℝ))).indicator (fun _=>1) (Real.toNNReal t : ℝ)

theorem rate_bound (t : ℝ) : ‖rate t‖≤1 := by
  by_cases h : (Real.toNNReal t : ℝ)∈range (fun q : ℚ => (q : ℝ))
  · simp only [rate,Set.indicator_of_mem h,norm_one,le_refl]
  · simp only [rate,Set.indicator_of_notMem h,norm_zero,zero_le_one]

private theorem native_time_measurable (d : ℕ) :
    @Measurable (ℝ≥0×Sample d) ℝ≥0 (jointNaturalFiltration d).predictable inferInstance Prod.fst := by
  apply measurable_of_Ioi
  intro a
  convert measurableSet_predictable_Ioi_prod (𝓕 := jointNaturalFiltration d)
    (i := a) MeasurableSet.univ using 1
  ext p
  simp only [mem_preimage,mem_prod,mem_univ,and_true]

theorem rate_predictable (d : ℕ) :
    StronglyMeasurable[predictableSigma d] (fun p : ℝ×Sample d=>rate p.1) := by
  have ht : @Measurable (ℝ×Sample d) ℝ≥0 (predictableSigma d) inferInstance
      (fun p=>Real.toNNReal p.1) :=
    (native_time_measurable d).comp (measurable_iff_comap_le.mpr le_rfl)
  exact ((measurable_const.indicator (Set.countable_range (fun q : ℚ=>(q : ℝ))).measurableSet).comp
    (measurable_subtype_coe.comp ht)).stronglyMeasurable

theorem rate_ae_zero : rate=ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] 0 := by
  have hz : ∀ᵐ t ∂(volume : Measure ℝ), t∉range (fun q : ℚ=>(q : ℝ)) := by
    rw [ae_iff]
    simpa only [not_not,Set.setOf_mem_eq] using (Set.countable_range (fun q : ℚ=>(q : ℝ))).measure_zero volume
  filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae hz] with t ht hz
  simp only [Pi.zero_apply,rate,Real.coe_toNNReal _ ht.1.le,Set.indicator_of_notMem hz]

/-- The actual Lebesgue drift on the horizon is zero. -/
theorem actual_integral_zero : (∫ t in (0 : ℝ)..1,rate t)=0 := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1)]
  exact integral_eq_zero_of_ae rate_ae_zero

theorem uniform_start_rate (n : ℕ) (i : Fin (n+1)) :
    rate (uniformClock 1 n i.castSucc : ℝ)=1 := by
  have hr : (uniformClock 1 n i.castSucc : ℝ)∈range (fun q : ℚ=>(q : ℝ)) := by
    refine ⟨(i : ℕ)/(n+1 : ℚ),?_⟩
    simp [uniformClock]
  simp only [rate,Real.coe_toNNReal _ (uniformClock 1 n i.castSucc).coe_nonneg,
    Set.indicator_of_mem hr]

/-- Every raw left-rate sum on the original rational uniform clocks is
one, despite actual Lebesgue drift zero; mesh still tends to zero. -/
theorem raw_start_sum_one (n : ℕ) :
    (∑ i : Fin (n+1),rate (uniformClock 1 n i.castSucc : ℝ)*
      ((uniformClock 1 n i.succ : ℝ)-(uniformClock 1 n i.castSucc : ℝ)))=1 := by
  simp_rw [uniform_start_rate,one_mul]
  rw [Finset.sum_sub_distrib]
  have h0:=Fin.sum_univ_succ (fun i : Fin (n+2)=>(uniformClock 1 n i : ℝ))
  have hn:=Fin.sum_univ_castSucc (fun i : Fin (n+2)=>(uniformClock 1 n i : ℝ))
  have he : (uniformClock 1 n (Fin.last (n+1)) : ℝ)=1 := by rw [uniformClock_end]; rfl
  have hz : (uniformClock 1 n 0 : ℝ)=0 := by rw [uniformClock_zero]; rfl
  linarith

theorem point_sampling_is_not_actual_drift (n : ℕ) :
    (∑ i : Fin (n+1),rate (uniformClock 1 n i.castSucc : ℝ)*
      ((uniformClock 1 n i.succ : ℝ)-(uniformClock 1 n i.castSucc : ℝ)))≠
      ∫ t in (0 : ℝ)..1,rate t := by
  rw [raw_start_sum_one,actual_integral_zero]
  norm_num

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PredictableDriftPointSamplingCounterexample
