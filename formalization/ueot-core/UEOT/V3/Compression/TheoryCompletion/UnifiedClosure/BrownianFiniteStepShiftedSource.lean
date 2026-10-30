import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianMeasuredStepTransport
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteStepTerminalKLSource

/-!
Original commitment: the actual finite policy table must produce a complete controlled noise path under its own computed Q.
Existing result: actual prefix densities and generic native one-block finite-law transport from a proved Brownian source.
Premise reduced: construct each literal shifted prefix and prove it Brownian under the actual prefixQ, retaining the exact original natural filtration.
Model/witness: SAME supplied ElementaryInput, actual returned H/clock and B/sourceLaw, all nonnegative observation times including after T.
Consumer: SAME final tableQ full shifted Brownian/originalFt source; general predictable-control limits remain separate.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteStepShiftedSource
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource BrownianIntegralClosure
open BrownianPastStepGaussianResidualSource BrownianFiniteStepExponentialSource
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

private theorem cell_mono {T : ℝ≥0} (r : ElementaryInput T) (i : Fin r.n) : r.clock i.castSucc ≤ r.clock i.succ :=
  r.clock_mono (by exact_mod_cast Nat.le_succ (i : ℕ))

def prefixDrift {T : ℝ≥0} (r : ElementaryInput T) (k : Fin (r.n+1)) (t : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ :=
  Fin.partialSum (fun i => r.coefficient i ω*overlap (r.clock i.castSucc) (r.clock i.succ) t) k

def prefixProcess {T : ℝ≥0} (r : ElementaryInput T) (k : Fin (r.n+1)) (t : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ :=
  process t ω-prefixDrift r k t ω

theorem prefixProcess_zero {T : ℝ≥0} (r : ElementaryInput T) : prefixProcess r 0=process := by
  funext t ω
  simp [prefixProcess,prefixDrift]

theorem prefixProcess_succ {T : ℝ≥0} (r : ElementaryInput T) (i : Fin r.n) :
    prefixProcess r i.succ=BrownianMeasuredStepTransport.shifted (prefixProcess r i.castSucc)
      (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ) := by
  funext t ω
  simp only [prefixProcess,prefixDrift,Fin.partialSum_succ,BrownianMeasuredStepTransport.shifted]
  ring

theorem prefixProcess_measurable {T : ℝ≥0} (r : ElementaryInput T) (k : Fin (r.n+1)) (t : ℝ≥0) :
    Measurable (prefixProcess r k t) := by
  have hd : ∀ k : Fin (r.n+1), Measurable (prefixDrift r k t) := by
    intro k
    refine Fin.induction ?_ ?_ k
    · have he : prefixDrift r 0 t=0 := funext (fun ω => Fin.partialSum_zero _)
      rw [he]
      exact measurable_const
    · intro i hi
      have he : prefixDrift r i.succ t=fun ω => prefixDrift r i.castSucc t ω+
          r.coefficient i ω*overlap (r.clock i.castSucc) (r.clock i.succ) t := by
        funext ω
        exact Fin.partialSum_succ _ i
      rw [he]
      exact hi.add (((r.coefficient_past i).mono (naturalFiltration.le _)).measurable.mul_const _)
  exact (measurable_process t).sub (hd k)

/-- At and after the consumed prefix endpoint, its drift is already fixed.
This is literal algebra, with no null set or future observation permission. -/
theorem prefixDrift_after {T : ℝ≥0} (r : ElementaryInput T) (k : Fin (r.n+1)) :
    ∀ t, r.clock k ≤ t → ∀ ω, prefixDrift r k t ω=
      Fin.partialSum (fun i => r.coefficient i ω*((r.clock i.succ : ℝ)-(r.clock i.castSucc : ℝ))) k := by
  refine Fin.induction ?_ ?_ k
  · intro t ht ω
    simp [prefixDrift]
  · intro i hi t ht ω
    have hp := hi t ((cell_mono r i).trans ht) ω
    simp only [prefixDrift,Fin.partialSum_succ] at hp ⊢
    rw [hp]
    unfold overlap
    rw [min_eq_right ht,min_eq_right ((cell_mono r i).trans ht)]

/-- Earlier controls have no increment on this row's own clock interval. -/
theorem prior_increment_eq {T : ℝ≥0} (r : ElementaryInput T) (i : Fin r.n) (ω : ℝ≥0 → ℝ) :
    BrownianMeasuredStepTransport.inc (prefixProcess r i.castSucc) (r.clock i.castSucc) (r.clock i.succ) ω=
      increment (r.clock i.castSucc) (r.clock i.succ) ω := by
  unfold BrownianMeasuredStepTransport.inc prefixProcess increment
  rw [prefixDrift_after r i.castSucc _ (cell_mono r i),prefixDrift_after r i.castSucc _ le_rfl]
  ring

/-- The generic one-block measure is EXACTLY the actual next prefixQ. -/
theorem next_tilted_eq {T : ℝ≥0} (r : ElementaryInput T) (i : Fin r.n) :
    BrownianMeasuredStepTransport.tilted (prefixLaw r i.castSucc) (prefixProcess r i.castSucc)
      (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ)=prefixLaw r i.succ := by
  rw [prefixLaw_step_composition]
  unfold BrownianMeasuredStepTransport.tilted
  congr 1
  funext ω
  unfold BrownianGaussianTiltSource.gaussianTiltWeight
  rw [prior_increment_eq]
  unfold stepFactor BrownianPastStepExponentialSource.stepExponential BrownianOneStepIntegral.oneStep
  rfl

private theorem natural_congr (B C : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ) (hB : ∀ t, Measurable (B t))
    (hC : ∀ t, Measurable (C t)) (he : B=C) :
    BrownianMeasuredStepTransport.natural B hB=BrownianMeasuredStepTransport.natural C hC := by
  subst C
  rfl

/-- Every actual prefix supplies the SAME measured Brownian source needed
by the next action, and has the EXACT original filtration. -/
theorem prefix_source {T : ℝ≥0} (r : ElementaryInput T) (k : Fin (r.n+1)) :
    IsPreBrownianReal (prefixProcess r k) (prefixLaw r k) ∧
      BrownianMeasuredStepTransport.natural (prefixProcess r k) (prefixProcess_measurable r k)=naturalFiltration := by
  refine Fin.induction ?_ ?_ k
  · constructor
    · rw [prefixProcess_zero,prefixLaw_zero]
      exact process_isPreBrownian
    · exact natural_congr _ _ (prefixProcess_measurable r 0) measurable_process (prefixProcess_zero r)
  · intro i hi
    have hH : StronglyMeasurable[BrownianMeasuredStepTransport.natural (prefixProcess r i.castSucc)
        (prefixProcess_measurable r i.castSucc) (r.clock i.castSucc)] (r.coefficient i) := by
      rw [hi.2]
      exact r.coefficient_past i
    have hBM := BrownianMeasuredStepTransport.shifted_isPreBrownian (prefixLaw r i.castSucc)
      (prefixProcess r i.castSucc) (prefixProcess_measurable r i.castSucc) hi.1
      (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ) (cell_mono r i) hH
    rw [← prefixProcess_succ r i,next_tilted_eq r i] at hBM
    refine ⟨hBM,?_⟩
    have hN := BrownianMeasuredStepTransport.shifted_natural_eq (prefixProcess r i.castSucc)
      (prefixProcess_measurable r i.castSucc) (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ) (cell_mono r i) hH
    exact (natural_congr _ _ (prefixProcess_measurable r i.succ) _ (prefixProcess_succ r i)).trans (hN.trans hi.2)

/-- The returned full finite-table noise path, on ALL nonnegative times. -/
def tableProcess {T : ℝ≥0} (r : ElementaryInput T) := prefixProcess r (Fin.last r.n)

theorem tableProcess_formula {T : ℝ≥0} (r : ElementaryInput T) (t : ℝ≥0) (ω : ℝ≥0 → ℝ) :
    tableProcess r t ω=process t ω-
      ∑ i : Fin r.n, r.coefficient i ω*overlap (r.clock i.castSucc) (r.clock i.succ) t := by
  unfold tableProcess prefixProcess prefixDrift Fin.partialSum
  congr 1
  change ((List.ofFn (fun i => r.coefficient i ω*overlap (r.clock i.castSucc) (r.clock i.succ) t)).take r.n).sum=_
  rw [List.take_of_length_le (by simp),List.sum_ofFn]

theorem tableProcess_continuous {T : ℝ≥0} (r : ElementaryInput T) (ω : ℝ≥0 → ℝ) :
    Continuous (tableProcess r · ω) := by
  simp_rw [tableProcess_formula]
  exact (process_continuous ω).sub (continuous_finsetSum _ (fun i _ =>
    continuous_const.mul (BrownianPastStepShiftedSource.overlap_continuous _ _)))

/-- Actual complete Brownian source under SAME computed tableQ. -/
theorem tableProcess_isBrownian {T : ℝ≥0} (r : ElementaryInput T) : IsBrownianReal (tableProcess r) (tableLaw r) :=
  ⟨(prefix_source r (Fin.last r.n)).1,Eventually.of_forall (tableProcess_continuous r)⟩

theorem tableProcess_natural_eq {T : ℝ≥0} (r : ElementaryInput T) :
    BrownianMeasuredStepTransport.natural (tableProcess r) (prefixProcess_measurable r (Fin.last r.n))=naturalFiltration :=
  (prefix_source r (Fin.last r.n)).2

/-- Future returned noise is independent of the ENTIRE original source
past, via the proved exact sigma-algebra identity, not adaptedness alone. -/
theorem tableProcess_indep_original_past {T : ℝ≥0} (r : ElementaryInput T) (s : ℝ≥0) :
    IndepFun (fun ω u => tableProcess r (s+u) ω-tableProcess r s ω)
      (fun ω (v : Iic s) => process v ω) (tableLaw r) := by
  have h := (tableProcess_isBrownian r).toIsPreBrownianReal.indepFun_shift s
  have hi : Indep (MeasurableSpace.comap
      (fun ω u => tableProcess r (s+u) ω-tableProcess r s ω) inferInstance)
      (MeasurableSpace.comap (fun ω (v : Iic s) => tableProcess r v ω) inferInstance) (tableLaw r) := h
  have he : BrownianMeasuredStepTransport.natural (tableProcess r) (prefixProcess_measurable r (Fin.last r.n)) s=
      MeasurableSpace.comap (fun ω (v : Iic s) => tableProcess r v ω) inferInstance :=
    Filtration.natural_eq_comap _ _ s
  rw [← he,tableProcess_natural_eq r,naturalFiltration,Filtration.natural_eq_comap] at hi
  exact hi

/-- Later controls have literal zero overlap with all reads through an
earlier consumed prefix endpoint, on every sample. -/
theorem prefixProcess_agrees_before {T : ℝ≥0} (r : ElementaryInput T) (j : Fin (r.n+1)) :
    ∀ k, k ≤ j → ∀ t, t ≤ r.clock k → ∀ ω, prefixProcess r j t ω=prefixProcess r k t ω := by
  refine Fin.induction ?_ ?_ j
  · intro k hk t ht ω
    have he : k=0 := le_antisymm hk (by exact bot_le)
    subst k
    rfl
  · intro i hi k hk t ht ω
    by_cases he : k=i.succ
    · subst k
      rfl
    · have hlt : k < i.succ := lt_of_le_of_ne hk he
      have hki : k ≤ i.castSucc := by
        change (k : ℕ)≤(i : ℕ)
        have hh : (k : ℕ)<(i : ℕ)+1 := hlt
        omega
      have hs : t≤r.clock i.castSucc := ht.trans (r.clock_mono hki)
      rw [prefixProcess_succ]
      rw [BrownianMeasuredStepTransport.shifted_before _ _ _ _ _ (cell_mono r i) hs]
      exact hi k hki t ht ω

/-- SAME full-table shifted process has exactly the literal centered
returned row increment, including repeated clock cells. -/
theorem tableProcess_row_increment {T : ℝ≥0} (r : ElementaryInput T) (i : Fin r.n) (ω : ℝ≥0 → ℝ) :
    tableProcess r (r.clock i.succ) ω-tableProcess r (r.clock i.castSucc) ω=
      BrownianFiniteStepConditionalSource.centeredRow r i ω := by
  have hb := prefixProcess_agrees_before r (Fin.last r.n) i.succ (Fin.le_last _) (r.clock i.succ) le_rfl ω
  have ha := prefixProcess_agrees_before r (Fin.last r.n) i.castSucc (Fin.le_last _) (r.clock i.castSucc) le_rfl ω
  change prefixProcess r (Fin.last r.n) (r.clock i.succ) ω-prefixProcess r (Fin.last r.n) (r.clock i.castSucc) ω=_
  rw [hb,ha,prefixProcess_succ]
  have hI := prior_increment_eq r i ω
  unfold BrownianMeasuredStepTransport.inc at hI
  unfold BrownianMeasuredStepTransport.shifted BrownianFiniteStepConditionalSource.centeredRow BrownianPastStepTiltKernelSource.centeredIncrement
  unfold overlap
  rw [min_self,min_eq_right (cell_mono r i),NNReal.coe_sub (cell_mono r i)]
  linarith

/-- The original terminal P-KL record's controlled integral is the finite
integral against THIS full Brownian path, with the SAME supplied coefficients. -/
theorem actual_terminal_integral_binding {T : ℝ≥0} (r : ElementaryInput T) (ω : ℝ≥0 → ℝ) :
    (BrownianFiniteStepTerminalKLSource.actualTerminalData r).controlledIntegral ω=
      ∑ i : Fin r.n, r.coefficient i ω*(tableProcess r (r.clock i.succ) ω-tableProcess r (r.clock i.castSucc) ω) := by
  change (∑ i : Fin r.n, r.coefficient i ω*BrownianFiniteStepConditionalSource.centeredRow r i ω)=_
  apply Finset.sum_congr rfl
  intro i _
  rw [tableProcess_row_increment]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteStepShiftedSource
