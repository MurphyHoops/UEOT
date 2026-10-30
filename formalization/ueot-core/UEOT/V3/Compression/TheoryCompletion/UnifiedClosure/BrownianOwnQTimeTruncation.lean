import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQFinitePaths
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQBoundedInput
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralLiteralIntervals

/-!
Original commitment: actual ownQ time values must integrate the SAME input cut off at the observation clock, not an unrelated conditional process.
Existing result: actual Q isometry on explicit elementary-span closure and original-Fs finite literal conditional paths; original pure interval cutoff identities.
Premise reduced: construct the native dtU×Q indicator cutoff, derive actual finite input decomposition and prove it preserves that SAME explicit closure.
Model/witness: fixed bounded source f/A/K/Q; caller integration U and observation u arbitrary, repeated/zero cells retain original START coefficient permission.
Consumer/boundary: actual ownQ cutoff integral process and conditional-prefix extension; closure is not identified with all Q predictable L2.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQTimeTruncation
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianMartingaleSource BrownianCommonRefinement BrownianTimeIntegrand BrownianPredictableInputs
open BrownianIntegralClosure (ElementaryInput)
open BrownianIntegralTimeTruncation (timeSet timeSet_measurable)
open BrownianIntegralLiteralIntervals BrownianBoundedExponentialLimitSource
open BrownianOwnQTimeInput BrownianOwnQBoundedInput BrownianOwnQIntegralClosure
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
variable (A : ℝ≥0) (f : fullPredictableL2 A) (K : ℝ) (hK : 0≤K)
    (hF : ∀ᵐ p ∂inputLaw A, |(f : Lp ℝ 2 (inputLaw A)) p|≤K)

private def cutoffClass (U u : ℝ≥0) : Lp ℝ ∞ (inputLawQ A f U) :=
  ((memLp_top_const (μ := inputLawQ A f U) (1 : ℝ)).indicator (timeSet_measurable U u)).toLp
    ((timeSet U u).indicator (fun _ => (1 : ℝ)))

/-- Native Holder multiplication, on the original dtU times SAME ownQ. -/
def truncateAmbient (U u : ℝ≥0) : Lp ℝ 2 (inputLawQ A f U) →L[ℝ] Lp ℝ 2 (inputLawQ A f U) :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL (inputLawQ A f U) ∞ 2 2 (cutoffClass A f U u)

theorem truncateAmbient_coe (U u : ℝ≥0) (g : Lp ℝ 2 (inputLawQ A f U)) :
    truncateAmbient A f U u g=ᵐ[inputLawQ A f U] (timeSet U u).indicator g := by
  have hc := ((memLp_top_const (μ := inputLawQ A f U) (1 : ℝ)).indicator (timeSet_measurable U u)).coeFn_toLp
  have hh := (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2) (cutoffClass A f U u) g
  apply hh.trans
  filter_upwards [hc] with p hp
  change cutoffClass A f U u p*g p=(timeSet U u).indicator g p
  change cutoffClass A f U u p=_ at hp
  rw [hp]
  by_cases ht : p∈timeSet U u <;> simp [ht]

include hK hF

/-- Exact native Q input of the original permitted interval record. -/
theorem interval_input_coe (U a b : ℝ≥0) (hab : a≤b) (hbU : b≤U)
    (H : (ℝ≥0 → ℝ) → ℝ) (hHpast : StronglyMeasurable[naturalFiltration a] H) (hH : MemLp H ∞ sourceLaw) :
    inputValueQ A f K hK hF (intervalRecord U a b hab hbU H hHpast hH)=ᵐ[inputLawQ A f U] intervalIntegrand H a b := by
  apply (BrownianOwnQTimeInput.integrand_memLp_two A f K hK hF (intervalRecord U a b hab hbU H hHpast hH)).coeFn_toLp.trans
  exact Eventually.of_forall (fun p => by
    change (∑ i : Fin 3, intervalIntegrand (![fun _ => 0,H,fun _ => 0] i)
      (![0,a,b,U] i.castSucc) (![0,a,b,U] i.succ) p)=intervalIntegrand H a b p
    simp [Fin.sum_univ_succ,intervalIntegrand])

/-- Existing source-P cutoff coefficient identity is transported by actual
product absolute continuity only; no stochastic output is relabelled. -/
theorem truncate_interval_input (U a b u : ℝ≥0) (hab : a≤b) (hbU : b≤U)
    (H : (ℝ≥0 → ℝ) → ℝ) (hHpast : StronglyMeasurable[naturalFiltration a] H) (hH : MemLp H ∞ sourceLaw) :
    truncateAmbient A f U u (inputValueQ A f K hK hF (intervalRecord U a b hab hbU H hHpast hH))=
      inputValueQ A f K hK hF (intervalRecord U a (clamp a b u) (clamp_bounds a b u hab).1
        ((clamp_bounds a b u hab).2.trans hbU) H hHpast hH) := by
  have hp := BrownianIntegralTimeTruncation.truncate_coe U u (intervalInput U a b hab hbU H hHpast hH)
  rw [truncate_intervalInput] at hp
  have heP : (timeSet U u).indicator (intervalIntegrand H a b)=ᵐ[inputLaw U] intervalIntegrand H a (clamp a b u) := by
    filter_upwards [hp,intervalInput_coe U a b hab hbU H hHpast hH,
      intervalInput_coe U a (clamp a b u) (clamp_bounds a b u hab).1
        ((clamp_bounds a b u hab).2.trans hbU) H hHpast hH] with p hc ho hn
    rw [hn] at hc
    rw [hc]
    by_cases ht : p∈timeSet U u <;> simp [ht,ho]
  apply Lp.ext
  filter_upwards [truncateAmbient_coe A f U u (inputValueQ A f K hK hF (intervalRecord U a b hab hbU H hHpast hH)),
    interval_input_coe A f K hK hF U a b hab hbU H hHpast hH,
    interval_input_coe A f K hK hF U a (clamp a b u) (clamp_bounds a b u hab).1
      ((clamp_bounds a b u hab).2.trans hbU) H hHpast hH,
    (inputLawQ_absolutelyContinuous A f U).ae_le heP] with p hc ho hn he
  rw [hc,hn,← he]
  by_cases ht : p∈timeSet U u <;> simp [ht,ho]

omit hK hF in
private theorem row_order {U : ℝ≥0} (r : ElementaryInput U) (i : Fin r.n) :
    r.clock i.castSucc≤r.clock i.succ := r.clock_mono (by exact_mod_cast Nat.le_succ (i : ℕ))
omit hK hF in
private theorem row_horizon {U : ℝ≥0} (r : ElementaryInput U) (i : Fin r.n) :
    r.clock i.succ≤U := (r.clock_mono (Fin.le_last _)).trans r.clock_end.le
private def rowRecord {U : ℝ≥0} (r : ElementaryInput U) (i : Fin r.n) : ElementaryInput U :=
  intervalRecord U (r.clock i.castSucc) (r.clock i.succ) (row_order r i) (row_horizon r i)
    (r.coefficient i) (r.coefficient_past i) (r.coefficient_bounded i)
private def cutoffRowRecord {U : ℝ≥0} (r : ElementaryInput U) (i : Fin r.n) (u : ℝ≥0) : ElementaryInput U :=
  intervalRecord U (r.clock i.castSucc) (clamp (r.clock i.castSucc) (r.clock i.succ) u)
    (clamp_bounds _ _ u (row_order r i)).1 ((clamp_bounds _ _ u (row_order r i)).2.trans (row_horizon r i))
    (r.coefficient i) (r.coefficient_past i) (r.coefficient_bounded i)

/-- Actual supplied finite input decomposes into its actual original-START
interval records in SAME native Q space. Native Lp finite-sum coercion is reused. -/
theorem literal_input_decomposition {U : ℝ≥0} (r : ElementaryInput U) :
    inputValueQ A f K hK hF r=∑ i : Fin r.n, inputValueQ A f K hK hF (rowRecord r i) := by
  apply Lp.ext
  have hi : ∀ᵐ p ∂inputLawQ A f U, ∀ i : Fin r.n,
      inputValueQ A f K hK hF (rowRecord r i) p=intervalIntegrand (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ) p :=
    ae_all_iff.mpr (fun i => interval_input_coe A f K hK hF U _ _ (row_order r i) (row_horizon r i)
      (r.coefficient i) (r.coefficient_past i) (r.coefficient_bounded i))
  filter_upwards [(BrownianOwnQTimeInput.integrand_memLp_two A f K hK hF r).coeFn_toLp,
    Lp.coeFn_fun_finsetSum Finset.univ (fun i => inputValueQ A f K hK hF (rowRecord r i)),hi] with p hp hs hi
  change inputValueQ A f K hK hF r p=integrand r.clock r.coefficient p at hp
  rw [hp,hs]
  exact Finset.sum_congr rfl (fun i _ => (hi i).symm)

/-- Actual indicator cutoff is a finite sum of actual original-permission
clamped interval records; collapsed intervals remain literal zero. -/
theorem truncate_literal_decomposition {U : ℝ≥0} (r : ElementaryInput U) (u : ℝ≥0) :
    truncateAmbient A f U u (inputValueQ A f K hK hF r)=
      ∑ i : Fin r.n, inputValueQ A f K hK hF (cutoffRowRecord r i u) := by
  rw [literal_input_decomposition A f K hK hF r,map_sum]
  exact Finset.sum_congr rfl (fun i _ => truncate_interval_input A f K hK hF U _ _ u
    (row_order r i) (row_horizon r i) (r.coefficient i) (r.coefficient_past i) (r.coefficient_bounded i))

private theorem truncate_span (U u : ℝ≥0) :
    elementarySpan A f K hK hF U≤(elementarySpan A f K hK hF U).comap (truncateAmbient A f U u).toLinearMap := by
  conv_lhs => rw [elementarySpan_eq_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨r,rfl⟩
  change truncateAmbient A f U u (inputValueQ A f K hK hF r)∈elementarySpan A f K hK hF U
  rw [truncate_literal_decomposition A f K hK hF r u]
  apply Submodule.sum_mem
  intro i _
  exact (elementaryPoint A f K hK hF (cutoffRowRecord r i u)).property

/-- Derived closure invariance, using actual finite cutoffs and continuity;
there is no cutoff-membership certificate supplied by the caller. -/
theorem truncate_memDomain (U u : ℝ≥0) (g : integralDomain A f K hK hF U) :
    truncateAmbient A f U u g∈integralDomain A f K hK hF U := by
  have hc : IsClosed (integralDomain A f K hK hF U : Set (Lp ℝ 2 (inputLawQ A f U))) := isClosed_closure
  have hle : elementarySpan A f K hK hF U≤(integralDomain A f K hK hF U).comap (truncateAmbient A f U u).toLinearMap :=
    (truncate_span A f K hK hF U u).trans (Submodule.comap_mono (elementarySpan A f K hK hF U).le_topologicalClosure)
  exact ((elementarySpan A f K hK hF U).topologicalClosure_minimal hle (hc.preimage (truncateAmbient A f U u).continuous)) g.property

/-- Native cutoff on the SAME explicit integral closure domain. -/
def truncate (U u : ℝ≥0) : integralDomain A f K hK hF U →L[ℝ] integralDomain A f K hK hF U :=
  ((truncateAmbient A f U u).comp (integralDomain A f K hK hF U).subtypeL).codRestrict
    (integralDomain A f K hK hF U) (truncate_memDomain A f K hK hF U u)

theorem truncate_coe (U u : ℝ≥0) (g : integralDomain A f K hK hF U) :
    (truncate A f K hK hF U u g : Lp ℝ 2 (inputLawQ A f U))=ᵐ[inputLawQ A f U]
      (timeSet U u).indicator (g : Lp ℝ 2 (inputLawQ A f U)) := truncateAmbient_coe A f U u g

theorem truncate_norm_le (U u : ℝ≥0) (g : integralDomain A f K hK hF U) :
    ‖truncate A f K hK hF U u g‖≤‖g‖ := by
  change ‖(truncate A f K hK hF U u g : Lp ℝ 2 (inputLawQ A f U))‖≤‖(g : Lp ℝ 2 (inputLawQ A f U))‖
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [truncate_coe A f K hK hF U u g] with p hp
  rw [hp]
  by_cases ht : p∈timeSet U u <;> simp [ht]

theorem truncate_zero (U : ℝ≥0) (g : integralDomain A f K hK hF U) : truncate A f K hK hF U 0 g=0 := by
  apply Subtype.ext
  change (truncate A f K hK hF U 0 g : Lp ℝ 2 (inputLawQ A f U))=0
  apply Lp.ext
  filter_upwards [truncate_coe A f K hK hF U 0 g,Lp.coeFn_zero ℝ 2 (inputLawQ A f U)] with p hp hz
  rw [hp,hz]
  simp [timeSet]

theorem truncate_horizon (U : ℝ≥0) (g : integralDomain A f K hK hF U) : truncate A f K hK hF U U g=g := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [truncate_coe A f K hK hF U U g,(inputLawQ_absolutelyContinuous A f U).ae_le (time_support_ae U)] with p hp ht
  rw [hp]
  exact Set.indicator_of_mem (by simpa only [timeSet,min_self,mem_prod,mem_univ,and_true] using ht) _

/-- The actual closed-domain cutoff of a supplied permitted interval is
precisely the original supplied interval with its endpoint clamped. -/
theorem truncate_represented_interval (U a b u : ℝ≥0) (hab : a≤b) (hbU : b≤U)
    (H : (ℝ≥0 → ℝ) → ℝ) (hHpast : StronglyMeasurable[naturalFiltration a] H) (hH : MemLp H ∞ sourceLaw) :
    truncate A f K hK hF U u (representedInput A f K hK hF (intervalRecord U a b hab hbU H hHpast hH))=
      representedInput A f K hK hF (intervalRecord U a (clamp a b u) (clamp_bounds a b u hab).1
        ((clamp_bounds a b u hab).2.trans hbU) H hHpast hH) :=
  Subtype.ext (truncate_interval_input A f K hK hF U a b u hab hbU H hHpast hH)

def integralClassProcess (U : ℝ≥0) (g : integralDomain A f K hK hF U) (u : ℝ≥0) : Lp ℝ 2 (fullLaw A f) :=
  integral A f K hK hF U (truncate A f K hK hF U u g)

theorem integralClassProcess_zero (U : ℝ≥0) (g : integralDomain A f K hK hF U) : integralClassProcess A f K hK hF U g 0=0 := by
  rw [integralClassProcess,truncate_zero,map_zero]

theorem integralClassProcess_horizon (U : ℝ≥0) (g : integralDomain A f K hK hF U) :
    integralClassProcess A f K hK hF U g U=integral A f K hK hF U g := by
  rw [integralClassProcess,truncate_horizon]

theorem integralClassProcess_norm_le (U u : ℝ≥0) (g : integralDomain A f K hK hF U) :
    ‖integralClassProcess A f K hK hF U g u‖≤‖g‖ := by
  rw [integralClassProcess,integral_norm]
  exact truncate_norm_le A f K hK hF U u g

omit hK hF in
private theorem lp_norm_sq {α : Type*} [MeasurableSpace α] (μ : Measure α) (g : Lp ℝ 2 μ) :
    ‖g‖^2=∫ a, g a^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]

/-- Actual dtU×Q time energy follows from the original Q isometry and literal
indicator identity. It is not a quadratic-variation assumption. -/
theorem integralClassProcess_energy (U u : ℝ≥0) (g : integralDomain A f K hK hF U) :
    (∫ ω, integralClassProcess A f K hK hF U g u ω^2 ∂fullLaw A f)=
      ∫ p in timeSet U u, (g : Lp ℝ 2 (inputLawQ A f U)) p^2 ∂inputLawQ A f U := by
  rw [← lp_norm_sq (fullLaw A f),integralClassProcess,integral_norm]
  change ‖(truncate A f K hK hF U u g : Lp ℝ 2 (inputLawQ A f U))‖^2=_
  rw [lp_norm_sq]
  have he : (fun p => (truncate A f K hK hF U u g : Lp ℝ 2 (inputLawQ A f U)) p^2)=ᵐ[inputLawQ A f U]
      (timeSet U u).indicator (fun p => (g : Lp ℝ 2 (inputLawQ A f U)) p^2) := by
    filter_upwards [truncate_coe A f K hK hF U u g] with p hp
    rw [hp]
    by_cases ht : p∈timeSet U u <;> simp [ht]
  rw [integral_congr_ae he,integral_indicator (timeSet_measurable U u)]

/-- Actual continuous linear time evaluation on the original explicit domain. -/
def integralAt (U u : ℝ≥0) : integralDomain A f K hK hF U →L[ℝ] Lp ℝ 2 (fullLaw A f) :=
  (integral A f K hK hF U).comp (truncate A f K hK hF U u)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQTimeTruncation
