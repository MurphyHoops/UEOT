import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQTimeTruncation

/-!
Original commitment: same-ownQ general integral time values must be actual cutoffs and actual original-Fs martingale, not assumed process fields.
Existing result: actual finite W paths/conditional prefixes and native time cutoffs preserve the explicit Q integral closure with real dt energy.
Premise reduced: derive conditional projection=cutoff integral by actual finite inputs and native dense CLM continuity; construct strongly adapted real process bound to these actual classes.
Model/witness: bounded original source f/A/K/Q fixed, any input g in proved dtU×Q elementary-span closure, all observation clocks including U=0/repeats/U>A.
Consumer/boundary: actual ownQ integral martingale/time energy and controlled Ito-noise conditional source; no identification with all Q predictable L2 or general continuous-path version claimed.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQIntegralMartingale
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianMartingaleSource BrownianCommonRefinement BrownianTimeIntegrand BrownianPredictableInputs
open BrownianIntegralClosure (ElementaryInput)
open BrownianIntegralLiteralIntervals BrownianBoundedExponentialLimitSource BrownianBoundedGirsanovSource
open BrownianOwnQOneStepIntegral BrownianOwnQSimpleIntegral BrownianOwnQTimeInput BrownianOwnQIntegralClosure
open BrownianOwnQConditionalStep BrownianOwnQFinitePaths BrownianOwnQTimeTruncation
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
variable (A : ℝ≥0) (f : fullPredictableL2 A) (K : ℝ) (hK : 0≤K)
    (hF : ∀ᵐ p ∂inputLaw A, |(f : Lp ℝ 2 (inputLaw A)) p|≤K)

private theorem row_order {U : ℝ≥0} (r : ElementaryInput U) (i : Fin r.n) :
    r.clock i.castSucc≤r.clock i.succ := r.clock_mono (by exact_mod_cast Nat.le_succ (i : ℕ))
private theorem row_horizon {U : ℝ≥0} (r : ElementaryInput U) (i : Fin r.n) :
    r.clock i.succ≤U := (r.clock_mono (Fin.le_last _)).trans r.clock_end.le
private def prefixRow {U : ℝ≥0} (r : ElementaryInput U) (i : Fin r.n) (u : ℝ≥0) : ElementaryInput U :=
  intervalRecord U (r.clock i.castSucc) (clamp (r.clock i.castSucc) (r.clock i.succ) u)
    (clamp_bounds _ _ u (row_order r i)).1 ((clamp_bounds _ _ u (row_order r i)).2.trans (row_horizon r i))
    (r.coefficient i) (r.coefficient_past i) (r.coefficient_bounded i)
include hK hF

/-- Q integral output of the actual original interval record is its actual W
step, bound as native L2 classes rather than by expectation only. -/
theorem interval_output (U a b : ℝ≥0) (hab : a≤b) (hbU : b≤U)
    (H : (ℝ≥0 → ℝ) → ℝ) (hHpast : StronglyMeasurable[naturalFiltration a] H) (hH : MemLp H ∞ sourceLaw) :
    outputValueQ A f K hK hF (intervalRecord U a b hab hbU H hHpast hH)=
      (oneStep_memLp_two A f K hK hF (coefficient_bounded_Q A f K hK hF hH) a b).toLp (oneStep A f K H a b) := by
  apply Lp.ext
  apply (simpleIntegral_memLp_two A f K hK hF (intervalRecord U a b hab hbU H hHpast hH)).coeFn_toLp.trans
  apply Filter.EventuallyEq.trans _ (oneStep_memLp_two A f K hK hF (coefficient_bounded_Q A f K hK hF hH) a b).coeFn_toLp.symm
  exact Eventually.of_forall (fun ω => by
    dsimp only [simpleIntegral,intervalRecord]
    simp [Fin.sum_univ_succ,oneStep,fullIncrement])

/-- The actual cutoff integral returns the SAME supplied finite path. -/
theorem integralClassProcess_returns_literal {U : ℝ≥0} (r : ElementaryInput U) (u : ℝ≥0) :
    integralClassProcess A f K hK hF U (representedInput A f K hK hF r) u=
      (literalPath_memLp_two A f K hK hF r u).toLp (literalPath A f K r u) := by
  have hd : truncate A f K hK hF U u (representedInput A f K hK hF r)=
      ∑ i : Fin r.n, representedInput A f K hK hF (prefixRow r i u) := by
    apply Subtype.ext
    change truncateAmbient A f U u (inputValueQ A f K hK hF r)=
      (∑ i : Fin r.n, representedInput A f K hK hF (prefixRow r i u) : integralDomain A f K hK hF U)
    rw [Submodule.coe_sum]
    exact truncate_literal_decomposition A f K hK hF r u
  rw [integralClassProcess,hd,map_sum]
  simp_rw [integral_returns_literal]
  have hi : ∀ᵐ ω ∂fullLaw A f, ∀ i : Fin r.n,
      outputValueQ A f K hK hF (prefixRow r i u) ω=
        oneStep A f K (r.coefficient i) (r.clock i.castSucc) (clamp (r.clock i.castSucc) (r.clock i.succ) u) ω :=
    ae_all_iff.mpr (fun i => by
      rw [show outputValueQ A f K hK hF (prefixRow r i u)=
        (oneStep_memLp_two A f K hK hF (coefficient_bounded_Q A f K hK hF (r.coefficient_bounded i))
          (r.clock i.castSucc) (clamp (r.clock i.castSucc) (r.clock i.succ) u)).toLp
          (oneStep A f K (r.coefficient i) (r.clock i.castSucc) (clamp (r.clock i.castSucc) (r.clock i.succ) u)) from
            interval_output A f K hK hF U _ _ (clamp_bounds _ _ u (row_order r i)).1
              ((clamp_bounds _ _ u (row_order r i)).2.trans (row_horizon r i))
              (r.coefficient i) (r.coefficient_past i) (r.coefficient_bounded i)]
      exact (oneStep_memLp_two A f K hK hF (coefficient_bounded_Q A f K hK hF (r.coefficient_bounded i)) _ _).coeFn_toLp)
  apply Lp.ext
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i => outputValueQ A f K hK hF (prefixRow r i u)),hi,
    (literalPath_memLp_two A f K hK hF r u).coeFn_toLp] with ω hs hi hp
  rw [hs,hp]
  exact Finset.sum_congr rfl (fun i _ => hi i)

/-- Native condExpL2 represents actual conditional expectation on SAME Q. -/
theorem naturalProjection_condExp (u : ℝ≥0) (g : Lp ℝ 2 (fullLaw A f)) :
    (naturalProjection A f u g : (ℝ≥0 → ℝ) → ℝ)=ᵐ[fullLaw A f] (fullLaw A f)[g | naturalFiltration u] := by
  let _ := fullLaw_probability A f K hK hF
  have h := (Lp.memLp g).condExpL2_ae_eq_condExp (𝕜 := ℝ) (naturalFiltration.le u)
  have he : (Lp.memLp g).toLp g=g := Lp.ext (Lp.memLp g).coeFn_toLp
  rw [he] at h
  exact h

private theorem literal_projection {U : ℝ≥0} (r : ElementaryInput U) (u : ℝ≥0) :
    naturalProjection A f u (outputValueQ A f K hK hF r)=
      integralClassProcess A f K hK hF U (representedInput A f K hK hF r) u := by
  rw [integralClassProcess_returns_literal A f K hK hF r u]
  apply Lp.ext
  exact (naturalProjection_condExp A f K hK hF u (outputValueQ A f K hK hF r)).trans
    ((condExp_congr_ae (m := naturalFiltration u) (simpleIntegral_memLp_two A f K hK hF r).coeFn_toLp).trans
      ((literalPath_conditional_terminal A f K hK hF r u).trans (literalPath_memLp_two A f K hK hF r u).coeFn_toLp.symm))

private def representedLinear (U : ℝ≥0) : (ElementaryInput U →₀ ℝ) →ₗ[ℝ] integralDomain A f K hK hF U :=
  Finsupp.linearCombination ℝ (representedInput A f K hK hF)

private theorem representedLinear_coe (U : ℝ≥0) (a : ElementaryInput U →₀ ℝ) :
    (representedLinear A f K hK hF U a : Lp ℝ 2 (inputLawQ A f U))=inputLinear A f K hK hF U a := by
  classical
  simp only [representedLinear,inputLinear,Finsupp.linearCombination_apply,Finsupp.sum,Submodule.coe_sum,Submodule.coe_smul]
  rfl

/-- The actual conditional L2 projection of the returned integral is the
SAME input's actual cutoff integral. Agreement on actual finite inputs is
extended through native dense linear combinations; no desired identity field. -/
theorem integral_projection_identity (U u : ℝ≥0) (g : integralDomain A f K hK hF U) :
    naturalProjection A f u (integral A f K hK hF U g)=integralClassProcess A f K hK hF U g u := by
  let L := (naturalProjection A f u).comp (integral A f K hK hF U)
  let R := integralAt A f K hK hF U u
  have hb (r : ElementaryInput U) : L (representedInput A f K hK hF r)=R (representedInput A f K hK hF r) := by
    change naturalProjection A f u (integral A f K hK hF U (representedInput A f K hK hF r))=
      integralClassProcess A f K hK hF U (representedInput A f K hK hF r) u
    rw [integral_returns_literal]
    exact literal_projection A f K hK hF r u
  have hcomb (a : ElementaryInput U →₀ ℝ) : L (representedLinear A f K hK hF U a)=R (representedLinear A f K hK hF U a) := by
    classical
    simp only [representedLinear,Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul]
    exact Finset.sum_congr rfl (fun r _ => congrArg (fun x => a r • x) (hb r))
  change L g=R g
  refine (inclusion_dense A f K hK hF U).induction_on g (isClosed_eq L.continuous R.continuous) ?_
  intro x
  obtain ⟨a,ha⟩ := x.property
  have hx : inclusionIsometry A f K hK hF U x=representedLinear A f K hK hF U a := by
    apply Subtype.ext
    change (x : Lp ℝ 2 (inputLawQ A f U))=(representedLinear A f K hK hF U a : Lp ℝ 2 (inputLawQ A f U))
    rw [representedLinear_coe]
    exact ha.symm
  rw [hx]
  exact hcomb a

/-- Native original-Fs canonical version of the ACTUAL Q integral process. -/
def integralProcess (U : ℝ≥0) (g : integralDomain A f K hK hF U) (u : ℝ≥0) : (ℝ≥0 → ℝ) → ℝ :=
  (fullLaw A f)[(integral A f K hK hF U g : (ℝ≥0 → ℝ) → ℝ) | naturalFiltration u]

/-- Each canonical value is the actual constructed integral of SAME cutoff
input. This theorem, rather than the condExp name alone, supplies the binding. -/
theorem integralProcess_eq_truncated (U u : ℝ≥0) (g : integralDomain A f K hK hF U) :
    integralProcess A f K hK hF U g u=ᵐ[fullLaw A f] integralClassProcess A f K hK hF U g u := by
  have h := naturalProjection_condExp A f K hK hF u (integral A f K hK hF U g)
  rw [integral_projection_identity A f K hK hF U u g] at h
  exact h.symm

theorem integralProcess_martingale (U : ℝ≥0) (g : integralDomain A f K hK hF U) :
    Martingale (integralProcess A f K hK hF U g) naturalFiltration (fullLaw A f) := by
  let _ := fullLaw_probability A f K hK hF
  exact martingale_condExp (integral A f K hK hF U g) naturalFiltration (fullLaw A f)

theorem integralProcess_stronglyAdapted (U : ℝ≥0) (g : integralDomain A f K hK hF U) :
    StronglyAdapted naturalFiltration (integralProcess A f K hK hF U g) :=
  (integralProcess_martingale A f K hK hF U g).stronglyAdapted

theorem integralProcess_memLp_two (U u : ℝ≥0) (g : integralDomain A f K hK hF U) :
    MemLp (integralProcess A f K hK hF U g u) 2 (fullLaw A f) :=
  (memLp_congr_ae (integralProcess_eq_truncated A f K hK hF U u g)).mpr (Lp.memLp (integralClassProcess A f K hK hF U g u))

theorem integralProcess_energy (U u : ℝ≥0) (g : integralDomain A f K hK hF U) :
    (∫ ω, integralProcess A f K hK hF U g u ω^2 ∂fullLaw A f)=
      ∫ p in BrownianIntegralTimeTruncation.timeSet U u, (g : Lp ℝ 2 (inputLawQ A f U)) p^2 ∂inputLawQ A f U := by
  have he := (integralProcess_eq_truncated A f K hK hF U u g).mono (fun _ h => congrArg (fun x : ℝ => x^2) h)
  rw [integral_congr_ae he,integralClassProcess_energy]

theorem integralProcess_zero (U : ℝ≥0) (g : integralDomain A f K hK hF U) :
    integralProcess A f K hK hF U g 0=ᵐ[fullLaw A f] 0 := by
  have h := integralProcess_eq_truncated A f K hK hF U 0 g
  rw [integralClassProcess_zero] at h
  exact h.trans (Lp.coeFn_zero ℝ 2 (fullLaw A f))

theorem integralProcess_horizon (U : ℝ≥0) (g : integralDomain A f K hK hF U) :
    integralProcess A f K hK hF U g U=ᵐ[fullLaw A f] integral A f K hK hF U g := by
  have h := integralProcess_eq_truncated A f K hK hF U U g
  rw [integralClassProcess_horizon] at h
  exact h

/-- The canonical process returns the actual supplied finite path at EVERY
fixed time, from the same native closure-domain integral. -/
theorem integralProcess_returns_literal {U : ℝ≥0} (r : ElementaryInput U) (u : ℝ≥0) :
    integralProcess A f K hK hF U (representedInput A f K hK hF r) u=ᵐ[fullLaw A f] literalPath A f K r u := by
  have h := integralProcess_eq_truncated A f K hK hF U u (representedInput A f K hK hF r)
  rw [integralClassProcess_returns_literal] at h
  exact h.trans (literalPath_memLp_two A f K hK hF r u).coeFn_toLp

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQIntegralMartingale
