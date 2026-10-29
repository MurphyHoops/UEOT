import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralL2TimeContinuity

/-!
Original commitment: completion must preserve the actual finite continuous source paths that approximate the integral.
Existing result: the same literal terminal output has proved arbitrary-time conditional prefix identities.
Premise reduced: derive continuous, genuinely naturally adapted finite-prefix paths and bind their finite combinations.
Model/witness: SAME fixed horizon/sourceLaw/process; all actual permitted finite records and their native finite span.
Consumer: weak maximal control and continuous modification; no full-input continuous-path field is assumed.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralFinitePaths
open MeasureTheory ProbabilityTheory Set Filter
open BrownianContinuousSource BrownianProjectiveSource BrownianMartingaleSource BrownianOneStepIntegral
open BrownianSimplePredictableIntegral BrownianCommonRefinement BrownianTimeIntegrand BrownianIntegralClosure
open BrownianPredictableInputs BrownianPredictableDensity BrownianIntegralConditionalStep BrownianIntegralMartingale
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- Literal finite prefix, using the SAME readout and coefficients as the original record. -/
def literalPath {T : ℝ≥0} (r : ElementaryInput T) (u : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ :=
  ∑ i : Fin r.n, oneStep (r.coefficient i) (r.clock i.castSucc)
    (clamp (r.clock i.castSucc) (r.clock i.succ) u) ω

theorem literalPath_continuous {T : ℝ≥0} (r : ElementaryInput T) (ω : ℝ≥0 → ℝ) :
    Continuous (fun u => literalPath r u ω) := by
  apply continuous_finsetSum
  intro i _
  have hc : Continuous (clamp (r.clock i.castSucc) (r.clock i.succ)) :=
    continuous_const.max (continuous_const.min continuous_id)
  exact continuous_const.mul (((process_continuous ω).comp hc).sub continuous_const)

/-- A prefix before the coefficient's start is literally zero; the coefficient
is never granted access to an earlier natural past. -/
theorem literalPath_stronglyAdapted {T : ℝ≥0} (r : ElementaryInput T) :
    StronglyAdapted naturalFiltration (literalPath r) := by
  intro u
  have he : literalPath r u = ∑ i : Fin r.n, oneStep (r.coefficient i) (r.clock i.castSucc)
      (clamp (r.clock i.castSucc) (r.clock i.succ) u) := by
    ext ω
    simp only [literalPath,Finset.sum_apply]
  rw [he]
  apply Finset.stronglyMeasurable_sum
  intro i _
  have hab : r.clock i.castSucc ≤ r.clock i.succ :=
    r.clock_mono (by exact_mod_cast Nat.le_succ (i : ℕ))
  by_cases hau : r.clock i.castSucc ≤ u
  · exact (oneStep_stronglyMeasurable_end _ _ (clamp_bounds _ _ u hab).1
      (r.coefficient_past i)).mono (naturalFiltration.mono (max_le hau (min_le_right _ _)))
  · have hcl : clamp (r.clock i.castSucc) (r.clock i.succ) u = r.clock i.castSucc :=
      max_eq_left ((min_le_right _ _).trans (le_of_not_ge hau))
    have hz : oneStep (r.coefficient i) (r.clock i.castSucc)
        (clamp (r.clock i.castSucc) (r.clock i.succ) u) = 0 := by
      ext ω
      simp [oneStep,increment,hcl]
    rw [hz]
    exact stronglyMeasurable_zero

theorem literalPath_memLp_two {T : ℝ≥0} (r : ElementaryInput T) (u : ℝ≥0) :
    MemLp (literalPath r u) 2 sourceLaw :=
  memLp_finsetSum Finset.univ (fun i _ => oneStep_memLp_two (r.coefficient_bounded i) _ _)

/-- Every fixed-time literal prefix is the actual canonical integral process,
proved via the original terminal output and its original conditional prefix. -/
theorem integralProcess_eq_literalPath {T : ℝ≥0} (r : ElementaryInput T) (u : ℝ≥0) :
    integralProcess T (literalPredictableInput r) u =ᵐ[sourceLaw] literalPath r u := by
  have ht : (predictableIntegral T (literalPredictableInput r) : (ℝ≥0 → ℝ) → ℝ) =ᵐ[sourceLaw]
      simpleIntegral r.clock r.coefficient := by
    rw [predictableIntegral_returns_literal]
    exact (simpleIntegral_memLp_two r.clock r.coefficient r.coefficient_bounded).coeFn_toLp
  have ha := condExp_congr_ae (m := naturalFiltration u) ht
  have hs := condExp_finsetSum (s := Finset.univ)
    (fun i _ => oneStep_integrable (r.coefficient_bounded i) (r.clock i.castSucc) (r.clock i.succ))
    (naturalFiltration u)
  have hi : ∀ᵐ ω ∂sourceLaw, ∀ i : Fin r.n,
      sourceLaw[oneStep (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ) | naturalFiltration u] ω =
      oneStep (r.coefficient i) (r.clock i.castSucc) (clamp (r.clock i.castSucc) (r.clock i.succ) u) ω :=
    ae_all_iff.mpr (fun i => oneStep_condExp_prefix _ _ u
      (r.clock_mono (by exact_mod_cast Nat.le_succ (i : ℕ)))
      (r.coefficient_past i) (r.coefficient_bounded i))
  apply ha.trans
  have he : simpleIntegral r.clock r.coefficient = ∑ i : Fin r.n,
      oneStep (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ) := by
    ext ω
    simp only [simpleIntegral,Finset.sum_apply]
  rw [he]
  apply hs.trans
  filter_upwards [hi] with ω hω
  simp only [Finset.sum_apply,literalPath]
  exact Finset.sum_congr rfl (fun i _ => hω i)

theorem literalPath_martingale {T : ℝ≥0} (r : ElementaryInput T) :
    Martingale (literalPath r) naturalFiltration sourceLaw :=
  (integralProcess_martingale T (literalPredictableInput r)).congr
    (literalPath_stronglyAdapted r) (integralProcess_eq_literalPath r)

/-- Native finite linear combination of the actual literal inputs. -/
def spanInput (T : ℝ≥0) : (ElementaryInput T →₀ ℝ) →ₗ[ℝ] fullPredictableL2 T :=
  Finsupp.linearCombination ℝ literalPredictableInput

/-- Literal path for exactly the SAME native finite combination. -/
def spanPath {T : ℝ≥0} (a : ElementaryInput T →₀ ℝ) (u : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ :=
  a.sum (fun r c => c * literalPath r u ω)

theorem spanPath_continuous {T : ℝ≥0} (a : ElementaryInput T →₀ ℝ) (ω : ℝ≥0 → ℝ) :
    Continuous (fun u => spanPath a u ω) := by
  classical
  exact continuous_finsetSum _ (fun r _ => continuous_const.mul (literalPath_continuous r ω))

theorem spanPath_stronglyAdapted {T : ℝ≥0} (a : ElementaryInput T →₀ ℝ) :
    StronglyAdapted naturalFiltration (spanPath a) := by
  intro u
  have he : spanPath a u = ∑ r ∈ a.support, a r • literalPath r u := by
    ext ω
    simp only [spanPath,Finsupp.sum,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [he]
  exact Finset.stronglyMeasurable_sum _ (fun r _ => (literalPath_stronglyAdapted r u).const_smul (a r))

theorem spanPath_memLp_two {T : ℝ≥0} (a : ElementaryInput T →₀ ℝ) (u : ℝ≥0) :
    MemLp (spanPath a u) 2 sourceLaw :=
  memLp_finsetSum _ (fun r _ => (literalPath_memLp_two r u).const_mul (a r))

private theorem lp_sum_coe {ι : Type*} (s : Finset ι) (F : ι → Lp ℝ 2 sourceLaw) :
    (∑ i ∈ s, F i : Lp ℝ 2 sourceLaw) =ᵐ[sourceLaw] fun ω => ∑ i ∈ s, F i ω := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℝ 2 sourceLaw] with ω hω
    simp only [Finset.sum_empty]
    exact hω
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (F i) (∑ j ∈ s, F j),ih] with ω ha hs
    simp only [Pi.add_apply] at ha
    rw [ha,hs]

/-- Full predictable integral linearity plus actual source conditional
linearity binds finite sums without a new desired-output certificate. -/
theorem integralProcess_eq_spanPath (T u : ℝ≥0) (a : ElementaryInput T →₀ ℝ) :
    integralProcess T (spanInput T a) u =ᵐ[sourceLaw] spanPath a u := by
  classical
  have he : predictableIntegral T (spanInput T a) = outputLinear T a := by
    simp only [spanInput,Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul,
      predictableIntegral_returns_literal,outputLinear]
  have ht : (predictableIntegral T (spanInput T a) : (ℝ≥0 → ℝ) → ℝ) =ᵐ[sourceLaw]
      (∑ r ∈ a.support, a r • simpleIntegral r.clock r.coefficient) := by
    rw [he]
    have hi : ∀ᵐ ω ∂sourceLaw, ∀ r ∈ a.support,
        (a r • outputValue r : Lp ℝ 2 sourceLaw) ω = a r * simpleIntegral r.clock r.coefficient ω := by
      apply (eventually_all_finset a.support).mpr
      intro r _
      filter_upwards [Lp.coeFn_smul (a r) (outputValue r),
        (simpleIntegral_memLp_two r.clock r.coefficient r.coefficient_bounded).coeFn_toLp] with ω hsm hr
      simp only [Pi.smul_apply,smul_eq_mul] at hsm
      rw [hsm]
      exact congrArg (fun x : ℝ => a r * x) hr
    filter_upwards [lp_sum_coe a.support (fun r => a r • outputValue r),hi] with ω hs hi
    rw [show outputLinear T a = ∑ r ∈ a.support, a r • outputValue r from rfl,hs]
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    exact Finset.sum_congr rfl hi
  have hc := condExp_congr_ae (m := naturalFiltration u) ht
  have hs := condExp_finsetSum (s := a.support)
    (fun r _ => ((simpleIntegral_memLp_two r.clock r.coefficient r.coefficient_bounded).integrable one_le_two).smul (a r))
    (naturalFiltration u)
  have hi : ∀ᵐ ω ∂sourceLaw, ∀ r ∈ a.support,
      sourceLaw[a r • simpleIntegral r.clock r.coefficient | naturalFiltration u] ω =
      a r * literalPath r u ω := by
    apply (eventually_all_finset a.support).mpr
    intro r _
    have hp := integralProcess_eq_literalPath r u
    have ht' := condExp_congr_ae (m := naturalFiltration u)
      (simpleIntegral_memLp_two r.clock r.coefficient r.coefficient_bounded).coeFn_toLp
    unfold integralProcess at hp
    rw [predictableIntegral_returns_literal] at hp
    change sourceLaw[(simpleIntegral_memLp_two r.clock r.coefficient r.coefficient_bounded).toLp
      (simpleIntegral r.clock r.coefficient) | naturalFiltration u] =ᵐ[sourceLaw] literalPath r u at hp
    filter_upwards [condExp_smul (a r) (simpleIntegral r.clock r.coefficient) (naturalFiltration u),hp,ht']
      with ω heω hpω htω
    simp only [Pi.smul_apply,smul_eq_mul] at heω
    rw [heω,← htω,hpω]
  apply hc.trans
  apply hs.trans
  filter_upwards [hi] with ω hω
  simp only [Finset.sum_apply,spanPath,Finsupp.sum]
  exact Finset.sum_congr rfl hω

theorem spanPath_martingale (T : ℝ≥0) (a : ElementaryInput T →₀ ℝ) :
    Martingale (spanPath a) naturalFiltration sourceLaw :=
  (integralProcess_martingale T (spanInput T a)).congr
    (spanPath_stronglyAdapted a) (fun u => integralProcess_eq_spanPath T u a)

/-- The already proved FULL predictable density supplies actual native finite
combinations arbitrarily close to each genuine input; no approximation record is assumed. -/
theorem exists_spanInput_dist_lt (T : ℝ≥0) (f : fullPredictableL2 T) (ε : ℝ) (hε : 0 < ε) :
    ∃ a : ElementaryInput T →₀ ℝ, dist (spanInput T a) f < ε := by
  have hf : (f : Lp ℝ 2 (inputLaw T)) ∈ closure (elementarySpan T : Set (Lp ℝ 2 (inputLaw T))) := by
    change (f : Lp ℝ 2 (inputLaw T)) ∈ integralDomain T
    rw [integralDomain_eq_fullPredictableL2]
    exact f.property
  obtain ⟨x,hx,hd⟩ := Metric.mem_closure_iff.mp hf ε hε
  obtain ⟨a,ha⟩ := hx
  refine ⟨a,?_⟩
  have he : (spanInput T a : Lp ℝ 2 (inputLaw T)) = inputLinear T a := by
    simp only [spanInput,inputLinear,Finsupp.linearCombination_apply,Finsupp.sum,Submodule.coe_sum,Submodule.coe_smul]
    rfl
  change dist (spanInput T a : Lp ℝ 2 (inputLaw T)) (f : Lp ℝ 2 (inputLaw T)) < ε
  rw [he,ha]
  exact (dist_comm x (f : Lp ℝ 2 (inputLaw T))).trans_lt hd

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralFinitePaths
