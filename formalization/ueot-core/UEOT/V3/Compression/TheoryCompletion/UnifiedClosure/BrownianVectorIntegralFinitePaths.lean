import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorIntegralL2TimeContinuity

/-!
Original commitment: the SAME joint-vector noise integral needs actual continuous finite paths before any sample-continuous completion.
Existing result: genuine Euclidean full predictable domain and exact literal finite prefixes under the original whole-joint past.
Premise reduced: derive continuous joint-adapted literal paths, their SAME finite native combinations and actual dense approximation.
Model/witness: productLaw d/jointNaturalFiltration/inputLaw d T, finite d including0 and T0/repeated clocks, cross-coordinate START permissions.
Consumer: actual weak maximal approximation and common-AE continuous version; L2 time continuity alone is never used as a path-continuity premise.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorIntegralFinitePaths
open MeasureTheory ProbabilityTheory Set Filter
open BrownianFiniteProductSource BrownianVectorOneStepIntegral BrownianVectorSimplePredictableIntegral
open BrownianCommonRefinement BrownianVectorTimeInput BrownianVectorIntegralClosure
open BrownianVectorPredictableInputs BrownianVectorPredictableDensity BrownianVectorIntegralTimeSource
open BrownianVectorIntegralConditionalSource BrownianVectorIntegralL2TimeContinuity
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
variable (d : ℕ)

/-- Literal finite prefix, using the SAME readout and coefficients as the original record. -/
def literalPath {T : ℝ≥0} (r : (ElementaryInput d) T) (u : ℝ≥0) (ω : Sample d) : ℝ :=
  ∑ i : Fin r.n, (oneStep d) (r.coefficient i) (r.clock i.castSucc)
    (clamp (r.clock i.castSucc) (r.clock i.succ) u) ω

theorem literalPath_continuous {T : ℝ≥0} (r : ElementaryInput d T) (ω : Sample d) :
    Continuous (fun u => literalPath d r u ω) := by
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro k _
  have hc : Continuous (clamp (r.clock i.castSucc) (r.clock i.succ)) :=
    continuous_const.max (continuous_const.min continuous_id)
  exact continuous_const.mul (((coordinate_continuous d k ω).comp hc).sub continuous_const)

private theorem oneStep_stronglyMeasurable_end {H : Fin d → Sample d → ℝ}
    (a b : ℝ≥0) (hab : a ≤ b)
    (hH : ∀ k, StronglyMeasurable[jointNaturalFiltration d a] (H k)) :
    StronglyMeasurable[jointNaturalFiltration d b] (oneStep d H a b) := by
  have he : oneStep d H a b = ∑ k : Fin d, component d H k a b := by
    funext ω
    simp only [oneStep,Finset.sum_apply]
  rw [he]
  exact Finset.stronglyMeasurable_sum _ (fun k _ => component_stronglyMeasurable_end k a b hab (hH k))

/-- A prefix before the coefficient's start is literally zero; the coefficient
is never granted access to an earlier natural past. -/
theorem literalPath_stronglyAdapted {T : ℝ≥0} (r : (ElementaryInput d) T) :
    StronglyAdapted (jointNaturalFiltration d) ((literalPath d) r) := by
  intro u
  have he : (literalPath d) r u = ∑ i : Fin r.n, (oneStep d) (r.coefficient i) (r.clock i.castSucc)
      (clamp (r.clock i.castSucc) (r.clock i.succ) u) := by
    ext ω
    simp only [literalPath,Finset.sum_apply]
  rw [he]
  apply Finset.stronglyMeasurable_sum
  intro i _
  have hab : r.clock i.castSucc ≤ r.clock i.succ :=
    r.clock_mono (by exact_mod_cast Nat.le_succ (i : ℕ))
  by_cases hau : r.clock i.castSucc ≤ u
  · exact (oneStep_stronglyMeasurable_end d _ _ (clamp_bounds _ _ u hab).1
      (r.coefficient_past i)).mono ((jointNaturalFiltration d).mono (max_le hau (min_le_right _ _)))
  · have hcl : clamp (r.clock i.castSucc) (r.clock i.succ) u = r.clock i.castSucc :=
      max_eq_left ((min_le_right _ _).trans (le_of_not_ge hau))
    have hz : (oneStep d) (r.coefficient i) (r.clock i.castSucc)
        (clamp (r.clock i.castSucc) (r.clock i.succ) u) = 0 := by
      ext ω
      simp [oneStep,component,coordinateIncrement,hcl]
    rw [hz]
    exact stronglyMeasurable_zero

theorem literalPath_memLp_two {T : ℝ≥0} (r : (ElementaryInput d) T) (u : ℝ≥0) :
    MemLp ((literalPath d) r u) 2 (productLaw d) :=
  memLp_finsetSum Finset.univ (fun i _ => oneStep_memLp_two (r.coefficient_bounded i) _ _)

/-- Every fixed-time literal prefix is the actual canonical integral process,
proved via the original terminal output and its original conditional prefix. -/
theorem integralProcess_eq_literalPath {T : ℝ≥0} (r : (ElementaryInput d) T) (u : ℝ≥0) :
    (integralProcess d) T ((literalPredictableInput d) r) u =ᵐ[(productLaw d)] (literalPath d) r u :=
  (integralProcess_returns_literal_prefix d) r u

theorem literalPath_martingale {T : ℝ≥0} (r : (ElementaryInput d) T) :
    Martingale ((literalPath d) r) (jointNaturalFiltration d) (productLaw d) :=
  ((integralProcess_martingale d) T ((literalPredictableInput d) r)).congr
    ((literalPath_stronglyAdapted d) r) ((integralProcess_eq_literalPath d) r)

/-- Native finite linear combination of the actual literal inputs. -/
def spanInput (T : ℝ≥0) : ((ElementaryInput d) T →₀ ℝ) →ₗ[ℝ] (fullPredictableL2 d) T :=
  Finsupp.linearCombination ℝ (literalPredictableInput d)

/-- Literal path for exactly the SAME native finite combination. -/
def spanPath {T : ℝ≥0} (a : (ElementaryInput d) T →₀ ℝ) (u : ℝ≥0) (ω : Sample d) : ℝ :=
  a.sum (fun r c => c * (literalPath d) r u ω)

theorem spanPath_continuous {T : ℝ≥0} (a : (ElementaryInput d) T →₀ ℝ) (ω : Sample d) :
    Continuous (fun u => (spanPath d) a u ω) := by
  classical
  exact continuous_finsetSum _ (fun r _ => continuous_const.mul ((literalPath_continuous d) r ω))

theorem spanPath_stronglyAdapted {T : ℝ≥0} (a : (ElementaryInput d) T →₀ ℝ) :
    StronglyAdapted (jointNaturalFiltration d) ((spanPath d) a) := by
  intro u
  have he : (spanPath d) a u = ∑ r ∈ a.support, a r • (literalPath d) r u := by
    ext ω
    simp only [spanPath,Finsupp.sum,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [he]
  exact Finset.stronglyMeasurable_sum _ (fun r _ => ((literalPath_stronglyAdapted d) r u).const_smul (a r))

theorem spanPath_memLp_two {T : ℝ≥0} (a : (ElementaryInput d) T →₀ ℝ) (u : ℝ≥0) :
    MemLp ((spanPath d) a u) 2 (productLaw d) :=
  memLp_finsetSum _ (fun r _ => ((literalPath_memLp_two d) r u).const_mul (a r))

/-- Full predictable integral linearity plus actual source conditional
linearity binds finite sums without a new desired-output certificate. -/
theorem integralProcess_eq_spanPath (T u : ℝ≥0) (a : (ElementaryInput d) T →₀ ℝ) :
    (integralProcess d) T ((spanInput d) T a) u =ᵐ[(productLaw d)] (spanPath d) a u := by
  classical
  have he : (predictableIntegral d) T ((spanInput d) T a) = (outputLinear d) T a := by
    simp only [spanInput,Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul,
      (predictableIntegral_returns_literal d),outputLinear]
  have ht : ((predictableIntegral d) T ((spanInput d) T a) : (Sample d) → ℝ) =ᵐ[(productLaw d)]
      (∑ r ∈ a.support, a r • (simpleIntegral d) r.clock r.coefficient) := by
    rw [he]
    have hi : ∀ᵐ ω ∂(productLaw d), ∀ r ∈ a.support,
        (a r • outputValue r : Lp ℝ 2 (productLaw d)) ω = a r * (simpleIntegral d) r.clock r.coefficient ω := by
      apply (eventually_all_finset a.support).mpr
      intro r _
      filter_upwards [Lp.coeFn_smul (a r) (outputValue r),
        (simpleIntegral_memLp_two r.clock r.coefficient r.coefficient_bounded).coeFn_toLp] with ω hsm hr
      simp only [Pi.smul_apply,smul_eq_mul] at hsm
      rw [hsm]
      exact congrArg (fun x : ℝ => a r * x) hr
    filter_upwards [Lp.coeFn_fun_finsetSum a.support (fun r => a r • outputValue r),hi] with ω hs hi
    rw [show (outputLinear d) T a = ∑ r ∈ a.support, a r • outputValue r from rfl,hs]
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    exact Finset.sum_congr rfl hi
  have hc := condExp_congr_ae (m := (jointNaturalFiltration d) u) ht
  have hs := condExp_finsetSum (s := a.support)
    (fun r _ => ((simpleIntegral_memLp_two r.clock r.coefficient r.coefficient_bounded).integrable one_le_two).smul (a r))
    ((jointNaturalFiltration d) u)
  have hi : ∀ᵐ ω ∂(productLaw d), ∀ r ∈ a.support,
      (productLaw d)[a r • (simpleIntegral d) r.clock r.coefficient | (jointNaturalFiltration d) u] ω =
      a r * (literalPath d) r u ω := by
    apply (eventually_all_finset a.support).mpr
    intro r _
    have hp := (integralProcess_eq_literalPath d) r u
    have ht' := condExp_congr_ae (m := (jointNaturalFiltration d) u)
      (simpleIntegral_memLp_two r.clock r.coefficient r.coefficient_bounded).coeFn_toLp
    unfold integralProcess at hp
    rw [(predictableIntegral_returns_literal d)] at hp
    change (productLaw d)[(simpleIntegral_memLp_two r.clock r.coefficient r.coefficient_bounded).toLp
      ((simpleIntegral d) r.clock r.coefficient) | (jointNaturalFiltration d) u] =ᵐ[(productLaw d)] (literalPath d) r u at hp
    filter_upwards [condExp_smul (a r) ((simpleIntegral d) r.clock r.coefficient) ((jointNaturalFiltration d) u),hp,ht']
      with ω heω hpω htω
    simp only [Pi.smul_apply,smul_eq_mul] at heω
    rw [heω,← htω,hpω]
  apply hc.trans
  apply hs.trans
  filter_upwards [hi] with ω hω
  simp only [Finset.sum_apply,spanPath,Finsupp.sum]
  exact Finset.sum_congr rfl hω

theorem spanPath_martingale (T : ℝ≥0) (a : (ElementaryInput d) T →₀ ℝ) :
    Martingale ((spanPath d) a) (jointNaturalFiltration d) (productLaw d) :=
  ((integralProcess_martingale d) T ((spanInput d) T a)).congr
    ((spanPath_stronglyAdapted d) a) (fun u => (integralProcess_eq_spanPath d) T u a)

/-- The already proved FULL predictable density supplies actual native finite
combinations arbitrarily close to each genuine input; no approximation record is assumed. -/
theorem exists_spanInput_dist_lt (T : ℝ≥0) (f : (fullPredictableL2 d) T) (ε : ℝ) (hε : 0 < ε) :
    ∃ a : (ElementaryInput d) T →₀ ℝ, dist ((spanInput d) T a) f < ε := by
  have hf : (f : Lp (EuclideanSpace ℝ (Fin d)) 2 ((inputLaw d) T)) ∈ closure ((elementarySpan d) T : Set (Lp (EuclideanSpace ℝ (Fin d)) 2 ((inputLaw d) T))) := by
    change (f : Lp (EuclideanSpace ℝ (Fin d)) 2 ((inputLaw d) T)) ∈ (integralDomain d) T
    rw [(integralDomain_eq_fullPredictableL2 d)]
    exact f.property
  obtain ⟨x,hx,hd⟩ := Metric.mem_closure_iff.mp hf ε hε
  obtain ⟨a,ha⟩ := hx
  refine ⟨a,?_⟩
  have he : ((spanInput d) T a : Lp (EuclideanSpace ℝ (Fin d)) 2 ((inputLaw d) T)) = (inputLinear d) T a := by
    simp only [spanInput,inputLinear,Finsupp.linearCombination_apply,Finsupp.sum,Submodule.coe_sum,Submodule.coe_smul]
    rfl
  change dist ((spanInput d) T a : Lp (EuclideanSpace ℝ (Fin d)) 2 ((inputLaw d) T)) (f : Lp (EuclideanSpace ℝ (Fin d)) 2 ((inputLaw d) T)) < ε
  rw [he,ha]
  exact (dist_comm x (f : Lp (EuclideanSpace ℝ (Fin d)) 2 ((inputLaw d) T))).trans_lt hd

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorIntegralFinitePaths
