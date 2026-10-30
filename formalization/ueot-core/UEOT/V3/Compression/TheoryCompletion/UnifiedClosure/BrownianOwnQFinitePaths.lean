import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQConditionalStep

/-!
Original commitment: the actual ownQ finite strategy has a genuine continuous original-Fs martingale PATH, not only a terminal value or row-clock prefix.
Existing result: actual W/Q one-step arbitrary-clock conditional prefixes, original START permissions and actual literal finite sums.
Premise reduced: construct that SAME finite strategy's all-time clamped literal path, prove original-Fs adaptation/continuity and actual conditional-terminal identity/martingale.
Model/witness: fixed bounded source f on A, SAME Q_A/W, arbitrary supplied ElementaryInput U with source-essentially bounded START rows, U independent of A including zero/repeats.
Consumer/boundary: real finite path inputs for Q closed-span conditional/continuous integral extension; no full Q predictable density or completed-filtration shortcut.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQFinitePaths
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianMartingaleSource BrownianCommonRefinement BrownianTimeIntegrand BrownianPredictableInputs BrownianIntegralClosure
open BrownianBoundedControlSource BrownianBoundedExponentialLimitSource BrownianBoundedGirsanovSource
open BrownianOwnQOneStepIntegral BrownianOwnQSimpleIntegral BrownianOwnQConditionalStep
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
variable (A : ℝ≥0) (f : fullPredictableL2 A) (K : ℝ) (hK : 0≤K)
    (hF : ∀ᵐ p ∂inputLaw A, |(f : Lp ℝ 2 (inputLaw A)) p|≤K)

def literalPath {U : ℝ≥0} (r : ElementaryInput U) (u : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ :=
  ∑ i : Fin r.n, oneStep A f K (r.coefficient i) (r.clock i.castSucc)
    (clamp (r.clock i.castSucc) (r.clock i.succ) u) ω

include hK in
/-- Every sample literal path is continuous; AE row bounds are not silently
upgraded to all-sample bounds on its coefficients. -/
theorem literalPath_continuous {U : ℝ≥0} (r : ElementaryInput U) (ω : ℝ≥0 → ℝ) :
    Continuous (fun u => literalPath A f K r u ω) := by
  apply continuous_finsetSum
  intro i _
  have hc : Continuous (clamp (r.clock i.castSucc) (r.clock i.succ)) :=
    continuous_const.max (continuous_const.min continuous_id)
  change Continuous (fun u => r.coefficient i ω*(shiftedProcess A f K (clamp (r.clock i.castSucc) (r.clock i.succ) u) ω-
    shiftedProcess A f K (r.clock i.castSucc) ω))
  exact continuous_const.mul (((shiftedProcess_continuous A f K hK ω).comp hc).sub continuous_const)

/-- A coefficient belonging to a later START is multiplied by a literally
zero prefix before START; no earlier permission is granted to H. -/
theorem literalPath_stronglyAdapted {U : ℝ≥0} (r : ElementaryInput U) :
    StronglyAdapted naturalFiltration (literalPath A f K r) := by
  intro u
  have he : literalPath A f K r u=∑ i : Fin r.n, oneStep A f K (r.coefficient i) (r.clock i.castSucc)
      (clamp (r.clock i.castSucc) (r.clock i.succ) u) := by
    ext ω
    simp only [literalPath,Finset.sum_apply]
  rw [he]
  apply Finset.stronglyMeasurable_sum
  intro i _
  have hab : r.clock i.castSucc≤r.clock i.succ := r.clock_mono (by exact_mod_cast Nat.le_succ (i : ℕ))
  by_cases hau : r.clock i.castSucc≤u
  · exact (oneStep_past_end A f K _ _ (clamp_bounds _ _ u hab).1
      (r.coefficient_past i)).mono (naturalFiltration.mono (max_le hau (min_le_right _ _)))
  · have hcl : clamp (r.clock i.castSucc) (r.clock i.succ) u=r.clock i.castSucc :=
      max_eq_left ((min_le_right _ _).trans (le_of_not_ge hau))
    have hz : oneStep A f K (r.coefficient i) (r.clock i.castSucc)
        (clamp (r.clock i.castSucc) (r.clock i.succ) u)=0 := by
      ext ω
      simp [oneStep,fullIncrement,hcl]
    rw [hz]
    exact stronglyMeasurable_zero

include hK hF

theorem literalPath_memLp_two {U : ℝ≥0} (r : ElementaryInput U) (u : ℝ≥0) :
    MemLp (literalPath A f K r u) 2 (fullLaw A f) :=
  memLp_finsetSum Finset.univ (fun i _ => oneStep_memLp_two A f K hK hF
    (coefficient_bounded_Q A f K hK hF (r.coefficient_bounded i)) _ _)

/-- Every actual clamped finite path value is the conditional prefix of the
SAME actual terminal finite integral, on SAME Q and ENTIRE original Fs. -/
theorem literalPath_conditional_terminal {U : ℝ≥0} (r : ElementaryInput U) (u : ℝ≥0) :
    (fullLaw A f)[simpleIntegral A f K r | naturalFiltration u]=ᵐ[fullLaw A f] literalPath A f K r u := by
  let _ := fullLaw_probability A f K hK hF
  have hs := condExp_finsetSum (s := Finset.univ)
    (fun i _ => (oneStep_memLp_two A f K hK hF (coefficient_bounded_Q A f K hK hF (r.coefficient_bounded i))
      (r.clock i.castSucc) (r.clock i.succ)).integrable one_le_two) (naturalFiltration u)
  have hi : ∀ᵐ ω ∂fullLaw A f, ∀ i : Fin r.n,
      (fullLaw A f)[oneStep A f K (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ) | naturalFiltration u] ω=
      oneStep A f K (r.coefficient i) (r.clock i.castSucc) (clamp (r.clock i.castSucc) (r.clock i.succ) u) ω :=
    ae_all_iff.mpr (fun i => oneStep_condExp_prefix A f K hK hF _ _ u
      (r.clock_mono (by exact_mod_cast Nat.le_succ (i : ℕ))) (r.coefficient_past i)
      (coefficient_bounded_Q A f K hK hF (r.coefficient_bounded i)))
  have he : simpleIntegral A f K r=∑ i : Fin r.n,
      oneStep A f K (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ) := by
    ext ω
    simp only [simpleIntegral,Finset.sum_apply]
  rw [he]
  apply hs.trans
  filter_upwards [hi] with ω hω
  simp only [Finset.sum_apply,literalPath]
  exact Finset.sum_congr rfl (fun i _ => hω i)

theorem literalPath_martingale {U : ℝ≥0} (r : ElementaryInput U) :
    Martingale (literalPath A f K r) naturalFiltration (fullLaw A f) := by
  let _ := fullLaw_probability A f K hK hF
  exact (martingale_condExp (simpleIntegral A f K r) naturalFiltration (fullLaw A f)).congr
    (literalPath_stronglyAdapted A f K r) (literalPath_conditional_terminal A f K hK hF r)

omit hK hF in
theorem literalPath_zero {U : ℝ≥0} (r : ElementaryInput U) : literalPath A f K r 0=0 := by
  ext ω
  simp [literalPath,clamp,oneStep,fullIncrement]

omit hK hF in
/-- At U the SAME actual terminal literal integral is returned pointwise. -/
theorem literalPath_horizon {U : ℝ≥0} (r : ElementaryInput U) :
    literalPath A f K r U=simpleIntegral A f K r := by
  ext ω
  apply Finset.sum_congr rfl
  intro i _
  have hab : r.clock i.castSucc≤r.clock i.succ := r.clock_mono (by exact_mod_cast Nat.le_succ (i : ℕ))
  have hbU : r.clock i.succ≤U := (r.clock_mono (Fin.le_last _)).trans r.clock_end.le
  simp only [clamp,min_eq_left hbU,max_eq_right hab]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQFinitePaths
