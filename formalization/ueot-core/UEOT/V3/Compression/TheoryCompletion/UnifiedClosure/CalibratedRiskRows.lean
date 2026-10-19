import UEOT.V3.FiniteRecurrentDecompositionStability
import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCApproximateLumpability
import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCModelKernelReconciliation
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StochasticPredictiveRobustObservability

/-!
Temporary integration draft.  Compiler validation is centralized in root.

Finite probability rows retain the project's measure/event normalization of
total variation.  A coordinate error budget is converted into a probability
budget by the already public half-L1 identity; normalization gives the cap 1.
The calibration composition below keeps errors of the two measured rows
separate and makes no statistical coverage claim without supplied bounds.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

noncomputable section

open scoped BigOperators
open UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
open UEOT.V3.Compression.RecursiveSufficientState

universe uX uY uA uR uO uI

theorem pmf_tv_le_clipped_coordinate_budget
    {Y : Type uY} [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (p q : PMF Y) (gamma : Y → ℝ)
    (hcoord : ∀ y, |(p y).toReal - (q y).toReal| ≤ gamma y) :
    UEOT.V3.TotalVariation.tvDist p.toMeasure q.toMeasure ≤
      min 1 ((1 / 2 : ℝ) * ∑ y, gamma y) := by
  apply le_min (UEOT.V3.TotalVariation.tvDist_le_one _ _)
  rw [UEOT.V3.FiniteRecurrentDecompositionStability.pmf_tv_eq_half_sum_abs]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Finset.sum_le_sum fun y _ => hcoord y

/-- Separate absolute calibration errors around two empirical coordinate rows
combine with their measured discrepancy before the true normalized PMF rows
are compared in total variation. Empirical rows need not be probabilities. -/
theorem calibrated_pmf_tv_budget
    {Y : Type uY} [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (p q : PMF Y) (pMeasured qMeasured alpha eta beta : Y → ℝ)
    (hp : ∀ y, |(p y).toReal - pMeasured y| ≤ alpha y)
    (hmeasured : ∀ y, |pMeasured y - qMeasured y| ≤ eta y)
    (hq : ∀ y, |qMeasured y - (q y).toReal| ≤ beta y) :
    UEOT.V3.TotalVariation.tvDist p.toMeasure q.toMeasure ≤
      min 1 ((1 / 2 : ℝ) * ∑ y, (alpha y + eta y + beta y)) := by
  apply pmf_tv_le_clipped_coordinate_budget
  intro y
  have hleft := abs_sub_le (p y).toReal (pMeasured y) (q y).toReal
  have hright := abs_sub_le (pMeasured y) (qMeasured y) (q y).toReal
  have hpy := hp y
  have hmy := hmeasured y
  have hqy := hq y
  linarith

/-- The existing exact real-row PMF constructor applied to the SAME source
transition table used by SISC's future-word and class-mass theorems. -/
def finiteKernelRowPMF
    {X : Type uX} {A : Type uA} [Fintype X]
    (K : FiniteControlledStochasticKernel X A) (x : X) (a : A) : PMF X :=
  UEOT.V3.FiniteDiscountedControl.FiniteProbabilityRow.ofRealRow
    (K.mass x a) (K.nonneg x a) (K.normalized x a)

@[simp] theorem finiteKernelRowPMF_apply_toReal
    {X : Type uX} {A : Type uA} [Fintype X]
    (K : FiniteControlledStochasticKernel X A) (x : X) (a : A) (z : X) :
    ((finiteKernelRowPMF K x a) z).toReal = K.mass x a z := by
  exact UEOT.V3.FiniteDiscountedControl.FiniteProbabilityRow.ofRealRow_apply_toReal
    (K.mass x a) (K.nonneg x a) (K.normalized x a) z

/-- Ordinary PMF pushforward has exactly the already registered real class
masses. No lumpability or representative-independence premise is needed. -/
theorem finiteKernelRowPMF_map_toReal
    {X : Type uX} {A : Type uA} {Y : Type uY} [Fintype X]
    (K : FiniteControlledStochasticKernel X A) (q : X → Y)
    (x : X) (a : A) (c : ReachableState q) :
    (((finiteKernelRowPMF K x a).map (toReachable q)) c).toReal =
      massIntoClass K q x a c := by
  classical
  rw [PMF.map_apply, tsum_fintype]
  rw [ENNReal.toReal_sum (by
    intro z _
    split_ifs
    · exact PMF.apply_ne_top (finiteKernelRowPMF K x a) z
    · exact ENNReal.zero_ne_top)]
  unfold massIntoClass
  apply Finset.sum_congr rfl
  intro z _
  have hclass : c = toReachable q z ↔ q z = c.1 := by
    constructor
    · intro h
      exact (congrArg Subtype.val h).symm
    · intro h
      exact Subtype.ext h.symm
  by_cases h : q z = c.1
  · simp [hclass.mpr h, h]
  · have hne : c ≠ toReachable q z := fun hc => h (hclass.mp hc)
    simp [hne, h]

/-- Quantitative future-word observability controls TV of actual normalized
pushforwards of the same K/read source. The target is the canonical predictive
class space, and the current readout agreement is stated explicitly. -/
theorem quantitative_future_probe_tv_budget
    {X : Type uX} {A : Type uA} {O : Type uO} {I : Type uI}
    [Fintype X] [Fintype I] [DecidableEq O]
    (K : FiniteControlledStochasticKernel X A) (read : X → O)
    (probe : I → List (A × O))
    (coeff : ReachableState (stochasticFuture K read) → I → ℝ)
    (hresolve : FutureTestsResolvePredictiveClasses K read probe coeff)
    (x y : X) (a : A) (hread : read x = read y)
    (eps : I → ℝ)
    (hprobe : ∀ i,
      |stochasticFuture K read x ((a, read x) :: probe i) -
       stochasticFuture K read y ((a, read x) :: probe i)| ≤ eps i) :
    letI : Fintype (ReachableState (stochasticFuture K read)) := Fintype.ofFinite _
    letI : MeasurableSpace (ReachableState (stochasticFuture K read)) := ⊤
    UEOT.V3.TotalVariation.tvDist
      ((finiteKernelRowPMF K x a).map (toReachable (stochasticFuture K read))).toMeasure
      ((finiteKernelRowPMF K y a).map (toReachable (stochasticFuture K read))).toMeasure ≤
      min 1 ((1 / 2 : ℝ) * ∑ c, ∑ i, |coeff c i| * eps i) := by
  classical
  let _ : Fintype (ReachableState (stochasticFuture K read)) := Fintype.ofFinite _
  let _ : MeasurableSpace (ReachableState (stochasticFuture K read)) := ⊤
  apply pmf_tv_le_clipped_coordinate_budget
  intro c
  simp only [finiteKernelRowPMF_map_toReal]
  exact quantitative_future_probe_mass_defect K read probe coeff hresolve
    x y a hread eps hprobe c

/-- Calibrated empirical future-word responses supply the true probe budget
consumed above. Separate source calibration radii plus the observed discrepancy
are amplified only by the existing indicator-reconstruction coefficients.
Coverage probabilities of the supplied calibration inequalities are external. -/
theorem calibrated_future_probe_tv_budget
    {X : Type uX} {A : Type uA} {O : Type uO} {I : Type uI}
    [Fintype X] [Fintype I] [DecidableEq O]
    (K : FiniteControlledStochasticKernel X A) (read : X → O)
    (probe : I → List (A × O))
    (coeff : ReachableState (stochasticFuture K read) → I → ℝ)
    (hresolve : FutureTestsResolvePredictiveClasses K read probe coeff)
    (x y : X) (a : A) (hread : read x = read y)
    (xMeasured yMeasured alpha beta : I → ℝ)
    (hx : ∀ i,
      |stochasticFuture K read x ((a, read x) :: probe i) - xMeasured i| ≤ alpha i)
    (hy : ∀ i,
      |stochasticFuture K read y ((a, read x) :: probe i) - yMeasured i| ≤ beta i) :
    letI : Fintype (ReachableState (stochasticFuture K read)) := Fintype.ofFinite _
    letI : MeasurableSpace (ReachableState (stochasticFuture K read)) := ⊤
    UEOT.V3.TotalVariation.tvDist
      ((finiteKernelRowPMF K x a).map (toReachable (stochasticFuture K read))).toMeasure
      ((finiteKernelRowPMF K y a).map (toReachable (stochasticFuture K read))).toMeasure ≤
      min 1 ((1 / 2 : ℝ) * ∑ c, ∑ i,
        |coeff c i| * (alpha i + |xMeasured i - yMeasured i| + beta i)) := by
  apply quantitative_future_probe_tv_budget K read probe coeff hresolve x y a hread
  intro i
  have hleft := abs_sub_le
    (stochasticFuture K read x ((a, read x) :: probe i)) (xMeasured i)
    (stochasticFuture K read y ((a, read x) :: probe i))
  have hright := abs_sub_le (xMeasured i) (yMeasured i)
    (stochasticFuture K read y ((a, read x) :: probe i))
  have hxi := hx i
  have hyi :
      |yMeasured i - stochasticFuture K read y ((a, read x) :: probe i)| ≤ beta i := by
    simpa only [abs_sub_comm] using hy i
  linarith

/-- A chosen finite partition with approximate indicator reconstruction and
approximately agreeing observations yields a true stochastic row budget.
The class count and uniform coefficient L1 bound expose the conditioning cost;
the theorem does not assert that the approximate quotient is exactly Markov. -/
theorem approximate_observable_partition_tv_budget
    {X : Type uX} {A : Type uA} {R : Type uR} {O : Type uO} {I : Type uI}
    [Fintype X] [Fintype A] [Fintype I]
    (M : UEOT.V3.FiniteStablePartition.Model X A R O) (S : Setoid X)
    (test : I → X → ℝ) (coeff : X → I → ℝ) (delta eps kappa : ℝ)
    (hspan : ApproxSpansPartitionIndicators S test coeff delta)
    (hobs : ApproxSameTestExpectationsOnFibers M S test eps)
    (heps : 0 ≤ eps) (hcondition : ∀ z, ∑ i, |coeff z i| ≤ kappa)
    {x y : X} (hxy : S.r x y) (a : A) :
    letI : Fintype (ReachableState (setoidRepresentation S)) := Fintype.ofFinite _
    letI : MeasurableSpace (ReachableState (setoidRepresentation S)) := ⊤
    UEOT.V3.TotalVariation.tvDist
      ((finiteKernelRowPMF (modelAsFiniteKernel M) x a).map
        (toReachable (setoidRepresentation S))).toMeasure
      ((finiteKernelRowPMF (modelAsFiniteKernel M) y a).map
        (toReachable (setoidRepresentation S))).toMeasure ≤
      min 1 ((1 / 2 : ℝ) *
        ((Fintype.card (ReachableState (setoidRepresentation S)) : ℝ) *
          (2 * delta + eps * kappa))) := by
  classical
  let _ : Fintype (ReachableState (setoidRepresentation S)) := Fintype.ofFinite _
  let _ : MeasurableSpace (ReachableState (setoidRepresentation S)) := ⊤
  have hcoord (c : ReachableState (setoidRepresentation S)) :
      |(((finiteKernelRowPMF (modelAsFiniteKernel M) x a).map
          (toReachable (setoidRepresentation S))) c).toReal -
        (((finiteKernelRowPMF (modelAsFiniteKernel M) y a).map
          (toReachable (setoidRepresentation S))) c).toReal| ≤
        2 * delta + eps * kappa := by
    obtain ⟨z, rfl⟩ := toReachable_surjective (setoidRepresentation S) c
    simp only [finiteKernelRowPMF_map_toReal, model_class_mass_reconciliation]
    exact (robust_class_mass_from_approx_observable_tests
      M S test coeff delta eps hspan hobs hxy a z).trans
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hcondition z) heps))
  have htv := pmf_tv_le_clipped_coordinate_budget
    ((finiteKernelRowPMF (modelAsFiniteKernel M) x a).map
      (toReachable (setoidRepresentation S)))
    ((finiteKernelRowPMF (modelAsFiniteKernel M) y a).map
      (toReachable (setoidRepresentation S)))
    (fun _ => 2 * delta + eps * kappa) hcoord
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using htv

/-- Calibrated one-step experiments give an approximate chosen-partition row
budget without assuming true test agreement. Each source expectation lies
within `rho` of its measured value; same-fibre measured responses differ by
at most `eta`. These hypotheses supply the SISC error `eta + 2*rho` and hence
an actual normalized PMF TV budget usable by a finite-horizon risk theorem. -/
theorem calibrated_observable_partition_tv_budget
    {X : Type uX} {A : Type uA} {R : Type uR} {O : Type uO} {I : Type uI}
    [Fintype X] [Fintype A] [Fintype I]
    (M : UEOT.V3.FiniteStablePartition.Model X A R O) (S : Setoid X)
    (test : I → X → ℝ) (coeff : X → I → ℝ)
    (measured : A → X → I → ℝ) (delta eta rho kappa : ℝ)
    (hspan : ApproxSpansPartitionIndicators S test coeff delta)
    (hcal : ∀ a x i,
      |transitionTestExpectation M (test i) a x - measured a x i| ≤ rho)
    (hmeasured : ∀ ⦃x y⦄, S.r x y → ∀ a i,
      |measured a x i - measured a y i| ≤ eta)
    (heta : 0 ≤ eta) (hrho : 0 ≤ rho)
    (hcondition : ∀ z, ∑ i, |coeff z i| ≤ kappa)
    {x y : X} (hxy : S.r x y) (a : A) :
    letI : Fintype (ReachableState (setoidRepresentation S)) := Fintype.ofFinite _
    letI : MeasurableSpace (ReachableState (setoidRepresentation S)) := ⊤
    UEOT.V3.TotalVariation.tvDist
      ((finiteKernelRowPMF (modelAsFiniteKernel M) x a).map
        (toReachable (setoidRepresentation S))).toMeasure
      ((finiteKernelRowPMF (modelAsFiniteKernel M) y a).map
        (toReachable (setoidRepresentation S))).toMeasure ≤
      min 1 ((1 / 2 : ℝ) *
        ((Fintype.card (ReachableState (setoidRepresentation S)) : ℝ) *
          (2 * delta + (eta + 2 * rho) * kappa))) := by
  have hobs : ApproxSameTestExpectationsOnFibers M S test (eta + 2 * rho) := by
    intro s t hst b i
    have hleft := abs_sub_le (transitionTestExpectation M (test i) b s)
      (measured b s i) (transitionTestExpectation M (test i) b t)
    have hright := abs_sub_le (measured b s i) (measured b t i)
      (transitionTestExpectation M (test i) b t)
    have hs := hcal b s i
    have ht : |measured b t i - transitionTestExpectation M (test i) b t| ≤ rho := by
      simpa only [abs_sub_comm] using hcal b t i
    have hm := hmeasured hst b i
    linarith
  exact approximate_observable_partition_tv_budget M S test coeff
    delta (eta + 2 * rho) kappa hspan hobs (by positivity) hcondition hxy a

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
