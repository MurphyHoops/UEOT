import UEOT.V3.Compression.Objecthood.ResourceClosure.MeanResourceClosure

/-!
# Theory Completion P6.5 — starvation and resource-closure boundaries

P6 deliberately distinguishes three claims:

1. mean/expected resource sustainability;
2. finite-horizon expected-accounting viability;
3. realized deterministic/pathwise resource viability.

The first two do not imply the third.  This module records explicit finite
counterexamples and the universal constant-deficit starvation theorem.

Resource units remain abstract accounting units; no theorem in P6 identifies
them with thermodynamic energy without a separate domain adapter.
-/

namespace UEOT.V3.Compression.Objecthood.ResourceClosure

open Filter Topology

noncomputable section

/-- If accumulated constant deficit exceeds initial stock, the resource balance
is already negative at that horizon. -/
theorem constant_deficit_starves_at
    (initial supply cost : ℝ) (N : ℕ)
    (hN : initial < (N : ℝ) * (cost - supply)) :
    cumulativeResourceBalance initial (fun _ => supply) (fun _ => cost) N < 0 := by
  unfold cumulativeResourceBalance
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  nlinarith

/-- Every finite real initial reserve is eventually exhausted under a constant
strict resource deficit.  No nonnegativity assumption on the initial balance is
needed; a negative initial balance has already failed earlier. -/
theorem constant_deficit_eventually_starves
    (initial supply cost : ℝ)
    (hdef : supply < cost) :
    ∃ N : ℕ,
      cumulativeResourceBalance initial (fun _ => supply) (fun _ => cost) N < 0 := by
  have hgap : 0 < cost - supply := sub_pos.mpr hdef
  obtain ⟨N, hN⟩ := exists_nat_gt (initial / (cost - supply))
  refine ⟨N, constant_deficit_starves_at initial supply cost N ?_⟩
  have hNreal : initial / (cost - supply) < (N : ℝ) := by
    exact_mod_cast hN
  have hmul := (div_lt_iff₀ hgap).mp hNreal
  simpa [mul_comm] using hmul

/-- Hence constant strict deficit rules out deterministic/pathwise resource
viability for every finite initial reserve. -/
theorem no_resourceViable_of_constant_deficit
    (initial supply cost : ℝ)
    (hdef : supply < cost) :
    ¬ ResourceViable initial (fun _ => supply) (fun _ => cost) := by
  intro h
  obtain ⟨N, hstarve⟩ := constant_deficit_eventually_starves
    initial supply cost hdef
  exact (not_lt_of_ge (h N)) hstarve

/-- One front-loaded resource-cost spike. -/
def spikeCost : ℕ → ℝ
  | 0 => 2
  | _ + 1 => 0

@[simp] theorem spikeCost_sum_succ (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), spikeCost n) = 2 := by
  induction N with
  | zero => norm_num [spikeCost]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      simp [spikeCost]

/-- The spike's Cesaro mean cost tends to zero. -/
theorem spikeCost_mean_tendsto_zero :
    Tendsto (meanRealSchedule spikeCost) atTop (𝓝 0) := by
  unfold meanRealSchedule
  simp_rw [spikeCost_sum_succ]
  have h : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  simpa [div_eq_mul_inv, mul_comm] using
    (Filter.Tendsto.const_div_atTop h (2 : ℝ))

/-- The long-run mean cost is eventually below unit replenishment. -/
theorem spikeCost_eventually_mean_lt_one :
    ∀ᶠ n in atTop, meanRealSchedule spikeCost n < 1 := by
  exact spikeCost_mean_tendsto_zero.eventually (Iio_mem_nhds zero_lt_one)

/-- But zero initial reserve and unit replenishment fail at the first step. -/
theorem spikeCost_not_resourceViable :
    ¬ ResourceViable 0 (fun _ => 1) spikeCost := by
  intro h
  have h1 := h 1
  norm_num [cumulativeResourceBalance, spikeCost] at h1

/-- **Mean sustainability does not imply pathwise non-starvation.**

The same cost schedule is eventually cheaper than supply on Cesaro average but
already violates the cumulative resource constraint. -/
theorem mean_resource_sustainability_does_not_imply_pathwise_viability :
    (∀ᶠ n in atTop, meanRealSchedule spikeCost n < 1) ∧
      ¬ ResourceViable 0 (fun _ => 1) spikeCost :=
  ⟨spikeCost_eventually_mean_lt_one, spikeCost_not_resourceViable⟩

/-- Two equiprobable accounting paths: one pays a front-loaded cost two,
the other pays nothing. -/
def twoPathCost (omega : Bool) : ℕ → ℝ
  | 0 => if omega then 2 else 0
  | _ + 1 => 0

@[simp] theorem twoPathCost_false (n : ℕ) :
    twoPathCost false n = 0 := by
  cases n <;> simp [twoPathCost]

@[simp] theorem twoPathCost_true (n : ℕ) :
    twoPathCost true n = spikeCost n := by
  cases n <;> simp [twoPathCost, spikeCost]

/-- With zero initial reserve and unit replenishment, the equal-weight average
cumulative balance of the two paths is nonnegative at every horizon. -/
theorem twoPath_averageAccountingBalance_nonneg :
    ∀ N : ℕ,
      0 ≤
        (cumulativeResourceBalance 0 (fun _ => 1) (twoPathCost false) N +
          cumulativeResourceBalance 0 (fun _ => 1) (twoPathCost true) N) / 2 := by
  intro N
  cases N with
  | zero => norm_num [cumulativeResourceBalance]
  | succ N =>
      have hfalse : (∑ n ∈ Finset.range (N + 1), twoPathCost false n) = 0 := by
        simp
      have htrue : (∑ n ∈ Finset.range (N + 1), twoPathCost true n) = 2 := by
        simpa only [twoPathCost_true] using spikeCost_sum_succ N
      have hsupply : (∑ _n ∈ Finset.range (N + 1), (1 : ℝ)) = (N + 1 : ℕ) := by
        simp
      unfold cumulativeResourceBalance
      rw [hfalse, htrue]
      have hN : (0 : ℝ) ≤ N := by positivity
      norm_num
      nlinarith

/-- Nevertheless the high-cost realization starves immediately. -/
theorem twoPath_highCost_not_resourceViable :
    ¬ ResourceViable 0 (fun _ => 1) (twoPathCost true) := by
  have hfun : twoPathCost true = spikeCost := by
    funext n
    exact twoPathCost_true n
  rw [hfun]
  exact spikeCost_not_resourceViable

/-- **Expected accounting closure does not imply pathwise resource viability.**
Even a nonnegative equal-weight expected cumulative balance at every horizon can
hide a realized path that violates the resource constraint. -/
theorem average_accounting_closure_does_not_imply_pathwise_viability :
    (∀ N : ℕ,
      0 ≤
        (cumulativeResourceBalance 0 (fun _ => 1) (twoPathCost false) N +
          cumulativeResourceBalance 0 (fun _ => 1) (twoPathCost true) N) / 2) ∧
      ¬ ResourceViable 0 (fun _ => 1) (twoPathCost true) :=
  ⟨twoPath_averageAccountingBalance_nonneg,
    twoPath_highCost_not_resourceViable⟩



/-- The explicit equal-prior probability law on the two accounting paths. -/
noncomputable def twoPathLaw : PMF Bool := PMF.uniformOfFintype Bool

/-- The expected cumulative balance under the explicit two-path probability law
is nonnegative at every horizon. -/
theorem twoPath_expectedBalance_nonneg :
    ∀ N : ℕ,
      0 ≤ pmfRealExpectation twoPathLaw
        (fun omega =>
          cumulativeResourceBalance 0 (fun _ => 1) (twoPathCost omega) N) := by
  intro N
  rw [show pmfRealExpectation twoPathLaw
      (fun omega => cumulativeResourceBalance 0 (fun _ => 1)
        (twoPathCost omega) N) =
      (cumulativeResourceBalance 0 (fun _ => 1) (twoPathCost false) N +
       cumulativeResourceBalance 0 (fun _ => 1) (twoPathCost true) N) / 2 by
    unfold pmfRealExpectation twoPathLaw
    simp [PMF.uniformOfFintype_apply]
    ring]
  exact twoPath_averageAccountingBalance_nonneg N

/-- **Expected accounting closure does not imply pathwise resource viability.**
The expectation is taken under an explicit equal-prior PMF, while the high-cost
realization still violates the cumulative resource constraint. -/
theorem expected_accounting_closure_does_not_imply_pathwise_viability :
    (∀ N : ℕ,
      0 ≤ pmfRealExpectation twoPathLaw
        (fun omega =>
          cumulativeResourceBalance 0 (fun _ => 1) (twoPathCost omega) N)) ∧
      ¬ ResourceViable 0 (fun _ => 1) (twoPathCost true) :=
  ⟨twoPath_expectedBalance_nonneg, twoPath_highCost_not_resourceViable⟩


end
end UEOT.V3.Compression.Objecthood.ResourceClosure
