import UEOT.V3.Compression.Objecthood.GeneralCausalDiscountedDirection
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.Filter.Cofinite

namespace UEOT.V3.Compression.Objecthood

open Filter MeasureTheory ProbabilityTheory
open UEOT.V3.FiniteHistory
open UEOT.V3.CompactCausalOptimalityCore
open UEOT.V3.ViabilityTrajectory
open scoped ProbabilityTheory

universe uX uA
noncomputable section

variable {X : Type uX} {A : Type uA}
variable [Fintype X] [Fintype A] [Nonempty A]
variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace A] [MeasurableSingletonClass A]

noncomputable def gcrBeta (n : ℕ) : ℝ :=
  1 - (1 / 2 : ℝ) ^ (n + 1)

theorem gcrBeta_pos (n : ℕ) : 0 < gcrBeta n := by
  unfold gcrBeta
  have hp : (0 : ℝ) < (1 / 2 : ℝ) ^ (n + 1) := pow_pos (by norm_num) _
  have hlt : (1 / 2 : ℝ) ^ (n + 1) < 1 := by
    have hpow := pow_lt_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 : ℝ) / 2 < 1) (Nat.succ_ne_zero n)
    simpa [Nat.succ_eq_add_one] using hpow
  linarith

theorem gcrBeta_lt_one (n : ℕ) : gcrBeta n < 1 := by
  unfold gcrBeta
  have hp : (0 : ℝ) < (1 / 2 : ℝ) ^ (n + 1) := pow_pos (by norm_num) _
  linarith

theorem gcrBeta_tendsto_one : Tendsto gcrBeta atTop (nhds (1 : ℝ)) := by
  have hp : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hs : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) atTop (nhds 0) := by
    simpa [Function.comp_def] using hp.comp (tendsto_add_atTop_nat 1)
  change Tendsto (fun n : ℕ => 1 - (1 / 2 : ℝ) ^ (n + 1)) atTop (nhds 1)
  simpa using hs.const_sub 1

noncomputable def gcrGreedyPolicy
    (P : X → A → PMF X) (K : Set X) (n : ℕ) : X → A :=
  (normalizedRepairGreedyCertificate P K (gcrBeta n)
    (gcrBeta_pos n) (gcrBeta_lt_one n)).selector

theorem greedyValue_eq_stationaryOccupation
    (P : X → A → PMF X) (K : Set X) (x : X)
    (beta : ℝ) (hbeta0 : 0 < beta) (hbeta1 : beta < 1) :
    let G := normalizedRepairGreedyCertificate P K beta hbeta0 hbeta1
    G.value x = causalNormalizedOccupation P K x
      (stationaryAdmissible G.selector) beta := by
  let G := normalizedRepairGreedyCertificate P K beta hbeta0 hbeta1
  have hval := G.stationary_infiniteValue_eq_value
    0 (initialHistory (A := A) x)
  have hocc := admissibleCausalNormalizedInfiniteValue_eq_occupation
    P K x (stationaryAdmissible G.selector) beta hbeta0 hbeta1
  unfold admissibleCausalNormalizedInfiniteValue at hocc
  change
    (causalNormalizedRepairModel P K beta hbeta0.le hbeta1).infiniteValue
      G.stationaryPolicy 0 (initialHistory (A := A) x) = G.value x at hval
  change
    (causalNormalizedRepairModel P K beta hbeta0.le hbeta1).infiniteValue
      G.stationaryPolicy 0 (initialHistory (A := A) x) =
      causalNormalizedOccupation P K x (stationaryAdmissible G.selector) beta at hocc
  exact hval.symm.trans hocc

private theorem causalNormalizedOccupation_le_one
    (P : X → A → PMF X) (K : Set X) (x : X)
    (pi : AdmissibleCausalRepairPolicy X A)
    (beta : ℝ) (hbeta0 : 0 < beta) (hbeta1 : beta < 1) :
    causalNormalizedOccupation P K x pi beta ≤ 1 := by
  have heq := causalNormalizedOccupation_eq_one_sub_survivalAbel
    P K x pi beta hbeta0 hbeta1
  let mu := causalRepairPathLaw (absorbedRepairPMF P K) x pi
  let surv : ℕ → ℝ := fun n => mu.real (UEOT.V3.RecoveryHittingNonnegative.survivalSet K n)
  have hnonneg : 0 ≤ geometricAbelAverage surv beta := by
    unfold geometricAbelAverage
    exact tsum_nonneg fun n => by
      have hp : 0 ≤ beta ^ n := pow_nonneg hbeta0.le n
      have hb : 0 ≤ 1 - beta := sub_nonneg.mpr hbeta1.le
      have hs : 0 ≤ surv n := measureReal_nonneg
      positivity
  change causalNormalizedOccupation P K x pi beta =
    1 - geometricAbelAverage surv beta at heq
  rw [heq]
  linarith

/-- Infinite pigeonhole extraction of one fixed deterministic stationary greedy
policy, together with a genuine atTop subsequence on which it repeats. -/
theorem exists_repeated_gcrGreedyPolicy
    (P : X → A → PMF X) (K : Set X) :
    ∃ g : X → A, ∃ sigma : ℕ → ℕ,
      Function.Injective sigma ∧ Tendsto sigma atTop atTop ∧
      ∀ n, gcrGreedyPolicy P K (sigma n) = g := by
  obtain ⟨g, hg⟩ := Finite.exists_infinite_fiber (gcrGreedyPolicy P K)
  let S : Set ℕ := (gcrGreedyPolicy P K) ⁻¹' {g}
  letI : Infinite S := by
    simpa [S] using hg
  let e : ℕ ↪ S := Infinite.natEmbedding S
  let sigma : ℕ → ℕ := fun n => (e n).1
  have hsigma : Function.Injective sigma := by
    intro m n hmn
    apply e.injective
    apply Subtype.ext
    exact hmn
  refine ⟨g, sigma, hsigma, hsigma.nat_tendsto_atTop, ?_⟩
  intro n
  have hn0 := (e n).2
  have hn : gcrGreedyPolicy P K (e n).1 = g := by
    change gcrGreedyPolicy P K (e n).1 ∈ ({g} : Set (X → A)) at hn0
    simpa using hn0
  simpa [sigma] using hn

/-- GCR4 finite-policy squeeze: if one arbitrary causal policy hits almost surely,
then one fixed deterministic stationary greedy selector has normalized exact
occupation tending to one along a genuine subsequence of the canonical discount
schedule. -/
theorem exists_stationaryOccupation_subsequence_tendsto_one
    (P : X → A → PMF X) (K : Set X) (x : X)
    (pi : AdmissibleCausalRepairPolicy X A)
    (hHit : ∀ᵐ omega ∂causalRepairPathLaw P x pi,
      ∃ n : ℕ, omega n ∈ K) :
    ∃ g : X → A, ∃ sigma : ℕ → ℕ,
      Function.Injective sigma ∧ Tendsto sigma atTop atTop ∧
      Tendsto
        (fun n => causalNormalizedOccupation P K x (stationaryAdmissible g)
          (gcrBeta (sigma n))) atTop (nhds 1) := by
  obtain ⟨g, sigma, hsigma, hsigma_top, hrepeat⟩ :=
    exists_repeated_gcrGreedyPolicy P K
  have hcausal := causalNormalizedOccupation_tendsto_one_of_ae_eventually_hits
    P K x pi hHit gcrBeta gcrBeta_pos gcrBeta_lt_one gcrBeta_tendsto_one
  have hlower : Tendsto
      (fun n => causalNormalizedOccupation P K x pi (gcrBeta (sigma n)))
      atTop (nhds 1) := by
    exact hcausal.comp hsigma_top
  have hleft : ∀ n,
      causalNormalizedOccupation P K x pi (gcrBeta (sigma n)) ≤
        causalNormalizedOccupation P K x (stationaryAdmissible g)
          (gcrBeta (sigma n)) := by
    intro n
    have hdom := causalNormalizedOccupation_le_greedyValue
      P K x pi (gcrBeta (sigma n))
      (gcrBeta_pos (sigma n)) (gcrBeta_lt_one (sigma n))
    have hval := greedyValue_eq_stationaryOccupation
      P K x (gcrBeta (sigma n))
      (gcrBeta_pos (sigma n)) (gcrBeta_lt_one (sigma n))
    have hsel := hrepeat n
    unfold gcrGreedyPolicy at hsel
    rw [hval] at hdom
    simpa [hsel] using hdom
  have hright : ∀ n,
      causalNormalizedOccupation P K x (stationaryAdmissible g)
        (gcrBeta (sigma n)) ≤ 1 := by
    intro n
    exact causalNormalizedOccupation_le_one P K x (stationaryAdmissible g)
      (gcrBeta (sigma n)) (gcrBeta_pos (sigma n)) (gcrBeta_lt_one (sigma n))
  have hone : Tendsto (fun _n : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have hmid := Filter.Tendsto.squeeze hlower hone hleft hright
  exact ⟨g, sigma, hsigma, hsigma_top, hmid⟩


private theorem neverHitReal_le_geometricAbelAverage
    (mu : Measure (ℕ → X)) [IsProbabilityMeasure mu]
    (K : Set X) (beta : ℝ) (hbeta0 : 0 < beta) (hbeta1 : beta < 1) :
    mu.real (neverHitSet K) ≤
      geometricAbelAverage
        (fun n => mu.real (UEOT.V3.RecoveryHittingNonnegative.survivalSet K n)) beta := by
  let q : ℝ := mu.real (neverHitSet K)
  let surv : ℕ → ℝ := fun n =>
    mu.real (UEOT.V3.RecoveryHittingNonnegative.survivalSet K n)
  have hq0 : 0 ≤ q := measureReal_nonneg
  have hqle (n : ℕ) : q ≤ surv n := by
    apply measureReal_mono
    · intro omega hnever
      exact (UEOT.V3.RecoveryHittingNonnegative.mem_survivalSet_iff K n omega).2
        (fun k hk => hnever k)
    · exact measure_ne_top _ _
  have hgeom : Summable (fun n : ℕ => beta ^ n) :=
    summable_geometric_of_lt_one hbeta0.le hbeta1
  have hweights : Summable (fun n : ℕ => beta ^ n * (1 - beta)) :=
    hgeom.mul_right (1 - beta)
  have hleft : Summable (fun n : ℕ => beta ^ n * (1 - beta) * q) :=
    hweights.mul_right q
  have hsurv : Summable (fun n : ℕ => beta ^ n * (1 - beta) * surv n) := by
    apply Summable.of_nonneg_of_le (f := fun n : ℕ => beta ^ n * (1 - beta))
    · intro n
      exact mul_nonneg
        (mul_nonneg (pow_nonneg hbeta0.le n) (sub_nonneg.mpr hbeta1.le))
        measureReal_nonneg
    · intro n
      have hw : 0 ≤ beta ^ n * (1 - beta) := by positivity
      exact mul_le_of_le_one_right hw measureReal_le_one
    · exact hweights
  have hsum :
      (∑' n : ℕ, beta ^ n * (1 - beta) * q) ≤
        ∑' n : ℕ, beta ^ n * (1 - beta) * surv n := by
    apply Summable.tsum_le_tsum
    · intro n
      have hw : 0 ≤ beta ^ n * (1 - beta) := by positivity
      exact mul_le_mul_of_nonneg_left (hqle n) hw
    · exact hleft
    · exact hsurv
  have hnorm : (∑' n : ℕ, beta ^ n * (1 - beta)) = 1 := by
    rw [hgeom.tsum_mul_right]
    rw [tsum_geometric_of_lt_one hbeta0.le hbeta1]
    exact inv_mul_cancel₀ (sub_ne_zero.mpr (ne_of_gt hbeta1))
  have hleft_eq : (∑' n : ℕ, beta ^ n * (1 - beta) * q) = q := by
    rw [hweights.tsum_mul_right q, hnorm, one_mul]
  unfold geometricAbelAverage
  simpa [q, surv, hleft_eq] using hsum

/-- If normalized occupation of one fixed policy tends to one along genuine
 discounts, then its absorbed exact path law hits the target almost surely. -/
theorem ae_eventually_hits_absorbed_of_stationaryOccupation_subsequence_tendsto_one
    (P : X → A → PMF X) (K : Set X) (x : X) (g : X → A)
    (sigma : ℕ → ℕ) (hsigma_top : Tendsto sigma atTop atTop)
    (hOcc : Tendsto
      (fun n => causalNormalizedOccupation P K x (stationaryAdmissible g)
        (gcrBeta (sigma n))) atTop (nhds 1)) :
    ∀ᵐ omega ∂causalRepairPathLaw (absorbedRepairPMF P K) x (stationaryAdmissible g),
      ∃ n : ℕ, omega n ∈ K := by
  let pi := stationaryAdmissible g
  let mu := causalRepairPathLaw (absorbedRepairPMF P K) x pi
  letI : IsProbabilityMeasure mu := by
    dsimp [mu, pi, causalRepairPathLaw]
    infer_instance
  let surv : ℕ → ℝ := fun n =>
    mu.real (UEOT.V3.RecoveryHittingNonnegative.survivalSet K n)
  have hbeta_sub : Tendsto (fun n => gcrBeta (sigma n)) atTop (nhds (1 : ℝ)) :=
    gcrBeta_tendsto_one.comp hsigma_top
  have hAbel : Tendsto
      (fun n => geometricAbelAverage surv (gcrBeta (sigma n)))
      atTop (nhds 0) := by
    have hEq : ∀ n,
        causalNormalizedOccupation P K x pi (gcrBeta (sigma n)) =
          1 - geometricAbelAverage surv (gcrBeta (sigma n)) := by
      intro n
      simpa [surv, mu, pi] using
        causalNormalizedOccupation_eq_one_sub_survivalAbel
          P K x pi (gcrBeta (sigma n))
          (gcrBeta_pos (sigma n)) (gcrBeta_lt_one (sigma n))
    have hsub := hOcc.const_sub 1
    have hfun :
        (fun n => 1 - causalNormalizedOccupation P K x pi (gcrBeta (sigma n))) =
          (fun n => geometricAbelAverage surv (gcrBeta (sigma n))) := by
      funext n
      rw [hEq n]
      ring
    rw [hfun] at hsub
    simpa using hsub
  let q : ℝ := mu.real (neverHitSet K)
  have hqle : ∀ n, q ≤ geometricAbelAverage surv (gcrBeta (sigma n)) := by
    intro n
    simpa [q, surv, mu, pi] using
      neverHitReal_le_geometricAbelAverage
        mu K (gcrBeta (sigma n)) (gcrBeta_pos (sigma n)) (gcrBeta_lt_one (sigma n))
  have hq0 : q ≤ 0 := ge_of_tendsto' hAbel hqle
  have hq_nonneg : 0 ≤ q := measureReal_nonneg
  have hq : q = 0 := le_antisymm hq0 hq_nonneg
  have hnever : mu (neverHitSet K) = 0 :=
    (measureReal_eq_zero_iff (μ := mu) (s := neverHitSet K)).1 (by simpa [q] using hq)
  apply (MeasureTheory.ae_iff).2
  simpa [mu, pi, neverHitSet, not_exists] using hnever

/-- **GCR4 stationary almost-sure witness.**  Arbitrary admissible causal almost-
sure repair yields one deterministic stationary policy whose canonical physical
stationary path law hits `K` almost surely.  No finite-expectation conclusion is
made here. -/
theorem exists_stationaryPolicy_ae_eventually_hits
    (P : X → A → PMF X) (K : Set X) (x : X)
    (pi : AdmissibleCausalRepairPolicy X A)
    (hHit : ∀ᵐ omega ∂causalRepairPathLaw P x pi,
      ∃ n : ℕ, omega n ∈ K) :
    ∃ g : X → A,
      ∀ᵐ omega ∂stationaryTrajMeasure P g (PMF.pure x),
        ∃ n : ℕ, omega n ∈ K := by
  obtain ⟨g, sigma, hsigma, hsigma_top, hOcc⟩ :=
    exists_stationaryOccupation_subsequence_tendsto_one P K x pi hHit
  have hHitAbs :=
    ae_eventually_hits_absorbed_of_stationaryOccupation_subsequence_tendsto_one
      P K x g sigma hsigma_top hOcc
  have hHitOrig :
      ∀ᵐ omega ∂causalRepairPathLaw P x (stationaryAdmissible g),
        ∃ n : ℕ, omega n ∈ K :=
    (causalRepairPathLaw_absorbed_eventually_hits_iff
      P K x (stationaryAdmissible g)).1 hHitAbs
  refine ⟨g, ?_⟩
  rw [stationaryCausal_pathLaw_eq_stationaryTrajMeasure P g x] at hHitOrig
  exact hHitOrig

end
end UEOT.V3.Compression.Objecthood
