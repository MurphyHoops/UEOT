import UEOT.V3.Compression.Objecthood.FinitePolicyAbelianStationaryWitness
import UEOT.V3.RecoveryHittingRestart
import Mathlib.Order.Filter.Finite

namespace UEOT.V3.Compression.Objecthood

open Set Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder ProbabilityTheory Filter
open UEOT.V3.DynamicsKernel
open UEOT.V3.RecoveryHittingNonnegative
open UEOT.V3.RecoveryHittingRestart
open UEOT.V3.RecoveryHittingFirstStep
open UEOT.V3.RecoveryHittingPoisson
open UEOT.V3.RecoveryHittingBound
open UEOT.V3.ViabilityTrajectory
open scoped ENNReal ProbabilityTheory

universe uX uA
noncomputable section

variable {X : Type uX} [Fintype X]
variable [MeasurableSpace X] [MeasurableSingletonClass X]

noncomputable def neverHitProb
    (Q : Kernel X X) [IsMarkovKernel Q]
    (x : X) (K : Set X) : ℝ≥0∞ :=
  homTrajMeasure (Measure.dirac x) Q (neverHitSet K)

theorem measurableSet_neverHitSet (K : Set X) : MeasurableSet (neverHitSet K) := by
  rw [neverHitSet_eq_iInter_survivalSet]
  exact MeasurableSet.iInter fun n =>
    measurableSet_survivalSet (Set.toFinite K).measurableSet n

/-- Finite survival tails decrease to the never-hit mass. -/
theorem survivalProb_tendsto_neverHitProb
    (Q : Kernel X X) [IsMarkovKernel Q]
    (x : X) (K : Set X) :
    Tendsto (fun n => survivalProb Q x K n) atTop
      (nhds (neverHitProb Q x K)) := by
  let mu := homTrajMeasure (Measure.dirac x) Q
  letI : IsProbabilityMeasure mu := by
    dsimp [mu]
    infer_instance
  have hK : MeasurableSet K := (Set.toFinite K).measurableSet
  have ht := tendsto_measure_iInter_atTop
    (μ := mu) (s := survivalSet K)
    (fun n => (measurableSet_survivalSet hK n).nullMeasurableSet)
    (antitone_survivalSet K)
    ⟨0, measure_ne_top _ _⟩
  rw [← neverHitSet_eq_iInter_survivalSet K] at ht
  have hfun :
      (fun n => survivalProb Q x K n) =
        (fun n => mu (survivalSet K n)) := by
    funext n
    exact survivalProb_eq_homTrajMeasure_apply Q x K hK n
  rw [hfun]
  simpa [neverHitProb, mu, Function.comp_def] using ht

/-- Outside the target, the never-hit probability is harmonic under one Markov
step. -/
theorem neverHitProb_first_step
    (Q : Kernel X X) [IsMarkovKernel Q]
    (x : X) (K : Set X) (hx : x ∉ K) :
    neverHitProb Q x K = ∫⁻ y, neverHitProb Q y K ∂Q x := by
  let mu := homTrajMeasure (Measure.dirac x) Q
  letI : IsProbabilityMeasure mu := by
    dsimp [mu]
    infer_instance
  have hK : MeasurableSet K := (Set.toFinite K).measurableSet
  have hNever : MeasurableSet (neverHitSet K) := measurableSet_neverHitSet K
  have hzero := homTrajMeasure_time_zero_general (Measure.dirac x) Q
  have hbad : mu {omega : ℕ → X | omega 0 ∈ K} = 0 := by
    have hm := congrArg (fun nu : Measure X => nu K) hzero
    rw [Measure.map_apply (measurable_pi_apply 0) hK] at hm
    rw [Measure.dirac_apply' x hK] at hm
    change mu ((fun omega : ℕ → X => omega 0) ⁻¹' K) = 0
    simpa [mu, hx] using hm
  have hae0 : ∀ᵐ omega ∂mu, omega 0 ∉ K := by
    apply (MeasureTheory.ae_iff).2
    simpa only [not_not] using hbad
  have hevent :
      neverHitSet K =ᵐ[mu] pathShift ⁻¹' neverHitSet K := by
    filter_upwards [hae0] with omega h0
    apply propext
    constructor
    · intro h n
      exact h (n + 1)
    · intro h n
      cases n with
      | zero => exact h0
      | succ n => exact h n
  unfold neverHitProb
  calc
    mu (neverHitSet K) = mu (pathShift ⁻¹' neverHitSet K) := measure_congr hevent
    _ = (mu.map pathShift) (neverHitSet K) := by
      symm
      exact Measure.map_apply measurable_pathShift hNever
    _ = (homTrajMeasure (Q x) Q) (neverHitSet K) := by
      have hshift := homTrajMeasure_shift (Measure.dirac x) Q
      rw [kernel_comp_dirac Q x] at hshift
      rw [hshift]
    _ = ∫⁻ y, homTrajMeasure (Measure.dirac y) Q (neverHitSet K) ∂Q x := by
      exact homTrajMeasure_apply_eq_lintegral_initial Q (Q x)
        (neverHitSet K) hNever

/-- Zero never-hit mass is closed under every positive-probability one-step
successor. -/
theorem neverHitProb_zero_support_closed
    (Q : Kernel X X) [IsMarkovKernel Q]
    (K : Set X) {x y : X}
    (hxK : x ∉ K) (hx0 : neverHitProb Q x K = 0)
    (hy : Q x {y} ≠ 0) :
    neverHitProb Q y K = 0 := by
  have hstep := neverHitProb_first_step Q x K hxK
  rw [hx0] at hstep
  have hmeas : Measurable (fun z => neverHitProb Q z K) := measurable_of_finite _
  have hae : (fun z => neverHitProb Q z K) =ᵐ[Q x] 0 :=
    (lintegral_eq_zero_iff hmeas).1 hstep.symm
  rw [Filter.EventuallyEq, ae_iff] at hae
  by_contra hy0
  have hsub : ({y} : Set X) ⊆ {z | neverHitProb Q z K ≠ 0} := by
    intro z hz
    have hzy : z = y := by simpa using hz
    subst z
    exact hy0
  have hzero : Q x ({y} : Set X) = 0 := measure_mono_null hsub hae
  exact hy hzero


/-- Zero never-hit mass propagates almost everywhere through one homogeneous
Markov step. -/
theorem neverHitProb_zero_ae_successor
    (Q : Kernel X X) [IsMarkovKernel Q]
    (K : Set X) {x : X}
    (hxK : x ∉ K) (hx0 : neverHitProb Q x K = 0) :
    ∀ᵐ y ∂Q x, neverHitProb Q y K = 0 := by
  have hstep := neverHitProb_first_step Q x K hxK
  rw [hx0] at hstep
  have hmeas : Measurable (fun z => neverHitProb Q z K) := measurable_of_finite _
  exact (lintegral_eq_zero_iff hmeas).1 hstep.symm

/-- Finiteness of the state space upgrades pointwise disappearance of survival
probability on the zero-never-hit class to one uniform half-contraction
horizon. -/
theorem exists_uniform_half_survival_horizon
    (Q : Kernel X X) [IsMarkovKernel Q]
    (K : Set X) :
    ∃ N : ℕ, ∀ y : X, neverHitProb Q y K = 0 →
      survivalProb Q y K N ≤ (1 / 2 : ENNReal) := by
  have hall : ∀ᶠ n : ℕ in atTop,
      ∀ y : X, neverHitProb Q y K = 0 →
        survivalProb Q y K n ≤ (1 / 2 : ENNReal) := by
    rw [Filter.eventually_all]
    intro y
    by_cases hy : neverHitProb Q y K = 0
    · have ht := survivalProb_tendsto_neverHitProb Q y K
      rw [hy] at ht
      have hev := ht.eventually_le_const (show (0 : ENNReal) < 1 / 2 by norm_num)
      exact hev.mono fun n hn _ => hn
    · exact Filter.Eventually.of_forall fun _ hzero => (hy hzero).elim
  rcases Filter.eventually_atTop.1 hall with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro y hy
  exact hN N le_rfl y hy


private theorem survivalProb_zero_eq_one_of_not_mem
    (Q : Kernel X X) [IsMarkovKernel Q]
    (K : Set X) (x : X) (hx : x ∉ K) :
    survivalProb Q x K 0 = 1 := by
  let e : ((i : Finset.Iic 0) → X) ≃ᵐ X :=
    MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => X)
  have hprefix : prefixLaw Q x 0 = (Measure.dirac x).map e.symm := by
    unfold prefixLaw
    simpa [e] using homTrajMeasure_prefix_zero (Measure.dirac x) Q
  have hK : MeasurableSet K := (Set.toFinite K).measurableSet
  have hS : MeasurableSet (historySurvivalSet K 0) :=
    measurableSet_historySurvivalSet hK 0
  unfold survivalProb
  rw [hprefix]
  rw [Measure.map_apply e.symm.measurable hS]
  rw [Measure.dirac_apply' x (hS.preimage e.symm.measurable)]
  have hcoord : (e.symm x) (lastHistoryIndex 0) = x := by
    have he := e.apply_symm_apply x
    change (e.symm x) default = x at he
    have hi : lastHistoryIndex 0 = default := Subsingleton.elim _ _
    simpa [hi] using he
  have hmem : e.symm x ∈ historySurvivalSet K 0 := by
    rw [mem_historySurvivalSet_iff]
    intro i
    have hi : i = lastHistoryIndex 0 := Subsingleton.elim _ _
    subst i
    simpa [hcoord] using hx
  simp [hmem]

/-- A uniform half-survival horizon contracts every later survival tail by the
same factor on the zero-never-hit class. -/
theorem survivalProb_add_uniform_horizon_le_half_mul
    (Q : Kernel X X) [IsMarkovKernel Q]
    (K : Set X) (N : ℕ)
    (hN : ∀ y : X, neverHitProb Q y K = 0 →
      survivalProb Q y K N ≤ (1 / 2 : ENNReal)) :
    ∀ m : ℕ, ∀ x : X, neverHitProb Q x K = 0 →
      survivalProb Q x K (m + N) ≤
        (1 / 2 : ENNReal) * survivalProb Q x K m := by
  have hK : MeasurableSet K := (Set.toFinite K).measurableSet
  intro m
  induction m with
  | zero =>
      intro x hx0
      simp only [Nat.zero_add]
      by_cases hxK : x ∈ K
      · rw [survivalProb_eq_zero_of_mem Q x K hK hxK N]
        simp
      · have hs0 := survivalProb_zero_eq_one_of_not_mem Q K x hxK
        simpa [hs0] using hN x hx0
  | succ m ih =>
      intro x hx0
      by_cases hxK : x ∈ K
      · rw [survivalProb_eq_zero_of_mem Q x K hK hxK ((m + 1) + N),
            survivalProb_eq_zero_of_mem Q x K hK hxK (m + 1)]
        simp
      · have hae := neverHitProb_zero_ae_successor Q K hxK hx0
        rw [show (m + 1) + N = (m + N) + 1 by omega]
        rw [survivalProb_succ_eq_lintegral Q x K hK hxK (m + N)]
        rw [survivalProb_succ_eq_lintegral Q x K hK hxK m]
        calc
          (∫⁻ y, survivalProb Q y K (m + N) ∂Q x) ≤
              ∫⁻ y, (1 / 2 : ENNReal) * survivalProb Q y K m ∂Q x := by
                apply lintegral_mono_ae
                exact hae.mono fun y hy => ih y hy
          _ = (1 / 2 : ENNReal) * ∫⁻ y, survivalProb Q y K m ∂Q x := by
                rw [MeasureTheory.lintegral_const_mul]
                exact measurable_of_finite _


private theorem survivalProb_le_one
    (Q : Kernel X X) [IsMarkovKernel Q]
    (x : X) (K : Set X) (n : ℕ) :
    survivalProb Q x K n ≤ 1 := by
  unfold survivalProb
  exact MeasureTheory.prob_le_one

private theorem truncatedExpectedHittingTime_le_nat
    (Q : Kernel X X) [IsMarkovKernel Q]
    (x : X) (K : Set X) (M : ℕ) :
    truncatedExpectedHittingTime Q x K M ≤ (M : ENNReal) := by
  unfold truncatedExpectedHittingTime
  calc
    (∑ n ∈ Finset.range M, survivalProb Q x K n) ≤
        ∑ _n ∈ Finset.range M, (1 : ENNReal) := by
      exact Finset.sum_le_sum fun n hn => survivalProb_le_one Q x K n
    _ = (M : ENNReal) := by simp

/-- Uniform block contraction yields an affine recursion for every truncated
survival-tail sum. -/
theorem truncatedExpectedHittingTime_add_horizon_le
    (Q : Kernel X X) [IsMarkovKernel Q]
    (K : Set X) (x : X) (N M : ℕ)
    (hx0 : neverHitProb Q x K = 0)
    (hN : ∀ y : X, neverHitProb Q y K = 0 →
      survivalProb Q y K N ≤ (1 / 2 : ENNReal)) :
    truncatedExpectedHittingTime Q x K (M + N) ≤
      (N : ENNReal) + (1 / 2 : ENNReal) *
        truncatedExpectedHittingTime Q x K M := by
  have hcontract := survivalProb_add_uniform_horizon_le_half_mul Q K N hN
  unfold truncatedExpectedHittingTime
  rw [show M + N = N + M by omega]
  rw [Finset.sum_range_add]
  apply add_le_add
  · calc
      (∑ n ∈ Finset.range N, survivalProb Q x K n) ≤
          ∑ _n ∈ Finset.range N, (1 : ENNReal) := by
        exact Finset.sum_le_sum fun n hn => survivalProb_le_one Q x K n
      _ = (N : ENNReal) := by simp
  · calc
      (∑ i ∈ Finset.range M, survivalProb Q x K (N + i)) ≤
          ∑ i ∈ Finset.range M,
            (1 / 2 : ENNReal) * survivalProb Q x K i := by
        apply Finset.sum_le_sum
        intro i hi
        simpa [Nat.add_comm] using hcontract i x hx0
      _ = (1 / 2 : ENNReal) *
          ∑ i ∈ Finset.range M, survivalProb Q x K i := by
        symm
        exact Finset.mul_sum _ _ _

/-- Once the uniform half-block horizon is positive, every finite hitting-time
truncation is bounded by twice that horizon. -/
theorem truncatedExpectedHittingTime_le_two_mul_horizon
    (Q : Kernel X X) [IsMarkovKernel Q]
    (K : Set X) (x : X) (N : ℕ) (hNpos : 0 < N)
    (hx0 : neverHitProb Q x K = 0)
    (hN : ∀ y : X, neverHitProb Q y K = 0 →
      survivalProb Q y K N ≤ (1 / 2 : ENNReal)) :
    ∀ M : ℕ,
      truncatedExpectedHittingTime Q x K M ≤
        2 * (N : ENNReal) := by
  intro M
  induction M using Nat.strong_induction_on with
  | h M ih =>
      by_cases hMN : M ≤ N
      · exact (truncatedExpectedHittingTime_le_nat Q x K M).trans <| by
          have hc : (M : ENNReal) ≤ (N : ENNReal) := by exact_mod_cast hMN
          calc
            (M : ENNReal) ≤ (N : ENNReal) := hc
            _ ≤ 2 * (N : ENNReal) := by
              exact le_mul_of_one_le_left (by simp) (by norm_num)
      · have hNMlt : N < M := Nat.lt_of_not_ge hMN
        have hNM : N ≤ M := hNMlt.le
        have hMpos : 0 < M := hNpos.trans hNMlt
        have hsub_lt : M - N < M := Nat.sub_lt hMpos hNpos
        have hrec := truncatedExpectedHittingTime_add_horizon_le
          Q K x N (M - N) hx0 hN
        rw [Nat.sub_add_cancel hNM] at hrec
        have hih := ih (M - N) hsub_lt
        calc
          truncatedExpectedHittingTime Q x K M ≤
              (N : ENNReal) + (1 / 2 : ENNReal) *
                truncatedExpectedHittingTime Q x K (M - N) := hrec
          _ ≤ (N : ENNReal) + (1 / 2 : ENNReal) *
                (2 * (N : ENNReal)) := by
              have hmul : (1 / 2 : ENNReal) *
                  truncatedExpectedHittingTime Q x K (M - N) ≤
                    (1 / 2 : ENNReal) * (2 * (N : ENNReal)) := by
                simpa [mul_comm] using
                  (mul_le_mul_left hih (1 / 2 : ENNReal))
              exact add_le_add_right hmul _
          _ = 2 * (N : ENNReal) := by
              rw [← mul_assoc]
              have hhalf : (1 / 2 : ENNReal) * 2 = 1 := by
                rw [one_div, mul_comm]
                exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
              rw [hhalf, one_mul, two_mul]


/-- Almost-sure eventual hitting is exactly zero never-hit mass for the
homogeneous canonical path law. -/
theorem neverHitProb_eq_zero_of_ae_eventually_hits
    (Q : Kernel X X) [IsMarkovKernel Q]
    (x : X) (K : Set X)
    (hHit : ∀ᵐ omega ∂homTrajMeasure (Measure.dirac x) Q,
      ∃ n : ℕ, omega n ∈ K) :
    neverHitProb Q x K = 0 := by
  have h0 := (MeasureTheory.ae_iff).1 hHit
  unfold neverHitProb
  simpa [neverHitSet, not_exists] using h0

/-- **Finite-state homogeneous a.s.-hitting implies finite mean hitting time.**
This is the quantitative GCR5 bridge.  The proof is finite-state and
homogeneous: zero never-hit mass gives one uniform half-survival block, whose
Markov restart contraction uniformly bounds all survival-tail truncations. -/
theorem expectedHittingTime_ne_top_of_ae_eventually_hits_finite
    (Q : Kernel X X) [IsMarkovKernel Q]
    (x : X) (K : Set X)
    (hHit : ∀ᵐ omega ∂homTrajMeasure (Measure.dirac x) Q,
      ∃ n : ℕ, omega n ∈ K) :
    expectedHittingTime Q x K ≠ ∞ := by
  have hK : MeasurableSet K := (Set.toFinite K).measurableSet
  have hx0 := neverHitProb_eq_zero_of_ae_eventually_hits Q x K hHit
  by_cases hxK : x ∈ K
  · rw [expectedHittingTime_eq_zero_of_mem_target Q x K hxK]
    simp
  · obtain ⟨N, hN⟩ := exists_uniform_half_survival_horizon Q K
    have hNpos : 0 < N := by
      by_contra hNzero
      have hNeq : N = 0 := Nat.eq_zero_of_not_pos hNzero
      have hxN := hN x hx0
      rw [hNeq, survivalProb_zero_eq_one_of_not_mem Q K x hxK] at hxN
      have : ¬ ((1 : ENNReal) ≤ 1 / 2) := by norm_num [one_div]
      exact this hxN
    rw [expectedHittingTime_eq_iSup_truncatedExpectedHittingTime Q x K hK]
    have hbound :
        (⨆ M : ℕ, truncatedExpectedHittingTime Q x K M) ≤
          2 * (N : ENNReal) := by
      apply iSup_le
      intro M
      exact truncatedExpectedHittingTime_le_two_mul_horizon
        Q K x N hNpos hx0 hN M
    exact ne_top_of_le_ne_top (by finiteness : (2 : ENNReal) * (N : ENNReal) ≠ ∞) hbound


variable {A : Type uA} [Fintype A]
variable [MeasurableSpace A] [MeasurableSingletonClass A]

/-- **GCR5 stationary specialization.**  On a finite controlled state space,
almost-sure target hitting under one deterministic stationary policy implies
finite canonical expected hitting time under its homogeneous stationary
kernel. -/
theorem stationary_expectedHittingTime_ne_top_of_ae_eventually_hits
    (P : X → A → PMF X) (pi : X → A) (x : X) (K : Set X)
    (hHit : ∀ᵐ omega ∂stationaryTrajMeasure P pi (PMF.pure x),
      ∃ n : ℕ, omega n ∈ K) :
    expectedHittingTime (stationaryKernel P pi) x K ≠ ∞ := by
  have hHit' :
      ∀ᵐ omega ∂homTrajMeasure (Measure.dirac x) (stationaryKernel P pi),
        ∃ n : ℕ, omega n ∈ K := by
    simpa [stationaryTrajMeasure, PMF.toMeasure_pure] using hHit
  exact expectedHittingTime_ne_top_of_ae_eventually_hits_finite
    (stationaryKernel P pi) x K hHit'

end
end UEOT.V3.Compression.Objecthood
