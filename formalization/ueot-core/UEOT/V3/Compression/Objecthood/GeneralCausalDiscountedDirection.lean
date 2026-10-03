import UEOT.V3.Compression.Objecthood.ExactPathLawDiscountedHittingTransform
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace UEOT.V3.Compression.Objecthood

open Set Finset MeasureTheory ProbabilityTheory
open UEOT.V3.FiniteHistory
open UEOT.V3.FiniteHistoryMeasurable
open UEOT.V3.ReflexiveStateAugmentation
open UEOT.V3.RecoveryHittingNonnegative
open UEOT.V3.DynamicsKernel
open scoped ENNReal ProbabilityTheory

universe uX uA
noncomputable section

variable {X : Type uX} {A : Type uA}
variable [Fintype X] [Fintype A]
variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace A] [MeasurableSingletonClass A]

private theorem fixedPolicyAugmented_current_map_absorbed_of_mem
    (P : X → A → PMF X) (K : Set X) (n : ℕ)
    (pi : Kernel (HistoryFiber X A n) A) [IsMarkovKernel pi]
    (h : HistoryFiber X A n) (hx : currentFiber n h ∈ K) :
    (fixedPolicyAugmented n pi (pmfControlledKernel (absorbedRepairPMF P K)) h).map
        Carrier.current = Measure.dirac (currentFiber n h) := by
  let q := controlledNext n (pmfControlledKernel (absorbedRepairPMF P K))
  let B := Kernel.id ×ₖ pi
  have hq : q.comap Prod.snd measurable_snd = Kernel.prodMkLeft (HistoryFiber X A n) q := by
    ext z S hS
    simp [Kernel.comap_apply, Kernel.prodMkLeft_apply]
  have hphys :
      (fixedPolicyAugmented n pi (pmfControlledKernel (absorbedRepairPMF P K))).map
          Carrier.current = q ∘ₖ B := by
    unfold fixedPolicyAugmented
    rw [← Kernel.map_comp_right _ (measurable_advance_fixed n) measurable_current]
    have hcomp : Carrier.current ∘
        (fun p : (HistoryFiber X A n × A) × X =>
          Carrier.advance (⟨n, p.1.1⟩ : Carrier X A) p.1.2 p.2) = Prod.snd := by
      funext p
      exact Carrier.current_advance _ _ _
    rw [hcomp, ← Kernel.snd_eq, hq]
    exact Kernel.snd_compProd_prodMkLeft B q
  have happly := congrArg (fun k : Kernel (HistoryFiber X A n) X => k h) hphys
  rw [← Kernel.map_apply _ measurable_current] at ⊢
  rw [happly]
  ext S hS
  rw [Kernel.comp_apply' _ _ _ hS]
  unfold B
  rw [Kernel.prod_apply, Kernel.id_apply]
  rw [Measure.dirac_prod]
  rw [MeasureTheory.lintegral_map (q.measurable_coe hS) measurable_prodMk_left]
  have hconst : ∀ a : A, q (h, a) = Measure.dirac (currentFiber n h) := by
    intro a
    unfold q controlledNext
    rw [Kernel.comap_apply]
    exact pmfControlledKernel_absorbedRepair_of_mem P K hx a
  simp_rw [hconst]
  rw [Measure.dirac_apply' _ hS]
  by_cases hs : currentFiber n h ∈ S <;> simp [hs]

private theorem historyKernel_absorbed_target_mass_one
    (P : X → A → PMF X) (K : Set X)
    (pi : CausalPolicy X A) [∀ n, IsMarkovKernel (pi n)]
    (z : Carrier X A) (hz : z ∈ historyRepairTarget (A := A) K) :
    historyKernel (pmfControlledKernel (absorbedRepairPMF P K)) pi z
      (historyRepairTarget (A := A) K) = 1 := by
  rcases z with ⟨n,h⟩
  have hmap := fixedPolicyAugmented_current_map_absorbed_of_mem P K n (pi n) h hz
  have hK : MeasurableSet K := (Set.toFinite K).measurableSet
  have hm := congrArg (fun mu : Measure X => mu K) hmap
  rw [Measure.map_apply measurable_current hK] at hm
  rw [Measure.dirac_apply' _ hK] at hm
  have hx : currentFiber n h ∈ K := hz
  change fixedPolicyAugmented n (pi n)
      (pmfControlledKernel (absorbedRepairPMF P K)) h
      (historyRepairTarget (A := A) K) = 1
  simpa [historyRepairTarget, hx] using hm

private theorem iterateKernel_isMarkov_local
    (Q : Kernel (Carrier X A) (Carrier X A)) [IsMarkovKernel Q] :
    ∀ n : ℕ, IsMarkovKernel (iterateKernel Q n) := by
  intro n
  induction n with
  | zero => rw [iterateKernel_zero]; infer_instance
  | succ n ih => rw [iterateKernel_succ]; letI := ih; infer_instance

private theorem iterateKernel_comm_local
    (Q : Kernel (Carrier X A) (Carrier X A)) :
    ∀ n : ℕ, Q ∘ₖ iterateKernel Q n = iterateKernel Q n ∘ₖ Q := by
  intro n
  induction n with
  | zero => simp [iterateKernel_zero]
  | succ n ih =>
      rw [iterateKernel_succ]
      calc
        Q ∘ₖ (Q ∘ₖ iterateKernel Q n) = Q ∘ₖ (iterateKernel Q n ∘ₖ Q) :=
          congrArg (fun R : Kernel (Carrier X A) (Carrier X A) => Q ∘ₖ R) ih
        _ = (Q ∘ₖ iterateKernel Q n) ∘ₖ Q := (Kernel.comp_assoc Q (iterateKernel Q n) Q).symm

private theorem iterateKernel_succ_right_local
    (Q : Kernel (Carrier X A) (Carrier X A)) (n : ℕ) :
    iterateKernel Q (n + 1) = iterateKernel Q n ∘ₖ Q := by
  rw [iterateKernel_succ, iterateKernel_comm_local Q n]

private noncomputable def carrierTargetMass
    (Q : Kernel (Carrier X A) (Carrier X A)) (K : Set X)
    (z : Carrier X A) (n : ℕ) : ℝ≥0∞ :=
  iterateKernel Q n z (historyRepairTarget (A := A) K)

private theorem carrierTargetMass_succ
    (Q : Kernel (Carrier X A) (Carrier X A)) [IsMarkovKernel Q]
    (K : Set X) (z : Carrier X A) (n : ℕ) :
    carrierTargetMass Q K z (n + 1) =
      ∫⁻ y, carrierTargetMass Q K y n ∂Q z := by
  have hT : MeasurableSet (historyRepairTarget (A := A) K) :=
    measurableSet_historyRepairTarget (A := A) K
  unfold carrierTargetMass
  rw [iterateKernel_succ_right_local]
  rw [Kernel.comp_apply' _ _ _ hT]

private theorem survivalProb_zero_eq_one_of_not_mem
    (Q : Kernel (Carrier X A) (Carrier X A)) [IsMarkovKernel Q]
    (K : Set X) (z : Carrier X A)
    (hz : z ∉ historyRepairTarget (A := A) K) :
    survivalProb Q z (historyRepairTarget (A := A) K) 0 = 1 := by
  let e : ((i : Finset.Iic 0) → Carrier X A) ≃ᵐ Carrier X A :=
    MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => Carrier X A)
  have hprefix :
      prefixLaw Q z 0 = (Measure.dirac z).map e.symm := by
    unfold prefixLaw
    simpa [e] using homTrajMeasure_prefix_zero (Measure.dirac z) Q
  have hT : MeasurableSet (historyRepairTarget (A := A) K) :=
    measurableSet_historyRepairTarget (A := A) K
  have hS : MeasurableSet (historySurvivalSet (historyRepairTarget (A := A) K) 0) :=
    measurableSet_historySurvivalSet hT 0
  unfold survivalProb
  rw [hprefix]
  rw [Measure.map_apply e.symm.measurable hS]
  rw [Measure.dirac_apply' z (hS.preimage e.symm.measurable)]
  have hcoord : (e.symm z) (lastHistoryIndex 0) = z := by
    have he := e.apply_symm_apply z
    change (e.symm z) default = z at he
    have hi : lastHistoryIndex 0 = default := Subsingleton.elim _ _
    simpa [hi] using he
  have hmem : e.symm z ∈ historySurvivalSet (historyRepairTarget (A := A) K) 0 := by
    rw [mem_historySurvivalSet_iff]
    intro i
    have hi : i = lastHistoryIndex 0 := Subsingleton.elim _ _
    subst i
    simpa [hcoord] using hz
  simp [hmem]

private theorem carrierTargetMass_add_survival_eq_one_of_absorbing
    (Q : Kernel (Carrier X A) (Carrier X A)) [IsMarkovKernel Q]
    (K : Set X)
    (hAbs : ∀ z, z ∈ historyRepairTarget (A := A) K →
      Q z (historyRepairTarget (A := A) K) = 1) :
    ∀ n z, carrierTargetMass Q K z n +
      survivalProb Q z (historyRepairTarget (A := A) K) n = 1 := by
  have hT : MeasurableSet (historyRepairTarget (A := A) K) :=
    measurableSet_historyRepairTarget (A := A) K
  intro n
  induction n with
  | zero =>
      intro z
      by_cases hz : z ∈ historyRepairTarget (A := A) K
      · rw [survivalProb_eq_zero_of_mem Q z _ hT hz 0]
        unfold carrierTargetMass
        rw [iterateKernel_zero, Kernel.id_apply]
        rw [Measure.dirac_apply' z hT]
        simp [hz]
      · rw [survivalProb_zero_eq_one_of_not_mem Q K z hz]
        unfold carrierTargetMass
        rw [iterateKernel_zero, Kernel.id_apply]
        rw [Measure.dirac_apply' z hT]
        simp [hz]
  | succ n ih =>
      intro z
      by_cases hz : z ∈ historyRepairTarget (A := A) K
      · rw [survivalProb_eq_zero_of_mem Q z _ hT hz (n + 1)]
        simp only [add_zero]
        rw [carrierTargetMass_succ]
        have hae : ∀ᵐ y ∂Q z, y ∈ historyRepairTarget (A := A) K := by
          apply (MeasureTheory.ae_iff).2
          change Q z (historyRepairTarget (A := A) K)ᶜ = 0
          exact (prob_compl_eq_zero_iff hT).2 (hAbs z hz)
        have hmass : ∀ᵐ y ∂Q z, carrierTargetMass Q K y n = 1 := by
          filter_upwards [hae] with y hy
          have hi := ih y
          rw [survivalProb_eq_zero_of_mem Q y _ hT hy n] at hi
          simpa using hi
        rw [lintegral_congr_ae hmass]
        simp
      · rw [carrierTargetMass_succ]
        rw [survivalProb_succ_eq_lintegral Q z _ hT hz n]
        have hmeas : Measurable (fun y => carrierTargetMass Q K y n) := by
          exact Kernel.measurable_coe (iterateKernel Q n) hT
        rw [← MeasureTheory.lintegral_add_left hmeas]
        calc
          (∫⁻ y, carrierTargetMass Q K y n +
              survivalProb Q y (historyRepairTarget (A := A) K) n ∂Q z) =
              ∫⁻ _y, (1 : ℝ≥0∞) ∂Q z := by
                apply lintegral_congr
                intro y
                exact ih y
          _ = 1 := by simp

private theorem absorbedHistory_targetMass_add_survival_eq_one
    (P : X → A → PMF X) (K : Set X)
    (pi : CausalPolicy X A) [∀ n, IsMarkovKernel (pi n)]
    (n : ℕ) (z : Carrier X A) :
    let Q := historyKernel (pmfControlledKernel (absorbedRepairPMF P K)) pi
    carrierTargetMass Q K z n +
      survivalProb Q z (historyRepairTarget (A := A) K) n = 1 := by
  dsimp only
  exact carrierTargetMass_add_survival_eq_one_of_absorbing
    (historyKernel (pmfControlledKernel (absorbedRepairPMF P K)) pi) K
    (historyKernel_absorbed_target_mass_one P K pi) n z


/-- In the absorbed exact causal law, the target-coordinate probability plus
finite survival probability is exactly one at every time. -/
theorem absorbed_targetProb_add_survivalReal_eq_one
    (P : X → A → PMF X) (K : Set X) (x : X)
    (pi : AdmissibleCausalRepairPolicy X A) (n : ℕ) :
    (causalRepairPathLaw (absorbedRepairPMF P K) x pi).real
        {omega | omega n ∈ K} +
      (causalRepairPathLaw (absorbedRepairPMF P K) x pi).real
        (survivalSet K n) = 1 := by
  letI : ∀ m, IsMarkovKernel (pi.policy m) := pi.markov
  let Q := historyKernel (pmfControlledKernel (absorbedRepairPMF P K)) pi.policy
  let z0 := Carrier.singleton (A := A) x
  have hsum := absorbedHistory_targetMass_add_survival_eq_one
    P K pi.policy n z0
  have hmass_top : carrierTargetMass Q K z0 n ≠ ∞ := by
    letI : IsMarkovKernel (iterateKernel Q n) := iterateKernel_isMarkov_local Q n
    exact measure_ne_top _ _
  have hsurv_top : survivalProb Q z0 (historyRepairTarget (A := A) K) n ≠ ∞ := by
    unfold survivalProb
    exact measure_ne_top _ _
  have hreal := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add hmass_top hsurv_top, ENNReal.toReal_one] at hreal
  rw [causalRepairPathLaw_targetProbability_eq_carrier P K x pi n]
  rw [measureReal_def]
  rw [causalRepairPathLaw_survival_eq_historySurvivalProb
    (absorbedRepairPMF P K) K x pi n]
  change (carrierTargetMass Q K z0 n).toReal +
      (survivalProb Q z0 (historyRepairTarget (A := A) K) n).toReal = 1
  simpa [carrierTargetProbability, carrierTargetMass, Q, z0, measureReal_def] using hreal

/-- Almost-sure eventual repair forces finite-horizon survival probabilities of
the absorbed exact causal path law to converge to zero. -/
theorem absorbed_survivalReal_tendsto_zero_of_ae_eventually_hits
    (P : X → A → PMF X) (K : Set X) (x : X)
    (pi : AdmissibleCausalRepairPolicy X A)
    (hHit : ∀ᵐ omega ∂causalRepairPathLaw P x pi,
      ∃ n : ℕ, omega n ∈ K) :
    Filter.Tendsto
      (fun n => (causalRepairPathLaw (absorbedRepairPMF P K) x pi).real
        (survivalSet K n))
      Filter.atTop (nhds 0) := by
  let mu := causalRepairPathLaw (absorbedRepairPMF P K) x pi
  letI : IsProbabilityMeasure mu := by
    dsimp [mu, causalRepairPathLaw]
    infer_instance
  have hHitAbs : ∀ᵐ omega ∂mu, ∃ n : ℕ, omega n ∈ K := by
    exact (causalRepairPathLaw_absorbed_eventually_hits_iff P K x pi).2 hHit
  have hNever : mu (neverHitSet K) = 0 := by
    have h0 := (MeasureTheory.ae_iff).1 hHitAbs
    have hset : {omega : ℕ → X | ¬ ∃ n : ℕ, omega n ∈ K} = neverHitSet K := by
      ext omega
      simp [neverHitSet]
    rwa [hset] at h0
  have hK : MeasurableSet K := (Set.toFinite K).measurableSet
  have hENN : Filter.Tendsto (fun n => mu (survivalSet K n))
      Filter.atTop (nhds 0) := by
    have ht := tendsto_measure_iInter_atTop
      (μ := mu)
      (s := survivalSet K)
      (fun n => (measurableSet_survivalSet hK n).nullMeasurableSet)
      (antitone_survivalSet K)
      ⟨0, measure_ne_top _ _⟩
    rw [← neverHitSet_eq_iInter_survivalSet K, hNever] at ht
    simpa [Function.comp_def] using ht
  have hReal := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hENN
  simpa [mu, Measure.real, Function.comp_def] using hReal


/-- Normalized geometric Abel average. -/
noncomputable def geometricAbelAverage (s : ℕ → ℝ) (beta : ℝ) : ℝ :=
  ∑' n : ℕ, beta ^ n * (1 - beta) * s n

private theorem summable_geometricWeighted
    (s : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hs1 : ∀ n, s n ≤ 1)
    (beta : ℝ) (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) :
    Summable (fun n : ℕ => beta ^ n * (1 - beta) * s n) := by
  have hgeom : Summable (fun n : ℕ => beta ^ n) :=
    summable_geometric_of_lt_one hbeta0 hbeta1
  apply Summable.of_nonneg_of_le (f := fun n : ℕ => beta ^ n)
  · intro n
    exact mul_nonneg (mul_nonneg (pow_nonneg hbeta0 n) (sub_nonneg.mpr hbeta1.le)) (hs0 n)
  · intro n
    have hp : 0 ≤ beta ^ n := pow_nonneg hbeta0 n
    have hcoef0 : 0 ≤ (1 - beta) * s n :=
      mul_nonneg (sub_nonneg.mpr hbeta1.le) (hs0 n)
    have hcoef1 : (1 - beta) * s n ≤ 1 := by
      have hsub : 0 ≤ 1 - beta := sub_nonneg.mpr hbeta1.le
      have hsub1 : 1 - beta ≤ 1 := by linarith
      nlinarith [hs0 n, hs1 n]
    calc
      beta ^ n * (1 - beta) * s n = beta ^ n * ((1 - beta) * s n) := by ring
      _ ≤ beta ^ n * 1 := mul_le_mul_of_nonneg_left hcoef1 hp
      _ = beta ^ n := by ring
  · exact hgeom

private theorem tsum_normalized_geometric
    (beta : ℝ) (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) :
    (∑' n : ℕ, beta ^ n * (1 - beta)) = 1 := by
  have hgeom : Summable (fun n : ℕ => beta ^ n) :=
    summable_geometric_of_lt_one hbeta0 hbeta1
  rw [hgeom.tsum_mul_right]
  rw [tsum_geometric_of_lt_one hbeta0 hbeta1]
  exact inv_mul_cancel₀ (sub_ne_zero.mpr (ne_of_gt hbeta1))

private theorem geometricAbelAverage_nonneg
    (s : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n)
    (beta : ℝ) (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1) :
    0 ≤ geometricAbelAverage s beta := by
  unfold geometricAbelAverage
  exact tsum_nonneg fun n =>
    mul_nonneg (mul_nonneg (pow_nonneg hbeta0 n) (sub_nonneg.mpr hbeta1)) (hs0 n)

private theorem geometricAbelAverage_le_one
    (s : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hs1 : ∀ n, s n ≤ 1)
    (beta : ℝ) (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) :
    geometricAbelAverage s beta ≤ 1 := by
  have hsumm := summable_geometricWeighted s hs0 hs1 beta hbeta0 hbeta1
  have hweights : Summable (fun n : ℕ => beta ^ n * (1 - beta)) :=
    (summable_geometric_of_lt_one hbeta0 hbeta1).mul_right (1 - beta)
  unfold geometricAbelAverage
  calc
    (∑' n : ℕ, beta ^ n * (1 - beta) * s n) ≤
        ∑' n : ℕ, beta ^ n * (1 - beta) := by
      apply Summable.tsum_le_tsum
      · intro n
        have hw : 0 ≤ beta ^ n * (1 - beta) := by positivity
        exact mul_le_of_le_one_right hw (hs1 n)
      · exact hsumm
      · exact hweights
    _ = 1 := tsum_normalized_geometric beta hbeta0 hbeta1


private theorem geometricAbelAverage_le_head_tail
    (s : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hs1 : ∀ n, s n ≤ 1)
    (delta : ℝ) (hdelta0 : 0 ≤ delta)
    (N : ℕ) (htail : ∀ n, N ≤ n → s n ≤ delta)
    (beta : ℝ) (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) :
    geometricAbelAverage s beta ≤ (N : ℝ) * (1 - beta) + delta := by
  let f : ℕ → ℝ := fun n => beta ^ n * (1 - beta) * s n
  let w : ℕ → ℝ := fun n => beta ^ n * (1 - beta)
  have hsumm : Summable f := by
    simpa [f] using summable_geometricWeighted s hs0 hs1 beta hbeta0 hbeta1
  have hwsumm : Summable w := by
    simpa [w] using (summable_geometric_of_lt_one hbeta0 hbeta1).mul_right (1 - beta)
  have hsplit := hsumm.sum_add_tsum_nat_add N
  have hhead : (∑ i ∈ Finset.range N, f i) ≤ (N : ℝ) * (1 - beta) := by
    calc
      (∑ i ∈ Finset.range N, f i) ≤ ∑ _i ∈ Finset.range N, (1 - beta) := by
        apply Finset.sum_le_sum
        intro i hi
        have hp0 : 0 ≤ beta ^ i := pow_nonneg hbeta0 i
        have hp1 : beta ^ i ≤ 1 := pow_le_one₀ hbeta0 hbeta1.le
        have hw0 : 0 ≤ beta ^ i * (1 - beta) :=
          mul_nonneg hp0 (sub_nonneg.mpr hbeta1.le)
        calc
          f i = (beta ^ i * (1 - beta)) * s i := by simp [f, mul_assoc]
          _ ≤ beta ^ i * (1 - beta) := mul_le_of_le_one_right hw0 (hs1 i)
          _ ≤ 1 * (1 - beta) :=
            mul_le_mul_of_nonneg_right hp1 (sub_nonneg.mpr hbeta1.le)
          _ = 1 - beta := one_mul _
      _ = (N : ℝ) * (1 - beta) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hfs_shift : Summable (fun n => f (n + N)) :=
    (summable_nat_add_iff N).2 hsumm
  have hws_shift : Summable (fun n => w (n + N)) :=
    (summable_nat_add_iff N).2 hwsumm
  have hweight_total : (∑' n, w n) = 1 := by
    simpa [w] using tsum_normalized_geometric beta hbeta0 hbeta1
  have htail_weight : (∑' n, w (n + N)) ≤ 1 := by
    have hwhead : 0 ≤ ∑ i ∈ Finset.range N, w i := by
      exact Finset.sum_nonneg fun i hi => by
        simp [w]
        positivity
    have hw := hwsumm.sum_add_tsum_nat_add N
    rw [hweight_total] at hw
    linarith
  have htail_sum : (∑' n, f (n + N)) ≤ delta := by
    have hdomSumm : Summable (fun n => delta * w (n + N)) :=
      hws_shift.mul_left delta
    calc
      (∑' n, f (n + N)) ≤ ∑' n, delta * w (n + N) := by
        apply Summable.tsum_le_tsum
        · intro n
          have hw0 : 0 ≤ w (n + N) := by
            simp [w]
            positivity
          have hsle : s (n + N) ≤ delta := htail (n + N) (Nat.le_add_left N n)
          calc
            f (n + N) = w (n + N) * s (n + N) := by simp [f, w, mul_assoc]
            _ ≤ w (n + N) * delta := mul_le_mul_of_nonneg_left hsle hw0
            _ = delta * w (n + N) := by ring
        · exact hfs_shift
        · exact hdomSumm
      _ = delta * (∑' n, w (n + N)) := hws_shift.tsum_mul_left delta
      _ ≤ delta * 1 := mul_le_mul_of_nonneg_left htail_weight hdelta0
      _ = delta := mul_one _
  unfold geometricAbelAverage
  change (∑' n, f n) ≤ _
  rw [← hsplit]
  linarith


/-- Sequential Abel theorem for normalized geometric averages.  It is stated for
an arbitrary sequence `beta_m -> 1` inside `[0,1)`, exactly the form consumed by
GCR4's finite-policy pigeonhole extraction. -/
theorem geometricAbelAverage_tendsto_zero
    (s : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hs1 : ∀ n, s n ≤ 1)
    (hs : Filter.Tendsto s Filter.atTop (nhds 0))
    (beta : ℕ → ℝ) (hbeta0 : ∀ m, 0 ≤ beta m)
    (hbeta1 : ∀ m, beta m < 1)
    (hbeta : Filter.Tendsto beta Filter.atTop (nhds 1)) :
    Filter.Tendsto (fun m => geometricAbelAverage s (beta m))
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  have hhalf : 0 < epsilon / 2 := by linarith
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hs) (epsilon / 2) hhalf
  have htail : ∀ n, N ≤ n → s n ≤ epsilon / 2 := by
    intro n hn
    have hd := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hs0 n)] at hd
    exact hd.le
  let eta : ℝ := epsilon / (2 * ((N : ℝ) + 1))
  have heta : 0 < eta := by
    dsimp [eta]
    positivity
  obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.mp hbeta) eta heta
  refine ⟨M, ?_⟩
  intro m hm
  have hclose := hM m hm
  have hgap0 : 0 ≤ 1 - beta m := sub_nonneg.mpr (hbeta1 m).le
  have hgap : 1 - beta m < eta := by
    rw [Real.dist_eq] at hclose
    have habs : |beta m - 1| = 1 - beta m := by
      rw [abs_of_nonpos (sub_nonpos.mpr (hbeta1 m).le)]
      ring
    rwa [habs] at hclose
  have hNcast : (0 : ℝ) ≤ N := by positivity
  have hN1pos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hhead : (N : ℝ) * (1 - beta m) < epsilon / 2 := by
    calc
      (N : ℝ) * (1 - beta m) ≤ ((N : ℝ) + 1) * (1 - beta m) := by
        exact mul_le_mul_of_nonneg_right (by linarith) hgap0
      _ < ((N : ℝ) + 1) * eta := mul_lt_mul_of_pos_left hgap hN1pos
      _ = epsilon / 2 := by
        dsimp [eta]
        field_simp
  have havg_nonneg := geometricAbelAverage_nonneg s hs0 (beta m)
    (hbeta0 m) (hbeta1 m).le
  have havg_le := geometricAbelAverage_le_head_tail s hs0 hs1
    (epsilon / 2) hhalf.le N htail (beta m) (hbeta0 m) (hbeta1 m)
  have havg_lt : geometricAbelAverage s (beta m) < epsilon := by
    linarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg havg_nonneg]
  exact havg_lt


/-- Exact GCR2 occupation is the infinite target-coordinate geometric series
for every genuine discount `0 < beta < 1`. -/
theorem causalNormalizedOccupation_eq_tsum_target
    (P : X → A → PMF X) (K : Set X) (x : X)
    (pi : AdmissibleCausalRepairPolicy X A)
    (beta : ℝ) (hbeta0 : 0 < beta) (hbeta1 : beta < 1) :
    causalNormalizedOccupation P K x pi beta =
      ∑' n : ℕ, beta ^ n * (1 - beta) *
        (causalRepairPathLaw (absorbedRepairPMF P K) x pi).real
          {omega | omega n ∈ K} := by
  letI : ∀ m, IsMarkovKernel (pi.policy m) := pi.markov
  letI : IsProbabilityMeasure
      (causalRepairPathLaw (absorbedRepairPMF P K) x pi) := by
    dsimp [causalRepairPathLaw]
    infer_instance
  let t : ℕ → ℝ := fun n =>
    (causalRepairPathLaw (absorbedRepairPMF P K) x pi).real {omega | omega n ∈ K}
  have ht0 : ∀ n, 0 ≤ t n := fun n => measureReal_nonneg
  have ht1 : ∀ n, t n ≤ 1 := fun n => measureReal_le_one
  have hsumm : Summable (fun n : ℕ => beta ^ n * (1 - beta) * t n) :=
    summable_geometricWeighted t ht0 ht1 beta hbeta0.le hbeta1
  have hpartial := causalNormalizedOccupationPartial_tendsto
    P K x pi beta hbeta0 hbeta1
  have htsum := hsumm.hasSum.tendsto_sum_nat
  have hpartial' : Filter.Tendsto
      (fun N => ∑ n ∈ Finset.range N, beta ^ n * (1 - beta) * t n)
      Filter.atTop (nhds (causalNormalizedOccupation P K x pi beta)) := by
    simpa [causalNormalizedOccupationPartial, t] using hpartial
  have htsum' : Filter.Tendsto
      (fun N => ∑ n ∈ Finset.range N, beta ^ n * (1 - beta) * t n)
      Filter.atTop (nhds (∑' n : ℕ, beta ^ n * (1 - beta) * t n)) := by
    simpa using htsum
  exact tendsto_nhds_unique hpartial' htsum'

/-- GCR3 survival representation: exact normalized occupation is one minus the
Abel average of finite survival probabilities. -/
theorem causalNormalizedOccupation_eq_one_sub_survivalAbel
    (P : X → A → PMF X) (K : Set X) (x : X)
    (pi : AdmissibleCausalRepairPolicy X A)
    (beta : ℝ) (hbeta0 : 0 < beta) (hbeta1 : beta < 1) :
    causalNormalizedOccupation P K x pi beta =
      1 - geometricAbelAverage
        (fun n => (causalRepairPathLaw (absorbedRepairPMF P K) x pi).real
          (survivalSet K n)) beta := by
  letI : ∀ m, IsMarkovKernel (pi.policy m) := pi.markov
  letI : IsProbabilityMeasure
      (causalRepairPathLaw (absorbedRepairPMF P K) x pi) := by
    dsimp [causalRepairPathLaw]
    infer_instance
  let t : ℕ → ℝ := fun n =>
    (causalRepairPathLaw (absorbedRepairPMF P K) x pi).real {omega | omega n ∈ K}
  let surv : ℕ → ℝ := fun n =>
    (causalRepairPathLaw (absorbedRepairPMF P K) x pi).real (survivalSet K n)
  have ht0 : ∀ n, 0 ≤ t n := fun n => measureReal_nonneg
  have ht1 : ∀ n, t n ≤ 1 := fun n => measureReal_le_one
  have hs0 : ∀ n, 0 ≤ surv n := fun n => measureReal_nonneg
  have hs1 : ∀ n, surv n ≤ 1 := fun n => measureReal_le_one
  have hcomp : ∀ n, t n + surv n = 1 := by
    intro n
    exact absorbed_targetProb_add_survivalReal_eq_one P K x pi n
  have hweights : Summable (fun n : ℕ => beta ^ n * (1 - beta)) :=
    (summable_geometric_of_lt_one hbeta0.le hbeta1).mul_right (1 - beta)
  have hsurv : Summable (fun n : ℕ => beta ^ n * (1 - beta) * surv n) :=
    summable_geometricWeighted surv hs0 hs1 beta hbeta0.le hbeta1
  rw [causalNormalizedOccupation_eq_tsum_target P K x pi beta hbeta0 hbeta1]
  change (∑' n : ℕ, beta ^ n * (1 - beta) * t n) =
    1 - geometricAbelAverage surv beta
  have hterm : ∀ n : ℕ,
      beta ^ n * (1 - beta) * t n =
        beta ^ n * (1 - beta) - beta ^ n * (1 - beta) * surv n := by
    intro n
    have ht : t n = 1 - surv n := by linarith [hcomp n]
    rw [ht]
    ring
  simp_rw [hterm]
  rw [hweights.tsum_sub hsurv]
  rw [tsum_normalized_geometric beta hbeta0.le hbeta1]
  rfl


/-- **GCR3 arbitrary-causal discounted direction.**  At every genuine discount,
the exact path-law normalized occupation of any admissible randomized complete-
history causal policy is bounded by the existing deterministic stationary greedy
Bellman certificate. -/
theorem causalNormalizedOccupation_le_greedyValue
    [Nonempty A]
    (P : X → A → PMF X) (K : Set X) (x : X)
    (pi : AdmissibleCausalRepairPolicy X A)
    (beta : ℝ) (hbeta0 : 0 < beta) (hbeta1 : beta < 1) :
    causalNormalizedOccupation P K x pi beta ≤
      (normalizedRepairGreedyCertificate P K beta hbeta0 hbeta1).value x := by
  letI : ∀ m, IsMarkovKernel (pi.policy m) := pi.markov
  have hdom := allCausal_normalizedDiscountedRepair_le_greedy
    P K beta hbeta0 hbeta1 pi.policy x
  have heq := admissibleCausalNormalizedInfiniteValue_eq_occupation
    P K x pi beta hbeta0 hbeta1
  have heq' :
      (causalNormalizedRepairModel P K beta hbeta0.le hbeta1).infiniteValue
          pi.policy 0
          (UEOT.V3.CompactCausalOptimalityCore.initialHistory (A := A) x) =
        causalNormalizedOccupation P K x pi beta := by
    simpa [admissibleCausalNormalizedInfiniteValue] using heq
  rw [heq'] at hdom
  exact hdom

/-- **GCR3 Abelian reachability direction.**  For any sequence of genuine
discounts approaching one, almost-sure eventual repair of an arbitrary
admissible complete-history causal policy forces its exact normalized path-law
hitting surrogate to converge to one. -/
theorem causalNormalizedOccupation_tendsto_one_of_ae_eventually_hits
    (P : X → A → PMF X) (K : Set X) (x : X)
    (pi : AdmissibleCausalRepairPolicy X A)
    (hHit : ∀ᵐ omega ∂causalRepairPathLaw P x pi,
      ∃ n : ℕ, omega n ∈ K)
    (beta : ℕ → ℝ) (hbeta0 : ∀ m, 0 < beta m)
    (hbeta1 : ∀ m, beta m < 1)
    (hbeta : Filter.Tendsto beta Filter.atTop (nhds 1)) :
    Filter.Tendsto
      (fun m => causalNormalizedOccupation P K x pi (beta m))
      Filter.atTop (nhds 1) := by
  letI : ∀ m, IsMarkovKernel (pi.policy m) := pi.markov
  let mu := causalRepairPathLaw (absorbedRepairPMF P K) x pi
  letI : IsProbabilityMeasure mu := by
    dsimp [mu, causalRepairPathLaw]
    infer_instance
  let surv : ℕ → ℝ := fun n => mu.real (survivalSet K n)
  have hs0 : ∀ n, 0 ≤ surv n := fun n => measureReal_nonneg
  have hs1 : ∀ n, surv n ≤ 1 := fun n => measureReal_le_one
  have hs : Filter.Tendsto surv Filter.atTop (nhds 0) := by
    simpa [surv, mu] using
      absorbed_survivalReal_tendsto_zero_of_ae_eventually_hits P K x pi hHit
  have hAbel := geometricAbelAverage_tendsto_zero
    surv hs0 hs1 hs beta (fun m => (hbeta0 m).le) hbeta1 hbeta
  have hOcc :
      (fun m => causalNormalizedOccupation P K x pi (beta m)) =
        (fun m => 1 - geometricAbelAverage surv (beta m)) := by
    funext m
    simpa [surv, mu] using
      causalNormalizedOccupation_eq_one_sub_survivalAbel
        P K x pi (beta m) (hbeta0 m) (hbeta1 m)
  rw [hOcc]
  simpa using hAbel.const_sub 1

end
end UEOT.V3.Compression.Objecthood
