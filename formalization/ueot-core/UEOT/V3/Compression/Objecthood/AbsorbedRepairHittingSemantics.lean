import UEOT.V3.Compression.Objecthood.AbsorbedDiscountedRepair
import UEOT.V3.RecoveryHittingPoisson
import UEOT.V3.ReflexiveStatePathLaw
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Track O / GCR1 — absorbed repair first-hitting semantics

This file closes the semantic obligation that target absorption changes only
post-hit behavior.  It proves equality of every finite survival probability for
the original and absorbed complete-history causal laws, then lifts that equality
to almost-sure eventual hitting.
-/

namespace UEOT.V3.Compression.Objecthood

open Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder ProbabilityTheory
open UEOT.V3.DynamicsKernel
open UEOT.V3.FiniteHistory
open UEOT.V3.FiniteHistoryMeasurable
open UEOT.V3.RecoveryHittingNonnegative
open UEOT.V3.RecoveryHittingFirstStep
open UEOT.V3.RecoveryHittingRestart
open UEOT.V3.RecoveryHittingPoisson
open UEOT.V3.ReflexiveStateAugmentation
open UEOT.V3.ReflexiveStatePathLaw
open scoped ENNReal ProbabilityTheory

universe uX uA uZ
noncomputable section

variable {Z : Type uZ} [MeasurableSpace Z]

/-- Homogeneous Ionescu--Tulcea event probability is the mixture of its
point-mass-start event probabilities over the initial law. -/
theorem homTrajMeasure_apply_eq_lintegral_initial
    (P : Kernel Z Z) [IsMarkovKernel P]
    (μ : Measure Z) (E : Set (ℕ → Z)) (hE : MeasurableSet E) :
    homTrajMeasure μ P E =
      ∫⁻ z, homTrajMeasure (Measure.dirac z) P E ∂μ := by
  letI : ∀ n, IsMarkovKernel (homHistoryKernel P n) :=
    fun n => isMarkovKernel_homHistoryKernel P n
  let e : ((i : Iic 0) → Z) ≃ᵐ Z :=
    MeasurableEquiv.piUnique (fun _ : Iic 0 => Z)
  have hinner : Measurable
      (fun h : (i : Iic 0) → Z =>
        Kernel.traj (X := fun _ : ℕ => Z) (homHistoryKernel P) 0 h E) :=
    (Kernel.traj (X := fun _ : ℕ => Z) (homHistoryKernel P) 0).measurable_coe hE
  unfold homTrajMeasure
  rw [Kernel.trajMeasure]
  rw [Measure.bind_apply hE (Kernel.aemeasurable _)]
  change
    (∫⁻ h : (i : Iic 0) → Z,
      Kernel.traj (X := fun _ : ℕ => Z) (homHistoryKernel P) 0 h E
      ∂μ.map e.symm) = _
  rw [lintegral_map hinner e.symm.measurable]
  apply lintegral_congr
  intro z
  rw [Kernel.trajMeasure]
  have hmap :
      Measure.map (MeasurableEquiv.piUnique (fun _ : Iic 0 => Z)).symm
          (Measure.dirac z) =
        Measure.dirac ((MeasurableEquiv.piUnique (fun _ : Iic 0 => Z)).symm z) := by
    exact Measure.map_dirac'
      (MeasurableEquiv.piUnique (fun _ : Iic 0 => Z)).symm.measurable z
  rw [hmap]
  rw [Measure.dirac_bind (Kernel.measurable _)
    ((MeasurableEquiv.piUnique (fun _ : Iic 0 => Z)).symm z)]


/-- Generic time-zero marginal of the homogeneous Ionescu--Tulcea path law.
Unlike the older viability-facing wrapper, this theorem needs no finite-state
assumption and therefore applies to the time-tagged complete-history carrier. -/
theorem homTrajMeasure_time_zero_general
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (P : Kernel Z Z) [IsMarkovKernel P] :
    (homTrajMeasure μ P).map (fun omega : ℕ → Z => omega 0) = μ := by
  let μpath := homTrajMeasure μ P
  have hzero := homTrajMeasure_prefix_zero μ P
  calc
    μpath.map (fun omega : ℕ → Z => omega 0) =
        (μpath.map (frestrictLe 0)).map
          (fun h => h (lastHistoryIndex 0)) := by
      symm
      rw [Measure.map_map
        (μ := μpath)
        (measurable_pi_apply (lastHistoryIndex 0))
        (measurable_frestrictLe 0)]
      rfl
    _ =
        (μ.map
          (MeasurableEquiv.piUnique
            (fun _ : Iic 0 => Z)).symm).map
          (fun h => h (lastHistoryIndex 0)) := by
      rw [hzero]
    _ = μ := by
      rw [Measure.map_map
        (measurable_pi_apply (lastHistoryIndex 0))
        (MeasurableEquiv.piUnique
          (fun _ : Iic 0 => Z)).symm.measurable]
      simpa [Function.comp_def] using (Measure.map_id μ)

/-- Survival probability is the full homogeneous path-law mass of the finite
survival event. -/
theorem survivalProb_eq_homTrajMeasure_apply
    (P : Kernel Z Z) [IsMarkovKernel P]
    (x : Z) (A : Set Z) (hA : MeasurableSet A) (n : ℕ) :
    survivalProb P x A n =
      homTrajMeasure (Measure.dirac x) P (survivalSet A n) := by
  unfold survivalProb prefixLaw survivalSet
  rw [Measure.map_apply (measurable_frestrictLe n)
    (measurableSet_historySurvivalSet hA n)]

/-- First-step recurrence for exact finite survival probabilities. -/
theorem survivalProb_succ_eq_lintegral
    (P : Kernel Z Z) [IsMarkovKernel P]
    (x : Z) (A : Set Z) (hA : MeasurableSet A)
    (hx : x ∉ A) (n : ℕ) :
    survivalProb P x A (n + 1) =
      ∫⁻ y, survivalProb P y A n ∂P x := by
  let μpath := homTrajMeasure (Measure.dirac x) P
  have hzero := homTrajMeasure_time_zero_general (Measure.dirac x) P
  have hbad : μpath {omega : ℕ → Z | omega 0 ∈ A} = 0 := by
    have hm := congrArg (fun ν : Measure Z => ν A) hzero
    rw [Measure.map_apply (measurable_pi_apply 0) hA] at hm
    rw [Measure.dirac_apply' x hA] at hm
    change μpath ((fun omega : ℕ → Z => omega 0) ⁻¹' A) = 0
    simpa [μpath, Set.indicator, hx] using hm
  have hae0 : ∀ᵐ omega ∂μpath, omega 0 ∉ A := by
    apply (MeasureTheory.ae_iff).2
    simpa only [not_not] using hbad
  have hevent :
      survivalSet A (n + 1) =ᵐ[μpath]
        pathShift ⁻¹' survivalSet A n := by
    filter_upwards [hae0] with omega h0
    exact propext (mem_survivalSet_succ_iff_shift A n omega h0)
  have hmeasure :
      μpath (survivalSet A (n + 1)) =
        (μpath.map pathShift) (survivalSet A n) := by
    calc
      μpath (survivalSet A (n + 1)) = μpath (pathShift ⁻¹' survivalSet A n) :=
        measure_congr hevent
      _ = (μpath.map pathShift) (survivalSet A n) := by
        symm
        exact Measure.map_apply measurable_pathShift
          (measurableSet_survivalSet hA n)
  rw [survivalProb_eq_homTrajMeasure_apply P x A hA (n + 1)]
  change μpath (survivalSet A (n + 1)) = _
  rw [hmeasure]
  have hshift := homTrajMeasure_shift (Measure.dirac x) P
  rw [kernel_comp_dirac P x] at hshift
  rw [hshift]
  rw [homTrajMeasure_apply_eq_lintegral_initial P (P x)
    (survivalSet A n) (measurableSet_survivalSet hA n)]
  apply lintegral_congr
  intro y
  symm
  exact survivalProb_eq_homTrajMeasure_apply P y A hA n

/-- If the initial state is already in the target, every finite survival
probability is zero. -/
theorem survivalProb_eq_zero_of_mem
    (P : Kernel Z Z) [IsMarkovKernel P]
    (x : Z) (A : Set Z) (hA : MeasurableSet A)
    (hx : x ∈ A) (n : ℕ) :
    survivalProb P x A n = 0 := by
  rw [survivalProb_eq_homTrajMeasure_apply P x A hA n]
  have hsubset : survivalSet A n ⊆ {omega : ℕ → Z | omega 0 ∉ A} := by
    intro omega hs
    exact (mem_survivalSet_iff A n omega).1 hs 0 (Nat.zero_le n)
  have hzero := homTrajMeasure_time_zero_general (Measure.dirac x) P
  have hbad : homTrajMeasure (Measure.dirac x) P {omega : ℕ → Z | omega 0 ∉ A} = 0 := by
    have hm := congrArg (fun ν : Measure Z => ν Aᶜ) hzero
    rw [Measure.map_apply (measurable_pi_apply 0) hA.compl] at hm
    rw [Measure.dirac_apply' x hA.compl] at hm
    change homTrajMeasure (Measure.dirac x) P
      ((fun omega : ℕ → Z => omega 0) ⁻¹' Aᶜ) = 0
    simpa [Set.indicator, hx] using hm
  exact measure_mono_null hsubset hbad

/-- Kernels that agree at every state outside the target have exactly the same
finite survival probabilities, hence the same finite hitting distribution. -/
theorem survivalProb_eq_of_eq_outside
    (P Q : Kernel Z Z) [IsMarkovKernel P] [IsMarkovKernel Q]
    (A : Set Z) (hA : MeasurableSet A)
    (hout : ∀ z, z ∉ A → P z = Q z) :
    ∀ (n : ℕ) (z : Z), survivalProb P z A n = survivalProb Q z A n := by
  intro n
  induction n with
  | zero =>
      intro z
      by_cases hz : z ∈ A
      · rw [survivalProb_eq_zero_of_mem P z A hA hz 0,
            survivalProb_eq_zero_of_mem Q z A hA hz 0]
      · rw [survivalProb_eq_homTrajMeasure_apply P z A hA 0,
            survivalProb_eq_homTrajMeasure_apply Q z A hA 0]
        have hP := homTrajMeasure_time_zero_general (Measure.dirac z) P
        have hQ := homTrajMeasure_time_zero_general (Measure.dirac z) Q
        have hS : MeasurableSet (survivalSet A 0) := measurableSet_survivalSet hA 0
        have hp := congrArg (fun μ : Measure Z => μ Aᶜ) hP
        have hq := congrArg (fun μ : Measure Z => μ Aᶜ) hQ
        rw [Measure.map_apply (measurable_pi_apply 0) hA.compl] at hp hq
        have hevent : survivalSet A 0 = (fun omega : ℕ → Z => omega 0) ⁻¹' Aᶜ := by
          ext omega
          simp [mem_survivalSet_zero_iff]
        rw [hevent, ← Measure.map_apply (measurable_pi_apply 0) hA.compl,
          ← Measure.map_apply (measurable_pi_apply 0) hA.compl, hP, hQ]
  | succ n ih =>
      intro z
      by_cases hz : z ∈ A
      · rw [survivalProb_eq_zero_of_mem P z A hA hz (n + 1),
            survivalProb_eq_zero_of_mem Q z A hA hz (n + 1)]
      · rw [survivalProb_succ_eq_lintegral P z A hA hz n,
            survivalProb_succ_eq_lintegral Q z A hA hz n,
            hout z hz]
        apply lintegral_congr
        intro y
        exact ih y


variable {X : Type uX} {A : Type uA}
variable [Fintype X] [Fintype A]
variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace A] [MeasurableSingletonClass A]

private theorem fixedPolicyAugmented_absorbed_of_current_not_mem
    (P : X → A → PMF X) (K : Set X) (n : ℕ)
    (pi : Kernel (HistoryFiber X A n) A) [IsMarkovKernel pi]
    (h : HistoryFiber X A n) (hx : currentFiber n h ∉ K) :
    fixedPolicyAugmented n pi (pmfControlledKernel (absorbedRepairPMF P K)) h =
      fixedPolicyAugmented n pi (pmfControlledKernel P) h := by
  let etaAbs : Kernel (HistoryFiber X A n × (HistoryFiber X A n × A)) X :=
    (controlledNext n (pmfControlledKernel (absorbedRepairPMF P K))).comap Prod.snd measurable_snd
  let etaOrig : Kernel (HistoryFiber X A n × (HistoryFiber X A n × A)) X :=
    (controlledNext n (pmfControlledKernel P)).comap Prod.snd measurable_snd
  let kappa : Kernel (HistoryFiber X A n) (HistoryFiber X A n × A) := Kernel.id ×ₖ pi
  have hprod : kappa h = (Measure.dirac h).prod (pi h) := by
    simp [kappa, Kernel.prod_apply, Kernel.id_apply]
  have hcomp :
      (kappa ⊗ₖ etaAbs) h = (kappa ⊗ₖ etaOrig) h := by
    rw [Kernel.compProd_apply_eq_compProd_sectR,
        Kernel.compProd_apply_eq_compProd_sectR]
    rw [hprod, Measure.dirac_prod]
    ext U hU
    rw [Measure.compProd_apply hU, Measure.compProd_apply hU]
    let fAbs : (HistoryFiber X A n × A) → ℝ≥0∞ := fun b =>
      (Kernel.sectR etaAbs h b) (Prod.mk b ⁻¹' U)
    let fOrig : (HistoryFiber X A n × A) → ℝ≥0∞ := fun b =>
      (Kernel.sectR etaOrig h b) (Prod.mk b ⁻¹' U)
    have hfAbs : Measurable fAbs := Kernel.measurable_kernel_prodMk_left hU
    have hfOrig : Measurable fOrig := Kernel.measurable_kernel_prodMk_left hU
    rw [MeasureTheory.lintegral_map hfAbs measurable_prodMk_left,
        MeasureTheory.lintegral_map hfOrig measurable_prodMk_left]
    apply lintegral_congr
    intro a
    unfold fAbs fOrig
    rw [Kernel.sectR_apply, Kernel.sectR_apply]
    unfold etaAbs etaOrig
    rw [Kernel.comap_apply, Kernel.comap_apply]
    have hnext := controlledNext_absorbedRepair_of_current_not_mem P K n h hx a
    exact congrArg (fun mu : Measure X => mu (Prod.mk (h, a) ⁻¹' U)) hnext
  unfold fixedPolicyAugmented
  rw [Kernel.map_apply _ (measurable_advance_fixed n) h,
      Kernel.map_apply _ (measurable_advance_fixed n) h]
  dsimp [kappa, etaAbs, etaOrig] at hcomp
  exact congrArg
    (Measure.map (fun p : (HistoryFiber X A n × A) × X =>
      Carrier.advance (⟨n, p.1.1⟩ : Carrier X A) p.1.2 p.2)) hcomp



/-- Complete-history target induced by the physical repair target. -/
def historyRepairTarget (K : Set X) : Set (Carrier X A) :=
  Carrier.current ⁻¹' K

theorem measurableSet_historyRepairTarget (K : Set X) :
    MeasurableSet (historyRepairTarget (A := A) K) :=
  (Set.toFinite K).measurableSet.preimage measurable_current

/-- At every history whose current physical state is outside `K`, replacing the
controlled PMF by its `K`-absorbed version leaves the entire one-step complete-
history transition measure unchanged. -/
theorem historyKernel_absorbed_of_current_not_mem
    (P : X → A → PMF X) (K : Set X)
    (pi : CausalPolicy X A) [∀ n, IsMarkovKernel (pi n)]
    (z : Carrier X A) (hz : z ∉ historyRepairTarget (A := A) K) :
    historyKernel (pmfControlledKernel (absorbedRepairPMF P K)) pi z =
      historyKernel (pmfControlledKernel P) pi z := by
  rcases z with ⟨n, h⟩
  change
    fixedPolicyAugmented n (pi n) (pmfControlledKernel (absorbedRepairPMF P K)) h =
      fixedPolicyAugmented n (pi n) (pmfControlledKernel P) h
  apply fixedPolicyAugmented_absorbed_of_current_not_mem P K n (pi n) h
  exact hz

/-- Dirac physical initialization is exactly Dirac initialization at the
canonical singleton complete history. -/
theorem initialHistoryLaw_dirac_eq
    (x : X) :
    initialHistoryLaw (A := A) (Measure.dirac x) =
      Measure.dirac (Carrier.singleton (A := A) x) := by
  unfold initialHistoryLaw
  rw [Measure.map_dirac' (measurable_singleton (X := X) (A := A))]

/-- The complete-history path law from a deterministic physical start is the
homogeneous path law of `historyKernel` from the singleton history. -/
theorem historyPathLaw_dirac_eq_homTrajMeasure
    (Kc : Kernel (X × A) X) [IsMarkovKernel Kc]
    (pi : CausalPolicy X A) [∀ n, IsMarkovKernel (pi n)] (x : X) :
    historyPathLaw (Measure.dirac x) Kc pi =
      homTrajMeasure (Measure.dirac (Carrier.singleton (A := A) x))
        (historyKernel Kc pi) := by
  unfold historyPathLaw
  rw [initialHistoryLaw_dirac_eq (A := A) x]
  rfl

/-- Finite complete-history survival probability packaged with the Markov
witness carried by an admissible causal policy. -/
noncomputable def causalHistorySurvivalProb
    (P : X → A → PMF X) (K : Set X) (x : X)
    (pi : AdmissibleCausalRepairPolicy X A) (n : ℕ) : ℝ≥0∞ := by
  letI : ∀ m, IsMarkovKernel (pi.policy m) := pi.markov
  exact survivalProb
    (historyKernel (pmfControlledKernel P) pi.policy)
    (Carrier.singleton (A := A) x)
    (historyRepairTarget (A := A) K) n

/-- Physical finite survival mass is exactly the homogeneous complete-history
survival probability for the induced history target. -/
theorem causalRepairPathLaw_survival_eq_historySurvivalProb
    (P : X → A → PMF X) (K : Set X) (x : X)
    (pi : AdmissibleCausalRepairPolicy X A) (n : ℕ) :
    causalRepairPathLaw P x pi (survivalSet K n) =
      causalHistorySurvivalProb P K x pi n := by
  letI : ∀ m, IsMarkovKernel (pi.policy m) := pi.markov
  have hK : MeasurableSet K := (Set.toFinite K).measurableSet
  have htarget : MeasurableSet (historyRepairTarget (A := A) K) :=
    measurableSet_historyRepairTarget (A := A) K
  have hpre :
      statePathReadout ⁻¹' survivalSet K n =
        survivalSet (historyRepairTarget (A := A) K) n := by
    ext omega
    change statePathReadout omega ∈ survivalSet K n ↔
      omega ∈ survivalSet (historyRepairTarget (A := A) K) n
    rw [mem_survivalSet_iff, mem_survivalSet_iff]
    rfl
  unfold causalRepairPathLaw reflexivePathLaw
  rw [Measure.map_apply measurable_statePathReadout
    (measurableSet_survivalSet hK n)]
  rw [hpre]
  rw [historyPathLaw_dirac_eq_homTrajMeasure
    (pmfControlledKernel P) pi.policy x]
  unfold causalHistorySurvivalProb
  symm
  exact survivalProb_eq_homTrajMeasure_apply
    (historyKernel (pmfControlledKernel P) pi.policy)
    (Carrier.singleton (A := A) x)
    (historyRepairTarget (A := A) K) htarget n

/-- **GCR1 exact finite first-hitting semantics.**  For every admissible
complete-history causal policy, target absorption preserves every finite
survival probability of the exact physical Ionescu--Tulcea law. -/
theorem causalRepairPathLaw_absorbed_survival_eq
    (P : X → A → PMF X) (K : Set X) (x : X)
    (pi : AdmissibleCausalRepairPolicy X A) (n : ℕ) :
    causalRepairPathLaw (absorbedRepairPMF P K) x pi (survivalSet K n) =
      causalRepairPathLaw P x pi (survivalSet K n) := by
  letI : ∀ m, IsMarkovKernel (pi.policy m) := pi.markov
  rw [causalRepairPathLaw_survival_eq_historySurvivalProb
        (absorbedRepairPMF P K) K x pi n,
      causalRepairPathLaw_survival_eq_historySurvivalProb P K x pi n]
  unfold causalHistorySurvivalProb
  exact survivalProb_eq_of_eq_outside
    (historyKernel (pmfControlledKernel (absorbedRepairPMF P K)) pi.policy)
    (historyKernel (pmfControlledKernel P) pi.policy)
    (historyRepairTarget (A := A) K)
    (measurableSet_historyRepairTarget (A := A) K)
    (fun z hz => historyKernel_absorbed_of_current_not_mem P K pi.policy z hz)
    n (Carrier.singleton (A := A) x)

/-- Paths that never reach `K`. -/
def neverHitSet (K : Set X) : Set (ℕ → X) :=
  {omega | ∀ n : ℕ, omega n ∉ K}

theorem neverHitSet_eq_iInter_survivalSet (K : Set X) :
    neverHitSet K = ⋂ n : ℕ, survivalSet K n := by
  ext omega
  constructor
  · intro h
    rw [Set.mem_iInter]
    intro n
    exact (mem_survivalSet_iff K n omega).2 fun k hk => h k
  · intro h n
    have hn := Set.mem_iInter.mp h n
    exact (mem_survivalSet_iff K n omega).1 hn n le_rfl

theorem antitone_survivalSet (K : Set X) :
    Antitone (survivalSet K) := by
  intro n m hnm omega hm
  apply (mem_survivalSet_iff K n omega).2
  intro k hk
  exact (mem_survivalSet_iff K m omega).1 hm k (hk.trans hnm)

private theorem neverHit_measure_eq_of_survival_eq
    (K : Set X) (hK : MeasurableSet K)
    (mu nu : Measure (ℕ → X))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hEq : ∀ n, mu (survivalSet K n) = nu (survivalSet K n)) :
    mu (neverHitSet K) = nu (neverHitSet K) := by
  rw [neverHitSet_eq_iInter_survivalSet,
    (antitone_survivalSet K).measure_iInter
      (fun n => (measurableSet_survivalSet hK n).nullMeasurableSet)
      ⟨0, measure_ne_top _ _⟩,
    (antitone_survivalSet K).measure_iInter
      (fun n => (measurableSet_survivalSet hK n).nullMeasurableSet)
      ⟨0, measure_ne_top _ _⟩]
  simp_rw [hEq]

private theorem ae_eventually_hit_iff_neverHit_measure_zero
    (K : Set X) (mu : Measure (ℕ → X)) :
    (∀ᵐ omega ∂mu, ∃ n : ℕ, omega n ∈ K) ↔ mu (neverHitSet K) = 0 := by
  rw [MeasureTheory.ae_iff]
  have hset : {omega : ℕ → X | ¬ ∃ n : ℕ, omega n ∈ K} = neverHitSet K := by
    ext omega
    simp [neverHitSet]
  rw [hset]

/-- **GCR1 almost-sure first-hitting invariance.**  Absorbing the target does
not change whether an arbitrary admissible causal policy reaches `K` almost
surely under its exact physical path law. -/
theorem causalRepairPathLaw_absorbed_eventually_hits_iff
    (P : X → A → PMF X) (K : Set X) (x : X)
    (pi : AdmissibleCausalRepairPolicy X A) :
    (∀ᵐ omega ∂causalRepairPathLaw (absorbedRepairPMF P K) x pi,
        ∃ n : ℕ, omega n ∈ K) ↔
      (∀ᵐ omega ∂causalRepairPathLaw P x pi,
        ∃ n : ℕ, omega n ∈ K) := by
  let mu := causalRepairPathLaw (absorbedRepairPMF P K) x pi
  let nu := causalRepairPathLaw P x pi
  letI : IsProbabilityMeasure mu := by
    dsimp [mu, causalRepairPathLaw]
    infer_instance
  letI : IsProbabilityMeasure nu := by
    dsimp [nu, causalRepairPathLaw]
    infer_instance
  have hK : MeasurableSet K := (Set.toFinite K).measurableSet
  have hEq : ∀ n, mu (survivalSet K n) = nu (survivalSet K n) := by
    intro n
    exact causalRepairPathLaw_absorbed_survival_eq P K x pi n
  have hNever : mu (neverHitSet K) = nu (neverHitSet K) :=
    neverHit_measure_eq_of_survival_eq K hK mu nu hEq
  rw [ae_eventually_hit_iff_neverHit_measure_zero K mu,
      ae_eventually_hit_iff_neverHit_measure_zero K nu,
      hNever]

end
end UEOT.V3.Compression.Objecthood
