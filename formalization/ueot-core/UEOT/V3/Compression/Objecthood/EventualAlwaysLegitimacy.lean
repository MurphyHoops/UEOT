import UEOT.V3.Compression.Objecthood.AutonomousSelfStabilization
import UEOT.V3.RecoveryHittingRestart

namespace UEOT.V3.Compression.Objecthood

open Set Finset MeasureTheory ProbabilityTheory
open UEOT.V3.DynamicsKernel
open UEOT.V3.ViabilityKernel
open UEOT.V3.ViabilityTrajectory
open UEOT.V3.Compression.CrossTrack
open scoped ENNReal ProbabilityTheory

universe uX
variable {X : Type uX}
variable [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]

def absorbingPrevHistoryIndex (n : ℕ) : Finset.Iic (n + 1) :=
  ⟨n, mem_Iic.mpr (Nat.le_succ n)⟩

def absorbingBadPrefix (L : Set X) (n : ℕ) : Set ((i : Finset.Iic (n + 1)) → X) :=
  {h | h (absorbingPrevHistoryIndex n) ∈ L ∧ h (lastHistoryIndex (n + 1)) ∉ L}

def absorbingBadPair (L : Set X) (n : ℕ) :
    Set (((i : Finset.Iic n) → X) × X) :=
  {p | p.1 (lastHistoryIndex n) ∈ L ∧ p.2 ∉ L}

theorem appendHistory_preimage_absorbingBadPrefix
    (L : Set X) (n : ℕ) :
    appendHistory n ⁻¹' absorbingBadPrefix L n = absorbingBadPair L n := by
  ext p
  simp [absorbingBadPrefix, absorbingBadPair, absorbingPrevHistoryIndex, appendHistory,
    IicProdIoc_def, lastHistoryIndex, MeasurableEquiv.piSingleton]

theorem absorbingSet_no_oneStep_exit
    (Q : Kernel X X) [IsMarkovKernel Q]
    (L : Set X)
    (hclosed : ∀ x ∈ L, Q x L = 1)
    (μ : Measure X) [IsProbabilityMeasure μ]
    (n : ℕ) :
    homTrajMeasure μ Q {ω | ω n ∈ L ∧ ω (n + 1) ∉ L} = 0 := by
  let μpath := homTrajMeasure μ Q
  let μn := μpath.map (Preorder.frestrictLe n)
  let Bp := absorbingBadPrefix L n
  let Bpair := absorbingBadPair L n
  have hBp : MeasurableSet Bp := (Set.toFinite Bp).measurableSet
  have hBpair : MeasurableSet Bpair := (Set.toFinite Bpair).measurableSet
  letI : IsMarkovKernel (homHistoryKernel Q n) :=
    isMarkovKernel_homHistoryKernel Q n
  have hstep := homTrajMeasure_prefix_succ μ Q n
  have hpre :
      Preorder.frestrictLe (n + 1) ⁻¹' Bp =
        {ω : ℕ → X | ω n ∈ L ∧ ω (n + 1) ∉ L} := by
    ext ω
    simp [Bp, absorbingBadPrefix, absorbingPrevHistoryIndex, lastHistoryIndex,
      Preorder.frestrictLe_apply]
  calc
    μpath {ω | ω n ∈ L ∧ ω (n + 1) ∉ L}
        = μpath (Preorder.frestrictLe (n + 1) ⁻¹' Bp) := by rw [hpre]
    _ = (μpath.map (Preorder.frestrictLe (n + 1))) Bp := by
      rw [Measure.map_apply (Preorder.measurable_frestrictLe (n + 1)) hBp]
    _ = (((μn) ⊗ₘ homHistoryKernel Q n).map (appendHistory n)) Bp := by
      rw [hstep]
    _ = ((μn) ⊗ₘ homHistoryKernel Q n) Bpair := by
      rw [Measure.map_apply (measurable_appendHistory n) hBp]
      rw [appendHistory_preimage_absorbingBadPrefix]
    _ = 0 := by
      rw [Measure.compProd_apply hBpair]
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards [] with h
      by_cases hh : h (lastHistoryIndex n) ∈ L
      · have hL : MeasurableSet L := (Set.toFinite L).measurableSet
        have hcomp : Q (h (lastHistoryIndex n)) Lᶜ = 0 :=
          (prob_compl_eq_zero_iff hL).2 (hclosed _ hh)
        have hfiber : Prod.mk h ⁻¹' Bpair = Lᶜ := by
          ext y
          simp [Bpair, absorbingBadPair, hh]
        rw [hfiber]
        unfold homHistoryKernel
        rw [Kernel.comap_apply']
        exact hcomp
      · have hfiber : Prod.mk h ⁻¹' Bpair = ∅ := by
          ext y
          simp [Bpair, absorbingBadPair, hh]
        rw [hfiber]
        simp

theorem absorbingSet_closed_steps_ae
    (Q : Kernel X X) [IsMarkovKernel Q]
    (L : Set X)
    (hclosed : ∀ x ∈ L, Q x L = 1)
    (μ : Measure X) [IsProbabilityMeasure μ] :
    ∀ᵐ ω ∂homTrajMeasure μ Q,
      ∀ n : ℕ, ω n ∈ L → ω (n + 1) ∈ L := by
  rw [ae_iff]
  have hbad : ∀ n : ℕ,
      homTrajMeasure μ Q {ω | ω n ∈ L ∧ ω (n + 1) ∉ L} = 0 :=
    absorbingSet_no_oneStep_exit Q L hclosed μ
  have hset :
      {ω : ℕ → X | ¬(∀ n : ℕ, ω n ∈ L → ω (n + 1) ∈ L)} =
        ⋃ n : ℕ, {ω | ω n ∈ L ∧ ω (n + 1) ∉ L} := by
    ext ω
    constructor
    · intro h
      change ¬(∀ n : ℕ, ω n ∈ L → ω (n + 1) ∈ L) at h
      by_contra hno
      apply h
      intro n hn
      by_contra hn1
      apply hno
      exact Set.mem_iUnion.2 ⟨n, ⟨hn, hn1⟩⟩
    · intro h
      change ¬(∀ n : ℕ, ω n ∈ L → ω (n + 1) ∈ L)
      rcases Set.mem_iUnion.1 h with ⟨n, hn⟩
      exact fun hall => hn.2 (hall n hn.1)
  rw [hset]
  exact measure_iUnion_null hbad

theorem eventually_always_of_eventually_hits_absorbing
    (Q : Kernel X X) [IsMarkovKernel Q]
    (L : Set X)
    (hclosed : ∀ x ∈ L, Q x L = 1)
    (μ : Measure X) [IsProbabilityMeasure μ]
    (hhit : ∀ᵐ ω ∂homTrajMeasure μ Q, ∃ n : ℕ, ω n ∈ L) :
    ∀ᵐ ω ∂homTrajMeasure μ Q,
      ∃ N : ℕ, ∀ m ≥ N, ω m ∈ L := by
  filter_upwards [hhit, absorbingSet_closed_steps_ae Q L hclosed μ] with ω hhitω hstep
  obtain ⟨N, hN⟩ := hhitω
  refine ⟨N, ?_⟩
  have htail : ∀ k : ℕ, ω (N + k) ∈ L := by
    intro k
    induction k with
    | zero => simpa using hN
    | succ k ih =>
        simpa [Nat.add_assoc] using hstep (N + k) ih
  intro m hm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  exact htail k



theorem autonomousRepair_eventually_always_legitimate_ae
    {X : Type uX} {A : Type*}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    (R : PhysicalRepairCertificate P K)
    {z : ConstitutiveState X A}
    (hz : z.1 ∈ R.basin) :
    ∀ᵐ omega ∂stationaryTrajMeasure
        (autonomousRepairLift P K hfix R) noExternalControl (PMF.pure z),
      ∃ N : ℕ, ∀ m ≥ N,
        omega m ∈ legitimateConstitutiveDomain P K := by
  let Q := autonomousRepairLift P K hfix R
  let L := legitimateConstitutiveDomain P K
  let KQ := stationaryKernel Q noExternalControl
  have hL : MeasurableSet L := (Set.toFinite L).measurableSet
  have hclosed : ∀ w ∈ L, KQ w L = 1 := by
    intro w hw
    change (Q w ()).toMeasure L = 1
    exact (staysIn_iff_toMeasure_eq_one _ hL).1
      (autonomousRepairLift_staysIn_legitimate P K hfix R hw)
  have hhit :
      ∀ᵐ omega ∂homTrajMeasure (PMF.pure z).toMeasure KQ,
        ∃ n : ℕ, omega n ∈ L := by
    simpa [Q, L, KQ, stationaryTrajMeasure] using
      autonomousRepair_eventually_legitimate_ae P K hfix R hz
  have hEA :=
    eventually_always_of_eventually_hits_absorbing
      KQ L hclosed (PMF.pure z).toMeasure hhit
  simpa [Q, L, KQ, stationaryTrajMeasure] using hEA

end UEOT.V3.Compression.Objecthood
