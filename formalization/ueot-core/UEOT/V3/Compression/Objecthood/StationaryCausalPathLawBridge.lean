import UEOT.V3.Compression.Objecthood.GeneralCausalRepairBoundary
import UEOT.V3.ConcreteHistoryMarkovization
import Mathlib.Probability.Kernel.Composition.KernelLemmas

namespace UEOT.V3.Compression.Objecthood
open MeasureTheory ProbabilityTheory
open UEOT.V3.FiniteHistory
open UEOT.V3.FiniteHistoryMeasurable
open UEOT.V3.ViabilityTrajectory
open UEOT.V3.ReflexiveStateAugmentation
open scoped ProbabilityTheory
universe uX uA
noncomputable section

noncomputable def stationaryCausalPolicy
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (pi : X → A) : CausalPolicy X A :=
  fun n => Kernel.deterministic
    (fun h : HistoryFiber X A n => pi (currentFiber n h))
    ((measurable_of_finite pi).comp (measurable_currentFiber n))

instance stationaryCausalPolicy_markov
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (pi : X → A) (n : ℕ) : IsMarkovKernel (stationaryCausalPolicy pi n) := by
  unfold stationaryCausalPolicy
  infer_instance

private theorem qcomap_eq_prodMkLeft
    {X : Type uX} {A : Type uA}
    [MeasurableSpace X] [MeasurableSpace A]
    (n : ℕ) (q : Kernel (HistoryFiber X A n × A) X) :
    q.comap Prod.snd measurable_snd = Kernel.prodMkLeft (HistoryFiber X A n) q := by
  ext z s hs
  simp [Kernel.comap_apply, Kernel.prodMkLeft_apply]

/-- The one-step physical marginal of the deterministic stationary causal embedding is exactly the existing stationary kernel. -/
theorem fixedPolicyAugmented_current_marginal
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (P : X → A → PMF X) (pi : X → A) (n : ℕ)
    (h : HistoryFiber X A n) :
    (fixedPolicyAugmented n (stationaryCausalPolicy pi n) (pmfControlledKernel P) h).map
        Carrier.current =
      stationaryKernel P pi (currentFiber n h) := by
  let q := controlledNext n (pmfControlledKernel P)
  let B := Kernel.id ×ₖ stationaryCausalPolicy pi n
  have hq : q.comap Prod.snd measurable_snd = Kernel.prodMkLeft (HistoryFiber X A n) q :=
    qcomap_eq_prodMkLeft n q
  have hphys :
      (fixedPolicyAugmented n (stationaryCausalPolicy pi n) (pmfControlledKernel P)).map
          Carrier.current = q ∘ₖ B := by
    unfold fixedPolicyAugmented
    rw [← Kernel.map_comp_right _ (measurable_advance_fixed n) measurable_current]
    have hcomp : Carrier.current ∘
        (fun p : (HistoryFiber X A n × A) × X =>
          Carrier.advance (⟨n, p.1.1⟩ : Carrier X A) p.1.2 p.2) = Prod.snd := by
      funext p
      exact Carrier.current_advance _ _ _
    rw [hcomp]
    rw [← Kernel.snd_eq]
    rw [hq]
    exact Kernel.snd_compProd_prodMkLeft B q
  have happly := congrArg (fun k : Kernel (HistoryFiber X A n) X => k h) hphys
  rw [← Kernel.map_apply _ measurable_current] at ⊢
  rw [happly]
  ext S hS
  rw [Kernel.comp_apply' _ _ _ hS]
  unfold B
  rw [Kernel.prod_apply]
  rw [Kernel.id_apply]
  have hpol : stationaryCausalPolicy pi n h =
      Measure.dirac (pi (currentFiber n h)) := by
    unfold stationaryCausalPolicy
    rw [Kernel.deterministic_apply]
  rw [hpol, Measure.dirac_prod_dirac]
  rw [lintegral_dirac']
  · unfold q controlledNext
    rw [Kernel.comap_apply]
    change (pmfControlledKernel P) (currentFiber n h, pi (currentFiber n h)) S = _
    rfl
  · exact (q.measurable_coe hS)


/-- A deterministic stationary policy packaged as the exact AR6 admissible complete-history causal policy. -/
noncomputable def stationaryAdmissible
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (pi : X → A) : AdmissibleCausalRepairPolicy X A where
  policy := stationaryCausalPolicy pi
  markov := fun n => stationaryCausalPolicy_markov pi n

/-- The complete-history Markovized kernel is strongly lumpable through the physical current-state readout. -/
theorem historyKernel_stationary_strongLumpability
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (P : X → A → PMF X) (pi : X → A) :
    UEOT.V3.DynamicsKernel.StrongLumpability
      (historyKernel (pmfControlledKernel P) (stationaryCausalPolicy pi))
      (stationaryKernel P pi) Carrier.current measurable_current := by
  rw [UEOT.V3.DynamicsKernel.strongLumpability_iff_apply]
  intro z
  rcases z with ⟨n, h⟩
  exact fixedPolicyAugmented_current_marginal P pi n h

theorem initialHistoryLaw_map_current_dirac
    {X : Type uX} {A : Type uA}
    [MeasurableSpace X] [MeasurableSpace A]
    (x : X) :
    (UEOT.V3.ReflexiveStatePathLaw.initialHistoryLaw (A := A) (Measure.dirac x)).map
      Carrier.current = Measure.dirac x := by
  unfold UEOT.V3.ReflexiveStatePathLaw.initialHistoryLaw
  rw [Measure.map_map measurable_current measurable_singleton]
  have hcomp :
      (Carrier.current (X := X) (A := A)) ∘
        (Carrier.singleton (X := X) (A := A)) = id := by
    funext y
    rfl
  rw [hcomp, Measure.map_id]

/-- **GCR0 path-law bridge.** The AR6 physical Ionescu--Tulcea law of a deterministic stationary causal embedding is exactly the canonical stationary trajectory law. -/
theorem stationaryCausal_pathLaw_eq_stationaryTrajMeasure
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (P : X → A → PMF X) (pi : X → A) (x : X) :
    causalRepairPathLaw P x (stationaryAdmissible pi) =
      stationaryTrajMeasure P pi (PMF.pure x) := by
  let HC := historyKernel (pmfControlledKernel P) (stationaryCausalPolicy pi)
  have hlump := historyKernel_stationary_strongLumpability P pi
  have hnat := UEOT.V3.DynamicsKernel.homTrajMeasure_path_naturality
    (UEOT.V3.ReflexiveStatePathLaw.initialHistoryLaw (A := A) (Measure.dirac x))
    HC (stationaryKernel P pi) Carrier.current measurable_current hlump
  unfold causalRepairPathLaw UEOT.V3.ReflexiveStatePathLaw.reflexivePathLaw
  change
    (UEOT.V3.ReflexiveStatePathLaw.historyPathLaw
      (Measure.dirac x) (pmfControlledKernel P) (stationaryCausalPolicy pi)).map
        UEOT.V3.ReflexiveStatePathLaw.statePathReadout = _
  have hhist :
      UEOT.V3.ReflexiveStatePathLaw.historyPathLaw
        (Measure.dirac x) (pmfControlledKernel P) (stationaryCausalPolicy pi) =
      UEOT.V3.DynamicsKernel.homTrajMeasure
        (UEOT.V3.ReflexiveStatePathLaw.initialHistoryLaw (A := A) (Measure.dirac x)) HC := by
    rfl
  rw [hhist]
  have hread :
      UEOT.V3.ReflexiveStatePathLaw.statePathReadout =
        UEOT.V3.DynamicsKernel.mapPath (Carrier.current (X := X) (A := A)) := by
    rfl
  rw [hread]
  rw [hnat]
  rw [initialHistoryLaw_map_current_dirac (A := A) x]
  unfold stationaryTrajMeasure
  rw [PMF.toMeasure_pure]


end
end UEOT.V3.Compression.Objecthood
