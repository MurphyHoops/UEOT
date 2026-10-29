import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MeasurablePredictiveSensor
import UEOT.V3.DynamicsKernel

/-!
# Actual finite joint C1 paths under the same visible belief policy

A clock and an optional last action/observation are only a record payload.
The initial payload is `Sum.inl ()`; the policy reads the clock and current visible
belief, not this payload or the hidden belief. Existing trajectory naturality
then transports every finite complete record, including its correlations.
Visible autonomy and the hidden-blind sensor remain sufficient source conditions.
The path object is the actual C1 belief/action/observation joint kernel.
A coupling with a separately sampled primitive physical/hidden trajectory and
its filter is a further source bridge, not established by this transport.
No minimal-image, history-adaptive-policy or infinite-path claim is made here.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MeasurablePredictiveJointPath
open MeasureTheory ProbabilityTheory
open UEOT.V3.GeneralBayesPosterior
open UEOT.V3.Compression.TheoryCompletion.ScientificClosure
open MeasurablePredictiveSource MeasurablePredictiveSensor
open UEOT.V3.DynamicsKernel
open scoped ENNReal
noncomputable section

/-- Clocked posterior with the literal last action/observation, initially absent (`Sum.inl ()`). -/
abbrev RecordState (Z A W : Type*) [MeasurableSpace Z] := ℕ × (ProbabilityMeasure Z × (Unit ⊕ (A × W)))

variable {Z A W : Type*} [MeasurableSpace Z] [MeasurableSpace A] [MeasurableSpace W]

/-- Any time-indexed family of measurable Markov policies is jointly measurable,
because time is discrete. It receives only the declared belief coordinate. -/
def timedPolicy (π : ℕ → Kernel (ProbabilityMeasure Z) A) :
    Kernel (ℕ × ProbabilityMeasure Z) A where
  toFun q := π q.1 q.2
  measurable' := measurable_from_prod_countable_right (fun t => (π t).measurable)

instance timedPolicy_isMarkov (π : ℕ → Kernel (ProbabilityMeasure Z) A)
    [∀ t, IsMarkovKernel (π t)] : IsMarkovKernel (timedPolicy π) where
  isProbabilityMeasure q := by change IsProbabilityMeasure (π q.1 q.2); infer_instance

private def execute {S E R : Type*} [MeasurableSpace S] [MeasurableSpace E]
    [MeasurableSpace R] (κ : Kernel S E) (f : S × E → R) (hf : Measurable f) : Kernel S R :=
  Kernel.snd (κ ⊗ₖ Kernel.deterministic f hf)

private theorem execute_apply {S E R : Type*} [MeasurableSpace S] [MeasurableSpace E]
    [MeasurableSpace R] (κ : Kernel S E) [IsMarkovKernel κ]
    (f : S × E → R) (hf : Measurable f) (x : S) :
    execute κ f hf x = (κ x).map (fun e => f (x,e)) := by
  ext s hs
  have hm : Measurable (fun e => f (x,e)) := hf.comp measurable_prodMk_left
  rw [execute, Kernel.snd_apply' _ _ hs, Kernel.compProd_apply (measurable_snd hs),
    Measure.map_apply hm hs]
  have hpre (e : E) : Prod.mk e ⁻¹' Prod.snd ⁻¹' s = s := rfl
  simp_rw [hpre, Kernel.deterministic_apply' hf _ hs]
  rw [← lintegral_indicator_one (hm hs)]
  apply lintegral_congr
  intro e
  rfl

variable [StandardBorelSpace Z] [Nonempty Z] [MeasurableSpace.CountablyGenerated W]

/-- The action and observation are sampled by the existing C1 source kernels. -/
def sampledEvent (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) W) [IsMarkovKernel O]
    (π : Kernel (ℕ × ProbabilityMeasure Z) A) [IsMarkovKernel π] :
    Kernel (RecordState Z A W) (A × W) :=
  (π.comap (fun s => (s.1,s.2.1)) (by fun_prop)) ⊗ₖ
    (c1BeliefObservationKernel P O).comap (fun sa => (sa.1.2.1,sa.2)) (by fun_prop)

instance sampledEvent_isMarkov (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) W) [IsMarkovKernel O]
    (π : Kernel (ℕ × ProbabilityMeasure Z) A) [IsMarkovKernel π] :
    IsMarkovKernel (sampledEvent P O π) := by unfold sampledEvent; infer_instance

/-- Execute the actual common posterior version and retain the sampled event. -/
def nextRecord (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) W) [IsMarkovKernel O]
    (q : RecordState Z A W × (A × W)) : RecordState Z A W :=
  (q.1.1+1, (c1ParametricPosteriorBelief P O ((q.1.2.1,q.2.1),q.2.2),Sum.inr q.2))

@[fun_prop] theorem measurable_nextRecord (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) W) [IsMarkovKernel O] : Measurable (nextRecord P O) := by
  unfold nextRecord
  fun_prop

/-- A minimal clocked recording interpreter; no independent path construction. -/
def recordKernel (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) W) [IsMarkovKernel O]
    (π : Kernel (ℕ × ProbabilityMeasure Z) A) [IsMarkovKernel π] :
    Kernel (RecordState Z A W) (RecordState Z A W) :=
  execute (sampledEvent P O π) (nextRecord P O) (measurable_nextRecord P O)

instance recordKernel_isMarkov (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) W) [IsMarkovKernel O]
    (π : Kernel (ℕ × ProbabilityMeasure Z) A) [IsMarkovKernel π] :
    IsMarkovKernel (recordKernel P O π) := by
  unfold recordKernel execute
  infer_instance

/-- Literal execution semantics: no independently chosen next belief or event. -/
theorem recordKernel_apply (P : Kernel (Z × A) Z) [IsMarkovKernel P]
    (O : Kernel (Z × A) W) [IsMarkovKernel O]
    (π : Kernel (ℕ × ProbabilityMeasure Z) A) [IsMarkovKernel π]
    (x : RecordState Z A W) :
    recordKernel P O π x = (sampledEvent P O π x).map
      (fun aw => nextRecord P O (x,aw)) :=
  execute_apply _ _ _ _

variable {Y H N : Type*} [MeasurableSpace Y] [MeasurableSpace H] [MeasurableSpace N]
variable [StandardBorelSpace Y] [StandardBorelSpace H] [Nonempty Y] [Nonempty H]

/-- Projection preserves clock and literal sampled events exactly. -/
def projectRecord (s : RecordState (Y × H) A W) : RecordState Y A W :=
  (s.1,(coordinate s.2.1,s.2.2))

omit [MeasurableSpace.CountablyGenerated W] [StandardBorelSpace Y] [StandardBorelSpace H]
  [Nonempty Y] [Nonempty H] in
@[fun_prop] theorem measurable_projectRecord : Measurable (projectRecord (Y:=Y) (H:=H) (A:=A) (W:=W)) := by
  unfold projectRecord
  fun_prop

variable (noise : Measure N) [IsProbabilityMeasure noise]
variable (visible : (Y × A) × N → Y) (hv : Measurable visible)
variable (hidden : ((Y × H) × A) × N → H) (hh : Measurable hidden)
variable (sensor : Kernel (Y × A) W) [IsMarkovKernel sensor]
variable (π : Kernel (ℕ × ProbabilityMeasure Y) A) [IsMarkovKernel π]

/-- Microscopic controller runs the same policy on the projected current belief. -/
def liftedPolicy : Kernel (ℕ × ProbabilityMeasure (Y × H)) A :=
  π.comap (fun q => (q.1,coordinate q.2)) (by fun_prop)

instance liftedPolicy_isMarkov : IsMarkovKernel (liftedPolicy (H:=H) π) := by
  unfold liftedPolicy
  infer_instance

/-- Complete one-step event transport, including action/observation correlations.
The posterior equality is needed only under its actual observation law. -/
theorem actual_joint_step (x : RecordState (Y × H) A W) :
    (recordKernel (source noise visible hv hidden hh) (liftedSensor sensor)
      (liftedPolicy π) x).map projectRecord =
    recordKernel (visibleKernel noise visible hv) sensor π (projectRecord x) := by
  classical
  have hm := measurable_nextRecord (source noise visible hv hidden hh) (liftedSensor sensor)
  have hc := measurable_nextRecord (visibleKernel noise visible hv) sensor
  have hp := measurable_projectRecord (Y:=Y) (H:=H) (A:=A) (W:=W)
  have hm0 : Measurable (fun e => nextRecord (source noise visible hv hidden hh)
      (liftedSensor sensor) (x,e)) := hm.comp measurable_prodMk_left
  have hc0 : Measurable (fun e => nextRecord (visibleKernel noise visible hv) sensor
      (projectRecord x,e)) := hc.comp measurable_prodMk_left
  rw [recordKernel, execute_apply, recordKernel, execute_apply]
  ext s hs
  rw [Measure.map_apply hp hs,
    Measure.map_apply hm0 (hp hs),
    Measure.map_apply hc0 hs]
  rw [sampledEvent, Kernel.compProd_apply (hm0 (hp hs)),
    sampledEvent, Kernel.compProd_apply (hc0 hs)]
  simp only [Kernel.comap_apply, liftedPolicy, projectRecord]
  apply lintegral_congr
  intro a
  change c1BeliefObservationKernel (source noise visible hv hidden hh) (liftedSensor sensor)
    (x.2.1,a) _ = c1BeliefObservationKernel (visibleKernel noise visible hv) sensor
    (coordinate x.2.1,a) _
  rw [show c1BeliefObservationKernel (source noise visible hv hidden hh) (liftedSensor sensor)
      (x.2.1,a) = observationLaw x.2.1.toMeasure (source noise visible hv hidden hh)
      (liftedSensor sensor) a from c1BeliefActionJoint_fst_eq_observationLaw _ _ _ _,
    show c1BeliefObservationKernel (visibleKernel noise visible hv) sensor (coordinate x.2.1,a) =
      observationLaw (coordinate x.2.1).toMeasure (visibleKernel noise visible hv) sensor a from
      c1BeliefActionJoint_fst_eq_observationLaw _ _ _ _]
  rw [← sensor_observationLaw_factors noise visible hv hidden hh sensor x.2.1 a]
  have hpost := actual_posterior_coordinate_ae noise visible hv hidden hh sensor x.2.1 a
  have hc1 : Measurable (fun e => nextRecord (visibleKernel noise visible hv) sensor
      ((x.1,(coordinate x.2.1,x.2.2)),e)) := hc0
  rw [← lintegral_indicator_one (measurable_prodMk_left (hm0 (hp hs))),
    ← lintegral_indicator_one (measurable_prodMk_left (hc1 hs))]
  apply lintegral_congr_ae
  filter_upwards [hpost] with w hw
  have heq : projectRecord (nextRecord (source noise visible hv hidden hh)
      (liftedSensor sensor) (x,(a,w))) =
      nextRecord (visibleKernel noise visible hv) sensor (projectRecord x,(a,w)) := by
    change (x.1+1,(coordinate (c1ParametricPosteriorBelief
      (source noise visible hv hidden hh) (liftedSensor sensor) ((x.2.1,a),w)),Sum.inr (a,w))) = _
    rw [hw]
    rfl
  exact congrArg (s.indicator (fun _ => (1 : ℝ≥0∞))) heq

/-- The source-derived event recorder is lumpable; this is proved, not a field. -/
theorem actual_record_lumpability :
    StrongLumpability
      (recordKernel (source noise visible hv hidden hh) (liftedSensor sensor) (liftedPolicy π))
      (recordKernel (visibleKernel noise visible hv) sensor π)
      projectRecord measurable_projectRecord := by
  rw [strongLumpability_iff_apply]
  exact actual_joint_step noise visible hv hidden hh sensor π

/-- Every finite complete record of the same policy has the projected law.
Time zero contains the registered initial belief and no fictitious event.
Taking `π = timedPolicy policies` covers every time-varying belief Markov policy. -/
theorem actual_finite_joint_path (b : ProbabilityMeasure (Y × H)) (T : ℕ) :
    ((homTrajMeasure (Measure.dirac (0,(b,Sum.inl ())))
      (recordKernel (source noise visible hv hidden hh) (liftedSensor sensor) (liftedPolicy π))).map
      (Preorder.frestrictLe T)).map (mapHistory projectRecord T) =
    (homTrajMeasure (Measure.dirac (0,(coordinate b,Sum.inl ())))
      (recordKernel (visibleKernel noise visible hv) sensor π)).map
      (Preorder.frestrictLe T) := by
  have h := homTrajMeasure_prefix_naturality
    (Measure.dirac (0,(b,Sum.inl ())))
    (recordKernel (source noise visible hv hidden hh) (liftedSensor sensor) (liftedPolicy π))
    (recordKernel (visibleKernel noise visible hv) sensor π)
    projectRecord measurable_projectRecord
    (actual_record_lumpability noise visible hv hidden hh sensor π) T
  simpa only [Measure.map_dirac' measurable_projectRecord, projectRecord] using h

/-- Downstream consumer: any measurable event of the entire finite joint record,
including action/observation correlations across times, has the same probability. -/
theorem actual_finite_record_event (b : ProbabilityMeasure (Y × H)) (T : ℕ)
    (E : Set ((i : Finset.Iic T) → RecordState Y A W)) (hE : MeasurableSet E) :
    ((homTrajMeasure (Measure.dirac (0,(b,Sum.inl ())))
      (recordKernel (source noise visible hv hidden hh) (liftedSensor sensor) (liftedPolicy π))).map
      (Preorder.frestrictLe T)) ((mapHistory projectRecord T) ⁻¹' E) =
    ((homTrajMeasure (Measure.dirac (0,(coordinate b,Sum.inl ())))
      (recordKernel (visibleKernel noise visible hv) sensor π)).map
      (Preorder.frestrictLe T)) E := by
  rw [← Measure.map_apply (measurable_mapHistory projectRecord measurable_projectRecord T) hE,
    actual_finite_joint_path noise visible hv hidden hh sensor π b T]

/-- Direct family-valued endpoint: the identical time-varying policy is used
on both sides, and receives neither the hidden belief nor past event payload. -/
theorem actual_timevarying_joint_path
    (policies : ℕ → Kernel (ProbabilityMeasure Y) A)
    [∀ t, IsMarkovKernel (policies t)] (b : ProbabilityMeasure (Y × H)) (T : ℕ) :
    ((homTrajMeasure (Measure.dirac (0,(b,Sum.inl ())))
      (recordKernel (source noise visible hv hidden hh) (liftedSensor sensor)
        (liftedPolicy (timedPolicy policies)))).map
      (Preorder.frestrictLe T)).map (mapHistory projectRecord T) =
    (homTrajMeasure (Measure.dirac (0,(coordinate b,Sum.inl ())))
      (recordKernel (visibleKernel noise visible hv) sensor (timedPolicy policies))).map
      (Preorder.frestrictLe T) :=
  actual_finite_joint_path noise visible hv hidden hh sensor (timedPolicy policies) b T

/-- Registered nonnegative costs of the complete finite record preserve their
expectation, not merely single-time posterior marginals. -/
theorem actual_finite_record_lintegral (b : ProbabilityMeasure (Y × H)) (T : ℕ)
    (F : ((i : Finset.Iic T) → RecordState Y A W) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ h, F (mapHistory projectRecord T h) ∂
      ((homTrajMeasure (Measure.dirac (0,(b,Sum.inl ())))
        (recordKernel (source noise visible hv hidden hh) (liftedSensor sensor) (liftedPolicy π))).map
        (Preorder.frestrictLe T))) =
    ∫⁻ h, F h ∂((homTrajMeasure (Measure.dirac (0,(coordinate b,Sum.inl ())))
      (recordKernel (visibleKernel noise visible hv) sensor π)).map
      (Preorder.frestrictLe T)) := by
  rw [← lintegral_map hF (measurable_mapHistory projectRecord measurable_projectRecord T),
    actual_finite_joint_path noise visible hv hidden hh sensor π b T]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MeasurablePredictiveJointPath
