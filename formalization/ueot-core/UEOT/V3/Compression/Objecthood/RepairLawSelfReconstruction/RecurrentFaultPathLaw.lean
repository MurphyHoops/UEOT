import UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction.SafeJointPathLaw
import UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction.TripleRedundancy

/-!
# RLSR-T9 — recurrent fault-process path law

T2 proved one-step masking whenever a damaged representation still decodes to
the intended repair program.  This module lifts that fact to an arbitrary
state-dependent stochastic fault process applied before every safe transition.

The fault process may arbitrarily corrupt the stored controller and program
representation.  It must leave physical state unchanged and remain inside the
codec fibre of the intended program.  Under exactly that envelope, fault then
safe reconstruction is path-law equivalent to the no-fault reconstructed
program dynamics.
-/

namespace UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction

open MeasureTheory ProbabilityTheory
open UEOT.V3.DynamicsKernel
open UEOT.V3.ViabilityTrajectory
open scoped ProbabilityTheory

universe uX uA uP uR

noncomputable section

variable {X : Type uX} {A : Type uA}
variable {Program : Type uP} {Representation : Type uR}
variable [Fintype X] [Fintype A]
variable [MeasurableSpace X] [MeasurableSingletonClass X]

/-- A stochastic pre-step fault stays within one correctable program fibre and
cannot directly move physical state.  Controller corruption is unrestricted. -/
structure RepairFaultEnvelope
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (r : Program)
    (F : CanonicalRepairCarrier T codec r →
      PMF (RepairOrganizationState X A Representation)) : Prop where
  physical_preserved :
    ∀ s d, d ∈ (F s).support → d.physical = s.1.physical
  decode_preserved :
    ∀ s d, d ∈ (F s).support → codec.decode d.repairProgram = r

/-- One macro-step: first sample an exogenous organizational fault, then apply
the repair-before-action semantics and return to the canonical recovered fibre. -/
noncomputable def faultThenSafeRecoveredPMF
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (P : X → A → PMF X) (r : Program)
    (F : CanonicalRepairCarrier T codec r →
      PMF (RepairOrganizationState X A Representation))
    (s : CanonicalRepairCarrier T codec r) :
    PMF (CanonicalRepairCarrier T codec r) :=
  (F s).bindOnSupport fun d _ =>
    (P d.physical
      (T.execute (codec.decode d.repairProgram) d.physical)).map
        (canonicalRepairCarrierEquiv T codec r)

omit [Fintype X] [Fintype A] [MeasurableSpace X] [MeasurableSingletonClass X] in
/-- Every admissible fault branch induces exactly the same repaired physical
step, so the stochastic fault mixture cancels completely. -/
theorem faultThenSafeRecoveredPMF_eq_recoveredSafePMF
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (P : X → A → PMF X) (r : Program)
    (F : CanonicalRepairCarrier T codec r →
      PMF (RepairOrganizationState X A Representation))
    (hF : RepairFaultEnvelope T codec r F)
    (s : CanonicalRepairCarrier T codec r) :
    faultThenSafeRecoveredPMF T codec P r F s =
      recoveredSafePMF T codec P r s := by
  unfold faultThenSafeRecoveredPMF
  have hbranch :
      (fun d (hd : d ∈ (F s).support) =>
        (P d.physical
          (T.execute (codec.decode d.repairProgram) d.physical)).map
            (canonicalRepairCarrierEquiv T codec r)) =
      (fun _ (_ : _ ∈ (F s).support) =>
        recoveredSafePMF T codec P r s) := by
    funext d hd
    have hp := hF.physical_preserved s d hd
    have hr := hF.decode_preserved s d hd
    unfold recoveredSafePMF
    rw [hr, hp]
  rw [hbranch]
  rw [PMF.bindOnSupport_eq_bind]
  simp

/-- Markov kernel of recurrent organizational fault followed by safe recovery. -/
noncomputable def recurrentFaultSafeKernel
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (P : X → A → PMF X) (r : Program)
    (F : CanonicalRepairCarrier T codec r →
      PMF (RepairOrganizationState X A Representation)) :
    Kernel (CanonicalRepairCarrier T codec r)
      (CanonicalRepairCarrier T codec r) :=
  Kernel.ofFunOfCountable fun s =>
    (faultThenSafeRecoveredPMF T codec P r F s).toMeasure

instance recurrentFaultSafeKernel_isMarkov
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (P : X → A → PMF X) (r : Program)
    (F : CanonicalRepairCarrier T codec r →
      PMF (RepairOrganizationState X A Representation)) :
    IsMarkovKernel (recurrentFaultSafeKernel T codec P r F) := by
  unfold recurrentFaultSafeKernel
  constructor
  intro s
  change IsProbabilityMeasure
    ((faultThenSafeRecoveredPMF T codec P r F s).toMeasure)
  infer_instance

omit [Fintype A] [MeasurableSpace X] [MeasurableSingletonClass X] in
/-- At macro-step scale, recurrent admissible faults are exactly invisible. -/
theorem recurrentFaultSafeKernel_eq_recoveredSafeKernel
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (P : X → A → PMF X) (r : Program)
    (F : CanonicalRepairCarrier T codec r →
      PMF (RepairOrganizationState X A Representation))
    (hF : RepairFaultEnvelope T codec r F) :
    recurrentFaultSafeKernel T codec P r F =
      recoveredSafeKernel T codec P r := by
  ext s B hB
  change (faultThenSafeRecoveredPMF T codec P r F s).toMeasure B =
    (recoveredSafePMF T codec P r s).toMeasure B
  rw [faultThenSafeRecoveredPMF_eq_recoveredSafePMF T codec P r F hF s]

omit [Fintype A] in
/-- The recurrent-fault macro kernel strongly lumps to the intended physical
stationary kernel. -/
theorem recurrentFaultSafeKernel_strongLumpability
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (P : X → A → PMF X) (r : Program)
    (F : CanonicalRepairCarrier T codec r →
      PMF (RepairOrganizationState X A Representation))
    (hF : RepairFaultEnvelope T codec r F) :
    StrongLumpability
      (recurrentFaultSafeKernel T codec P r F)
      (stationaryKernel P (T.execute r))
      (canonicalRepairPhysicalProjection T codec r)
      (measurable_canonicalRepairPhysicalProjection T codec r) := by
  rw [recurrentFaultSafeKernel_eq_recoveredSafeKernel T codec P r F hF]
  exact recoveredSafeKernel_strongLumpability T codec P r

/-- **Recurrent-fault path-law theorem.**  Projecting the entire trajectory of
repeated fault -> safe-reconstruction cycles to physical state gives exactly the
same Ionescu--Tulcea law as running the reconstructed program with no such
organizational faults. -/
theorem recurrentFaultSafeKernel_pathLaw_projection
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (P : X → A → PMF X) (r : Program)
    (F : CanonicalRepairCarrier T codec r →
      PMF (RepairOrganizationState X A Representation))
    (hF : RepairFaultEnvelope T codec r F)
    (x : X) :
    (homTrajMeasure
        (Measure.dirac ((canonicalRepairCarrierEquiv T codec r) x))
        (recurrentFaultSafeKernel T codec P r F)).map
      (mapPath (canonicalRepairPhysicalProjection T codec r)) =
      homTrajMeasure (Measure.dirac x)
        (stationaryKernel P (T.execute r)) := by
  have h := homTrajMeasure_path_naturality
    (Measure.dirac ((canonicalRepairCarrierEquiv T codec r) x))
    (recurrentFaultSafeKernel T codec P r F)
    (stationaryKernel P (T.execute r))
    (canonicalRepairPhysicalProjection T codec r)
    (measurable_canonicalRepairPhysicalProjection T codec r)
    (recurrentFaultSafeKernel_strongLumpability T codec P r F hF)
  have hdirac :
      (Measure.dirac ((canonicalRepairCarrierEquiv T codec r) x)).map
        (canonicalRepairPhysicalProjection T codec r) = Measure.dirac x := by
    rw [Measure.map_dirac'
      (measurable_canonicalRepairPhysicalProjection T codec r)]
    rfl
  rw [hdirac] at h
  exact h

section TripleInstance

variable [DecidableEq Program]

/-- A concrete state-dependent single-replica fault process.  At every cycle it
may choose a new damaged replica, bad program value, and arbitrary controller. -/
noncomputable def tripleSingleReplicaFaultPMF
    (T : TrustedRepairSubstrate Program X A)
    (r : Program)
    (bad : CanonicalRepairCarrier T
      (tripleRepairCodec (Program := Program)) r → Program)
    (index : CanonicalRepairCarrier T
      (tripleRepairCodec (Program := Program)) r → Fin 3)
    (controllerFault : CanonicalRepairCarrier T
      (tripleRepairCodec (Program := Program)) r → (X → A))
    (s : CanonicalRepairCarrier T
      (tripleRepairCodec (Program := Program)) r) :
    PMF (RepairOrganizationState X A (TripleProgramRepresentation Program)) :=
  PMF.pure
    { physical := s.1.physical
      controller := controllerFault s
      repairProgram := replaceProgramReplica (index s) (bad s)
        (tripleProgramEncode r) }

omit [Fintype X] [Fintype A] [MeasurableSpace X] [MeasurableSingletonClass X] in
/-- The concrete recurrent one-replica process satisfies the generic fault
envelope for arbitrary state-dependent bad values/locations/controllers. -/
theorem tripleSingleReplicaFaultPMF_envelope
    (T : TrustedRepairSubstrate Program X A)
    (r : Program)
    (bad : CanonicalRepairCarrier T
      (tripleRepairCodec (Program := Program)) r → Program)
    (index : CanonicalRepairCarrier T
      (tripleRepairCodec (Program := Program)) r → Fin 3)
    (controllerFault : CanonicalRepairCarrier T
      (tripleRepairCodec (Program := Program)) r → (X → A)) :
    RepairFaultEnvelope T (tripleRepairCodec (Program := Program)) r
      (tripleSingleReplicaFaultPMF T r bad index controllerFault) := by
  constructor
  · intro s d hd
    have heq : d =
        { physical := s.1.physical
          controller := controllerFault s
          repairProgram := replaceProgramReplica (index s) (bad s)
            (tripleProgramEncode r) } := by
      simpa [tripleSingleReplicaFaultPMF, PMF.mem_support_iff] using hd
    subst d
    rfl
  · intro s d hd
    have heq : d =
        { physical := s.1.physical
          controller := controllerFault s
          repairProgram := replaceProgramReplica (index s) (bad s)
            (tripleProgramEncode r) } := by
      simpa [tripleSingleReplicaFaultPMF, PMF.mem_support_iff] using hd
    subst d
    exact tripleProgramDecode_replace_encode r (bad s) (index s)

end TripleInstance

end
end UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
