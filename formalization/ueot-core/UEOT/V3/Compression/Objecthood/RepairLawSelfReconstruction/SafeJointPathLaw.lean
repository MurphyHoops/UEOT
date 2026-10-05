import UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction.TightenedSameParentRestoration
import UEOT.V3.DynamicsKernel

namespace UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction

open MeasureTheory ProbabilityTheory
open UEOT.V3.DynamicsKernel
open UEOT.V3.ViabilityTrajectory
open scoped ProbabilityTheory

universe uX uA uP uR

noncomputable section

variable {X : Type uX} {A : Type uA} {Program : Type uP} {Representation : Type uR}
variable [Fintype X] [Fintype A]
variable [MeasurableSpace X] [MeasurableSingletonClass X]

/-- Canonical recovered manifold for one fixed internal program. -/
abbrev CanonicalRepairCarrier
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (r : Program) :=
  {s : RepairOrganizationState X A Representation //
    ∃ x : X, s = canonicalRepairOrganizationState T codec r x}

/-- The recovered manifold is canonically equivalent to the physical state space. -/
def canonicalRepairCarrierEquiv
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (r : Program) :
    X ≃ CanonicalRepairCarrier T codec r where
  toFun x := ⟨canonicalRepairOrganizationState T codec r x, ⟨x, rfl⟩⟩
  invFun s := s.1.physical
  left_inv x := rfl
  right_inv s := by
    rcases s with ⟨s, x, rfl⟩
    rfl

instance canonicalRepairCarrierMeasurableSpace
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (r : Program) :
    MeasurableSpace (CanonicalRepairCarrier T codec r) := ⊤

instance canonicalRepairCarrierDiscrete
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (r : Program) :
    DiscreteMeasurableSpace (CanonicalRepairCarrier T codec r) := inferInstance

instance canonicalRepairCarrierCountable
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (r : Program) :
    Countable (CanonicalRepairCarrier T codec r) :=
  Countable.of_equiv X (canonicalRepairCarrierEquiv T codec r)

/-- PMF-level recovered transition on the canonical manifold. -/
noncomputable def recoveredSafePMF
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (P : X → A → PMF X) (r : Program)
    (s : CanonicalRepairCarrier T codec r) :
    PMF (CanonicalRepairCarrier T codec r) :=
  (P s.1.physical (T.execute r s.1.physical)).map
    (canonicalRepairCarrierEquiv T codec r)

omit [Fintype X] [Fintype A] [MeasurableSpace X] [MeasurableSingletonClass X] in
/-- Forgetting the subtype proof turns one recovered-manifold step into exactly
the existing mode-free `safeRepairKernel` step on the underlying canonical
organization state. -/
theorem recoveredSafePMF_map_val_eq_safeRepairKernel
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (P : X → A → PMF X) (r : Program)
    (s : CanonicalRepairCarrier T codec r) :
    (recoveredSafePMF T codec P r s).map Subtype.val =
      safeRepairKernel T codec P s.1 := by
  rcases s with ⟨s, ⟨x, hx⟩⟩
  subst s
  rw [safeRepairKernel_canonical]
  unfold recoveredSafePMF
  rw [PMF.map_comp]
  change PMF.map (canonicalRepairOrganizationState T codec r)
      (P x (T.execute r x)) =
    PMF.map (canonicalRepairOrganizationState T codec r)
      (P x (T.execute r x))
  rfl

/-- Markov kernel on the canonical recovered manifold.  Its one-step law is the
safe mode-free physical transition lifted back through the canonical embedding. -/
noncomputable def recoveredSafeKernel
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (P : X → A → PMF X) (r : Program) :
    Kernel (CanonicalRepairCarrier T codec r) (CanonicalRepairCarrier T codec r) :=
  Kernel.ofFunOfCountable fun s =>
    (recoveredSafePMF T codec P r s).toMeasure

instance recoveredSafeKernel_isMarkov
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (P : X → A → PMF X) (r : Program) :
    IsMarkovKernel (recoveredSafeKernel T codec P r) := by
  unfold recoveredSafeKernel recoveredSafePMF
  constructor
  intro s
  change IsProbabilityMeasure
    (((P s.1.physical (T.execute r s.1.physical)).map
      (canonicalRepairCarrierEquiv T codec r)).toMeasure)
  infer_instance

/-- Physical projection from the canonical recovered manifold. -/
def canonicalRepairPhysicalProjection
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (r : Program) : CanonicalRepairCarrier T codec r → X :=
  fun s => s.1.physical

omit [Fintype X] [Fintype A] [MeasurableSingletonClass X] in
@[fun_prop] theorem measurable_canonicalRepairPhysicalProjection
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (r : Program) :
    Measurable (canonicalRepairPhysicalProjection T codec r) := by
  fun_prop

omit [Fintype A] in
/-- The canonical recovered kernel strongly lumps exactly to the reconstructed
program's physical stationary kernel. -/
theorem recoveredSafeKernel_strongLumpability
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (P : X → A → PMF X) (r : Program) :
    StrongLumpability
      (recoveredSafeKernel T codec P r)
      (stationaryKernel P (T.execute r))
      (canonicalRepairPhysicalProjection T codec r)
      (measurable_canonicalRepairPhysicalProjection T codec r) := by
  rw [strongLumpability_iff_apply]
  intro s
  rcases s with ⟨s, ⟨x, hx⟩⟩
  subst s
  change Measure.map (canonicalRepairPhysicalProjection T codec r)
      (recoveredSafePMF T codec P r
        ((canonicalRepairCarrierEquiv T codec r) x)).toMeasure =
    (P x (T.execute r x)).toMeasure
  unfold recoveredSafePMF
  change Measure.map (canonicalRepairPhysicalProjection T codec r)
      (((P x (T.execute r x)).map
        (canonicalRepairCarrierEquiv T codec r)).toMeasure) =
    (P x (T.execute r x)).toMeasure
  rw [PMF.toMeasure_map
    (canonicalRepairPhysicalProjection T codec r)
    ((P x (T.execute r x)).map (canonicalRepairCarrierEquiv T codec r))
    (measurable_canonicalRepairPhysicalProjection T codec r)]
  rw [PMF.toMeasure_inj]
  rw [PMF.map_comp]
  have hcomp :
      canonicalRepairPhysicalProjection T codec r ∘
        (canonicalRepairCarrierEquiv T codec r) = id := by
    funext y
    rfl
  rw [hcomp, PMF.map_id]

/-- **Full recovered joint path-law theorem.**  Projecting the complete
Ionescu--Tulcea trajectory of the safe recovered organization to physical state
is exactly the reconstructed program's physical Markov trajectory. -/
theorem recoveredSafeKernel_pathLaw_projection
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (P : X → A → PMF X) (r : Program) (x : X) :
    (homTrajMeasure
        (Measure.dirac ((canonicalRepairCarrierEquiv T codec r) x))
        (recoveredSafeKernel T codec P r)).map
      (mapPath (canonicalRepairPhysicalProjection T codec r)) =
      homTrajMeasure (Measure.dirac x)
        (stationaryKernel P (T.execute r)) := by
  have h := homTrajMeasure_path_naturality
    (Measure.dirac ((canonicalRepairCarrierEquiv T codec r) x))
    (recoveredSafeKernel T codec P r)
    (stationaryKernel P (T.execute r))
    (canonicalRepairPhysicalProjection T codec r)
    (measurable_canonicalRepairPhysicalProjection T codec r)
    (recoveredSafeKernel_strongLumpability T codec P r)
  have hdirac :
      (Measure.dirac ((canonicalRepairCarrierEquiv T codec r) x)).map
        (canonicalRepairPhysicalProjection T codec r) = Measure.dirac x := by
    rw [Measure.map_dirac' (measurable_canonicalRepairPhysicalProjection T codec r)]
    rfl
  rw [hdirac] at h
  exact h

end
end UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
