import UEOT.V3.Compression.TheoryCompletion.OperationalObject
import UEOT.V3.Compression.TheoryCompletion.Purpose
import UEOT.V3.Compression.TheoryCompletion.GOD
import UEOT.V3.Compression.TheoryCompletion.GOA
import UEOT.V3.Compression.TheoryCompletion.Scale
import UEOT.V3.Compression.TopologyChangingGoaSemantics

namespace UEOT.V3.Compression.TheoryCompletion

noncomputable section

open Set MeasureTheory
open UEOT.V3
open UEOT.V3.FiniteDobrushin
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.CrossTrack
open UEOT.V3.Compression.InvariantSetGaugeInvariance
open UEOT.V3.Compression.TopologyChangingGoaSemantics

/-- Collapsed response family: both candidate tokens have exactly the same
observable response under the only probe. -/
noncomputable def collapsedBoolResponseFamily :
    InteractionResponseFamily Bool Unit Unit where
  response := fun _ _ => Measure.dirac ()
  probability := by
    intro _ _
    infer_instance

/-- Formation/carrier provenance alone does not make an operational object:
one formed token can fail every object-specific interaction-delimitation test. -/
theorem formedProvenance_does_not_imply_interactionDelimitation :
    FormedProvenance (Set.univ : Set Bool) true ∧
    ¬ InteractionDelimitedAt collapsedBoolResponseFamily {()} true := by
  constructor
  · simp [FormedProvenance]
  · intro h
    have hne : false ≠ true := by decide
    rcases h (other := false) hne with ⟨probe, _hprobe, hresp⟩
    cases probe
    exact hresp rfl

/-- The canonical two-absorbing-state chain also has the right point mass as
an invariant law. -/
theorem twoStateSource_pureOne_invariant :
    pureSimplex (1 : Fin 2) ∈
      invariantLawSet twoStateSourceKernel twoStateSourceKernel_stochastic := by
  apply Subtype.ext
  funext y
  rw [step_apply, Fin.sum_univ_two]
  fin_cases y <;>
    norm_num [twoStateSourceKernel, pureSimplex, Pi.single]

/-- GOA invariant-law semantics can genuinely be non-singleton. Therefore a
universal GOA definition cannot require a unique fixed/invariant law. -/
theorem invariantGOA_can_be_nonunique :
    ∃ mu nu : stdSimplex ℝ (Fin 2),
      mu ≠ nu ∧
      mu ∈ invariantLawSet twoStateSourceKernel twoStateSourceKernel_stochastic ∧
      nu ∈ invariantLawSet twoStateSourceKernel twoStateSourceKernel_stochastic := by
  refine ⟨pureSimplex (0 : Fin 2), pureSimplex (1 : Fin 2), ?_, ?_,
    twoStateSource_pureOne_invariant⟩
  · intro h
    have h0 := congrArg Subtype.val h
    have h00 := congrFun h0 (0 : Fin 2)
    norm_num [pureSimplex, Pi.single] at h00
  · exact twoStateSource_pureZero_invariant

/-- A one-state control model with two exactly tied admissible actions. -/
noncomputable def tiedActionModel : Model Unit (fun _ => Bool) where
  transition := fun _ _ _ => 1
  reward := fun _ _ => 0
  rewardBound := 0
  discount := 1 / 2
  transition_nonneg := by
    intro _ _ _
    norm_num
  transition_sum_one := by
    intro _ _
    simp
  reward_abs_le := by
    intro _ _
    simp
  discount_pos := by
    norm_num
  discount_lt_one := by
    norm_num

theorem tiedActionModel_qValue_eq
    (v : Unit → ℝ) (a b : Bool) :
    tiedActionModel.qValue v () a =
      tiedActionModel.qValue v () b := by
  simp [Model.qValue, Model.expect, tiedActionModel]

/-- Bellman GOD semantics need not be single-valued: the same finite model can
have two distinct optimal local actions. Therefore uniqueness is an additional
certificate/domain property, not part of universal GOD semantics. -/
theorem bellmanGOD_can_be_nonunique :
    ∃ a b : Bool,
      a ≠ b ∧
      a ∈ BellmanGODCorrespondence tiedActionModel () ∧
      b ∈ BellmanGODCorrespondence tiedActionModel () := by
  refine ⟨false, true, by decide, ?_, ?_⟩
  · rw [mem_bellmanGODCorrespondence_iff]
    calc
      tiedActionModel.qValue tiedActionModel.optimalValue () false =
          tiedActionModel.qValue tiedActionModel.optimalValue ()
            (tiedActionModel.greedyAction ()) := by
              exact tiedActionModel_qValue_eq _ _ _
      _ = tiedActionModel.optimalValue () :=
        tiedActionModel.greedyAction_spec ()
  · rw [mem_bellmanGODCorrespondence_iff]
    calc
      tiedActionModel.qValue tiedActionModel.optimalValue () true =
          tiedActionModel.qValue tiedActionModel.optimalValue ()
            (tiedActionModel.greedyAction ()) := by
              exact tiedActionModel_qValue_eq _ _ _
      _ = tiedActionModel.optimalValue () :=
        tiedActionModel.greedyAction_spec ()

/-- Trivial one-state source dynamics used to separate quotient structure from
cross-scale dynamic compatibility. -/
noncomputable def unitDiracDynamics : Unit → Unit → Measure Unit :=
  fun _ _ => Measure.dirac ()

noncomputable def unitZeroDynamics : Unit → Unit → Measure Unit :=
  fun _ _ => 0

/-- A surjective quotient/state map alone does not imply even exact dynamic
intertwining. Thus generic quotient/coarse-graining data cannot be silently
upgraded to a stronger scale-dynamics or Wilsonian-RG claim. -/
theorem quotientMap_does_not_imply_dynamicIntertwining :
    IsQuotientMap (id : Unit → Unit) ∧
    ¬ ExactDynamicScaleIntertwining
      Set.univ unitDiracDynamics unitZeroDynamics id := by
  constructor
  · exact Function.surjective_id
  · intro h
    have hbad := h () (by simp) ()
    have hmass :=
      congrArg (fun mu : Measure Unit => mu Set.univ) hbad
    simp [unitDiracDynamics, unitZeroDynamics] at hmass

end

end UEOT.V3.Compression.TheoryCompletion
