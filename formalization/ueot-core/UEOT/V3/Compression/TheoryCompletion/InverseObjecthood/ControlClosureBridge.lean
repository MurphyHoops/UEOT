import UEOT.V3.Compression.TheoryCompletion.StatisticalConsistency.TerminalClosure
import UEOT.V3.Compression.TheoryCompletion.SameObjectIdentity

/-!
# P4.7 — conditional bridge from recovered object class to P3 control closure

Inverse evidence classes, control fibres and same-parent identity are three
separate equivalence layers.  P4 may consume P3 only after an explicit bridge
states that the recovered scientific object class determines the same control
encoder.  A separate bridge is required for same-parent identity.
-/

namespace UEOT.V3.Compression.TheoryCompletion.InverseObjecthood

open Filter Topology
open UEOT.V3
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.TheoryCompletion
open UEOT.V3.Compression.TheoryCompletion.StatisticalConsistency
open UEOT.V3.Compression.MovingEncoderSemanticGoaClosure

universe uCandidate uParent uX uS uA

/-- Explicit adapter saying that one recovered target object class determines
one control encoder/fibre map.  This is not derivable from evidence-class
recovery alone. -/
structure ObjectClassControlEncoderBridge
    {Candidate : Type uCandidate}
    (objectClass : Setoid Candidate)
    {X : Type uX} {S : Type uS}
    (encoder : Candidate → X → S) : Prop where
  encoder_eq_of_class : ∀ a b,
    objectClass.r a b → encoder a = encoder b

/-- Separate adapter for same-parent identity.  Keeping this distinct from the
control-encoder bridge prevents P2 identity from being silently reconstructed
from equal control data. -/
structure ObjectClassParentBridge
    {Candidate : Type uCandidate}
    (objectClass : Setoid Candidate)
    {Parent : Type uParent}
    (parent : Candidate → Parent) : Prop where
  parent_eq_of_class : ∀ a b,
    objectClass.r a b → parent a = parent b

/-- Recovered target-class membership transports to equality of control
encoders only through the declared control bridge. -/
theorem recoveredClass_controlEncoder_eq
    {Candidate : Type uCandidate}
    {objectClass : Setoid Candidate}
    {X : Type uX} {S : Type uS}
    {encoder : Candidate → X → S}
    (B : ObjectClassControlEncoderBridge objectClass encoder)
    {estimate truth : Candidate}
    (hrecovered : objectClass.r estimate truth) :
    encoder estimate = encoder truth :=
  B.encoder_eq_of_class estimate truth hrecovered

/-- Same-parent identity requires its own bridge even after object-class
recovery. -/
theorem recoveredClass_parent_eq
    {Candidate : Type uCandidate}
    {objectClass : Setoid Candidate}
    {Parent : Type uParent}
    {parent : Candidate → Parent}
    (B : ObjectClassParentBridge objectClass parent)
    {estimate truth : Candidate}
    (hrecovered : objectClass.r estimate truth) :
    parent estimate = parent truth :=
  B.parent_eq_of_class estimate truth hrecovered

/-- Transport a realized P3 estimator across literal equality of encoder maps.
No estimator theorem is invented here; this is only equality transport. -/
def transportRealizedControlEstimator
    {X : Type uX} [Fintype X]
    {S : Type uS} [Fintype S]
    {Act : Type uA} [Fintype Act] [Nonempty Act]
    {micro : Model X (fun _ => Act)}
    {C D : X → S}
    (h : D = C)
    (E : RealizedControlEstimator C micro) :
    RealizedControlEstimator D micro := by
  subst D
  exact E

/-- **Recovered object class -> exact P3 value/GOD closure.**

Once the target object class is known to determine the same control encoder,
the truth-side realized estimator transports to the recovered candidate's
encoder and P3 exactification applies there.  No action gap or GOA isolation is
needed for exact values or the set-valued Bellman-GOD correspondence. -/
theorem recoveredClass_exact_value_and_god
    {Candidate : Type uCandidate}
    {objectClass : Setoid Candidate}
    {X : Type uX} [Fintype X]
    {S : Type uS} [Fintype S]
    {Act : Type uA} [Fintype Act] [Nonempty Act]
    (encoder : Candidate → X → S)
    (B : ObjectClassControlEncoderBridge objectClass encoder)
    (estimate truth : Candidate)
    (hrecovered : objectClass.r estimate truth)
    (htruthSurj : Function.Surjective (encoder truth))
    (micro : Model X (fun _ => Act))
    (E : RealizedControlEstimator (encoder truth) micro) :
    ∃ (hestSurj : Function.Surjective (encoder estimate))
      (Eest : RealizedControlEstimator (encoder estimate) micro),
      let Q := exactControlQuotient_of_realizedEstimator
        (encoder estimate) hestSurj micro Eest
      (∀ x : X,
        BellmanGODCorrespondence micro x =
          BellmanGODCorrespondence Q.macroModel ((encoder estimate) x)) ∧
      (∀ x : X,
        micro.optimalValue x =
          Q.macroModel.optimalValue ((encoder estimate) x)) := by
  have henc : encoder estimate = encoder truth :=
    B.encoder_eq_of_class estimate truth hrecovered
  have hestSurj : Function.Surjective (encoder estimate) := by
    rw [henc]
    exact htruthSurj
  let Eest : RealizedControlEstimator (encoder estimate) micro :=
    transportRealizedControlEstimator henc E
  refine ⟨hestSurj, Eest, ?_⟩
  let Q := exactControlQuotient_of_realizedEstimator
    (encoder estimate) hestSurj micro Eest
  refine ⟨?_, ?_⟩
  · intro x
    exact exact_bellmanGODCorrespondence_eq Q x
  · intro x
    exact Q.optimalValue_apply x

/-- **Recovered object class -> strengthened P3 policy/GOA closure.**

The class-to-encoder bridge licenses use of the same truth-side P3 control
fibres.  Exact canonical selector recovery still requires a positive action
gap, and unique/stable GOA still requires Dobrushin isolation; P4 does not
weaken either condition. -/
theorem recoveredClass_policy_goa_closure
    {Candidate : Type uCandidate}
    {objectClass : Setoid Candidate}
    {X : Type uX} [Fintype X] [Nonempty X]
    {S : Type uS} [Fintype S] [Nonempty S]
    {Act : Type uA} [Fintype Act] [Nonempty Act]
    (encoder : Candidate → X → S)
    (B : ObjectClassControlEncoderBridge objectClass encoder)
    (estimate truth : Candidate)
    (hrecovered : objectClass.r estimate truth)
    (htruthSurj : Function.Surjective (encoder truth))
    (micro : Model X (fun _ => Act))
    (E : RealizedControlEstimator (encoder truth) micro)
    (hdiscount : ∀ n, micro.discount = (E.macroHat n).discount)
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hsourceGap :
      let Qexact := exactControlQuotient_of_realizedEstimator
        (encoder truth) htruthSurj micro E
      ∀ s a, a ≠ Qexact.macroModel.greedyAction s →
        gamma ≤
          Qexact.macroModel.qValue Qexact.macroModel.optimalValue s
              (Qexact.macroModel.greedyAction s) -
            Qexact.macroModel.qValue Qexact.macroModel.optimalValue s a)
    (halpha :
      let Qexact := exactControlQuotient_of_realizedEstimator
        (encoder truth) htruthSurj micro E
      FiniteDobrushin.dobrushinAlpha
        (GoaGaugeInvariance.selectorClosedLoopMatrix
          Qexact.macroModel Qexact.macroModel.greedyAction)
        (GoaGaugeInvariance.selectorClosedLoopMatrix_rowStochastic
          Qexact.macroModel Qexact.macroModel.greedyAction) < 1) :
    encoder estimate = encoder truth ∧
      (let Qexact := exactControlQuotient_of_realizedEstimator
          (encoder truth) htruthSurj micro E
       let Qref : ApproxControlQuotient X S (fun _ => Act) := exactAsApprox Qexact
       let Qseq : ℕ → ApproxControlQuotient X S (fun _ => Act) :=
         fun n => estimatedApproxControlQuotient E htruthSurj hdiscount n
       (∀ᶠ n in atTop, ∀ s,
         (E.macroHat n).greedyAction s = Qexact.macroModel.greedyAction s) ∧
       (∀ eta : ℝ, 0 < eta →
         ∀ᶠ n in atTop,
           ∃! e : S ≃ S,
             OptimalPolicyNearGoaGaugeAt Qref (Qseq n) e ∧
             movingNearGoaRadius Qref Qseq Qref.macroModel.greedyAction n < eta)) := by
  refine ⟨B.encoder_eq_of_class estimate truth hrecovered, ?_⟩
  exact p3_policy_goa_terminal_closure
    (encoder truth) htruthSurj micro E hdiscount gamma hgamma hsourceGap halpha

/-- P2's identity witness remains a P4 boundary: even literally identical
history-control specifications can belong to distinct parent identities.  Thus
the control-encoder bridge above cannot be treated as a same-parent theorem. -/
theorem equalControlData_still_does_not_identify_parent :
    ∃ M N :
        ParentBoundHistoryControlSpec Bool Unit Unit Unit (fun _ => ()),
      M.control = N.control ∧ ¬ SameControlParent M N :=
  identical_historyControlSpec_does_not_imply_sameParent

end UEOT.V3.Compression.TheoryCompletion.InverseObjecthood
