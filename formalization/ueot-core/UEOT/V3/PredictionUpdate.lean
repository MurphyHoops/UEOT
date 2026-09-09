import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# P-PRED-03 foundation — recursive Bayes update factorization

The source proof observes that, after an action and a positive-probability
observation, every continuation probability is a ratio of a joint cylinder
probability and the observation probability.  If both are stored by the
current canonical state, then the updated continuation response factors
through that state.  This file machine-checks that algebraic/measurable core.
-/

namespace UEOT.V3.PredictionUpdate

universe uH uS uA uO uI

variable {H : Type uH} {S : Type uS} {A : Type uA}
variable {O : Type uO} {I : Type uI}

/-- Bayes continuation response written on full histories.  Zero-denominator
branches receive an arbitrary mathematical extension (chosen here as zero),
matching the source caveat that such branches are not empirically certified. -/
noncomputable def historyBayesResponse
    (joint : H → A → O → I → ℝ)
    (obs : H → A → O → ℝ)
    (h : H) (a : A) (o : O) (i : I) : ℝ :=
  if obs h a o = 0 then 0 else joint h a o i / obs h a o

/-- The same Bayes update computed only from a candidate canonical state. -/
noncomputable def stateBayesUpdate
    (joint : S → A → O → I → ℝ)
    (obs : S → A → O → ℝ)
    (s : S) (a : A) (o : O) (i : I) : ℝ :=
  if obs s a o = 0 then 0 else joint s a o i / obs s a o

/-- Core factorization step in the source P-PRED-03 proof: when both the
joint continuation cylinders and the observation marginal factor through the
current state, the entire one-step Bayes update factors through it as well. -/
theorem bayes_update_factors_through_state
    (C : H → S)
    (jointH : H → A → O → I → ℝ)
    (obsH : H → A → O → ℝ)
    (jointS : S → A → O → I → ℝ)
    (obsS : S → A → O → ℝ)
    (hJoint : ∀ h a o i, jointH h a o i = jointS (C h) a o i)
    (hObs : ∀ h a o, obsH h a o = obsS (C h) a o) :
    ∀ h a o i,
      historyBayesResponse jointH obsH h a o i =
        stateBayesUpdate jointS obsS (C h) a o i := by
  intro h a o i
  simp [historyBayesResponse, stateBayesUpdate,
    hObs h a o, hJoint h a o i]

theorem bayes_update_equal_of_same_state
    (jointS : S → A → O → I → ℝ)
    (obsS : S → A → O → ℝ)
    {s t : S} (hst : s = t) (a : A) (o : O) (i : I) :
    stateBayesUpdate jointS obsS s a o i =
      stateBayesUpdate jointS obsS t a o i := by
  subst hst
  rfl

section Measurable

variable [MeasurableSpace S]

/-- Each continuation coordinate of the state update is measurable whenever
the stored numerator and denominator coordinates are measurable. -/
theorem measurable_stateBayesUpdate_coordinate
    (jointS : S → A → O → I → ℝ)
    (obsS : S → A → O → ℝ)
    (a : A) (o : O) (i : I)
    (hJoint : Measurable (fun s => jointS s a o i))
    (hObs : Measurable (fun s => obsS s a o)) :
    Measurable (fun s => stateBayesUpdate jointS obsS s a o i) := by
  unfold stateBayesUpdate
  exact Measurable.ite
    (measurableSet_eq_fun hObs measurable_const)
    measurable_const
    (hJoint.div hObs)

end Measurable


/-- All continuation-event Bayes coordinates bundled as one response vector.
The index type `I` represents the finite/countable family of allowed future
record cylinders stored by the canonical predictive state. -/
noncomputable def historyBayesResponseVector
    (joint : H → A → O → I → ℝ)
    (obs : H → A → O → ℝ)
    (h : H) (a : A) (o : O) : I → ℝ :=
  fun i => historyBayesResponse joint obs h a o i

/-- State-only version of the full continuation response vector. -/
noncomputable def stateBayesUpdateVector
    (joint : S → A → O → I → ℝ)
    (obs : S → A → O → ℝ)
    (s : S) (a : A) (o : O) : I → ℝ :=
  fun i => stateBayesUpdate joint obs s a o i

/-- Vector form of the source P-PRED-03 factorization: if every joint future
cylinder and the observation marginal are stored by the current state, then
the entire updated continuation response, not merely one coordinate, factors
through that state. -/
theorem bayes_update_vector_factors_through_state
    (C : H → S)
    (jointH : H → A → O → I → ℝ)
    (obsH : H → A → O → ℝ)
    (jointS : S → A → O → I → ℝ)
    (obsS : S → A → O → ℝ)
    (hJoint : ∀ h a o i, jointH h a o i = jointS (C h) a o i)
    (hObs : ∀ h a o, obsH h a o = obsS (C h) a o) :
    ∀ h a o,
      historyBayesResponseVector jointH obsH h a o =
        stateBayesUpdateVector jointS obsS (C h) a o := by
  intro h a o
  funext i
  exact bayes_update_factors_through_state
    C jointH obsH jointS obsS hJoint hObs h a o i

section VectorMeasurable

variable [MeasurableSpace S]

/-- The whole continuation response is measurable for fixed finite-alphabet
action/observation symbols once each stored joint-cylinder coordinate and the
observation marginal are measurable.  The target carries the canonical
product measurable structure. -/
theorem measurable_stateBayesUpdateVector
    (jointS : S → A → O → I → ℝ)
    (obsS : S → A → O → ℝ)
    (a : A) (o : O)
    (hJoint : ∀ i, Measurable (fun s => jointS s a o i))
    (hObs : Measurable (fun s => obsS s a o)) :
    Measurable (fun s => stateBayesUpdateVector jointS obsS s a o) := by
  rw [measurable_pi_iff]
  intro i
  exact measurable_stateBayesUpdate_coordinate
    jointS obsS a o i (hJoint i) hObs

end VectorMeasurable


section JointMeasurable

variable [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
variable [Fintype A] [Fintype O]
variable [MeasurableSingletonClass A] [MeasurableSingletonClass O]

/-- Jointly measurable update map on state, action and observation for finite
alphabets.  The finite action/observation alphabet supplies a countable
measurable partition, while the continuation coordinates carry the product
measurable structure. -/
theorem measurable_stateBayesUpdateVector_joint
    (jointS : S → A → O → I → ℝ)
    (obsS : S → A → O → ℝ)
    (hJoint : ∀ a o i, Measurable (fun s => jointS s a o i))
    (hObs : ∀ a o, Measurable (fun s => obsS s a o)) :
    Measurable
      (fun z : S × (A × O) =>
        stateBayesUpdateVector jointS obsS z.1 z.2.1 z.2.2) := by
  apply measurable_from_prod_countable_left
  rintro ⟨a, o⟩
  exact measurable_stateBayesUpdateVector
    jointS obsS a o (hJoint a o) (hObs a o)

/-- Existence packaging matching the source notation
`C_{t+1} = U_t(C_t,a_t,o_{t+1})`: under the stored-coordinate hypotheses,
there is a jointly measurable state/action/observation update whose value on
every current history is the full Bayes continuation-response vector. -/
theorem exists_measurable_bayes_update
    (C : H → S)
    (jointH : H → A → O → I → ℝ)
    (obsH : H → A → O → ℝ)
    (jointS : S → A → O → I → ℝ)
    (obsS : S → A → O → ℝ)
    (hJointFactor :
      ∀ h a o i, jointH h a o i = jointS (C h) a o i)
    (hObsFactor :
      ∀ h a o, obsH h a o = obsS (C h) a o)
    (hJointMeas :
      ∀ a o i, Measurable (fun s => jointS s a o i))
    (hObsMeas :
      ∀ a o, Measurable (fun s => obsS s a o)) :
    ∃ U : S × (A × O) → (I → ℝ),
      Measurable U ∧
      ∀ h a o,
        historyBayesResponseVector jointH obsH h a o =
          U (C h, (a, o)) := by
  refine ⟨
    (fun z : S × (A × O) =>
      stateBayesUpdateVector jointS obsS z.1 z.2.1 z.2.2),
    measurable_stateBayesUpdateVector_joint
      jointS obsS hJointMeas hObsMeas,
    ?_⟩
  intro h a o
  exact bayes_update_vector_factors_through_state
    C jointH obsH jointS obsS hJointFactor hObsFactor h a o

end JointMeasurable


/-- Semantic witness of the protocol-closure hypothesis in P-PRED-03.
`J` indexes the coordinates stored by the current canonical predictive state.
For each action/observation symbol, `obsIndex` identifies the observation
marginal coordinate, while `jointIndex` identifies every required joint
observation-plus-continuation cylinder coordinate. -/
structure RecursiveCoordinateClosure
    (A : Type uA) (O : Type uO) (I : Type uI) (J : Type*) where
  obsIndex : A → O → J
  jointIndex : A → O → I → J

/-- Bayes update read directly from the coordinates of the current canonical
state.  The zero-probability branch is the arbitrary mathematical extension
allowed by the source theorem. -/
noncomputable def coordinateBayesUpdate
    {J : Type*}
    (cl : RecursiveCoordinateClosure A O I J)
    (c : J → ℝ) (a : A) (o : O) : I → ℝ :=
  fun i =>
    if c (cl.obsIndex a o) = 0 then 0
    else c (cl.jointIndex a o i) / c (cl.obsIndex a o)

/-- If the current canonical state really stores the observation marginal and
joint future-cylinder probabilities at the closure-witness coordinates, then
the history-level Bayes continuation response is exactly the coordinate update
of the current canonical state. -/
theorem coordinateBayesUpdate_recovers_history
    {J : Type*}
    (cl : RecursiveCoordinateClosure A O I J)
    (C : H → (J → ℝ))
    (jointH : H → A → O → I → ℝ)
    (obsH : H → A → O → ℝ)
    (hJoint :
      ∀ h a o i,
        jointH h a o i = C h (cl.jointIndex a o i))
    (hObs :
      ∀ h a o,
        obsH h a o = C h (cl.obsIndex a o)) :
    ∀ h a o,
      historyBayesResponseVector jointH obsH h a o =
        coordinateBayesUpdate cl (C h) a o := by
  intro h a o
  funext i
  simp [historyBayesResponseVector, historyBayesResponse,
    coordinateBayesUpdate, hJoint h a o i, hObs h a o]

/-- Equality of current canonical states is preserved by the next-step
continuation response generated by the same action and observation. -/
theorem coordinateBayesUpdate_equal_of_same_state
    {J : Type*}
    (cl : RecursiveCoordinateClosure A O I J)
    {c d : J → ℝ} (hcd : c = d) (a : A) (o : O) :
    coordinateBayesUpdate cl c a o =
      coordinateBayesUpdate cl d a o := by
  subst d
  rfl

section CoordinateClosureMeasurable

variable {J : Type*}
variable [MeasurableSpace A] [MeasurableSpace O]
variable [Fintype A] [Fintype O]
variable [MeasurableSingletonClass A] [MeasurableSingletonClass O]

/-- For fixed action and observation, the coordinate Bayes update is
measurable on the canonical product state `J → ℝ`. -/
theorem measurable_coordinateBayesUpdate_fixed
    (cl : RecursiveCoordinateClosure A O I J)
    (a : A) (o : O) :
    Measurable
      (fun c : J → ℝ => coordinateBayesUpdate cl c a o) := by
  rw [measurable_pi_iff]
  intro i
  unfold coordinateBayesUpdate
  exact Measurable.ite
    (measurableSet_eq_fun
      (measurable_pi_apply (cl.obsIndex a o)) measurable_const)
    measurable_const
    ((measurable_pi_apply (cl.jointIndex a o i)).div
      (measurable_pi_apply (cl.obsIndex a o)))

/-- Source-facing measurable update map
`U_t : C_t × A × O → C_{t+1}` for finite alphabets. -/
theorem measurable_coordinateBayesUpdate_joint
    (cl : RecursiveCoordinateClosure A O I J) :
    Measurable
      (fun z : (J → ℝ) × (A × O) =>
        coordinateBayesUpdate cl z.1 z.2.1 z.2.2) := by
  apply measurable_from_prod_countable_left
  rintro ⟨a, o⟩
  exact measurable_coordinateBayesUpdate_fixed cl a o

/-- Existence form closest to the manuscript statement
`C_{t+1} = U_t(C_t,a_t,o_{t+1})`: the protocol-closure coordinate witness
constructs a jointly measurable update directly on the current canonical
state. -/
theorem exists_measurable_coordinate_update
    (cl : RecursiveCoordinateClosure A O I J) :
    ∃ U : (J → ℝ) × (A × O) → (I → ℝ),
      Measurable U ∧
      ∀ c a o, U (c, (a, o)) = coordinateBayesUpdate cl c a o := by
  exact ⟨
    (fun z : (J → ℝ) × (A × O) =>
      coordinateBayesUpdate cl z.1 z.2.1 z.2.2),
    measurable_coordinateBayesUpdate_joint cl,
    fun _ _ _ => rfl⟩

end CoordinateClosureMeasurable


/-- Source-facing P-PRED-03 wrapper.

The manuscript assumes finite action/observation alphabets and a finite or
countable family of continuation-cylinder coordinates.  Protocol closure is
represented by `RecursiveCoordinateClosure`: every observation marginal and
every observation-plus-continuation cylinder needed by Bayes updating is a
coordinate of the current canonical state.

For an actual history-level process whose stored coordinates equal those
probabilities, the next continuation-response vector is therefore a jointly
measurable function of the current canonical state, action, and observation.
The zero-observation branch is the arbitrary mathematical extension already
built into `coordinateBayesUpdate`. -/
theorem p_pred_03_recursive_update
    {J : Type*}
    [Countable I]
    [MeasurableSpace A] [MeasurableSpace O]
    [Fintype A] [Fintype O]
    [MeasurableSingletonClass A] [MeasurableSingletonClass O]
    (cl : RecursiveCoordinateClosure A O I J)
    (C : H → (J → ℝ))
    (jointH : H → A → O → I → ℝ)
    (obsH : H → A → O → ℝ)
    (hJoint :
      ∀ h a o i,
        jointH h a o i = C h (cl.jointIndex a o i))
    (hObs :
      ∀ h a o,
        obsH h a o = C h (cl.obsIndex a o)) :
    ∃ U : (J → ℝ) × (A × O) → (I → ℝ),
      Measurable U ∧
      (∀ h a o,
        historyBayesResponseVector jointH obsH h a o =
          U (C h, (a, o))) ∧
      (∀ {h h' : H}, C h = C h' →
        ∀ a o,
          historyBayesResponseVector jointH obsH h a o =
            historyBayesResponseVector jointH obsH h' a o) := by
  refine ⟨
    (fun z : (J → ℝ) × (A × O) =>
      coordinateBayesUpdate cl z.1 z.2.1 z.2.2),
    measurable_coordinateBayesUpdate_joint cl,
    ?_,
    ?_⟩
  · intro h a o
    exact coordinateBayesUpdate_recovers_history
      cl C jointH obsH hJoint hObs h a o
  · intro h h' hsame a o
    rw [
      coordinateBayesUpdate_recovers_history
        cl C jointH obsH hJoint hObs h a o,
      coordinateBayesUpdate_recovers_history
        cl C jointH obsH hJoint hObs h' a o,
      hsame]

end UEOT.V3.PredictionUpdate
