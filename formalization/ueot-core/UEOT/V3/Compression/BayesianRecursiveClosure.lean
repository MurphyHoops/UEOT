import UEOT.V3.PredictionUpdate
import UEOT.V3.PRef02

/-!
# Experimental M-BU-01 — Bayesian recursive closure

This module independently tests the proposed compression between P-PRED-03 and
P-REF-02.  The generic core is the Bayes ratio update determined by state,
action, and observation.  Source-specific normalization, disintegration,
zero-evidence semantics, and control data remain explicit adapters.

The module is experimental and does not alter the frozen compression ledger.
-/

namespace UEOT.V3.Compression.BayesianRecursiveClosure

open MeasureTheory
open UEOT.V3

universe uH uS uA uO uI uJ uTheta uX uY

/-- Generic Bayes coordinate with an explicit fallback on zero evidence. -/
noncomputable def bayesCoordinate
    {S : Type uS} {A : Type uA} {O : Type uO} {I : Type uI}
    (joint : S → A → O → I → ℝ)
    (evidence : S → A → O → ℝ)
    (fallback : I → ℝ)
    (s : S) (a : A) (o : O) (i : I) : ℝ :=
  if evidence s a o = 0 then fallback i
  else joint s a o i / evidence s a o

/-- Positive-evidence branch of the generic Bayes coordinate. -/
theorem bayesCoordinate_of_ne
    {S : Type uS} {A : Type uA} {O : Type uO} {I : Type uI}
    (joint : S → A → O → I → ℝ)
    (evidence : S → A → O → ℝ)
    (fallback : I → ℝ)
    (s : S) (a : A) (o : O) (i : I)
    (h : evidence s a o ≠ 0) :
    bayesCoordinate joint evidence fallback s a o i =
      joint s a o i / evidence s a o := by
  simp [bayesCoordinate, h]

/-- Zero-evidence branch is deliberately parameterized instead of silently
identifying the P-PRED-03 arbitrary extension with P-REF-02 modelConflict. -/
theorem bayesCoordinate_of_eq_zero
    {S : Type uS} {A : Type uA} {O : Type uO} {I : Type uI}
    (joint : S → A → O → I → ℝ)
    (evidence : S → A → O → ℝ)
    (fallback : I → ℝ)
    (s : S) (a : A) (o : O) (i : I)
    (h : evidence s a o = 0) :
    bayesCoordinate joint evidence fallback s a o i = fallback i := by
  simp [bayesCoordinate, h]

/-- State-factorization theorem: once numerator and denominator factor through
the state, the whole Bayes coordinate factors through that state. -/
theorem bayesCoordinate_factors_through_state
    {H : Type uH} {S : Type uS} {A : Type uA} {O : Type uO} {I : Type uI}
    (C : H → S)
    (jointH : H → A → O → I → ℝ)
    (evidenceH : H → A → O → ℝ)
    (jointS : S → A → O → I → ℝ)
    (evidenceS : S → A → O → ℝ)
    (fallback : I → ℝ)
    (hJoint : ∀ h a o i, jointH h a o i = jointS (C h) a o i)
    (hEvidence : ∀ h a o, evidenceH h a o = evidenceS (C h) a o) :
    ∀ h a o i,
      bayesCoordinate jointH evidenceH fallback h a o i =
        bayesCoordinate jointS evidenceS fallback (C h) a o i := by
  intro h a o i
  simp [bayesCoordinate, hJoint h a o i, hEvidence h a o]

/-- Vector-valued Bayes update. -/
noncomputable def bayesUpdate
    {S : Type uS} {A : Type uA} {O : Type uO} {I : Type uI}
    (joint : S → A → O → I → ℝ)
    (evidence : S → A → O → ℝ)
    (fallback : I → ℝ)
    (s : S) (a : A) (o : O) : I → ℝ :=
  fun i => bayesCoordinate joint evidence fallback s a o i

section Measurable

variable {S : Type uS} {A : Type uA} {O : Type uO} {I : Type uI}
variable [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
variable [Fintype A] [Fintype O]
variable [MeasurableSingletonClass A] [MeasurableSingletonClass O]

/-- For finite action/observation alphabets, coordinatewise measurable
numerator/denominator data give a jointly measurable recursive Bayes update. -/
theorem measurable_bayesUpdate_joint
    (joint : S → A → O → I → ℝ)
    (evidence : S → A → O → ℝ)
    (fallback : I → ℝ)
    (hJoint : ∀ a o i, Measurable (fun s => joint s a o i))
    (hEvidence : ∀ a o, Measurable (fun s => evidence s a o)) :
    Measurable
      (fun z : S × (A × O) =>
        bayesUpdate joint evidence fallback z.1 z.2.1 z.2.2) := by
  apply measurable_from_prod_countable_left
  rintro ⟨a, o⟩
  rw [measurable_pi_iff]
  intro i
  unfold bayesUpdate bayesCoordinate
  exact Measurable.ite
    (measurableSet_eq_fun (hEvidence a o) measurable_const)
    measurable_const
    ((hJoint a o i).div (hEvidence a o))

end Measurable

/-- Independent source-facing rederivation of P-PRED-03 through the generic
Bayesian recursive-closure core. -/
theorem p_pred_03_via_bayesianRecursiveClosure
    {H : Type uH} {A : Type uA} {O : Type uO} {I : Type uI} {J : Type uJ}
    [Countable I]
    [MeasurableSpace A] [MeasurableSpace O]
    [Fintype A] [Fintype O]
    [MeasurableSingletonClass A] [MeasurableSingletonClass O]
    (cl : PredictionUpdate.RecursiveCoordinateClosure A O I J)
    (C : H → (J → ℝ))
    (jointH : H → A → O → I → ℝ)
    (obsH : H → A → O → ℝ)
    (hJoint :
      ∀ h a o i, jointH h a o i = C h (cl.jointIndex a o i))
    (hObs :
      ∀ h a o, obsH h a o = C h (cl.obsIndex a o)) :
    ∃ U : (J → ℝ) × (A × O) → (I → ℝ),
      Measurable U ∧
      (∀ h a o,
        PredictionUpdate.historyBayesResponseVector jointH obsH h a o =
          U (C h, (a, o))) ∧
      (∀ {h h' : H}, C h = C h' →
        ∀ a o,
          PredictionUpdate.historyBayesResponseVector jointH obsH h a o =
            PredictionUpdate.historyBayesResponseVector jointH obsH h' a o) := by
  let jointS : (J → ℝ) → A → O → I → ℝ :=
    fun c a o i => c (cl.jointIndex a o i)
  let evidenceS : (J → ℝ) → A → O → ℝ :=
    fun c a o => c (cl.obsIndex a o)
  let fallback : I → ℝ := fun _ => 0
  let U : (J → ℝ) × (A × O) → (I → ℝ) :=
    fun z => bayesUpdate jointS evidenceS fallback z.1 z.2.1 z.2.2
  have hUmeas : Measurable U := by
    apply measurable_bayesUpdate_joint jointS evidenceS fallback
    · intro a o i
      exact measurable_pi_apply (cl.jointIndex a o i)
    · intro a o
      exact measurable_pi_apply (cl.obsIndex a o)
  refine ⟨U, hUmeas, ?_, ?_⟩
  · intro h a o
    funext i
    change
      PredictionUpdate.historyBayesResponse jointH obsH h a o i =
        bayesCoordinate jointS evidenceS fallback (C h) a o i
    unfold PredictionUpdate.historyBayesResponse
    simp [bayesCoordinate, jointS, evidenceS, fallback, hJoint h a o i, hObs h a o]
  · intro h h' hsame a o
    funext i
    change
      PredictionUpdate.historyBayesResponse jointH obsH h a o i =
        PredictionUpdate.historyBayesResponse jointH obsH h' a o i
    unfold PredictionUpdate.historyBayesResponse
    rw [hObs h a o, hObs h' a o, hsame]
    by_cases hz : C h' (cl.obsIndex a o) = 0
    · simp [hz]
    · simp [hz, hJoint h a o i, hJoint h' a o i, hsame]

section FiniteBeliefAdapter

variable {Theta : Type uTheta} {X : Type uX} {A : Type uA} {Y : Type uY}
variable [Fintype Theta] [Fintype X] [Fintype Y]

/-- The positive-evidence finite P-REF-02 Bayes fraction is an instance of the
same generic Bayes coordinate used above.  Normalization of the posterior
belief remains a finite-probability adapter. -/
theorem p_ref_02_discrete_posterior_via_bayesianRecursiveClosure
    (M : FiniteBayesBelief.Model Theta X A Y)
    (b : FiniteBayesBelief.Belief Theta X) (a : A) (y : Y)
    (h : FiniteBayesBelief.evidence M b a y ≠ 0)
    (theta : Theta) (x' : X) :
    (FiniteBayesBelief.posterior M b a y h).mass theta x' =
      bayesCoordinate
        (fun b a y p =>
          FiniteBayesBelief.jointObservationMass M b a y p.1 p.2)
        (fun b a y => FiniteBayesBelief.evidence M b a y)
        (fun _ : Theta × X => 0)
        b a y (theta, x') := by
  rw [FiniteBayesBelief.posterior_mass]
  symm
  exact bayesCoordinate_of_ne
    (fun b a y p =>
      FiniteBayesBelief.jointObservationMass M b a y p.1 p.2)
    (fun b a y => FiniteBayesBelief.evidence M b a y)
    (fun _ : Theta × X => 0)
    b a y (theta, x') h

/-- Zero evidence is intentionally *not* identified with the arbitrary
P-PRED-03 fallback.  P-REF-02 keeps the stronger source semantics:
impossible observations are explicit model conflicts. -/
theorem p_ref_02_zero_evidence_boundary
    (M : FiniteBayesBelief.Model Theta X A Y)
    (b : FiniteBayesBelief.Belief Theta X) (a : A) (y : Y) :
    FiniteBayesBelief.updateResult M b a y =
        FiniteBayesBelief.UpdateResult.modelConflict ↔
      FiniteBayesBelief.evidence M b a y = 0 :=
  PRef02.p_ref_02_discrete_modelConflict M b a y

end FiniteBeliefAdapter

end UEOT.V3.Compression.BayesianRecursiveClosure
