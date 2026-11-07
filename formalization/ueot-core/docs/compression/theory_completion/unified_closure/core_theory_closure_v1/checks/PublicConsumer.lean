import UEOT

/-!
# Public-only acceptance consumer for Core theory closure

This file imports only the supported `UEOT` entry. The examples pin the
parameterized source contracts used by the definitive Core text. They do not
rerun the finite native enumeration or claim an empirical validation.

The source keeps environmental inflow explicit, includes stop and rejected
requests, separates retained identities from newborn identities, and uses a
finite-horizon probability statement for actual selection. The lawful quotient
is checked on the full public history, not merely on its first moments.
-/

namespace UEOT.CoreTheoryPublicAcceptance

open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open CoreRegenerativeSource SourceCohortFeedback
open scoped BigOperators

/-! ## The source is nonempty and its transactions really pay -/

example : ∃ p : Parameters, Valid p :=
  CoreTheoryClosure.positive_source_class_nonempty

example (x : Body) (a : Action) (z : Noise) :
    (step x a z).repairPaid + (step x a z).operationPaid +
      outputCapital (step x a z) + (step x a z).refund = 1 + 5 :=
  step_budget x a z

example (p : Parameters) (theta i tag : Bool) (a : Action) (j : Kind) :
    realizedMean p theta i tag a j = realizedRow p i a j :=
  realizedMean_eq p theta i tag a j

-- The formed-parent factory is available through the same public root.
#check CoreRegenerativeSource.actual_formed_candidate_family_nonempty
#check CoreRegenerativeSource.bootstrap_cut_changes_future

section Repair

open UEOT.V3.Compression.Objecthood UEOT.V3.ViabilityKernel

example (theta tag : Bool) :
    repairRank repairKernel (recoveredSet theta tag) (startState theta true tag)
      (source_strongRepairable theta true tag) = 1 :=
  damaged_repairRank_one theta tag

example (theta tag : Bool) :
    ¬ StrongRepairable repairKernel (recoveredSet theta tag) (bootCutState theta tag) :=
  bootstrap_cut_not_repairable theta tag

example (theta tag : Bool) :
    ¬ StrongRepairable repairKernel (recoveredSet theta tag) (underfundedState theta tag) :=
  underfunded_not_repairable theta tag

end Repair

/-! ## Full-menu control and one physical inherited program -/

section Growth

open FiniteSourceGrowthControl.SourceConsumer
open CoreRegenerativePopulation CoreRegenerativeControlPopulation

example (p : Parameters) (hp : Valid p) (i : Kind) (a : Action) :
    (∑ j, realizedRow p i a j * sourceValue p j) ≤
      growthRate p true * sourceValue p i :=
  actual_row_bound p hp i a

example (p : Parameters) (hp : Valid p) (index : ℕ) (tag : Bool) :
    (paidRepair (startState true true tag)).body = encode true false tag ∧
    rawExecute (paidRepair (startState true true tag)).body true = some .care ∧
    (paidRepair (startState true true tag)).balance.val = 3 ∧
    (∀ z : Noise, programStep (founder index true true tag).body z =
      step (startState true true tag).body .care z) ∧
    ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧ ∀ n,
      lo * growthRate p true ^ n ≤ populationExpectation p bestPolicy
        (CoreTheoryClosure.commonFounder index tag) n
        (fun s => (s.population.length : ℝ)) ∧
      populationExpectation p bestPolicy (CoreTheoryClosure.commonFounder index tag) n
        (fun s => (s.population.length : ℝ)) ≤ hi * growthRate p true ^ n :=
  CoreTheoryClosure.same_program_regenerates_and_attains p hp index tag

-- Growth optimality does not become maximal original-identity survival.
example (p : Parameters) (hp : Valid p) (tag : Bool) :
    actualRetainedProbability p (programBody true false tag) (programAction true false) <
      actualRetainedProbability p (programBody true false tag) .care :=
  growth_choice_not_identity_survival_maximal p hp tag

end Growth

/-! ## Real identities and marked genealogy -/

section Genealogy

open CoreRegenerativePopulation CoreRegenerativeFeedback CoreRegenerativeLineage
open FiniteSourceGrowthControl.SourceConsumer

example (t : ℕ) (old : Member) (body : Body) :
    (newbornMember t old body).parent = some old.identity ∧
    (newbornMember t old body).identity ≠ old.identity ∧
    (newbornMember t old body).bornAt = t + 1 ∧
    (newbornMember t old body).age = 0 :=
  newborn_actual_parent t old body

example (p : Parameters) (hp : Valid p) (T t : ℕ) (old : Member) (i tag : Bool)
    (hbody : old.body = programBody true i tag) (F : List Mark → ℝ) :
    (∑ w : NoiseTree T, treeWeight p T w *
      ((descendants T t old w).map
        (fun m => sourceValue p (diagnostic m.body) * F (markedPath m))).sum) =
      growthRate p true ^ T * sourceValue p i *
        lineageExpectation p T i (markedPath old) F :=
  actual_marked_many_to_one p hp T t old i tag hbody F

end Genealogy

/-! ## Actual finite-cohort selection and its resource bill -/

section Selection

open CoreRegenerativeFeedback

example (p : Parameters) (hp : Valid p) (ε η : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hη : 0 < η) :
    ∃ T n : ℕ, 0 < T ∧ 0 < n ∧
      1 - η ≤ eventMass (iidWeight (cohortWeight p T) n) (ActualSelectionGood T n ε) :=
  exists_finite_cohort_selection p hp ε η hε0 hε1 hη

example (T n : ℕ) (w : Samples (CohortAtoms T) n) :
    sampleSum (cohortResource T) n w ≤ (n : ℝ) * (2 + 10 * ((2 : ℝ) ^ T - 1)) :=
  actual_sample_resource_bound T n w

#check SourceCohortFeedback.iid_badRatio_mass_le

end Selection

section SelectionBoundaries

open CoreRegenerativeFeedbackBoundary

example :
    eventMass (productWeight (noiseWeight concreteParameters) (noiseWeight concreteParameters))
      (fun z => actualCount true z.2 = 0 ∧ 0 < actualCount false z.1) = 243/2048 :=
  concrete_best_extinct_inferior_nonzero

example :
    twoFounderMean concreteParameters (fun a b => (b : ℝ) / ((a : ℝ) + b)) ≠
      twoFounderMean concreteParameters (fun _ b => (b : ℝ)) /
        twoFounderMean concreteParameters (fun a b => (a : ℝ) + b) :=
  expected_ratio_ne_ratio_expected_counts

end SelectionBoundaries

/-! ## Actual finite histories, two-way values and lawful representation -/

section Representation

open CoreRegenerativeQuotient CoreRegenerativeControlPopulation

example : ¬ Function.Injective quotient := quotient_is_noninjective

example (p : Parameters) (K : Policy) (initial : State) (n : ℕ) (F : State → ℝ) :
    populationExpectation p K (eraseState initial) n F =
      populationExpectation p K initial n (fun s => F (eraseState s)) :=
  populationExpectation_eraseState p K initial n F

example (p : Parameters) (initial : State) (n : ℕ)
    (F : State → ℝ) (hF : ∀ s, F (eraseState s) = F s) :
    Set.range (fun K : Policy => populationExpectation p K (eraseState initial) n F) =
      Set.range (fun K : Policy => populationExpectation p K initial n F) :=
  attainable_test_values_eraseState p initial n F hF

example (p : Parameters) (K : Policy) (initial : State)
    (n : ℕ) (F : List (List PublicReceipt) → ℝ) :
    populationExpectation p K (eraseState initial) n (fun s => F s.publicHistory) =
      populationExpectation p K initial n (fun s => F s.publicHistory) :=
  public_history_test_expectation_eq p K initial n F

#check CoreRegenerativeQuotient.dropping_diagnostic_is_not_lawful
#check CoreRegenerativeQuotient.code_only_prediction_loses_execution

end Representation

end UEOT.CoreTheoryPublicAcceptance
