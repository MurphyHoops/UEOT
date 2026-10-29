#!/usr/bin/env python3
"""Closed data-only Lean obligations; no true parameter or observed Good input."""
from fractions import Fraction as Q

from selector import N
from emit_lean_witness import lean

PREFIX = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure."



def fine_reference(proposal):
    text = """def qReferencePrepared : State → ℚ := PREPARED

theorem qReferencePrepared_legal : ValidRow qReferencePrepared := by decide +kernel

theorem literal_preparation_row : rowPMF prep prep_legal =
    selection (tilt estimate) (tilt_valid estimate estimate_legal) := by
  apply PMF.ext
  intro a
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [rowPMF_toReal, selection_real]
  exact prep_coordinates a

/-- The supplied reference initial vector is the actual noisy preparation. -/
theorem reference_prepared_identity : literalPrepared estimate estimate_legal prep prep_legal =
    rowPMF qReferencePrepared qReferencePrepared_legal := by
  unfold literalPrepared
  rw [literal_preparation_row]
  change prepared estimate estimate_legal (tilt estimate) (tilt_valid estimate estimate_legal) = _
  rw [prepared_eq_selected]
  apply PMF.ext
  intro z
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [selectedRow_real_safe estimate estimate_legal (tilt estimate)
    (tilt_valid estimate estimate_legal) 0 (by decide) z, rowPMF_toReal]
  fin_cases z <;> norm_num [qReferencePrepared, tilt, estimate, qEstimate, counts,
    Matrix.cons_val_two, Matrix.cons_val_three]

def initialResidual : ℚ := INITIAL

def rowResidual : Fin horizon → ℚ := RESIDUALS

def referenceBound : ℚ := BOUND

def qLoss (v : ℚ) : ℚ := v*qEstimate 2+(1-v)*qEstimate 3

theorem initialResidual_formula : (initialResidual : ℝ) = preparationLoss estimate (tilt estimate) := by
  norm_num [initialResidual, preparationLoss, tilt, estimate, qEstimate, counts,
    Matrix.cons_val_two, Matrix.cons_val_three]

theorem qLoss_cast (v : ℚ) : (qLoss v : ℝ) = preparationLoss estimate (v : ℝ) := by
  simp only [qLoss, preparationLoss, estimate, Rat.cast_add, Rat.cast_mul, Rat.cast_sub, Rat.cast_one]

theorem residuals_formula_q : ∀ t, rowResidual t =
    if t.val+1<horizon then qLoss (prep 1) else qLoss (1/2) := by decide +kernel

def epsilon (n : ℕ) : ℝ := if n+1<horizon then preparationLoss estimate (tilt estimate)
    else preparationLoss estimate (1/2)

theorem rowResidual_formula (t : Fin horizon) : (rowResidual t : ℝ) = epsilon t.val := by
  rw [residuals_formula_q]
  unfold epsilon
  by_cases h : t.val+1<horizon
  · rw [if_pos h, if_pos h, qLoss_cast]
    have hc : (prep 1 : ℝ) = tilt estimate := by simpa using prep_coordinates 1
    rw [hc]
  · rw [if_neg h, if_neg h, qLoss_cast]
    norm_num

theorem reference_sum : min (1 : ℝ) ((initialResidual : ℝ) +
    ∑ t : Fin horizon, (rowResidual t : ℝ)) = (referenceBound : ℝ) := by
  have hq : min (1 : ℚ) (initialResidual+∑ t : Fin horizon, rowResidual t) = referenceBound := by decide +kernel
  exact_mod_cast hq

/-- Computed initial and occupied-row residuals certify this same reference path. -/
theorem fine_reference_path :
    tvDist (literalDeployment estimate estimate_legal prep prep_legal horizon weights weights_legal).toMeasure
      (target estimate estimate_legal horizon).toMeasure ≤ (referenceBound : ℝ) := by
  rw [literal_deployment_eq_direct estimate estimate_legal estimate estimate_legal
    prep prep_legal horizon weights weights_legal prep_coordinates weights_coordinates]
  have h := causal_path_tv_le
    (prepared estimate estimate_legal (tilt estimate) (tilt_valid estimate estimate_legal))
    (nu estimate estimate_legal)
    (timeMixtureKernel (model estimate estimate_legal) observe (controller estimate estimate_legal horizon))
    (fun n h => targetRow estimate estimate_legal horizon n (currentState n h)) horizon
    (initialResidual : ℝ) epsilon (by
      change tvDist (prepared estimate estimate_legal (tilt estimate) (tilt_valid estimate estimate_legal)).toMeasure
        (safePMF (tilt estimate) (tilt_valid estimate estimate_legal)).toMeasure ≤ _
      rw [prepared_eq_selected, selected_row_tv estimate estimate_legal (tilt estimate)
        (tilt_valid estimate estimate_legal) 0 (by decide), initialResidual_formula]) (by
      intro n hn h hh
      have hs := target_occupied_safe estimate estimate_legal horizon n (currentState n h) ⟨h,hh,rfl⟩
      by_cases hc : n+1<horizon
      · simp only [timeMixtureKernel, controller, targetRow, if_pos hc, epsilon]
        change tvDist (selectedRow estimate estimate_legal (tilt estimate)
          (tilt_valid estimate estimate_legal) (currentState n h)).toMeasure
          (safePMF (tilt estimate) (tilt_valid estimate estimate_legal)).toMeasure ≤ _
        rw [selected_row_tv estimate estimate_legal (tilt estimate) (tilt_valid estimate estimate_legal) _ hs]
      · simp only [timeMixtureKernel, controller, targetRow, if_neg hc, epsilon]
        change tvDist (selectedRow estimate estimate_legal (1/2) (by norm_num) (currentState n h)).toMeasure
          (safePMF (1/2) (by norm_num)).toMeasure ≤ _
        rw [selected_row_tv estimate estimate_legal (1/2) (by norm_num) _ hs])
  have hsum : (∑ t : Fin horizon, (rowResidual t : ℝ)) = ∑ n ∈ Finset.range horizon, epsilon n := by
    simp_rw [rowResidual_formula]
    exact Fin.sum_univ_eq_sum_range epsilon horizon
  rw [← hsum, reference_sum] at h
  simpa only [deployed, target, if_neg (show horizon ≠ 0 by decide), targetPath] using h

/-- The reference target also has the original estimated-source conditioning identity. -/
theorem fine_reference_actual_path :
    tvDist (literalDeployment estimate estimate_legal prep prep_legal horizon weights weights_legal).toMeasure
      (actualConditionedPrefix (model estimate estimate_legal) observe baseline initial
        FiniteDataConditioned.safe horizon 0
        (FiniteDataConditioned.source_positive estimate estimate_legal horizon)).toMeasure ≤ (referenceBound : ℝ) := by
  rw [← FiniteDataConditioned.target_eq_actual estimate estimate_legal horizon]
  exact fine_reference_path
"""
    return text.replace("PREPARED", lean(proposal["reference_prepared"])).replace(
        "INITIAL", lean(proposal["reference_initial_residual"])).replace(
        "RESIDUALS", lean(proposal["reference_row_residuals"])).replace(
        "BOUND", lean(proposal["reference_path_bound"])).splitlines()


def emit(proposal):
    if proposal["status"] not in ("CANDIDATE_STATISTICAL_APPROX", "CANDIDATE_STATISTICAL_NO_GO"):
        raise ValueError("no statistical certificate candidate")
    T = proposal["T"]
    if T <= 0:
        raise ValueError("positive statistical horizon required")
    lines = [f"import {PREFIX}FiniteDataJoint", f"import {PREFIX}FiniteDataCertifiedConsumer", "",
             f"namespace {PREFIX}FiniteDataRuntimeCertificate", "",
             "open MeasureTheory UEOT.V3.PathError UEOT.V3.TotalVariation",
             "open UEOT.V3.FiniteDiscountedControl UEOT.V3.CoreOperationalAssembly",
             "open FiniteDataSource FiniteDataLiteral FiniteActionCertificateCheck",
             "open SameSourceFiniteWindowCheck FiniteDataNumericalBounds",
             "open ConditionedActionTransportCheck FiniteDataPathBounds", "open scoped BigOperators",
             "noncomputable section", "local instance : MeasurableSpace State := ⊤",
             "local instance : MeasurableSpace Bool := ⊤", "",
             f"def horizon : ℕ := {T}", f"def counts : Fin 4 → ℕ := {lean(proposal['counts'])}",
             f"def qEstimate : Fin 4 → ℚ := fun j => (counts j : ℚ) / {N}",
             "def estimate : Param := ⟨(qEstimate 0 : ℝ), (qEstimate 1 : ℝ),",
             "  (qEstimate 2 : ℝ), (qEstimate 3 : ℝ)⟩",
             "theorem counts_legal : ∀ j, counts j ≤ 262144 := by decide +kernel",
             "theorem estimate_legal : Admissible estimate := by",
             "  norm_num [Admissible, estimate, qEstimate, counts, Matrix.cons_val_two, Matrix.cons_val_three]", ""]
    if proposal["status"] == "CANDIDATE_STATISTICAL_APPROX":
        lines += [f"def prep : Action → ℚ := {lean(proposal['preparation'])}",
                  f"def weights : Fin horizon → Unit → Action → ℚ := fun t _ => {lean(proposal['weights'])} t",
                  "theorem prep_legal : ValidRow prep := by decide +kernel",
                  "theorem weights_legal : ∀ t y, ValidRow (weights t y) := by decide +kernel",
                  "theorem weights_formula : ∀ t a, weights t () a =",
                  "    if t.val+1<horizon then prep a else ![0,1/2,1/2] a := by decide +kernel",
                  "theorem prep_coordinates : ∀ a, (prep a : ℝ) = ![0,tilt estimate,1-tilt estimate] a := by",
                  "  intro a; fin_cases a <;> norm_num [prep, tilt, estimate, qEstimate, counts]",
                  "theorem weights_coordinates : ∀ t a, (weights t () a : ℝ) =",
                  "    if t.val+1<horizon then ![0,tilt estimate,1-tilt estimate] a else ![0,1/2,1/2] a := by",
                  "  intro t a", "  rw [weights_formula]", "  by_cases h : t.val+1<horizon",
                  "  · rw [if_pos h, if_pos h]; exact prep_coordinates a",
                  "  · rw [if_neg h, if_neg h]; fin_cases a <;> norm_num",
                  f"def beta : ℚ := {lean(proposal['beta_prep'])}",
                  "theorem budget_identity : budget estimate horizon = (beta : ℝ) := by",
                  "  norm_num [budget, prepBudget, estimate, qEstimate, counts, horizon, beta, Matrix.cons_val_two, Matrix.cons_val_three]",
                  "theorem accepted_threshold : (beta : ℝ) ≤ 1/5 := by norm_num [beta]", "",
                  "/-- The same literal preparation and weights, on every calibrated true source. -/",
                  "theorem returned_policy_actual_path (p : Param) (hb : Box p)",
                  "    (hg : Good p estimate (1/250)) :",
                  "    tvDist (literalDeployment p (box_admissible hb) prep prep_legal",
                  "      horizon weights weights_legal).toMeasure",
                  "      (actualConditionedPrefix (model p (box_admissible hb)) observe baseline initial",
                  "        FiniteDataConditioned.safe horizon 0",
                  "        (FiniteDataConditioned.source_positive p (box_admissible hb) horizon)).toMeasure ≤ (beta : ℝ) := by",
                  "  simpa only [budget_identity] using FiniteDataCertifiedConsumer.literal_statistical_certificate",
                  "    p (box_admissible hb) estimate estimate_legal prep prep_legal horizon (by decide)",
                  "    weights weights_legal prep_coordinates weights_coordinates hg", "",
                  "/-- Same bound for the full action/state record projected after preparation. -/",
                  "theorem returned_full_record_actual_path (p : Param) (hb : Box p)",
                  "    (hg : Good p estimate (1/250)) :",
                  "    tvDist ((fullLiteralExperiment p (box_admissible hb) prep prep_legal horizon weights weights_legal).map",
                  "      (postPreparationStateWindow horizon)).toMeasure",
                  "      (actualConditionedPrefix (model p (box_admissible hb)) observe baseline initial",
                  "        FiniteDataConditioned.safe horizon 0",
                  "        (FiniteDataConditioned.source_positive p (box_admissible hb) horizon)).toMeasure ≤ (beta : ℝ) := by",
                  "  simpa only [budget_identity] using FiniteDataCertifiedConsumer.full_record_statistical_certificate",
                  "    p (box_admissible hb) estimate estimate_legal prep prep_legal horizon (by decide)",
                  "    weights weights_legal prep_coordinates weights_coordinates hg"]
        lines += fine_reference(proposal)
    else:
        lines += [f"def lower : ℚ := {lean(proposal['failure_probability_lower'])}",
                  "theorem lower_identity : 1-(1-dataFailureFloor estimate.e0 estimate.e1)^horizon = (lower : ℝ) := by",
                  "  norm_num [dataFailureFloor, estimate, qEstimate, counts, horizon, lower, Matrix.cons_val_two, Matrix.cons_val_three]",
                  "theorem strict_obstacle : (1/5 : ℝ) < lower := by norm_num [lower]", "",
                  "/-- A statistical, Good-conditional obstacle; no hidden true value is read. -/",
                  "theorem statistical_no_go (p : Param) (hb : Box p)",
                  "    (hg : Good p estimate (1/250))",
                  "    (sigma : ∀ n, CausalHistory State State n → PMF Action) (p0 : PMF State) :",
                  "    (1/5 : ℝ) < tvDist (causalLaw p0",
                  "      (FiniteDataObstacles.allowedKernel p (box_admissible hb) sigma) horizon).toMeasure",
                  "      (actualConditionedPrefix (model p (box_admissible hb)) observe baseline initial",
                  "        FiniteDataConditioned.safe horizon 0",
                  "        (FiniteDataConditioned.source_positive p (box_admissible hb) horizon)).toMeasure := by",
                  "  rw [← FiniteDataConditioned.target_eq_actual p (box_admissible hb) horizon]",
                  "  have h := FiniteDataObstacles.statistical_path_floor p estimate hb hg sigma p0 horizon",
                  "  rw [lower_identity] at h", "  exact strict_obstacle.trans_le h"]
    lines += ["", "/-- Joint Accept∩Fail bound for the actual ideal training-selection-deployment law.",
              "It is not a conditional-on-acceptance or observed-Good assertion. -/",
              "theorem registered_training_joint_risk (p : Param) (hp : Admissible p) :",
              "    (FiniteDataJoint.jointLaw p hp horizon).toMeasure.real",
              "      {z | z.2 ∈ FiniteDataJoint.acceptedFailure z.1 horizon} ≤ 76/375 :=",
              "  FiniteDataJoint.registered_joint_failure_le p hp horizon (by decide)",
              "", "end", f"end {PREFIX}FiniteDataRuntimeCertificate", ""]
    return "\n".join(lines)
