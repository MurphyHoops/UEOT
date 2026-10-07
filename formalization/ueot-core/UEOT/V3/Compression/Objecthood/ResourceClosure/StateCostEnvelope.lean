import UEOT.V3.Compression.Objecthood.ResourceClosure.ResourceAccounting

/-!
# Theory Completion P6.1 — state-level resource-cost envelope

P6 does not decree a physical energy for an Objecthood state.  Instead this
module supplies one minimal finite-state accounting adapter:

* baseline maintenance is always charged;
* repair surcharge is charged outside declared legitimacy;
* reconstruction surcharge is charged on a separately declared program-
  organization mismatch predicate.

If every program mismatch is also a damaged state, expected actual cost is
bounded by baseline maintenance plus the combined damaged-state surcharge times
P5 damaged probability.
-/

namespace UEOT.V3.Compression.Objecthood.ResourceClosure

open Set MeasureTheory
open UEOT.V3.Compression.Objecthood
open UEOT.V3.Compression.Objecthood.JointHomeostasis
open UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
open scoped ENNReal BigOperators

universe uZ uX uA uP uR
noncomputable section

/-- Real-valued indicator used only for accounting, not for probability-law
construction. -/
noncomputable def realIndicator (p : Prop) : ℝ := by
  classical
  exact if p then 1 else 0

/-- Concrete state-level accounting cost from one validity predicate and one
program-reconstruction predicate. -/
noncomputable def stateResourceCost
    {Z : Type uZ}
    (C : ResourceCostModel)
    (legitimate programMismatch : Z → Prop)
    (z : Z) : ℝ := by
  classical
  exact C.maintenance +
    C.repair * realIndicator (¬ legitimate z) +
    C.reconstruction * realIndicator (programMismatch z)

/-- Finite PMF expectation in real accounting units. -/
noncomputable def pmfRealExpectation
    {Z : Type uZ} [Fintype Z]
    (mu : PMF Z) (f : Z → ℝ) : ℝ :=
  ∑ z, (mu z).toReal * f z

theorem pmf_toReal_sum_eq_one
    {Z : Type uZ} [Fintype Z]
    (mu : PMF Z) :
    (∑ z, (mu z).toReal) = 1 := by
  have h := congrArg ENNReal.toReal (PMF.tsum_coe mu)
  rw [tsum_fintype,
    ENNReal.toReal_sum (fun z _ => PMF.apply_ne_top mu z)] at h
  simpa using h

/-- Real damaged mass represented as a finite PMF sum. -/
noncomputable def realDamagedMass
    {Z : Type uZ} [Fintype Z]
    (mu : PMF Z) (legitimate : Set Z) : ℝ := by
  classical
  exact ∑ z, (mu z).toReal * realIndicator (z ∉ legitimate)

/-- The finite-sum damaged mass is exactly the ordinary PMF measure of the
complement. -/
theorem realDamagedMass_eq_measureReal_compl
    {Z : Type uZ} [Fintype Z]
    [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (mu : PMF Z) (legitimate : Set Z) :
    realDamagedMass mu legitimate =
      mu.toMeasure.real legitimateᶜ := by
  classical
  unfold realDamagedMass realIndicator
  rw [measureReal_def, PMF.toMeasure_apply_fintype]
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro z hz
    by_cases hL : z ∈ legitimate
    · simp [hL]
    · simp [hL]
  · intro z hz
    by_cases hL : z ∈ legitimate
    · simp [hL]
    · simpa [hL] using PMF.apply_ne_top mu z

/-- If every reconstruction mismatch is also outside legitimacy, the full
state-level cost is pointwise bounded by one damaged-state surcharge envelope. -/
theorem stateResourceCost_le_damageEnvelope
    {Z : Type uZ}
    (C : ResourceCostModel)
    (legitimate programMismatch : Z → Prop)
    (hmismatch : ∀ z, programMismatch z → ¬ legitimate z)
    (z : Z) :
    stateResourceCost C legitimate programMismatch z ≤
      C.maintenance + C.variableCost * realIndicator (¬ legitimate z) := by
  classical
  by_cases hleg : legitimate z
  · have hnomis : ¬ programMismatch z := by
      intro hm
      exact hmismatch z hm hleg
    simp [stateResourceCost, realIndicator, hleg, hnomis,
      ResourceCostModel.variableCost]
  · by_cases hmis : programMismatch z
    · simp [stateResourceCost, realIndicator, hleg, hmis,
        ResourceCostModel.variableCost, add_assoc]
    · simp [stateResourceCost, realIndicator, hleg, hmis,
        ResourceCostModel.variableCost]
      exact C.reconstruction_nonneg

/-- Expected actual state cost is bounded by baseline maintenance plus the
combined repair/reconstruction surcharge times damaged probability. -/
theorem pmfRealExpectation_stateResourceCost_le
    {Z : Type uZ} [Fintype Z]
    [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (C : ResourceCostModel)
    (L : Set Z) (programMismatch : Z → Prop)
    (hmismatch : ∀ z, programMismatch z → z ∉ L)
    (mu : PMF Z) :
    pmfRealExpectation mu (stateResourceCost C (fun z => z ∈ L) programMismatch) ≤
      C.maintenance + C.variableCost * mu.toMeasure.real Lᶜ := by
  classical
  have hpoint : ∀ z,
      stateResourceCost C (fun z => z ∈ L) programMismatch z ≤
        C.maintenance + C.variableCost * realIndicator (z ∉ L) := by
    intro z
    exact stateResourceCost_le_damageEnvelope C (fun z => z ∈ L)
      programMismatch hmismatch z
  have hsum :
      (∑ z, (mu z).toReal *
        stateResourceCost C (fun z => z ∈ L) programMismatch z) ≤
      ∑ z, (mu z).toReal *
        (C.maintenance + C.variableCost * realIndicator (z ∉ L)) := by
    apply Finset.sum_le_sum
    intro z hz
    exact mul_le_mul_of_nonneg_left (hpoint z) ENNReal.toReal_nonneg
  have hweight : (∑ z, (mu z).toReal) = 1 := pmf_toReal_sum_eq_one mu
  have hdam :
      (∑ z, (mu z).toReal * realIndicator (z ∉ L)) =
        mu.toMeasure.real Lᶜ := by
    simpa [realDamagedMass] using realDamagedMass_eq_measureReal_compl mu L
  have hrhs :
      (∑ z, (mu z).toReal *
        (C.maintenance + C.variableCost * realIndicator (z ∉ L))) =
      C.maintenance + C.variableCost * mu.toMeasure.real Lᶜ := by
    calc
      (∑ z, (mu z).toReal *
          (C.maintenance + C.variableCost * realIndicator (z ∉ L))) =
          (∑ z, (mu z).toReal * C.maintenance) +
            ∑ z, (mu z).toReal *
              (C.variableCost * realIndicator (z ∉ L)) := by
                rw [← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro z hz
                ring
      _ = C.maintenance * (∑ z, (mu z).toReal) +
          C.variableCost *
            (∑ z, (mu z).toReal * realIndicator (z ∉ L)) := by
            congr 1
            · rw [mul_comm C.maintenance]
              rw [Finset.sum_mul]
            · rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro z hz
              ring
      _ = C.maintenance + C.variableCost * mu.toMeasure.real Lᶜ := by
            rw [hweight, hdam]
            ring
  unfold pmfRealExpectation
  rw [hrhs] at hsum
  exact hsum

/-- P5-specific reconstruction mismatch: the stored controller/program
organization is not the canonical organization generated by the intended
internal repair program. -/
def jointProgramMismatch
    {X : Type uX} {A : Type uA}
    {Program : Type uP} {Representation : Type uR}
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (r : Program)
    (s : RepairOrganizationState X A Representation) : Prop :=
  ¬ CanonicalProgramOrganization T codec r s

/-- Exact same-program P5 legitimacy implies canonical organization; hence a
program-organization mismatch is necessarily a P5 damaged state. -/
theorem jointProgramMismatch_not_jointLegitimate
    {X : Type uX} {A : Type uA}
    {Program : Type uP} {Representation : Type uR}
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (K : Set X) (r : Program)
    (s : RepairOrganizationState X A Representation) :
    jointProgramMismatch T codec r s → s ∉ jointLegitimate T codec K r := by
  intro hmis hleg
  rcases hleg with ⟨x, _hxK, rfl⟩
  apply hmis
  unfold CanonicalProgramOrganization canonicalRepairOrganizationState
  rfl

/-- Concrete P5 state-cost expectation bound. -/
theorem p5_pmfRealExpectation_stateResourceCost_le
    {X : Type uX} {A : Type uA}
    {Program : Type uP} {Representation : Type uR}
    [Fintype X] [Fintype A] [Fintype Representation]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (C : ResourceCostModel)
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (K : Set X) (r : Program)
    (mu : PMF (RepairOrganizationState X A Representation)) :
    pmfRealExpectation mu
        (stateResourceCost C
          (fun s => s ∈ jointLegitimate T codec K r)
          (jointProgramMismatch T codec r)) ≤
      C.maintenance + C.variableCost *
        mu.toMeasure.real (jointLegitimate T codec K r)ᶜ := by
  exact pmfRealExpectation_stateResourceCost_le
    C (jointLegitimate T codec K r) (jointProgramMismatch T codec r)
    (fun s => jointProgramMismatch_not_jointLegitimate T codec K r s) mu

end
end UEOT.V3.Compression.Objecthood.ResourceClosure
