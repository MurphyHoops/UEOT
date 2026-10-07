import UEOT.V3.Compression.Objecthood.ResourceClosure.MeanResourceClosure

/-!
# Theory Completion P6.3 — finite-horizon reserve and replenishment closure

The RH/P5 occupation budget naturally splits into a transient term and a steady
load.  P6 turns that split into an explicit accounting theorem:

* initial reserve covers the transient `V0 / kappa` resource debt;
* constant replenishment covers baseline maintenance plus the steady damaged-
  occupation load `lambda / kappa`;
* the conclusion is viability of the deterministic schedule of **expected**
  P5 state costs.

This is stronger than an asymptotic mean statement but still is not a realized
pathwise-stock theorem.
-/

namespace UEOT.V3.Compression.Objecthood.ResourceClosure

open Set Filter Topology MeasureTheory ProbabilityTheory
open UEOT.V3.ViabilityKernel
open UEOT.V3.Compression.Objecthood
open UEOT.V3.Compression.Objecthood.JointHomeostasis
open UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
open scoped ENNReal BigOperators

universe uX uA uP uR
noncomputable section

/-- Finite-horizon sum of the damaged-mass resource envelope. -/
noncomputable def ResourceCostModel.cumulativeExpectedCostEnvelope
    (C : ResourceCostModel) (D : ℕ → ENNReal) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N,
    (C.maintenance + C.variableCost * (D n).toReal)

/-- Any actual expected-cost sequence dominated pointwise by the envelope is
also dominated cumulatively. -/
theorem ResourceCostModel.cumulativeActualCost_le_envelope
    (C : ResourceCostModel)
    (actual : ℕ → ℝ) (D : ℕ → ENNReal)
    (hactual : ∀ n,
      actual n ≤ C.maintenance + C.variableCost * (D n).toReal)
    (N : ℕ) :
    (∑ n ∈ Finset.range N, actual n) ≤
      C.cumulativeExpectedCostEnvelope D N := by
  unfold ResourceCostModel.cumulativeExpectedCostEnvelope
  exact Finset.sum_le_sum fun n hn => hactual n

/-- Generic RH occupation budget → finite-horizon resource envelope.

The transient term is `variableCost * V0/kappa`; the steady term is
`maintenance + variableCost * lambda/kappa`. -/
theorem ResourceCostModel.cumulativeExpectedCostEnvelope_le_transient_add_steady
    (C : ResourceCostModel)
    (D : ℕ → ENNReal) (kappa lambda V0 : ENNReal)
    (hDtop : ∀ n, D n ≠ ∞)
    (hk0 : kappa ≠ 0) (hktop : kappa ≠ ∞)
    (hlamtop : lambda ≠ ∞) (hVtop : V0 ≠ ∞)
    (N : ℕ) (hN : 0 < N)
    (hbound : kappa * (∑ n ∈ Finset.range N, D n) ≤
      V0 + (N : ENNReal) * lambda) :
    C.cumulativeExpectedCostEnvelope D N ≤
      C.variableCost * (V0.toReal / kappa.toReal) +
        (N : ℝ) *
          (C.maintenance +
            C.variableCost * (lambda.toReal / kappa.toReal)) := by
  have havg := real_average_bound_of_ennreal_homeostatic_budget
    D kappa lambda V0 hDtop hk0 hktop hlamtop hVtop N hN hbound
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hmul := mul_le_mul_of_nonneg_left havg (le_of_lt hNreal)
  field_simp at hmul
  have hkpos : 0 < kappa.toReal := ENNReal.toReal_pos hk0 hktop
  have hsum :
      (∑ n ∈ Finset.range N, (D n).toReal) ≤
        V0.toReal / kappa.toReal +
          (N : ℝ) * (lambda.toReal / kappa.toReal) := by
    calc
      (∑ n ∈ Finset.range N, (D n).toReal)
          ≤ (V0.toReal + (N : ℝ) * lambda.toReal) / kappa.toReal := by
            simpa using hmul
      _ = V0.toReal / kappa.toReal +
          (N : ℝ) * (lambda.toReal / kappa.toReal) := by
            field_simp [ne_of_gt hkpos]
  unfold ResourceCostModel.cumulativeExpectedCostEnvelope
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  have hscaled := mul_le_mul_of_nonneg_left hsum C.variableCost_nonneg
  nlinarith

/-- P5 actual expected-cost sequence accumulated through horizon `N` is bounded
by the RH transient+steady resource envelope. -/
theorem finiteJoint_cumulativeActualResourceCost_le_transient_add_steady
    {X : Type uX} {A : Type uA}
    {Program : Type uP} {Representation : Type uR}
    [Fintype X] [Fintype A] [Nonempty A] [Fintype Representation]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    (R : PhysicalRepairCertificate P K)
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (r : Program)
    (himpl : RepairProgramDynamicsImplementsPolicy T P r
      (repairThenPreservePolicy P K hfix R.repairPolicy))
    (F : RepairOrganizationState X A Representation →
      PMF (RepairOrganizationState X A Representation))
    (epsilon : NNReal) (hepsilon : epsilon ≤ 1)
    (hF : FiniteJointFaultEnvelope P K R T codec r F)
    (mu0 : PMF (RepairOrganizationState X A Representation))
    (hmu0 : StaysIn mu0 (finiteJointRepairCarrier P K R T codec r))
    (hhazard : epsilon < 1)
    (C : ResourceCostModel)
    (N : ℕ) (hN : 0 < N) :
    let S := finiteJointRecurrentHomeostasisSystem
      P K hfix R T codec r himpl F epsilon hepsilon hF
    let actual : ℕ → ℝ := fun n =>
      pmfRealExpectation (homeostaticMarginal S.mixedKernel mu0 n)
        (stateResourceCost C
          (fun s => s ∈ jointLegitimate T codec K r)
          (jointProgramMismatch T codec r))
    let kappa : ENNReal :=
      ((1 - epsilon : NNReal) : ENNReal) * S.repairDrift
    let lambda : ENNReal :=
      (epsilon : ENNReal) * canonicalFaultBurden S
    let V0 : ENNReal := homeostaticENNExpectation mu0 S.potential
    (∑ n ∈ Finset.range N, actual n) ≤
      C.variableCost * (V0.toReal / kappa.toReal) +
        (N : ℝ) *
          (C.maintenance + C.variableCost * (lambda.toReal / kappa.toReal)) := by
  dsimp only
  let S := finiteJointRecurrentHomeostasisSystem
    P K hfix R T codec r himpl F epsilon hepsilon hF
  let D : ℕ → ENNReal := fun n =>
    (homeostaticMarginal S.mixedKernel mu0 n).toMeasure S.legitimateᶜ
  let actual : ℕ → ℝ := fun n =>
    pmfRealExpectation (homeostaticMarginal S.mixedKernel mu0 n)
      (stateResourceCost C
        (fun s => s ∈ jointLegitimate T codec K r)
        (jointProgramMismatch T codec r))
  let kappa : ENNReal :=
    ((1 - epsilon : NNReal) : ENNReal) * S.repairDrift
  let lambda : ENNReal := (epsilon : ENNReal) * canonicalFaultBurden S
  let V0 : ENNReal := homeostaticENNExpectation mu0 S.potential
  have hactual : ∀ n,
      actual n ≤ C.maintenance + C.variableCost * (D n).toReal := by
    intro n
    have h := p5_pmfRealExpectation_stateResourceCost_le
      C T codec K r (homeostaticMarginal S.mixedKernel mu0 n)
    change actual n ≤ C.maintenance + C.variableCost * (D n).toReal
    change actual n ≤ C.maintenance + C.variableCost * (D n).toReal at h
    exact h
  have hsubpos : 0 < (1 - epsilon : NNReal) := tsub_pos_iff_lt.mpr hhazard
  have hsub0 : ((1 - epsilon : NNReal) : ENNReal) ≠ 0 := by
    exact_mod_cast (ne_of_gt hsubpos)
  have hk0 : kappa ≠ 0 := mul_ne_zero hsub0 S.repairDrift_ne_zero
  have hktop : kappa ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) S.repairDrift_ne_top
  have hpotfin := finiteJointRecurrentHomeostasisSystem_potential_ne_top
    P K hfix R T codec r himpl F epsilon hepsilon hF
  have hlamtop : lambda ≠ ∞ := by
    exact ENNReal.mul_ne_top (by simp)
      (canonicalFaultBurden_ne_top_of_carrierPotentialFinite S hpotfin)
  have hVtop : V0 ≠ ∞ := by
    exact homeostaticENNExpectation_ne_top_of_staysIn
      mu0 S.carrier S.potential hmu0 hpotfin
  have hDtop : ∀ n, D n ≠ ∞ := by
    intro n
    exact MeasureTheory.measure_ne_top _ _
  have hbudget : kappa * (∑ n ∈ Finset.range N, D n) ≤
      V0 + (N : ENNReal) * lambda := by
    simpa [S, D, kappa, lambda, V0] using
      finiteJoint_finiteHorizonDamagedOccupation
        P K hfix R T codec r himpl F epsilon hepsilon hF mu0 hmu0 N
  exact (C.cumulativeActualCost_le_envelope actual D hactual N).trans
    (C.cumulativeExpectedCostEnvelope_le_transient_add_steady
      D kappa lambda V0 hDtop hk0 hktop hlamtop hVtop N hN hbudget)

/-- P6 expected-accounting viability for the P5 joint system.

Initial reserve covers the transient RH debt; constant replenishment covers the
steady maintenance+damage load.  The schedule being paid is the actual expected
state cost at each P5 marginal. -/
theorem finiteJoint_expectedAccountingResourceViable
    {X : Type uX} {A : Type uA}
    {Program : Type uP} {Representation : Type uR}
    [Fintype X] [Fintype A] [Nonempty A] [Fintype Representation]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    (R : PhysicalRepairCertificate P K)
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (r : Program)
    (himpl : RepairProgramDynamicsImplementsPolicy T P r
      (repairThenPreservePolicy P K hfix R.repairPolicy))
    (F : RepairOrganizationState X A Representation →
      PMF (RepairOrganizationState X A Representation))
    (epsilon : NNReal) (hepsilon : epsilon ≤ 1)
    (hF : FiniteJointFaultEnvelope P K R T codec r F)
    (mu0 : PMF (RepairOrganizationState X A Representation))
    (hmu0 : StaysIn mu0 (finiteJointRepairCarrier P K R T codec r))
    (hhazard : epsilon < 1)
    (C : ResourceCostModel) (initial supply : ℝ)
    (hreserve :
      let S := finiteJointRecurrentHomeostasisSystem
        P K hfix R T codec r himpl F epsilon hepsilon hF
      let kappa : ENNReal :=
        ((1 - epsilon : NNReal) : ENNReal) * S.repairDrift
      let V0 := homeostaticENNExpectation mu0 S.potential
      C.variableCost * (V0.toReal / kappa.toReal) ≤ initial)
    (hsupply :
      let S := finiteJointRecurrentHomeostasisSystem
        P K hfix R T codec r himpl F epsilon hepsilon hF
      let kappa : ENNReal :=
        ((1 - epsilon : NNReal) : ENNReal) * S.repairDrift
      let lambda : ENNReal :=
        (epsilon : ENNReal) * canonicalFaultBurden S
      C.maintenance + C.variableCost * (lambda.toReal / kappa.toReal) ≤ supply) :
    let S := finiteJointRecurrentHomeostasisSystem
      P K hfix R T codec r himpl F epsilon hepsilon hF
    let actual : ℕ → ℝ := fun n =>
      pmfRealExpectation (homeostaticMarginal S.mixedKernel mu0 n)
        (stateResourceCost C
          (fun s => s ∈ jointLegitimate T codec K r)
          (jointProgramMismatch T codec r))
    ResourceViable initial (fun _ => supply) actual := by
  dsimp only
  let S := finiteJointRecurrentHomeostasisSystem
    P K hfix R T codec r himpl F epsilon hepsilon hF
  let actual : ℕ → ℝ := fun n =>
    pmfRealExpectation (homeostaticMarginal S.mixedKernel mu0 n)
      (stateResourceCost C
        (fun s => s ∈ jointLegitimate T codec K r)
        (jointProgramMismatch T codec r))
  intro N
  by_cases hN0 : N = 0
  · subst N
    unfold cumulativeResourceBalance
    simp
    have hnonneg : 0 ≤ initial := by
      let kappa : ENNReal :=
        ((1 - epsilon : NNReal) : ENNReal) * S.repairDrift
      let V0 : ENNReal := homeostaticENNExpectation mu0 S.potential
      have hterm : 0 ≤ C.variableCost * (V0.toReal / kappa.toReal) := by
        exact mul_nonneg C.variableCost_nonneg
          (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      exact hterm.trans (by simpa [S, kappa, V0] using hreserve)
    exact hnonneg
  · have hN : 0 < N := Nat.pos_of_ne_zero hN0
    have hcost := finiteJoint_cumulativeActualResourceCost_le_transient_add_steady
      P K hfix R T codec r himpl F epsilon hepsilon hF
      mu0 hmu0 hhazard C N hN
    let kappa : ENNReal :=
      ((1 - epsilon : NNReal) : ENNReal) * S.repairDrift
    let lambda : ENNReal := (epsilon : ENNReal) * canonicalFaultBurden S
    let V0 : ENNReal := homeostaticENNExpectation mu0 S.potential
    have hreserve' : C.variableCost * (V0.toReal / kappa.toReal) ≤ initial := by
      simpa [S, kappa, V0] using hreserve
    have hsupply' :
        C.maintenance + C.variableCost * (lambda.toReal / kappa.toReal) ≤ supply := by
      simpa [S, kappa, lambda] using hsupply
    have hsteady := mul_le_mul_of_nonneg_left hsupply' (by positivity : 0 ≤ (N : ℝ))
    unfold cumulativeResourceBalance
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    linarith

end
end UEOT.V3.Compression.Objecthood.ResourceClosure
