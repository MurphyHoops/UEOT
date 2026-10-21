import SourcePolicyPathBridge
import UEOT.V3.QSDPerron

/-!
# Actual risk-path survival and the same-source killed matrix

PRIVATE CANDIDATE — actual compile status is recorded in separate receipts.
The imported private SourcePolicyPathBridge has a separate compile PASS.

The killed matrix is defined by restricting the existing policyMatrix of
the original model. The initial row is the actual initial PMF restricted
to the safe subtype, without normalization. Survival includes time zero.
There is no Nonempty assumption on the safe subtype, no positive survival
premise, and no assumed equality between independently supplied sources.

The two final theorems concern the actual action/state risk-path PMF.
They reuse the passed complete state-path pushforward theorem. All events
here are state-path events; arbitrary action-dependent events are outside
this erasure argument.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceKilledPathCheck

open MeasureTheory
open UEOT.V3.PathError
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.CoreOperationalAssembly
open UEOT.V3.QSDPerron
open SourcePolicyPathBridgeCheck
open scoped BigOperators Classical

noncomputable section

universe u

/-- The actual closed-loop matrix restricted to the safe subtype.
No renormalization is performed. -/
def killedMatrix
    {X A : Type u} [Fintype X] [Fintype A] [Nonempty A]
    (M : Model X (fun _ => A)) (pi : StationaryPolicy (fun _ : X => A))
    (K : Set X) : Matrix K K ℝ :=
  fun x y => policyMatrix M pi x.1 y.1

/-- Actual initial mass inside K. It need not have total mass one. -/
def safeInitialRow {X : Type u} (p0 : PMF X) (K : Set X) : K → ℝ :=
  fun x => (p0 x.1).toReal

/-- Every recorded state, including the initial state, lies in K. -/
def stateSurvives {X : Type u} (K : Set X) :
    ∀ n, CausalHistory X X n → Prop
  | 0, h => h ∈ K
  | n + 1, h => stateSurvives K n h.1 ∧ h.2 ∈ K

private theorem stateSurvives_current_mem
    {X : Type u} (K : Set X) (n : ℕ) (h : CausalHistory X X n)
    (hs : stateSurvives K n h) : currentState n h ∈ K := by
  cases n with
  | zero => exact hs
  | succ n => exact hs.2

/-- Unnormalized safe terminal mass of the existing pure-state path law. -/
def stateTerminalMass
    {X A : Type u} [Fintype X] [Fintype A] [Nonempty A]
    (M : Model X (fun _ => A)) (pi : StationaryPolicy (fun _ : X => A))
    (p0 : PMF X) (K : Set X) (n : ℕ) (v : K) : ℝ :=
  ∑ h : CausalHistory X X n,
    if stateSurvives K n h ∧ currentState n h = v.1 then
      (causalLaw p0 (policyPathKernel M pi) n h).toReal
    else 0

theorem killedMatrix_nonneg
    {X A : Type u} [Fintype X] [Fintype A] [Nonempty A]
    (M : Model X (fun _ => A)) (pi : StationaryPolicy (fun _ : X => A))
    (K : Set X) (x y : K) : 0 ≤ killedMatrix M pi K x y :=
  M.policyTransition_nonneg pi x.1 y.1

/-- Substochasticity is inherited from the original model and policy. -/
theorem killedMatrix_row_sum_le_one
    {X A : Type u} [Fintype X] [Fintype A] [Nonempty A]
    (M : Model X (fun _ => A)) (pi : StationaryPolicy (fun _ : X => A))
    (K : Set X) (x : K) : ∑ y : K, killedMatrix M pi K x y ≤ 1 := by
  classical
  change (∑ y : K, M.policyTransition pi x.1 y.1) ≤ 1
  calc
    (∑ y : K, M.policyTransition pi x.1 y.1) =
        ∑ y ∈ Finset.univ.filter (fun z : X => z ∈ K),
          M.policyTransition pi x.1 y := by
      exact (Finset.sum_subtype
        (Finset.univ.filter (fun z : X => z ∈ K))
        (by intro z; simp) (fun z => M.policyTransition pi x.1 z)).symm
    _ ≤ ∑ y : X, M.policyTransition pi x.1 y := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro y _ _
      exact M.policyTransition_nonneg pi x.1 y
    _ = 1 := M.policyTransition_sum_one pi x.1

/-! The next grouping identity has no probability assumptions. It merely
partitions a finite family of good histories by its final safe state. -/

private theorem sum_by_safe_last
    {H X : Type u} [Fintype H] [Fintype X]
    (K : Set X) (good : H → Prop) (last : H → X)
    (hgood : ∀ h, good h → last h ∈ K)
    (w : H → ℝ) (f : X → ℝ) :
    (∑ h : H, if good h then w h * f (last h) else 0) =
      ∑ v : K, (∑ h : H, if good h ∧ last h = v.1 then w h else 0) * f v.1 := by
  classical
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  by_cases hh : good h
  · let v : K := ⟨last h, hgood h hh⟩
    rw [if_pos hh, Finset.sum_eq_single v]
    · simp [hh, v]
    · intro z _ hz
      have hlast : last h ≠ z.1 := by
        intro heq
        apply hz
        exact Subtype.ext heq.symm
      simp [hh, hlast]
    · simp
  · simp [hh]

/-- One actual PMF extension gives the killed row recurrence. No conditional
probability or positive-history premise is used. -/
private theorem stateTerminalMass_succ
    {X A : Type u} [Fintype X] [Fintype A] [Nonempty A]
    (M : Model X (fun _ => A)) (pi : StationaryPolicy (fun _ : X => A))
    (p0 : PMF X) (K : Set X) (n : ℕ) (v : K) :
    stateTerminalMass M pi p0 K (n + 1) v =
      rowApply (stateTerminalMass M pi p0 K n) (killedMatrix M pi K) v := by
  classical
  let mu := causalLaw p0 (policyPathKernel M pi) n
  have hterminal (h : CausalHistory X X n) :
      (∑ z : X,
        if (stateSurvives K n h ∧ z ∈ K) ∧ z = v.1 then
          (mu h).toReal * (policyPathKernel M pi n h z).toReal
        else 0) =
      if stateSurvives K n h then
        (mu h).toReal * policyMatrix M pi (currentState n h) v.1
      else 0 := by
    rw [Finset.sum_eq_single v.1]
    · by_cases hs : stateSurvives K n h
      · simp [hs, v.property, policyPathKernel, policyMatrix,
          policyTransitionPMF_apply_toReal]
      · simp [hs]
    · intro z _ hz
      simp [hz]
    · simp
  calc
    stateTerminalMass M pi p0 K (n + 1) v =
        ∑ h : CausalHistory X X n, ∑ z : X,
          if (stateSurvives K n h ∧ z ∈ K) ∧ z = v.1 then
            (mu h).toReal * (policyPathKernel M pi n h z).toReal
          else 0 := by
      unfold stateTerminalMass
      change (∑ hz : CausalHistory X X n × X,
        if stateSurvives K (n + 1) hz ∧ currentState (n + 1) hz = v.1 then
          (causalLaw p0 (policyPathKernel M pi) (n + 1) hz).toReal else 0) = _
      simp only [stateSurvives, currentState, causalLaw]
      rw [← Finset.univ_product_univ, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro h _
      apply Finset.sum_congr rfl
      intro z _
      by_cases hh : (stateSurvives K n h ∧ z ∈ K) ∧ z = v.1
      · simp only [if_pos hh]
        simpa only [ENNReal.toReal_mul, mu] using
          congrArg ENNReal.toReal
            (UEOT.V3.PathError.pmfExtend_apply mu (policyPathKernel M pi n) h z)
      · simp only [if_neg hh]
    _ = ∑ h : CausalHistory X X n,
        if stateSurvives K n h then
          (mu h).toReal * policyMatrix M pi (currentState n h) v.1
        else 0 := by
      apply Finset.sum_congr rfl
      intro h _
      exact hterminal h
    _ = rowApply (stateTerminalMass M pi p0 K n) (killedMatrix M pi K) v := by
      simpa only [rowApply, stateTerminalMass, killedMatrix, mu] using
        sum_by_safe_last K (stateSurvives K n) (currentState n)
          (fun h hh => stateSurvives_current_mem K n h hh)
          (fun h => (mu h).toReal)
          (fun x => policyMatrix M pi x v.1)

/-- Finite pure-state survival/terminal mass equals the power of the actual
closed-loop matrix restricted to K. The theorem includes n = 0 and empty K. -/
theorem state_terminal_mass_eq_killed_pow
    {X A : Type u} [Fintype X] [Fintype A] [Nonempty A]
    (M : Model X (fun _ => A)) (pi : StationaryPolicy (fun _ : X => A))
    (p0 : PMF X) (K : Set X) :
    ∀ n (v : K), stateTerminalMass M pi p0 K n v =
      rowApply (safeInitialRow p0 K) ((killedMatrix M pi K) ^ n) v := by
  classical
  intro n
  induction n with
  | zero =>
      intro v
      calc
        stateTerminalMass M pi p0 K 0 v = (p0 v.1).toReal := by
          change (∑ x : X, if x ∈ K ∧ x = v.1 then (p0 x).toReal else 0) = _
          rw [Finset.sum_eq_single v.1]
          · simp [v.property]
          · intro x _ hx
            simp [hx]
          · simp
        _ = rowApply (safeInitialRow p0 K) ((killedMatrix M pi K) ^ 0) v := by
          simp [rowApply, Matrix.one_apply, safeInitialRow, mul_ite]
  | succ n ih =>
      intro v
      rw [stateTerminalMass_succ, pow_succ, rowApply_mul]
      unfold rowApply
      apply Finset.sum_congr rfl
      intro x _
      rw [ih x]
      rfl

private theorem sum_stateTerminalMass
    {X A : Type u} [Fintype X] [Fintype A] [Nonempty A]
    (M : Model X (fun _ => A)) (pi : StationaryPolicy (fun _ : X => A))
    (p0 : PMF X) (K : Set X) (n : ℕ) :
    (∑ h : CausalHistory X X n, if stateSurvives K n h then
      (causalLaw p0 (policyPathKernel M pi) n h).toReal else 0) =
      ∑ v : K, stateTerminalMass M pi p0 K n v := by
  simpa only [mul_one, stateTerminalMass] using
    sum_by_safe_last K (stateSurvives K n) (currentState n)
      (fun h hh => stateSurvives_current_mem K n h hh)
      (fun h => (causalLaw p0 (policyPathKernel M pi) n h).toReal)
      (fun _ => 1)

private theorem stateSurvives_erase_iff
    {X A : Type u} (K : Set X) :
    ∀ n (h : CausalHistory X (A × X) n),
      stateSurvives K n (eraseActionHistory n h) ↔
        ¬ riskEverFailure (fun x => x ∉ K) n h := by
  intro n
  induction n with
  | zero =>
      intro h
      change (h ∈ K) ↔ ¬ (h ∉ K)
      tauto
  | succ n ih =>
      intro h
      change (stateSurvives K n (eraseActionHistory n h.1) ∧ h.2.2 ∈ K) ↔
        ¬ (riskEverFailure (fun x => x ∉ K) n h.1 ∨ h.2.2 ∉ K)
      rw [ih h.1]
      tauto

private theorem currentState_erase
    {X A : Type u} (n : ℕ) (h : CausalHistory X (A × X) n) :
    currentState n (eraseActionHistory n h) = riskLastState n h := by
  cases n <;> rfl

private theorem finite_event_mass
    {S : Type u} [Fintype S]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (p : PMF S) (E : S → Prop) :
    p.toMeasure.real {x | E x} = ∑ x : S, if E x then (p x).toReal else 0 := by
  classical
  have hset : {x | E x} = (Finset.univ.filter E : Set S) := by
    ext x
    simp
  rw [hset, pmfMeasureReal_eq_sum_finset, Finset.sum_filter]

private theorem finite_map_event_mass
    {H S : Type u} [Fintype H] [Fintype S]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (p : PMF H) (f : H → S) (E : Set S) :
    (p.map f).toMeasure.real E = p.toMeasure.real (f ⁻¹' E) := by
  rw [← PMF.toMeasure_map f p (measurable_of_finite f)]
  simp only [Measure.real,
    Measure.map_apply (measurable_of_finite f) (Set.toFinite E).measurableSet]

/-- K1, joint form: the ORIGINAL action-record risk experiment stays in K
from time zero through n and finishes at v with exactly eta0 Q^n(v) mass.
The action-erased source identity is called internally, not assumed. -/
theorem actual_survival_terminal_mass_eq_killed_pow
    {X Y A : Type u} [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (M : Model X (fun _ => A)) (q : X → Y) (sigma : Y → PMF A)
    (p0 : PMF X) (K : Set X) (n : ℕ) (v : K) :
    (causalLaw p0 (riskMicroControlKernel q (fun _ => M.transitionPMF)
      (observationMarkovPolicy sigma)) n).toMeasure.real
        {h | ¬ riskEverFailure (fun x => x ∉ K) n h ∧ riskLastState n h = v.1} =
      rowApply (safeInitialRow p0 K)
        ((killedMatrix M (liftedStationaryPolicy q sigma) K) ^ n) v := by
  let mu := causalLaw p0 (riskMicroControlKernel q (fun _ => M.transitionPMF)
    (observationMarkovPolicy sigma)) n
  let E : Set (CausalHistory X X n) :=
    {h | stateSurvives K n h ∧ currentState n h = v.1}
  have hevent : (eraseActionHistory (X := X) (A := A) n) ⁻¹' E =
      {h | ¬ riskEverFailure (fun x => x ∉ K) n h ∧ riskLastState n h = v.1} := by
    ext h
    simp only [E, Set.mem_preimage, Set.mem_setOf_eq,
      stateSurvives_erase_iff, currentState_erase]
  have hpush : mu.map (eraseActionHistory n) =
      causalLaw p0 (policyPathKernel M (liftedStationaryPolicy q sigma)) n :=
    actual_state_path_eq_stationary_path M q sigma p0 n
  calc
    mu.toMeasure.real
        {h | ¬ riskEverFailure (fun x => x ∉ K) n h ∧ riskLastState n h = v.1} =
        (mu.map (eraseActionHistory n)).toMeasure.real E := by
      rw [finite_map_event_mass, hevent]
    _ = (causalLaw p0 (policyPathKernel M (liftedStationaryPolicy q sigma)) n).toMeasure.real E := by
      rw [hpush]
    _ = stateTerminalMass M (liftedStationaryPolicy q sigma) p0 K n v := by
      dsimp only [E]
      rw [finite_event_mass]
      unfold stateTerminalMass
      apply Finset.sum_congr rfl
      intro h _
      by_cases hh : stateSurvives K n h ∧ currentState n h = v.1
      · simp only [if_pos hh]
      · simp only [if_neg hh]
    _ = _ := state_terminal_mass_eq_killed_pow M (liftedStationaryPolicy q sigma) p0 K n v

/-- K1, total form. This includes p0 mass outside K and the empty safe set;
there is no normalization, division, QSD or positive survival assumption. -/
theorem actual_survival_mass_eq_killed_pow_sum
    {X Y A : Type u} [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (M : Model X (fun _ => A)) (q : X → Y) (sigma : Y → PMF A)
    (p0 : PMF X) (K : Set X) (n : ℕ) :
    (causalLaw p0 (riskMicroControlKernel q (fun _ => M.transitionPMF)
      (observationMarkovPolicy sigma)) n).toMeasure.real
        {h | ¬ riskEverFailure (fun x => x ∉ K) n h} =
      ∑ v : K, rowApply (safeInitialRow p0 K)
        ((killedMatrix M (liftedStationaryPolicy q sigma) K) ^ n) v := by
  let mu := causalLaw p0 (riskMicroControlKernel q (fun _ => M.transitionPMF)
    (observationMarkovPolicy sigma)) n
  let E : Set (CausalHistory X X n) := {h | stateSurvives K n h}
  have hevent : (eraseActionHistory (X := X) (A := A) n) ⁻¹' E =
      {h | ¬ riskEverFailure (fun x => x ∉ K) n h} := by
    ext h
    simp only [E, Set.mem_preimage, Set.mem_setOf_eq, stateSurvives_erase_iff]
  have hpush : mu.map (eraseActionHistory n) =
      causalLaw p0 (policyPathKernel M (liftedStationaryPolicy q sigma)) n :=
    actual_state_path_eq_stationary_path M q sigma p0 n
  calc
    mu.toMeasure.real {h | ¬ riskEverFailure (fun x => x ∉ K) n h} =
        (mu.map (eraseActionHistory n)).toMeasure.real E := by
      rw [finite_map_event_mass, hevent]
    _ = (causalLaw p0 (policyPathKernel M (liftedStationaryPolicy q sigma)) n).toMeasure.real E := by
      rw [hpush]
    _ = ∑ h : CausalHistory X X n, if stateSurvives K n h then
        (causalLaw p0 (policyPathKernel M (liftedStationaryPolicy q sigma)) n h).toReal
        else 0 := by
      exact finite_event_mass
        (causalLaw p0 (policyPathKernel M (liftedStationaryPolicy q sigma)) n)
        (stateSurvives K n)
    _ = ∑ v : K, stateTerminalMass M (liftedStationaryPolicy q sigma) p0 K n v :=
      sum_stateTerminalMass M (liftedStationaryPolicy q sigma) p0 K n
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v _
      exact state_terminal_mass_eq_killed_pow M (liftedStationaryPolicy q sigma) p0 K n v

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceKilledPathCheck

#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceKilledPathCheck.actual_survival_terminal_mass_eq_killed_pow
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceKilledPathCheck.actual_survival_mass_eq_killed_pow_sum
