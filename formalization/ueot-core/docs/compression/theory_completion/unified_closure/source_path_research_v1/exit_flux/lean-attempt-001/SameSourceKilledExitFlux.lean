import SameSourceKilledPath

/-!
PRIVATE FINITE-WINDOW SOURCE BRIDGE — NOT A PRODUCTION MODULE.

The original static draft and contract are preserved separately. Actual
focused compilation status is recorded in the attempt receipts, not certified
by this source banner.

The source is the same model, initial PMF, observation map and stationary
current-observation policy as K1. The prefix identity is proved below
from pmfExtend's actual bind/map construction; it is not an assumption.

The first-exit event excludes initial failure. The final decomposition
keeps initial failure separately. Empty K and horizon zero are included.
This file contains no infinite-path assertion, Perron assumption,
positive-survival condition, normalization of the safe initial row,
or new axiom/admitted proof.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceKilledExitFluxCheck

open MeasureTheory
open UEOT.V3.PathError
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.CoreOperationalAssembly
open UEOT.V3.QSDPerron
open SourcePolicyPathBridgeCheck SameSourceKilledPathCheck
open scoped BigOperators Classical

noncomputable section
universe u

/-! ## Actual causal-prefix consistency: no model-specific premise -/

/-- Dropping the freshly sampled record recovers the actual input PMF. -/
theorem pmfExtend_map_fst
    {H Z : Type*} (p : PMF H) (L : H → PMF Z) :
    (pmfExtend p L).map Prod.fst = p := by
  unfold pmfExtend
  rw [PMF.map_bind]
  simp_rw [PMF.map_comp]
  change p.bind (fun h => (L h).map (Function.const Z h)) = p
  simp only [PMF.map_const, PMF.bind_pure]

/-- The two finite laws are coherent because they use the same recursion.
This lemma even permits a general history-dependent next-record family. -/
theorem causalLaw_map_prefix
    {H Z : Type u} (p0 : PMF H)
    (L : ∀ n, CausalHistory H Z n → PMF Z) (n : ℕ) :
    (causalLaw p0 L (n + 1)).map
        (fun h : CausalHistory H Z (n + 1) => h.1) = causalLaw p0 L n := by
  change (pmfExtend (causalLaw p0 L n) (L n)).map Prod.fst = _
  exact pmfExtend_map_fst (causalLaw p0 L n) (L n)

/-- Every actual finite prefix event has the same mass before and after
one PMF extension. The equality is derived, never an input hypothesis. -/
theorem causalLaw_prefix_event_real
    {H Z : Type u} [Fintype H] [Fintype Z]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (p0 : PMF H) (L : ∀ n, CausalHistory H Z n → PMF Z)
    (n : ℕ) (E : Set (CausalHistory H Z n)) :
    (causalLaw p0 L (n + 1)).toMeasure.real
        ((fun h : CausalHistory H Z (n + 1) => h.1) ⁻¹' E) =
      (causalLaw p0 L n).toMeasure.real E := by
  have hm := PMF.toMeasure_map_apply
    (fun h : CausalHistory H Z (n + 1) => h.1)
    (causalLaw p0 L (n + 1)) E
    (measurable_of_finite _) (Set.toFinite E).measurableSet
  rw [causalLaw_map_prefix] at hm
  simpa only [Measure.real] using congrArg ENNReal.toReal hm.symm

/-! ## The small finite algebra layer -/

/-- The outflow of an unnormalized row through the row deficits of Q. -/
def killedExitFlux {S : Type u} [Fintype S]
    (eta : S → ℝ) (Q : Matrix S S ℝ) : ℝ :=
  ∑ u, eta u * (1 - ∑ v, Q u v)

/-- Algebra valid for every finite real row and matrix. Probability
meaning is supplied only by the actual-source theorems below. -/
theorem row_mass_sub_next_eq_killedExitFlux
    {S : Type u} [Fintype S] (eta : S → ℝ) (Q : Matrix S S ℝ) :
    (∑ u, eta u) - (∑ v, rowApply eta Q v) = killedExitFlux eta Q := by
  have hsum : (∑ v, rowApply eta Q v) = ∑ u, eta u * (∑ v, Q u v) := by
    unfold rowApply
    rw [Finset.sum_comm]
    simp_rw [Finset.mul_sum]
  rw [hsum, ← Finset.sum_sub_distrib]
  unfold killedExitFlux
  apply Finset.sum_congr rfl
  intro u _
  ring

/-- One finite matrix-power step loses exactly the stated row-deficit mass. -/
theorem killed_pow_mass_drop
    {S : Type u} [Fintype S] (eta0 : S → ℝ) (Q : Matrix S S ℝ) (n : ℕ) :
    (∑ u, rowApply eta0 (Q ^ n) u) -
        (∑ v, rowApply eta0 (Q ^ (n + 1)) v) =
      killedExitFlux (rowApply eta0 (Q ^ n)) Q := by
  rw [pow_succ, rowApply_mul]
  exact row_mass_sub_next_eq_killedExitFlux (rowApply eta0 (Q ^ n)) Q

/-! ## First exit in the original action/state record -/

/-- Safe at all times 0,...,n and first outside K at time n+1.
An initially unsafe path never belongs to one of these positive-time exits. -/
def riskFirstExitAfter {X A : Type u} (K : Set X) (n : ℕ) :
    Set (CausalHistory X (A × X) (n + 1)) :=
  {h | ¬ riskEverFailure (fun x => x ∉ K) n h.1 ∧ h.2.2 ∉ K}

section ActualSource

variable {X Y A : Type u} [Fintype X] [Fintype A] [Nonempty A]
variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace A] [MeasurableSingletonClass A]
variable (M : Model X (fun _ => A)) (q : X → Y) (sigma : Y → PMF A)
variable (p0 : PMF X) (K : Set X)

local notation "L" => riskMicroControlKernel q (fun _ => M.transitionPMF)
  (observationMarkovPolicy sigma)
local notation "nu" => causalLaw p0 L
local notation "Q" => killedMatrix M (liftedStationaryPolicy q sigma) K
local notation "eta0" => safeInitialRow p0 K
local notation "s" => (fun n => Measure.real (PMF.toMeasure (nu n))
  (Set.ofPred (fun h => ¬ riskEverFailure (fun x => x ∉ K) n h)))
local notation "flux" => (fun n => killedExitFlux (rowApply eta0 (Q ^ n)) Q)

/-- K1 followed by the small algebra lemma gives the actual survival drop. -/
theorem actual_survival_drop_eq_killedExitFlux (n : ℕ) :
    s n - s (n + 1) = flux n := by
  rw [actual_survival_mass_eq_killed_pow_sum,
    actual_survival_mass_eq_killed_pow_sum]
  exact killed_pow_mass_drop eta0 Q n

/-- The drop is the mass of an event in the SAME actual (n+1)-step law.
Prefix coherence is proved from causalLaw, not supplied as a hypothesis. -/
theorem actual_first_exit_mass_eq_survival_drop (n : ℕ) :
    (nu (n + 1)).toMeasure.real (riskFirstExitAfter (A := A) K n) =
      s n - s (n + 1) := by
  classical
  let prefix : Set (CausalHistory X (A × X) (n + 1)) :=
    {h | ¬ riskEverFailure (fun x => x ∉ K) n h.1}
  let stay : Set (CausalHistory X (A × X) (n + 1)) :=
    {h | ¬ riskEverFailure (fun x => x ∉ K) (n + 1) h}
  let leave := riskFirstExitAfter (A := A) K n
  have hsplit : prefix = stay ∪ leave := by
    ext h
    simp only [prefix, stay, leave, riskFirstExitAfter,
      Set.mem_ofPred_eq, Set.mem_union, riskEverFailure, not_or]
    tauto
  have hdisjoint : Disjoint stay leave := by
    apply Set.disjoint_left.mpr
    intro h hs he
    change ¬ (riskEverFailure (fun x => x ∉ K) n h.1 ∨ h.2.2 ∉ K) at hs
    change ¬ riskEverFailure (fun x => x ∉ K) n h.1 ∧ h.2.2 ∉ K at he
    exact hs (Or.inr he.2)
  have hprefix : (nu (n + 1)).toMeasure.real prefix = s n := by
    exact causalLaw_prefix_event_real p0 L n
      {h | ¬ riskEverFailure (fun x => x ∉ K) n h}
  have hadd : s n = s (n + 1) +
      (nu (n + 1)).toMeasure.real (riskFirstExitAfter (A := A) K n) := by
    calc
      s n = (nu (n + 1)).toMeasure.real prefix := hprefix.symm
      _ = (nu (n + 1)).toMeasure.real stay +
          (nu (n + 1)).toMeasure.real leave := by
        rw [hsplit]
        exact measureReal_union hdisjoint (Set.toFinite leave).measurableSet
      _ = _ := rfl
  linarith

/-- The row-deficit formula has now been identified with actual first exit. -/
theorem actual_first_exit_mass_eq_killedExitFlux (n : ℕ) :
    (nu (n + 1)).toMeasure.real (riskFirstExitAfter (A := A) K n) = flux n := by
  rw [actual_first_exit_mass_eq_survival_drop M q sigma p0 K n,
    actual_survival_drop_eq_killedExitFlux M q sigma p0 K n]

/-- Nonnegativity is inherited from the actual event probability. -/
theorem actual_killedExitFlux_nonneg (n : ℕ) : 0 ≤ flux n := by
  rw [← actual_first_exit_mass_eq_killedExitFlux M q sigma p0 K n]
  exact ENNReal.toReal_nonneg

/-- At horizon zero survival is exactly the ORIGINAL initial mass in K. -/
theorem actual_survival_zero : s 0 = p0.toMeasure.real K := by
  change p0.toMeasure.real {x | ¬ x ∉ K} = p0.toMeasure.real K
  congr 1
  ext x
  simp

/-- Finite telescoping, including initial failure, T=0 and empty K. -/
theorem actual_failure_mass_telescope (T : ℕ) :
    1 - s T = (1 - p0.toMeasure.real K) +
      ∑ n ∈ Finset.range T, flux n := by
  have htel : (∑ n ∈ Finset.range T, flux n) = s 0 - s T := by
    calc
      (∑ n ∈ Finset.range T, flux n) =
          ∑ n ∈ Finset.range T, (s n - s (n + 1)) := by
        apply Finset.sum_congr rfl
        intro n _
        exact (actual_survival_drop_eq_killedExitFlux M q sigma p0 K n).symm
      _ = s 0 - s T := Finset.sum_range_sub' s T
  rw [actual_survival_zero M q sigma p0 K] at htel
  linarith

/-- The left side is exactly the real probability of the existing failure
event. Complementation is within the same original T-step PMF. -/
theorem actual_ever_failure_mass (T : ℕ) :
    (nu T).toMeasure.real {h | riskEverFailure (fun x => x ∉ K) T h} =
      1 - s T := by
  have hevent :
      {h : CausalHistory X (A × X) T | riskEverFailure (fun x => x ∉ K) T h} =
        {h | ¬ riskEverFailure (fun x => x ∉ K) T h}ᶜ := by
    ext h
    simp
  rw [hevent]
  exact probReal_compl_eq_one_sub (Set.toFinite _).measurableSet

/-- Final actual-event statement: initial failure plus finite first exits.
Each summand uses a coherent prefix of the same specified source. -/
theorem actual_failure_eq_initial_failure_add_first_exits (T : ℕ) :
    (nu T).toMeasure.real {h | riskEverFailure (fun x => x ∉ K) T h} =
      p0.toMeasure.real Kᶜ +
        ∑ n ∈ Finset.range T,
          (nu (n + 1)).toMeasure.real (riskFirstExitAfter (A := A) K n) := by
  rw [actual_ever_failure_mass M q sigma p0 K T,
    probReal_compl_eq_one_sub (Set.toFinite K).measurableSet]
  simp_rw [actual_first_exit_mass_eq_killedExitFlux M q sigma p0 K]
  exact actual_failure_mass_telescope M q sigma p0 K T

end ActualSource
end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceKilledExitFluxCheck

#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceKilledExitFluxCheck.pmfExtend_map_fst
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceKilledExitFluxCheck.causalLaw_map_prefix
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceKilledExitFluxCheck.causalLaw_prefix_event_real
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceKilledExitFluxCheck.actual_first_exit_mass_eq_survival_drop
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceKilledExitFluxCheck.actual_first_exit_mass_eq_killedExitFlux
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceKilledExitFluxCheck.actual_killedExitFlux_nonneg
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceKilledExitFluxCheck.actual_survival_zero
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceKilledExitFluxCheck.actual_failure_mass_telescope
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceKilledExitFluxCheck.actual_ever_failure_mass
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceKilledExitFluxCheck.actual_failure_eq_initial_failure_add_first_exits
