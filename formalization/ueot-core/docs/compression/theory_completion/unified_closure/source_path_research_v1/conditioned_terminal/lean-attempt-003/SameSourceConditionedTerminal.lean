import SameSourceKilledPath
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# General same-source positive-survival conditional terminal law

PRIVATE PROOF DRAFT — NOT COMPILED.

The actual initial PMF is arbitrary. Only the CURRENT horizon's actual
survival mass is required to be positive. The actual history PMF is filtered
on survival through time n (including time zero), then mapped to its last
state. Its safe-state masses are the same-source killed row eta0 Q^n divided
by that actual survival mass. The normalized row is also represented as a
PMF on the safe subtype, with a PROVED equality to the actual filtered law.

There are no QSD/Perron hypotheses, no prior support restriction on p0,
no Nonempty hypothesis on the safe subtype, and no assumed source identity.
The two imported K1 endpoints have separate actual focused Lean PASS receipts.
All proof bodies in THIS file remain proposals until an actual Lean run.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceConditionedTerminalCheck

open MeasureTheory
open UEOT.V3.PathError
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.CoreOperationalAssembly
open UEOT.V3.QSDPerron
open SourcePolicyPathBridgeCheck SameSourceKilledPathCheck
open scoped BigOperators Classical

noncomputable section
universe u

private theorem positive_event_mass_iff_support
    {H : Type u} [Fintype H]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    (p : PMF H) (S : Set H) :
    0 < p.toMeasure.real S ↔ ∃ h ∈ S, h ∈ p.support := by
  classical
  constructor
  · intro hpos
    by_contra hnone
    have hzero : p.toMeasure S = 0 := by
      apply (p.toMeasure_apply_eq_zero_iff (Set.toFinite S).measurableSet).2
      apply Set.disjoint_left.mpr
      intro h hsupp hS
      exact hnone ⟨h, hS, hsupp⟩
    change 0 < (p.toMeasure S).toReal at hpos
    rw [hzero, ENNReal.toReal_zero] at hpos
    exact (lt_irrefl 0) hpos
  · rintro ⟨h, hS, hsupp⟩
    have hnonzero : p.toMeasure S ≠ 0 := by
      intro hzero
      have hd := (p.toMeasure_apply_eq_zero_iff
        (Set.toFinite S).measurableSet).1 hzero
      exact Set.disjoint_left.1 hd hsupp hS
    exact ENNReal.toReal_pos hnonzero (measure_ne_top p.toMeasure S)

/-- This local adapter evaluates Mathlib's actual filter/map construction;
it does not supply a separately chosen conditional distribution. -/
private theorem filter_map_apply_real
    {H Z : Type u} [Fintype H]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    (p : PMF H) (S : Set H) (hs : ∃ h ∈ S, h ∈ p.support)
    (f : H → Z) (z : Z) :
    (((p.filter S hs).map f) z).toReal =
      p.toMeasure.real {h | h ∈ S ∧ f h = z} / p.toMeasure.real S := by
  have he : ((p.filter S hs).map f) z =
      p.toMeasure {h | h ∈ S ∧ f h = z} / p.toMeasure S := by
    rw [PMF.map_apply, tsum_fintype]
    simp only [PMF.toMeasure_apply_fintype, div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro h _
    rw [PMF.filter_apply, tsum_fintype]
    by_cases hS : h ∈ S
    · by_cases hz : f h = z
      · subst z
        simp [Set.indicator_apply, hS]
      · have hz' : z ≠ f h := Ne.symm hz
        simp [Set.indicator_apply, hS, hz, hz']
    · simp [Set.indicator_apply, hS]
  simpa only [ENNReal.toReal_div, Measure.real] using congrArg ENNReal.toReal he

private theorem survives_last_mem
    {X A : Type u} (K : Set X) (n : ℕ)
    (h : CausalHistory X (A × X) n)
    (hs : ¬ riskEverFailure (fun x => x ∉ K) n h) :
    riskLastState n h ∈ K := by
  cases n with
  | zero => simpa only [riskEverFailure, riskLastState, not_not] using hs
  | succ n =>
      change ¬ (riskEverFailure (fun x => x ∉ K) n h.1 ∨ h.2.2 ∉ K) at hs
      exact not_not.mp (not_or.mp hs).2

private theorem map_injective_atom {S T : Type*} (f : S → T)
    (hf : Function.Injective f) (p : PMF S) (s : S) :
    (p.map f) (f s) = p s := by
  rw [PMF.map_apply]
  refine (tsum_eq_single s ?_).trans ?_
  · intro t ht
    exact if_neg (fun h => ht (hf h).symm)
  · simp

section ActualSource

variable {X Y A : Type u} [Fintype X] [Fintype A] [Nonempty A]
variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace A] [MeasurableSingletonClass A]
variable (M : Model X (fun _ => A)) (q : X → Y) (sigma : Y → PMF A)
variable (p0 : PMF X) (K : Set X) (n : ℕ)

local notation "nu" => causalLaw p0
  (riskMicroControlKernel q (fun _ => M.transitionPMF)
    (observationMarkovPolicy sigma)) n
local notation "S" => Set.ofPred (fun h : CausalHistory X (A × X) n =>
  ¬ riskEverFailure (fun x => x ∉ K) n h)
local notation "s" => Measure.real (PMF.toMeasure nu) S
local notation "Q" => killedMatrix M (liftedStationaryPolicy q sigma) K
local notation "w" => rowApply (safeInitialRow p0 K) (Q ^ n)

/-- Positivity of the actual event is precisely the input required by
Mathlib's filter constructor. The support witness is not a new assumption. -/
theorem actual_survival_pos_iff_support :
    0 < s ↔ ∃ h ∈ S, h ∈ (nu).support :=
  positive_event_mass_iff_support nu S

/-- The actual complete history is conditioned first, then its final state
is observed. This definition is available only at a positive-mass horizon. -/
def actualConditionedTerminal (hpos : 0 < s) : PMF X :=
  ((nu).filter S ((actual_survival_pos_iff_support M q sigma p0 K n).1 hpos)).map
    (riskLastState n)

/-- K2: every safe atom of the actual conditional terminal law is the
same-source unnormalized killed mass divided by actual total survival. -/
theorem actual_conditioned_terminal_mass (hpos : 0 < s) (v : K) :
    (actualConditionedTerminal M q sigma p0 K n hpos v.1).toReal = w v / s := by
  unfold actualConditionedTerminal
  rw [filter_map_apply_real]
  rw [actual_survival_terminal_mass_eq_killed_pow M q sigma p0 K n v]

/-- Conditioning on survival cannot put terminal mass outside the safe set. -/
theorem actual_conditioned_terminal_support (hpos : 0 < s) :
    (actualConditionedTerminal M q sigma p0 K n hpos).support ⊆ K := by
  intro x hx
  let hs := (actual_survival_pos_iff_support M q sigma p0 K n).1 hpos
  change x ∈ (((nu).filter S hs).map (riskLastState n)).support at hx
  rcases (PMF.mem_support_map_iff (riskLastState n) ((nu).filter S hs) x).1 hx with
    ⟨h, hh, heq⟩
  have hsafe := (PMF.mem_support_filter_iff hs).1 hh
  exact heq ▸ survives_last_mem K n h hsafe.1

theorem actual_conditioned_terminal_eq_zero_of_notMem
    (hpos : 0 < s) (x : X) (hx : x ∉ K) :
    actualConditionedTerminal M q sigma p0 K n hpos x = 0 := by
  apply (PMF.apply_eq_zero_iff _ x).2
  intro hmem
  exact hx (actual_conditioned_terminal_support M q sigma p0 K n hpos hmem)

/-- An algebraic representation of K2 on the safe subtype. Nonnegativity
and normalization are derived from K1 for this same p0/model/policy. -/
def normalizedKilledTerminal (hpos : 0 < s) : PMF K := by
  refine FiniteProbabilityRow.ofRealRow (fun v => w v / s) ?_ ?_
  · intro v
    apply div_nonneg ?_ hpos.le
    rw [← actual_survival_terminal_mass_eq_killed_pow M q sigma p0 K n v]
    exact measureReal_nonneg
  · rw [← Finset.sum_div,
      ← actual_survival_mass_eq_killed_pow_sum M q sigma p0 K n]
    exact div_self hpos.ne'

@[simp] theorem normalizedKilledTerminal_apply_toReal
    (hpos : 0 < s) (v : K) :
    (normalizedKilledTerminal M q sigma p0 K n hpos v).toReal = w v / s := by
  simp only [normalizedKilledTerminal, FiniteProbabilityRow.ofRealRow_apply_toReal]

/-- The normalized killed row is the very same terminal law obtained by
filtering the actual action/state histories. This identity is proved. -/
theorem actual_conditioned_terminal_eq_normalized_killed_map (hpos : 0 < s) :
    actualConditionedTerminal M q sigma p0 K n hpos =
      (normalizedKilledTerminal M q sigma p0 K n hpos).map Subtype.val := by
  apply PMF.ext
  intro x
  by_cases hx : x ∈ K
  · let v : K := ⟨x, hx⟩
    apply (ENNReal.toReal_eq_toReal_iff'
      ((actualConditionedTerminal M q sigma p0 K n hpos).apply_ne_top x)
      (((normalizedKilledTerminal M q sigma p0 K n hpos).map
        Subtype.val).apply_ne_top x)).1
    calc
      (actualConditionedTerminal M q sigma p0 K n hpos x).toReal = w v / s :=
        actual_conditioned_terminal_mass M q sigma p0 K n hpos v
      _ = (normalizedKilledTerminal M q sigma p0 K n hpos v).toReal :=
        (normalizedKilledTerminal_apply_toReal M q sigma p0 K n hpos v).symm
      _ = (((normalizedKilledTerminal M q sigma p0 K n hpos).map
          Subtype.val) x).toReal := by
        exact (congrArg ENNReal.toReal
          (map_injective_atom Subtype.val Subtype.val_injective
            (normalizedKilledTerminal M q sigma p0 K n hpos) v)).symm
  · have hactual :=
      actual_conditioned_terminal_eq_zero_of_notMem M q sigma p0 K n hpos x hx
    have hmap : ((normalizedKilledTerminal M q sigma p0 K n hpos).map
        Subtype.val) x = 0 := by
      apply (PMF.apply_eq_zero_iff _ x).2
      intro hmem
      rcases (PMF.mem_support_map_iff Subtype.val
        (normalizedKilledTerminal M q sigma p0 K n hpos) x).1 hmem with
        ⟨v, _, heq⟩
      exact hx (heq ▸ v.property)
    rw [hactual, hmap]

/-- Positive survival entails a nonempty safe set; it is never an independent
input used to hide the empty-safe-set boundary. -/
theorem safe_set_nonempty_of_survival_pos (hpos : 0 < s) : K.Nonempty := by
  rcases (actual_survival_pos_iff_support M q sigma p0 K n).1 hpos with
    ⟨h, hsafe, _⟩
  exact ⟨riskLastState n h, survives_last_mem K n h hsafe⟩

/-- Zero actual survival supplies no support witness for PMF.filter.
No normalized conditional PMF is assigned to this null event. -/
theorem actual_zero_survival_no_filter_witness (hzero : s = 0) :
    ¬ ∃ h ∈ S, h ∈ (nu).support := by
  intro hw
  have hp := (actual_survival_pos_iff_support M q sigma p0 K n).2 hw
  rw [hzero] at hp
  exact (lt_irrefl 0) hp

/-- Survival at horizon zero is precisely actual initial mass in K,
not one unless p0 is supported there. -/
theorem actual_survival_mass_at_zero :
    (causalLaw p0 (riskMicroControlKernel q (fun _ => M.transitionPMF)
      (observationMarkovPolicy sigma)) 0).toMeasure.real
        {h | ¬ riskEverFailure (fun x => x ∉ K) 0 h} = p0.toMeasure.real K := by
  change p0.toMeasure.real {x : X | ¬ (x ∉ K)} = p0.toMeasure.real K
  have hset : {x : X | ¬ (x ∉ K)} = K := by
    ext x
    simp only [Set.mem_setOf_eq, not_not]
  rw [hset]

/-- The n=0 conditional formula includes an initially unsafe population.
The denominator is p0(K), and no preliminary normalization of p0 was used. -/
theorem actual_conditioned_terminal_mass_at_zero
    (hpos : 0 < (causalLaw p0
      (riskMicroControlKernel q (fun _ => M.transitionPMF)
        (observationMarkovPolicy sigma)) 0).toMeasure.real
          {h | ¬ riskEverFailure (fun x => x ∉ K) 0 h}) (v : K) :
    (actualConditionedTerminal M q sigma p0 K 0 hpos v.1).toReal =
      (p0 v.1).toReal / p0.toMeasure.real K := by
  rw [actual_conditioned_terminal_mass M q sigma p0 K 0 hpos v,
    actual_survival_mass_at_zero M q sigma p0 K]
  simp [rowApply, Matrix.one_apply, safeInitialRow, mul_ite]

/-- The empty safe set has zero survival even at horizon zero. -/
theorem actual_survival_mass_empty :
    (causalLaw p0 (riskMicroControlKernel q (fun _ => M.transitionPMF)
      (observationMarkovPolicy sigma)) n).toMeasure.real
        {h | ¬ riskEverFailure (fun x => x ∉ (∅ : Set X)) n h} = 0 := by
  rw [actual_survival_mass_eq_killed_pow_sum M q sigma p0 (∅ : Set X) n]
  exact Finset.sum_eq_zero fun v _ => False.elim v.property

end ActualSource
end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceConditionedTerminalCheck

-- These commands are requests for a future actual run, not executed receipts.
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceConditionedTerminalCheck.actual_conditioned_terminal_mass
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceConditionedTerminalCheck.actual_conditioned_terminal_eq_normalized_killed_map
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceConditionedTerminalCheck.actual_zero_survival_no_filter_witness
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceConditionedTerminalCheck.actual_conditioned_terminal_mass_at_zero
#print axioms UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceConditionedTerminalCheck.actual_survival_mass_empty
