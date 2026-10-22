import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceKilledExitFlux

/-!
# Same-source finite-window survival conditioning

The prefix is a complete microscopic state prefix. Its joint mass with survival
to the original horizon is derived from the existing causal PMF recursion.
The initial PMF is never pre-normalized. Every conditional PMF filters the
original action/state experiment, and every matrix is its existing killed
restriction. The normalized row PMF requires strictly positive remaining
survival; no probability distribution is assigned to a null row.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceFiniteWindowCheck

open MeasureTheory
open UEOT.V3.PathError
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.CoreOperationalAssembly
open UEOT.V3.QSDPerron
open SourcePolicyPathBridgeCheck SameSourceKilledPathCheck
open SameSourceConditionedTerminalCheck
open scoped BigOperators Classical

noncomputable section
universe u

/-- Drop the final r records, retaining the complete prefix through time t. -/
def statePrefix {X : Type u} (t : ℕ) :
    ∀ r, CausalHistory X X (t + r) → CausalHistory X X t
  | 0, h => h
  | r + 1, h => statePrefix t r h.1

private theorem stateSurvives_prefix
    {X : Type u} (K : Set X) (t : ℕ) :
    ∀ r (h : CausalHistory X X (t + r)),
      stateSurvives K (t + r) h → stateSurvives K t (statePrefix t r h) := by
  intro r
  induction r with
  | zero => intro h hh; exact hh
  | succ r ih => intro h hh; exact ih h.1 hh.1

/-- The same killed matrix supplies the remaining-survival function. -/
def remainingSurvival {S : Type u} [Fintype S]
    (Q : Matrix S S ℝ) (r : ℕ) (i : S) : ℝ :=
  ∑ j : S, (Q ^ r) i j

@[simp] theorem remainingSurvival_zero
    {S : Type u} [Fintype S] (Q : Matrix S S ℝ) (i : S) :
    remainingSurvival Q 0 i = 1 := by
  simp [remainingSurvival, Matrix.one_apply]

theorem remainingSurvival_succ
    {S : Type u} [Fintype S] (Q : Matrix S S ℝ) (r : ℕ) (i : S) :
    remainingSurvival Q (r + 1) i =
      ∑ j : S, Q i j * remainingSurvival Q r j := by
  simp only [remainingSurvival, pow_succ', Matrix.mul_apply]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

theorem remainingSurvival_nonneg
    {S : Type u} [Fintype S] (Q : Matrix S S ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (r : ℕ) (i : S) :
    0 ≤ remainingSurvival Q r i := by
  induction r generalizing i with
  | zero => simp
  | succ r ih =>
      rw [remainingSurvival_succ]
      exact Finset.sum_nonneg fun j _ => mul_nonneg (hQ i j) (ih j)

/-- Finite path weight for an unnormalized initial row and an arbitrary matrix.
Its probability meaning is supplied by the source theorem below. -/
def matrixPathWeight {S : Type u} (eta : S → ℝ) (Q : Matrix S S ℝ) :
    ∀ n, CausalHistory S S n → ℝ
  | 0, h => eta h
  | n + 1, h => matrixPathWeight eta Q n h.1 * Q (currentState n h.1) h.2

/-- Embed a complete safe-state history in the original state alphabet. -/
def safeHistory {X : Type u} (K : Set X) (n : ℕ) :
    CausalHistory K K n → CausalHistory X X n :=
  riskHistoryMap Subtype.val Subtype.val n

private theorem safeHistory_current
    {X : Type u} (K : Set X) (n : ℕ) (h : CausalHistory K K n) :
    currentState n (safeHistory K n h) = (currentState n h).1 := by
  cases n <;> rfl

private theorem safeHistory_survives
    {X : Type u} (K : Set X) :
    ∀ n (h : CausalHistory K K n), stateSurvives K n (safeHistory K n h) := by
  intro n
  induction n with
  | zero => intro h; exact h.property
  | succ n ih => intro h; exact ⟨ih h.1, h.2.property⟩

private theorem sum_safe_subtype
    {X : Type u} [Fintype X] (K : Set X) (f : X → ℝ) :
    (∑ x : X, if x ∈ K then f x else 0) = ∑ x : K, f x.1 := by
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype (Finset.univ.filter (fun x : X => x ∈ K))
    (by intro x; simp) f

private theorem finite_event_mass
    {H : Type u} [Fintype H]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    (p : PMF H) (E : H → Prop) :
    p.toMeasure.real {h | E h} = ∑ h : H, if E h then (p h).toReal else 0 := by
  have hset : {h | E h} = (Finset.univ.filter E : Set H) := by
    ext h
    simp
  rw [hset, pmfMeasureReal_eq_sum_finset, Finset.sum_filter]

private theorem stateSurvives_erase_iff
    {X A : Type u} (K : Set X) :
    ∀ n (h : CausalHistory X (A × X) n),
      stateSurvives K n (eraseActionHistory n h) ↔
        ¬ riskEverFailure (fun x => x ∉ K) n h := by
  intro n
  induction n with
  | zero => intro h; change (h ∈ K) ↔ ¬ (h ∉ K); tauto
  | succ n ih =>
      intro h
      change (stateSurvives K n (eraseActionHistory n h.1) ∧ h.2.2 ∈ K) ↔
        ¬ (riskEverFailure (fun x => x ∉ K) n h.1 ∨ h.2.2 ∉ K)
      rw [ih h.1]
      tauto

section StateSource

variable {X A : Type u} [Fintype X] [Fintype A] [Nonempty A]
variable (M : Model X (fun _ => A)) (pi : StationaryPolicy (fun _ : X => A))
variable (p0 : PMF X) (K : Set X)

local instance : DecidableEq K := Classical.decEq K

private def weightedPrefixMass (t r : ℕ) (h : CausalHistory X X t)
    (f : X → ℝ) : ℝ :=
  ∑ g : CausalHistory X X (t + r),
    if stateSurvives K (t + r) g ∧ statePrefix t r g = h then
      (causalLaw p0 (policyPathKernel M pi) (t + r) g).toReal *
        f (currentState (t + r) g)
    else 0

set_option backward.isDefEq.respectTransparency false in
private theorem weightedPrefixMass_eq
    (t r : ℕ) (h : CausalHistory X X t)
    (hs : stateSurvives K t h) (i : K) (hi : currentState t h = i.1)
    (f : X → ℝ) :
    weightedPrefixMass M pi p0 K t r h f =
      (causalLaw p0 (policyPathKernel M pi) t h).toReal *
        ∑ j : K, ((killedMatrix M pi K) ^ r) i j * f j.1 := by
  induction r generalizing f with
  | zero =>
      unfold weightedPrefixMass
      change (∑ g : CausalHistory X X t,
        if stateSurvives K t g ∧ g = h then
          (causalLaw p0 (policyPathKernel M pi) t g).toReal * f (currentState t g)
        else 0) = _
      rw [Finset.sum_eq_single h]
      · simp [hs, hi, Matrix.one_apply]
      · intro g _ hg
        simp [hg]
      · simp
  | succ r ih =>
      let mu := causalLaw p0 (policyPathKernel M pi) (t + r)
      let F : X → ℝ := fun x => ∑ j : K, policyMatrix M pi x j.1 * f j.1
      have hinner (g : CausalHistory X X (t + r)) :
          (∑ z : X,
            if (stateSurvives K (t + r) g ∧ z ∈ K) ∧ statePrefix t r g = h then
              (mu g).toReal * (policyPathKernel M pi (t + r) g z).toReal * f z
            else 0) =
          if stateSurvives K (t + r) g ∧ statePrefix t r g = h then
            (mu g).toReal * F (currentState (t + r) g) else 0 := by
        by_cases hsafe : stateSurvives K (t + r) g
        · by_cases hpre : statePrefix t r g = h
          · simp only [hsafe, hpre, true_and, and_true, if_true]
            calc
              (∑ z : X, if z ∈ K then
                (mu g).toReal * (policyPathKernel M pi (t + r) g z).toReal * f z
                else 0) =
                  (mu g).toReal * ∑ z : X, if z ∈ K then
                    (policyPathKernel M pi (t + r) g z).toReal * f z else 0 := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro z _
                by_cases hz : z ∈ K <;> simp [hz, mul_assoc]
              _ = (mu g).toReal * F (currentState (t + r) g) := by
                rw [sum_safe_subtype]
                simp only [F, policyPathKernel, policyTransitionPMF_apply_toReal, policyMatrix]
          · simp [hpre]
        · simp [hsafe]
      have hrec :
          weightedPrefixMass M pi p0 K t (r + 1) h f =
            weightedPrefixMass M pi p0 K t r h F := by
        unfold weightedPrefixMass
        change (∑ gz : CausalHistory X X (t + r) × X,
          if stateSurvives K ((t + r) + 1) gz ∧ statePrefix t (r + 1) gz = h then
            (causalLaw p0 (policyPathKernel M pi) ((t + r) + 1) gz).toReal *
              f (currentState ((t + r) + 1) gz)
          else 0) = _
        rw [← Finset.univ_product_univ, Finset.sum_product]
        apply Finset.sum_congr rfl
        intro g _
        calc
          _ = (∑ z : X,
              if (stateSurvives K (t + r) g ∧ z ∈ K) ∧ statePrefix t r g = h then
                (mu g).toReal * (policyPathKernel M pi (t + r) g z).toReal * f z
              else 0) := by
            apply Finset.sum_congr rfl
            intro z _
            by_cases he : (stateSurvives K (t + r) g ∧ z ∈ K) ∧
                statePrefix t r g = h
            · have he' : stateSurvives K ((t + r) + 1) (g, z) ∧
                  statePrefix t (r + 1) (g, z) = h := he
              rw [if_pos he', if_pos he]
              change (pmfExtend mu (policyPathKernel M pi (t + r)) (g, z)).toReal *
                f z = _
              rw [UEOT.V3.PathError.pmfExtend_apply, ENNReal.toReal_mul]
            · have he' : ¬ (stateSurvives K ((t + r) + 1) (g, z) ∧
                  statePrefix t (r + 1) (g, z) = h) := he
              rw [if_neg he', if_neg he]
          _ = _ := hinner g
      rw [hrec, ih F]
      congr 1
      change (∑ j : K, ((killedMatrix M pi K) ^ r) i j *
          ∑ k : K, killedMatrix M pi K j k * f k.1) =
        ∑ j : K, ((killedMatrix M pi K) ^ (r + 1)) i j * f j.1
      simp only [pow_succ, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring

/-- The actual state-law atom on a safe path is its killed product weight.
The PMF recursion supplies every factor; the equality is not an assumption. -/
theorem state_safe_atom_eq_matrixPathWeight :
    ∀ n (h : CausalHistory K K n),
      (causalLaw p0 (policyPathKernel M pi) n (safeHistory K n h)).toReal =
        matrixPathWeight (safeInitialRow p0 K) (killedMatrix M pi K) n h := by
  intro n
  induction n with
  | zero => intro h; rfl
  | succ n ih =>
      intro h
      change (pmfExtend (causalLaw p0 (policyPathKernel M pi) n)
        (policyPathKernel M pi n) (safeHistory K n h.1, h.2.1)).toReal = _
      rw [UEOT.V3.PathError.pmfExtend_apply, ENNReal.toReal_mul, ih h.1]
      simp only [matrixPathWeight, policyPathKernel, policyTransitionPMF_apply_toReal,
        safeHistory_current, killedMatrix, policyMatrix]

/-- Joint mass of a fixed safe prefix and survival through t+r. -/
theorem state_prefix_survival_mass
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (t r : ℕ) (h : CausalHistory X X t)
    (hs : stateSurvives K t h) (i : K) (hi : currentState t h = i.1) :
    (causalLaw p0 (policyPathKernel M pi) (t + r)).toMeasure.real
      {g | stateSurvives K (t + r) g ∧ statePrefix t r g = h} =
      (causalLaw p0 (policyPathKernel M pi) t h).toReal *
        remainingSurvival (killedMatrix M pi K) r i := by
  rw [finite_event_mass]
  calc
    _ = weightedPrefixMass M pi p0 K t r h (fun _ => 1) := by
      unfold weightedPrefixMass
      apply Finset.sum_congr rfl
      intro g _
      by_cases he : stateSurvives K (t + r) g ∧ statePrefix t r g = h
      · simp only [he, mul_one]
      · simp only [he, if_false]
    _ = _ := by
      simpa only [mul_one, remainingSurvival] using
        weightedPrefixMass_eq M pi p0 K t r h hs i hi (fun _ => 1)

end StateSource

/-- Positive remaining-survival row, with r further steps after this transition. -/
def finiteWindowRow {S : Type u} [Fintype S]
    (Q : Matrix S S ℝ) (r : ℕ) (i j : S) : ℝ :=
  Q i j * remainingSurvival Q r j / remainingSurvival Q (r + 1) i

/-- Only a positive row is normalized; no total-row claim is made at zero mass. -/
def finiteWindowRowPMF
    {S : Type u} [Fintype S] (Q : Matrix S S ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (r : ℕ) (i : S)
    (hpos : 0 < remainingSurvival Q (r + 1) i) : PMF S :=
  FiniteProbabilityRow.ofRealRow (finiteWindowRow Q r i)
    (fun j => div_nonneg
      (mul_nonneg (hQ i j) (remainingSurvival_nonneg Q hQ r j)) hpos.le)
    (by
      simp only [finiteWindowRow, ← Finset.sum_div, ← remainingSurvival_succ]
      exact div_self hpos.ne')

@[simp] theorem finiteWindowRowPMF_apply_toReal
    {S : Type u} [Fintype S] (Q : Matrix S S ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (r : ℕ) (i : S)
    (hpos : 0 < remainingSurvival Q (r + 1) i) (j : S) :
    (finiteWindowRowPMF Q hQ r i hpos j).toReal = finiteWindowRow Q r i j := by
  unfold finiteWindowRowPMF
  exact FiniteProbabilityRow.ofRealRow_apply_toReal (finiteWindowRow Q r i) _ _ j

section ActualSource

variable {X Y A : Type u} [Fintype X] [Fintype A] [Nonempty A]
variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace A] [MeasurableSingletonClass A]
variable (M : Model X (fun _ => A)) (q : X → Y) (sigma : Y → PMF A)
variable (p0 : PMF X) (K : Set X)

local notation "pi" => liftedStationaryPolicy q sigma
local notation "Q" => killedMatrix M pi K

/-- Actual survival probability in the original action/state experiment. -/
def actualSurvivalMass (n : ℕ) : ℝ :=
  (causalLaw p0 (riskMicroControlKernel q (fun _ => M.transitionPMF)
    (observationMarkovPolicy sigma)) n).toMeasure.real
      {g | ¬ riskEverFailure (fun x => x ∉ K) n g}

/-- The actual complete state prefix and the original final survival event. -/
def actualPrefixSurvivalMass (t r : ℕ) (h : CausalHistory X X t) : ℝ :=
  (causalLaw p0 (riskMicroControlKernel q (fun _ => M.transitionPMF)
    (observationMarkovPolicy sigma)) (t + r)).toMeasure.real
      {g | ¬ riskEverFailure (fun x => x ∉ K) (t + r) g ∧
        statePrefix t r (eraseActionHistory (t + r) g) = h}

/-- The source identity is proved from action erasure and the actual suffix sum. -/
theorem actual_prefix_survival_mass
    (t r : ℕ) (h : CausalHistory X X t)
    (hs : stateSurvives K t h) (i : K) (hi : currentState t h = i.1) :
    actualPrefixSurvivalMass M q sigma p0 K t r h =
      (causalLaw p0 (policyPathKernel M pi) t h).toReal *
        remainingSurvival Q r i := by
  let nu := causalLaw p0 (riskMicroControlKernel q (fun _ => M.transitionPMF)
    (observationMarkovPolicy sigma)) (t + r)
  let E : Set (CausalHistory X X (t + r)) :=
    {g | stateSurvives K (t + r) g ∧ statePrefix t r g = h}
  have hevent : (eraseActionHistory (X := X) (A := A) (t + r)) ⁻¹' E =
      {g | ¬ riskEverFailure (fun x => x ∉ K) (t + r) g ∧
        statePrefix t r (eraseActionHistory (t + r) g) = h} := by
    ext g
    simp only [E, Set.mem_preimage, Set.mem_ofPred_eq, stateSurvives_erase_iff]
  have hm := PMF.toMeasure_map_apply (eraseActionHistory (X := X) (A := A) (t + r))
    nu E (measurable_of_finite _) (Set.toFinite E).measurableSet
  calc
    actualPrefixSurvivalMass M q sigma p0 K t r h =
        (nu.map (eraseActionHistory (t + r))).toMeasure.real E := by
      simpa only [actualPrefixSurvivalMass, nu, Measure.real, hevent] using
        (congrArg ENNReal.toReal hm).symm
    _ = (causalLaw p0 (policyPathKernel M pi) (t + r)).toMeasure.real E := by
      rw [actual_state_path_eq_stationary_path M q sigma p0 (t + r)]
    _ = _ := state_prefix_survival_mass M pi p0 K t r h hs i hi

private theorem filter_map_atom_real
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

/-- Filter the original complete experiment at t+r, then retain its state prefix. -/
def actualConditionedPrefix (t r : ℕ)
    (hpos : 0 < actualSurvivalMass M q sigma p0 K (t + r)) :
    PMF (CausalHistory X X t) :=
  ((causalLaw p0 (riskMicroControlKernel q (fun _ => M.transitionPMF)
    (observationMarkovPolicy sigma)) (t + r)).filter
      {g | ¬ riskEverFailure (fun x => x ∉ K) (t + r) g}
      ((actual_survival_pos_iff_support M q sigma p0 K (t + r)).1 hpos)).map
    (fun g => statePrefix t r (eraseActionHistory (t + r) g))

/-- Filtering the actual final-survival event leaves only safe retained prefixes. -/
theorem actual_conditioned_prefix_support
    (t r : ℕ) (hpos : 0 < actualSurvivalMass M q sigma p0 K (t + r)) :
    (actualConditionedPrefix M q sigma p0 K t r hpos).support ⊆
      {h | stateSurvives K t h} := by
  intro h hh
  unfold actualConditionedPrefix at hh
  rcases (PMF.mem_support_map_iff _ _ _).1 hh with ⟨g, hg, rfl⟩
  have hsafe := (PMF.mem_support_filter_iff
    ((actual_survival_pos_iff_support M q sigma p0 K (t + r)).1 hpos)).1 hg
  exact stateSurvives_prefix K t r _
    ((stateSurvives_erase_iff K (t + r) g).2 hsafe.1)

/-- Unsafe prefix atoms vanish in the actual conditioned PMF, including
complete-window atoms outside the safe history subtype. -/
theorem actual_conditioned_prefix_eq_zero_of_not_survives
    (t r : ℕ) (hpos : 0 < actualSurvivalMass M q sigma p0 K (t + r))
    (h : CausalHistory X X t) (hunsafe : ¬ stateSurvives K t h) :
    actualConditionedPrefix M q sigma p0 K t r hpos h = 0 := by
  apply (PMF.apply_eq_zero_iff _ h).2
  intro hh
  exact hunsafe (actual_conditioned_prefix_support M q sigma p0 K t r hpos hh)

/-- Every conditional prefix atom is calculated in the same filtered experiment. -/
theorem actual_conditioned_prefix_mass
    (t r : ℕ) (hpos : 0 < actualSurvivalMass M q sigma p0 K (t + r))
    (h : CausalHistory X X t)
    (hs : stateSurvives K t h) (i : K) (hi : currentState t h = i.1) :
    (actualConditionedPrefix M q sigma p0 K t r hpos h).toReal =
      (causalLaw p0 (policyPathKernel M pi) t h).toReal *
        remainingSurvival Q r i / actualSurvivalMass M q sigma p0 K (t + r) := by
  unfold actualConditionedPrefix
  rw [filter_map_atom_real]
  change actualPrefixSurvivalMass M q sigma p0 K t r h /
    actualSurvivalMass M q sigma p0 K (t + r) = _
  rw [actual_prefix_survival_mass M q sigma p0 K t r h hs i hi]

/-- Future survival changes the initial law by the actual remaining-survival weight.
At T=0 this retains and normalizes the original safe initial mass. -/
theorem actual_conditioned_initial_mass
    (T : ℕ) (hpos : 0 < actualSurvivalMass M q sigma p0 K (0 + T)) (i : K) :
    (actualConditionedPrefix M q sigma p0 K 0 T hpos i.1).toReal =
      safeInitialRow p0 K i * remainingSurvival Q T i /
        actualSurvivalMass M q sigma p0 K T := by
  rw [actual_conditioned_prefix_mass M q sigma p0 K 0 T hpos i.1 i.property i rfl]
  change (p0 i.1).toReal * remainingSurvival Q T i /
      actualSurvivalMass M q sigma p0 K (0 + T) =
    (p0 i.1).toReal * remainingSurvival Q T i /
      actualSurvivalMass M q sigma p0 K T
  rw [Nat.zero_add]

/-- The complete conditional safe path has the actual killed product weight. -/
theorem actual_conditioned_safe_path_mass
    (T : ℕ) (hpos : 0 < actualSurvivalMass M q sigma p0 K (T + 0))
    (h : CausalHistory K K T) :
    (actualConditionedPrefix M q sigma p0 K T 0 hpos (safeHistory K T h)).toReal =
      matrixPathWeight (safeInitialRow p0 K) Q T h /
        actualSurvivalMass M q sigma p0 K T := by
  rw [actual_conditioned_prefix_mass M q sigma p0 K T 0 hpos
    (safeHistory K T h) (safeHistory_survives K T h) (currentState T h)
    (safeHistory_current K T h)]
  rw [remainingSurvival_zero, mul_one, state_safe_atom_eq_matrixPathWeight, Nat.add_zero]

/-- A positive actual prefix-survival event forces the relevant row denominator
to be positive. Global positive survival alone is not used for this conclusion. -/
theorem actual_positive_prefix_remaining_pos
    (t r : ℕ) (h : CausalHistory X X t)
    (hs : stateSurvives K t h) (i : K) (hi : currentState t h = i.1)
    (hpos : 0 < actualPrefixSurvivalMass M q sigma p0 K t r h) :
    0 < remainingSurvival Q r i := by
  rw [actual_prefix_survival_mass M q sigma p0 K t r h hs i hi] at hpos
  have hp : 0 ≤ (causalLaw p0 (policyPathKernel M pi) t h).toReal :=
    ENNReal.toReal_nonneg
  by_contra hn
  have hnonpos := mul_nonpos_of_nonneg_of_nonpos hp (le_of_not_gt hn)
  linarith

/-- The ratio of actual child and parent events is the finite-window row.
The two event horizons (t+1)+r and t+(r+1) are the same natural number.
The positive parent premise excludes exactly the undefined conditional rows. -/
theorem actual_next_prefix_ratio
    (t r : ℕ) (h : CausalHistory X X t)
    (hs : stateSurvives K t h) (i j : K) (hi : currentState t h = i.1)
    (hpos : 0 < actualPrefixSurvivalMass M q sigma p0 K t (r + 1) h) :
    actualPrefixSurvivalMass M q sigma p0 K (t + 1) r (h, j.1) /
        actualPrefixSurvivalMass M q sigma p0 K t (r + 1) h =
      finiteWindowRow Q r i j := by
  have hparent := actual_prefix_survival_mass M q sigma p0 K t (r + 1) h hs i hi
  have hchild := actual_prefix_survival_mass M q sigma p0 K (t + 1) r
    (h, j.1) ⟨hs, j.property⟩ j rfl
  have hg := actual_positive_prefix_remaining_pos M q sigma p0 K t (r + 1)
    h hs i hi hpos
  have hp : 0 < (causalLaw p0 (policyPathKernel M pi) t h).toReal := by
    rw [hparent] at hpos
    by_contra hn
    have hnonpos := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hg.le
    linarith
  have hstep :
      (causalLaw p0 (policyPathKernel M pi) (t + 1) (h, j.1)).toReal =
        (causalLaw p0 (policyPathKernel M pi) t h).toReal * Q i j := by
    change (pmfExtend (causalLaw p0 (policyPathKernel M pi) t)
      (policyPathKernel M pi t) (h, j.1)).toReal = _
    rw [UEOT.V3.PathError.pmfExtend_apply, ENNReal.toReal_mul]
    simp only [policyPathKernel, policyTransitionPMF_apply_toReal, hi,
      killedMatrix, policyMatrix]
  rw [hchild, hparent, hstep]
  unfold finiteWindowRow
  field_simp [hp.ne', hg.ne']

end ActualSource
end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceFiniteWindowCheck
