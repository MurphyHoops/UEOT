import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteWindowDoob
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscape

/-!
# Total finite-window kernels generate the original conditioned experiment

Every row is a PMF, including zero remaining-survival rows, where an arbitrary
fallback is used. The initial law is constructed from the actual killed row.
The generated law is proved equal to the complete original experiment filtered
on survival, rather than being defined as that filter. The proof retains null
prefixes, time zero, and arbitrary original initial unsafe mass.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.TotalFiniteWindowCheck

open MeasureTheory UEOT.V3.PathError UEOT.V3.FiniteDiscountedControl
open UEOT.V3.CoreOperationalAssembly UEOT.V3.QSDPerron
open SourcePolicyPathBridgeCheck SameSourceKilledPathCheck
open SameSourceConditionedTerminalCheck SameSourceFiniteWindowCheck FiniteWindowDoobCheck
open scoped BigOperators Classical

noncomputable section
universe u

/-- A total row on the conditioned state alphabet. The fallback is consulted
only when this row has zero remaining-survival mass. -/
def totalWindowRow {S : Type u} [Fintype S]
    (Q : Matrix S S ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (fallback : ℕ → S → PMF S) (r : ℕ) (i : S) : PMF S :=
  if hp : 0 < remainingSurvival Q (r + 1) i then
    finiteWindowRowPMF Q hQ r i hp
  else fallback r i

/-- The positive branch is exactly the previously proved finite-window row. -/
theorem totalWindowRow_apply_toReal_of_pos
    {S : Type u} [Fintype S] (Q : Matrix S S ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (fallback : ℕ → S → PMF S)
    (r : ℕ) (i j : S) (hp : 0 < remainingSurvival Q (r + 1) i) :
    (totalWindowRow Q hQ fallback r i j).toReal = finiteWindowRow Q r i j := by
  rw [totalWindowRow, dif_pos hp, finiteWindowRowPMF_apply_toReal]

/-- The finite-horizon initial tilt is normalized by its own full path mass. -/
def windowInitial {S : Type u} [Fintype S]
    (Q : Matrix S S ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (eta : S → ℝ) (heta : ∀ i, 0 ≤ eta i) (T : ℕ)
    (hpos : 0 < initialPairing eta (remainingSurvival Q T)) : PMF S :=
  FiniteProbabilityRow.ofRealRow
    (fun i => eta i * remainingSurvival Q T i /
      initialPairing eta (remainingSurvival Q T))
    (fun i => div_nonneg
      (mul_nonneg (heta i) (remainingSurvival_nonneg Q hQ T i)) hpos.le)
    (by
      rw [← Finset.sum_div]
      exact div_self hpos.ne')

private theorem windowInitial_apply_toReal
    {S : Type u} [Fintype S] (Q : Matrix S S ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (eta : S → ℝ) (heta : ∀ i, 0 ≤ eta i)
    (T : ℕ) (hpos : 0 < initialPairing eta (remainingSurvival Q T)) (i : S) :
    (windowInitial Q hQ eta heta T hpos i).toReal =
      eta i * remainingSurvival Q T i / initialPairing eta (remainingSurvival Q T) := by
  exact FiniteProbabilityRow.ofRealRow_apply_toReal _ _ _ i

/-- Actual PMF recursion using total, time-dependent next-state rows.
Only prefixes through T have a conditioning interpretation. -/
def windowPathLaw {S : Type u} [Fintype S]
    (Q : Matrix S S ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (eta : S → ℝ) (heta : ∀ i, 0 ≤ eta i) (T : ℕ)
    (hpos : 0 < initialPairing eta (remainingSurvival Q T))
    (fallback : ℕ → S → PMF S) (n : ℕ) : PMF (CausalHistory S S n) :=
  causalLaw (windowInitial Q hQ eta heta T hpos)
    (fun k h => totalWindowRow Q hQ fallback (T - (k + 1)) (currentState k h)) n

private theorem successor_weight_zero_of_remaining_zero
    {S : Type u} [Fintype S] (Q : Matrix S S ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (r : ℕ) (i j : S)
    (hz : remainingSurvival Q (r + 1) i = 0) :
    Q i j * remainingSurvival Q r j = 0 := by
  have hnonneg (k : S) : 0 ≤ Q i k * remainingSurvival Q r k :=
    mul_nonneg (hQ i k) (remainingSurvival_nonneg Q hQ r k)
  have hle : Q i j * remainingSurvival Q r j ≤ remainingSurvival Q (r + 1) i := by
    rw [remainingSurvival_succ]
    exact Finset.single_le_sum (fun k _ => hnonneg k) (Finset.mem_univ j)
  exact le_antisymm (hz ▸ hle) (hnonneg j)

/-- Every generated prefix has the killed prefix weight times its remaining
survival mass. The zero-denominator branch is proved using nonnegative suffix
weights, so the statement has no positive-prefix assumption. -/
theorem windowPathLaw_prefix_atom
    {S : Type u} [Fintype S] (Q : Matrix S S ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (eta : S → ℝ) (heta : ∀ i, 0 ≤ eta i)
    (T : ℕ) (hpos : 0 < initialPairing eta (remainingSurvival Q T))
    (fallback : ℕ → S → PMF S) :
    ∀ n, n ≤ T → ∀ h : CausalHistory S S n,
      (windowPathLaw Q hQ eta heta T hpos fallback n h).toReal =
        matrixPathWeight eta Q n h * remainingSurvival Q (T - n) (currentState n h) /
          initialPairing eta (remainingSurvival Q T) := by
  intro n
  induction n with
  | zero =>
      intro _ h
      simpa only [windowPathLaw, causalLaw, matrixPathWeight, currentState,
        Nat.sub_zero] using windowInitial_apply_toReal Q hQ eta heta T hpos h
  | succ n ih =>
      intro hn h
      rcases h with ⟨g, j⟩
      have hn' : n ≤ T := by omega
      have hsub : T - n = (T - (n + 1)) + 1 := by omega
      change (pmfExtend (windowPathLaw Q hQ eta heta T hpos fallback n)
        (fun g => totalWindowRow Q hQ fallback (T - (n + 1))
          (currentState n g)) (g, j)).toReal = _
      rw [UEOT.V3.PathError.pmfExtend_apply, ENNReal.toReal_mul, ih hn' g, hsub]
      change (matrixPathWeight eta Q n g *
          remainingSurvival Q ((T - (n + 1)) + 1) (currentState n g) /
          initialPairing eta (remainingSurvival Q T)) *
          (totalWindowRow Q hQ fallback (T - (n + 1)) (currentState n g) j).toReal =
        (matrixPathWeight eta Q n g * Q (currentState n g) j) *
          remainingSurvival Q (T - (n + 1)) j /
          initialPairing eta (remainingSurvival Q T)
      by_cases hp : 0 < remainingSurvival Q ((T - (n + 1)) + 1) (currentState n g)
      · rw [totalWindowRow_apply_toReal_of_pos Q hQ fallback _ _ _ hp]
        unfold finiteWindowRow
        field_simp [hp.ne', hpos.ne']
      · have hz : remainingSurvival Q ((T - (n + 1)) + 1) (currentState n g) = 0 :=
          le_antisymm (le_of_not_gt hp) (remainingSurvival_nonneg Q hQ _ _)
        have hterm := successor_weight_zero_of_remaining_zero Q hQ
          (T - (n + 1)) (currentState n g) j hz
        rw [hz, mul_zero, zero_div, zero_mul, mul_assoc, hterm, mul_zero, zero_div]

/-- Any two choices on null rows generate exactly the same complete prefix
law through the conditioning horizon. -/
theorem windowPathLaw_fallback_independent
    {S : Type u} [Fintype S] (Q : Matrix S S ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (eta : S → ℝ) (heta : ∀ i, 0 ≤ eta i)
    (T : ℕ) (hpos : 0 < initialPairing eta (remainingSurvival Q T))
    (fallback other : ℕ → S → PMF S) (n : ℕ) (hn : n ≤ T) :
    windowPathLaw Q hQ eta heta T hpos fallback n =
      windowPathLaw Q hQ eta heta T hpos other n := by
  apply PMF.ext
  intro h
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _)
    (PMF.apply_ne_top _ _)).mp
  rw [windowPathLaw_prefix_atom Q hQ eta heta T hpos fallback n hn,
    windowPathLaw_prefix_atom Q hQ eta heta T hpos other n hn]

private theorem safeHistory_survives_all {X : Type u} (K : Set X) :
    ∀ n (h : CausalHistory K K n), stateSurvives K n (safeHistory K n h) := by
  intro n
  induction n with
  | zero => intro h; exact h.property
  | succ n ih => intro h; exact ⟨ih h.1, h.2.property⟩

private theorem safeHistory_exists {X : Type u} (K : Set X) :
    ∀ n (h : CausalHistory X X n), stateSurvives K n h →
      ∃ g : CausalHistory K K n, safeHistory K n g = h := by
  intro n
  induction n with
  | zero => intro h hh; exact ⟨⟨h, hh⟩, rfl⟩
  | succ n ih =>
      intro h hh
      obtain ⟨g, hg⟩ := ih h.1 hh.1
      refine ⟨(g, ⟨h.2, hh.2⟩), ?_⟩
      change (safeHistory K n g, h.2) = h
      rw [hg]

section ActualSource

variable {X Y A : Type u} [Fintype X] [Fintype A] [Nonempty A]
variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace A] [MeasurableSingletonClass A]
variable (M : Model X (fun _ => A)) (q : X → Y) (sigma : Y → PMF A)
variable (p0 : PMF X) (K : Set X)

local notation "pi" => liftedStationaryPolicy q sigma
local notation "Q" => killedMatrix M pi K
local notation "eta" => safeInitialRow p0 K

private theorem actual_pairing_pos (T : ℕ)
    (hpos : 0 < actualSurvivalMass M q sigma p0 K T) :
    0 < initialPairing eta (remainingSurvival Q T) := by
  simpa only [actual_survival_mass_eq_initial_remaining_sum, initialPairing] using hpos

/-- A separately generated prefix law on safe states, from the total rows and
the actual initial remaining-survival tilt. No filtered law occurs in this definition. -/
def generatedConditionedPrefix (T : ℕ)
    (hpos : 0 < actualSurvivalMass M q sigma p0 K T)
    (fallback : ℕ → K → PMF K) (n : ℕ) : PMF (CausalHistory K K n) :=
  windowPathLaw Q (killedMatrix_nonneg M pi K) eta (safeInitialRow_nonneg p0 K)
    T (actual_pairing_pos M q sigma p0 K T hpos) fallback n

/-- Whole-prefix source identity, including all null and unsafe atoms.
For n=T this is the complete original survival-conditioned state path. -/
theorem generated_prefix_eq_actual
    (t r : ℕ) (hpos : 0 < actualSurvivalMass M q sigma p0 K (t + r))
    (fallback : ℕ → K → PMF K) :
    (generatedConditionedPrefix M q sigma p0 K (t + r) hpos fallback t).map
        (safeHistory K t) = actualConditionedPrefix M q sigma p0 K t r hpos := by
  apply PMF.ext
  intro h
  by_cases hs : stateSurvives K t h
  · obtain ⟨g, rfl⟩ := safeHistory_exists K t h hs
    have hinj : Function.Injective (safeHistory K t) :=
      PathObservationEscapeCheck.riskHistoryMap_injective_general
        Subtype.val Subtype.val Subtype.val_injective Subtype.val_injective t
    rw [pmf_map_injective_atom (safeHistory K t) hinj]
    apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _)
      (PMF.apply_ne_top _ _)).mp
    unfold generatedConditionedPrefix
    rw [windowPathLaw_prefix_atom Q (killedMatrix_nonneg M pi K) eta
      (safeInitialRow_nonneg p0 K) (t + r)
      (actual_pairing_pos M q sigma p0 K (t + r) hpos) fallback t (by omega)]
    rw [actual_conditioned_prefix_mass M q sigma p0 K t r hpos
      (safeHistory K t g) (safeHistory_survives_all K t g) (currentState t g)
      (by cases t <;> rfl), state_safe_atom_eq_matrixPathWeight]
    rw [actual_survival_mass_eq_initial_remaining_sum]
    simp only [Nat.add_sub_cancel_left, initialPairing]
  · rw [actual_conditioned_prefix_eq_zero_of_not_survives M q sigma p0 K t r hpos h hs]
    apply (PMF.apply_eq_zero_iff _ h).2
    intro hh
    rcases (PMF.mem_support_map_iff _ _ _).1 hh with ⟨g, _, hg⟩
    exact hs (hg ▸ safeHistory_survives_all K t g)

/-- Total next-state PMF on the original microscopic state space. Unsafe
states also have explicit fallback rows; no value of a partial kernel is used. -/
def ambientWindowRow (fallback : ℕ → K → PMF K)
    (outside : ℕ → X → PMF X) (r : ℕ) (x : X) : PMF X :=
  if hx : x ∈ K then
    (totalWindowRow Q (killedMatrix_nonneg M pi K) fallback r ⟨x, hx⟩).map Subtype.val
  else outside r x

/-- The independent total-kernel process on the original state alphabet.
Its initial PMF is the explicit remaining-survival tilt, not a path filter. -/
def generatedAmbientPrefix (T : ℕ)
    (hpos : 0 < actualSurvivalMass M q sigma p0 K T)
    (fallback : ℕ → K → PMF K) (outside : ℕ → X → PMF X) (n : ℕ) :
    PMF (CausalHistory X X n) :=
  causalLaw
    ((windowInitial Q (killedMatrix_nonneg M pi K) eta (safeInitialRow_nonneg p0 K)
      T (actual_pairing_pos M q sigma p0 K T hpos)).map Subtype.val)
    (fun k h => ambientWindowRow M q sigma K fallback outside
      (T - (k + 1)) (currentState k h)) n

private theorem generated_map_eq_ambient
    (T : ℕ) (hpos : 0 < actualSurvivalMass M q sigma p0 K T)
    (fallback : ℕ → K → PMF K) (outside : ℕ → X → PMF X) :
    ∀ n, (generatedConditionedPrefix M q sigma p0 K T hpos fallback n).map
      (safeHistory K n) = generatedAmbientPrefix M q sigma p0 K T hpos fallback outside n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      let P := generatedConditionedPrefix M q sigma p0 K T hpos fallback n
      let L : CausalHistory K K n → PMF K := fun g =>
        totalWindowRow Q (killedMatrix_nonneg M pi K) fallback
          (T - (n + 1)) (currentState n g)
      let B : CausalHistory X X n → PMF X := fun g =>
        ambientWindowRow M q sigma K fallback outside (T - (n + 1)) (currentState n g)
      have hrow : (fun g => (L g).map Subtype.val) =
          (fun g => B (safeHistory K n g)) := by
        funext g
        have hcurrent : currentState n (safeHistory K n g) = (currentState n g).1 := by
          cases n <;> rfl
        simp only [L, B, hcurrent, ambientWindowRow,
          dif_pos (currentState n g).property]
      change (pmfExtend P L).map
        (fun gz => (safeHistory K n gz.1, gz.2.1)) =
          pmfExtend (generatedAmbientPrefix M q sigma p0 K T hpos fallback outside n) B
      calc
        _ = ((pmfExtend P L).map (fun gz => (gz.1, gz.2.1))).map
              (fun gz => (safeHistory K n gz.1, gz.2)) := by
                rw [PMF.map_comp]
                rfl
        _ = (pmfExtend P (fun g => B (safeHistory K n g))).map
              (fun gz => (safeHistory K n gz.1, gz.2)) := by
                rw [risk_map_extend_right, hrow]
        _ = pmfExtend (P.map (safeHistory K n)) B :=
              coverage_map_extend_reference P (safeHistory K n) B
        _ = _ := by rw [ih]

/-- The complete generated law on X equals the state projection of the
original action/state experiment conditioned on survival through t+r. This
includes T=0 and requires only positivity of this actual horizon's mass. -/
theorem generated_ambient_eq_actual
    (t r : ℕ) (hpos : 0 < actualSurvivalMass M q sigma p0 K (t + r))
    (fallback : ℕ → K → PMF K) (outside : ℕ → X → PMF X) :
    generatedAmbientPrefix M q sigma p0 K (t + r) hpos fallback outside t =
      actualConditionedPrefix M q sigma p0 K t r hpos := by
  rw [← generated_map_eq_ambient M q sigma p0 K (t + r) hpos fallback outside t]
  exact generated_prefix_eq_actual M q sigma p0 K t r hpos fallback

/-- Both zero-survival and unsafe-state fallback choices are irrelevant for
every generated prefix through the conditioning horizon. -/
theorem generated_ambient_fallback_independent
    (t r : ℕ) (hpos : 0 < actualSurvivalMass M q sigma p0 K (t + r))
    (fallback other : ℕ → K → PMF K) (outside otherOutside : ℕ → X → PMF X) :
    generatedAmbientPrefix M q sigma p0 K (t + r) hpos fallback outside t =
      generatedAmbientPrefix M q sigma p0 K (t + r) hpos other otherOutside t := by
  rw [generated_ambient_eq_actual M q sigma p0 K t r hpos fallback outside,
    generated_ambient_eq_actual M q sigma p0 K t r hpos other otherOutside]

end ActualSource
end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.TotalFiniteWindowCheck
