import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataSource

/-! The rank-one target is derived from the same baseline source and safety
experiment. The existing total finite-window identity supplies the full path;
no source/target path equality is a hypothesis. -/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataConditioned
open MeasureTheory UEOT.V3.PathError UEOT.V3.FiniteDiscountedControl
open UEOT.V3.CoreOperationalAssembly UEOT.V3.QSDPerron
open FiniteDataSource SourcePolicyPathBridgeCheck SameSourceKilledPathCheck
open SameSourceConditionedTerminalCheck SameSourceFiniteWindowCheck
open FiniteWindowDoobCheck TotalFiniteWindowCheck ConditionedActionTransportCheck
open scoped BigOperators Classical
noncomputable section

def safe : Set State := {x | x.val < 2}
def safeEquiv : Fin 2 ≃ safe where
  toFun i := ⟨⟨i.val, by omega⟩, i.isLt⟩
  invFun i := ⟨i.val.val, i.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem sum_safe {M : Type*} [AddCommMonoid M] (f : safe → M) :
    (∑ i : safe, f i) = f (safeEquiv 0) + f (safeEquiv 1) := by
  simpa [Fin.sum_univ_succ] using (safeEquiv.sum_comp f).symm

def rate (p : Param) (x : State) : ℝ := if x = 0 then p.r0 else p.r1
def mean (p : Param) : ℝ := (p.r0+p.r1)/2
abbrev killed (p : Param) (hp : Admissible p) : Matrix safe safe ℝ :=
  killedMatrix (model p hp) (liftedStationaryPolicy observe baseline) safe

private theorem rate_pos (p : Param) (hp : Admissible p) (i : safe) : 0 < rate p i.val := by
  unfold rate
  split
  · exact hp.1
  · exact hp.2.2.1

private theorem mean_pos (p : Param) (hp : Admissible p) : 0 < mean p := by
  exact div_pos (add_pos hp.1 hp.2.2.1) (by norm_num)

/-- The actual killed risk matrix has identical safe columns. -/
theorem killed_entry (p : Param) (hp : Admissible p) (i j : safe) :
    killed p hp i j = rate p i.val / 2 := by
  rcases safeEquiv.surjective i with ⟨i,rfl⟩
  rcases safeEquiv.surjective j with ⟨j,rfl⟩
  fin_cases i <;> fin_cases j <;>
    simp [killed, killedMatrix, policyMatrix, Model.policyTransition,
      liftedStationaryPolicy, baseline, model, transition, rate,
      safeEquiv, Fin.sum_univ_succ]

/-- For a positive remaining horizon the original safe mass factors into
one initial risk rate and a power of the mean rate. -/
theorem remaining_succ (p : Param) (hp : Admissible p) :
    ∀ n i, remainingSurvival (killed p hp) (n+1) i = rate p i.val * mean p ^ n := by
  intro n
  induction n with
  | zero =>
      intro i
      rw [remainingSurvival_succ, sum_safe]
      simp only [remainingSurvival_zero, killed_entry, mul_one, pow_zero]
      ring
  | succ n ih =>
      intro i
      rw [remainingSurvival_succ, sum_safe, ih, ih, killed_entry, killed_entry]
      change rate p i.val / 2 * (p.r0 * mean p ^ n) +
        rate p i.val / 2 * (p.r1 * mean p ^ n) = rate p i.val * mean p ^ (n+1)
      rw [pow_succ]
      unfold mean
      ring

private theorem remaining_pos (p : Param) (hp : Admissible p) (n : ℕ) (i : safe) :
    0 < remainingSurvival (killed p hp) n i := by
  cases n with
  | zero => simp
  | succ n => rw [remaining_succ]; exact mul_pos (rate_pos p hp i) (pow_pos (mean_pos p hp) n)

private theorem initial_safe_real (i : safe) : (initial i.val).toReal = 1/2 := by
  rcases safeEquiv.surjective i with ⟨i,rfl⟩
  fin_cases i <;> norm_num [initial, safePMF_real, safeEquiv]

private theorem nu_safe_real (p : Param) (hp : Admissible p) (i : safe) :
    (nu p hp i.val).toReal = rate p i.val / (p.r0+p.r1) := by
  have hs : p.r0+p.r1 ≠ 0 := (add_pos hp.1 hp.2.2.1).ne'
  rcases safeEquiv.surjective i with ⟨i,rfl⟩
  fin_cases i <;> simp [nu, safePMF_real, tilt, rate, safeEquiv]
  field_simp
  ring

private theorem mapped_safe_real (s : PMF safe) (x : State) :
    ((s.map Subtype.val) x).toReal =
      if x=0 then (s (safeEquiv 0)).toReal else
      if x=1 then (s (safeEquiv 1)).toReal else 0 := by
  rw [PMF.map_apply, tsum_fintype, sum_safe]
  fin_cases x <;> simp [safeEquiv]

/-- The explicit positive-window row of this same killed source: earlier
rows use the normalized risk rates; the final safe transition is fair. -/
theorem safe_window_row (p : Param) (hp : Admissible p) (r : ℕ) (i j : safe) :
    finiteWindowRow (killed p hp) r i j =
      if r=0 then 1/2 else rate p j.val / (p.r0+p.r1) := by
  have hi : rate p i.val ≠ 0 := (rate_pos p hp i).ne'
  have hm : mean p ≠ 0 := (mean_pos p hp).ne'
  have hs : p.r0+p.r1 ≠ 0 := (add_pos hp.1 hp.2.2.1).ne'
  cases r with
  | zero =>
      simp [finiteWindowRow, killed_entry, remaining_succ]
      field_simp
  | succ n =>
      simp only [finiteWindowRow, killed_entry, remaining_succ, Nat.succ_ne_zero, if_false]
      rw [pow_succ]
      field_simp [hi, hm, hs, pow_ne_zero n hm]
      unfold mean
      ring

private theorem initial_ratio (p : Param) (hp : Admissible p) (n : ℕ) (r : ℝ) :
    (1/2 : ℝ)*r*mean p ^ n / mean p ^ (n+1) = r/(p.r0+p.r1) := by
  have hm : mean p ≠ 0 := (mean_pos p hp).ne'
  have hs : p.r0+p.r1 ≠ 0 := (add_pos hp.1 hp.2.2.1).ne'
  rw [pow_succ]
  field_simp [hm, hs, pow_ne_zero n hm]
  unfold mean
  ring


private theorem ambient_row (p : Param) (hp : Admissible p) (r : ℕ) (x : State) :
    ambientWindowRow (model p hp) observe baseline safe (fun _ i => PMF.pure i)
      (fun r _ => if r=0 then fair else nu p hp) r x =
        if r=0 then fair else nu p hp := by
  by_cases hx : x ∈ safe
  · rw [ambientWindowRow, dif_pos hx]
    have hsaf (j : safe) :
        (totalWindowRow (killed p hp) (killedMatrix_nonneg (model p hp)
          (liftedStationaryPolicy observe baseline) safe) (fun _ i => PMF.pure i) r ⟨x,hx⟩ j).toReal =
            ((if r=0 then fair else nu p hp) j.val).toReal := by
      rw [totalWindowRow_apply_toReal_of_pos _ _ _ _ _ _ (remaining_pos p hp (r+1) ⟨x,hx⟩),
        safe_window_row]
      by_cases hr : r=0
      · simp only [if_pos hr, fair]
        exact (initial_safe_real j).symm
      · simp only [if_neg hr]
        exact (nu_safe_real p hp j).symm
    apply PMF.ext
    intro z
    apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
    by_cases hz : z ∈ safe
    · rw [pmf_map_injective_atom Subtype.val Subtype.val_injective _ ⟨z,hz⟩]
      exact hsaf ⟨z,hz⟩
    · rw [mapped_safe_real]
      fin_cases z <;> simp_all [safe, fair, initial, nu]
      split_ifs <;> simp
  · rw [ambientWindowRow, dif_neg hx]


variable [MeasurableSpace State] [MeasurableSingletonClass State]

/-- The actual original baseline survival mass, including initial safety. -/
theorem source_mass (p : Param) (hp : Admissible p) (T : ℕ) :
    actualSurvivalMass (model p hp) observe baseline initial safe T = mean p ^ T := by
  rw [actual_survival_mass_eq_initial_remaining_sum, sum_safe]
  simp only [safeInitialRow, initial_safe_real]
  change (1/2 : ℝ) * remainingSurvival (killed p hp) T (safeEquiv 0) +
    (1/2 : ℝ) * remainingSurvival (killed p hp) T (safeEquiv 1) = mean p ^ T
  cases T with
  | zero => norm_num
  | succ n =>
      rw [remaining_succ, remaining_succ]
      simp only [rate, safeEquiv]
      norm_num
      unfold mean
      rw [pow_succ]
      ring

/-- Positivity is structural throughout the declared parameter domain,
independently of a rare-event reference-mass gap. -/
theorem source_positive (p : Param) (hp : Admissible p) (T : ℕ) :
    0 < actualSurvivalMass (model p hp) observe baseline initial safe T := by
  rw [source_mass]
  exact pow_pos (mean_pos p hp) T

private theorem pairing_eq (p : Param) (hp : Admissible p) (T : ℕ) :
    initialPairing (safeInitialRow initial safe) (remainingSurvival (killed p hp) T) =
      mean p ^ T := by
  exact (actual_survival_mass_eq_initial_remaining_sum
    (model p hp) observe baseline initial safe T).symm.trans (source_mass p hp T)

/-- The initial conditional law is actually computed from the source. At zero
horizon it remains the original safe initial law; at positive horizons it is nu. -/
theorem prepared_initial (p : Param) (hp : Admissible p) (T : ℕ)
    (fallback : ℕ → safe → PMF safe) (outside : ℕ → State → PMF State) :
    preparedInitial (model p hp) observe baseline initial safe T
      (source_positive p hp T) fallback outside =
        if T=0 then initial else nu p hp := by
  apply PMF.ext
  intro x
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  change (((windowInitial (killed p hp) _ (safeInitialRow initial safe) _ T _).map
    Subtype.val) x).toReal = ((if T=0 then initial else nu p hp) x).toReal
  by_cases hx : x ∈ safe
  · rw [pmf_map_injective_atom Subtype.val Subtype.val_injective _ ⟨x,hx⟩]
    simp only [windowInitial, FiniteProbabilityRow.ofRealRow_apply_toReal, pairing_eq]
    change (initial x).toReal * remainingSurvival (killed p hp) T ⟨x,hx⟩ / mean p ^ T = _
    rw [initial_safe_real ⟨x,hx⟩]
    cases T with
    | zero => simp [initial_safe_real ⟨x,hx⟩]
    | succ n =>
        simp only [Nat.succ_ne_zero, if_false]
        rw [nu_safe_real p hp ⟨x,hx⟩, remaining_succ]
        simpa only [mul_assoc] using initial_ratio p hp n (rate p x)
  · rw [mapped_safe_real]
    fin_cases x <;> simp_all [safe, initial, nu]
    split_ifs <;> simp

/-- The complete rank-one target is the actual same-source baseline path
conditioned on its original safety event. This holds for T=0 as well: its
initial law is then initial, not the positive-horizon tilt. -/
theorem target_eq_actual (p : Param) (hp : Admissible p) (T : ℕ) :
    target p hp T = actualConditionedPrefix (model p hp) observe baseline initial safe T 0
      (source_positive p hp T) := by
  let fallback : ℕ → safe → PMF safe := fun _ i => PMF.pure i
  let outside : ℕ → State → PMF State := fun r _ => if r=0 then fair else nu p hp
  have hgenerated : generatedAmbientPrefix (model p hp) observe baseline initial safe T
      (source_positive p hp T) fallback outside T = target p hp T := by
    change causalLaw (preparedInitial (model p hp) observe baseline initial safe T
      (source_positive p hp T) fallback outside)
      (fun t h => ambientWindowRow (model p hp) observe baseline safe fallback outside
        (T-(t+1)) (currentState t h)) T = _
    rw [prepared_initial]
    apply congrArg (fun K => causalLaw (if T=0 then initial else nu p hp) K T)
    funext t h
    rw [show ambientWindowRow (model p hp) observe baseline safe fallback outside
        (T-(t+1)) (currentState t h) =
          if T-(t+1)=0 then fair else nu p hp from ambient_row p hp _ _]
    unfold targetRow
    by_cases ht : t+1<T
    · rw [if_neg (by omega), if_pos ht]
    · rw [if_pos (by omega), if_neg ht]
  exact hgenerated.symm.trans (generated_ambient_eq_actual
    (model p hp) observe baseline initial safe T 0 (source_positive p hp T) fallback outside)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataConditioned
