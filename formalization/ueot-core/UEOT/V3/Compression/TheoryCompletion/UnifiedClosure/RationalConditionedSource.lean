import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionCertificate

/-!
# Executable finite rational conditioning from the original source

Safety includes time zero. The horizon counts transitions, and null rows use
an explicit self-loop fallback. Casting the computed rows to PMFs connects to
the existing killed-source finite-window experiment.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RationalConditionedSourceCheck

open MeasureTheory UEOT.V3.PathError UEOT.V3.FiniteDiscountedControl
open UEOT.V3.CoreOperationalAssembly
open FiniteActionCertificateCheck FiniteActionRealizabilityCheck
open SourcePolicyPathBridgeCheck SameSourceKilledPathCheck
open SameSourceConditionedTerminalCheck SameSourceFiniteWindowCheck
open FiniteWindowDoobCheck TotalFiniteWindowCheck ConditionedActionTransportCheck
open scoped BigOperators

universe u

set_option backward.isDefEq.respectTransparency false

/-- Exact finite source interpreted as the existing controlled model. The
reward and discount fields are unused by finite path semantics. -/
noncomputable def rationalModel {X A : Type u} [Fintype X] [Fintype A]
    (P : X → A → X → ℚ) (hP : ∀ x a, ValidRow (P x a)) : Model X (fun _ => A) where
  transition := fun x a z => (P x a z : ℝ)
  reward := fun _ _ => 0
  rewardBound := 1
  discount := 1 / 2
  transition_nonneg := fun x a z => by exact_mod_cast (hP x a).1 z
  transition_sum_one := fun x a => by exact_mod_cast (hP x a).2
  reward_abs_le := by intros; norm_num
  discount_pos := by norm_num
  discount_lt_one := by norm_num

/-- The interpreted source preserves every exact input transition row. -/
theorem rationalModel_transitionPMF {X A : Type u} [Fintype X] [Fintype A] [Nonempty A]
    (P : X → A → X → ℚ) (hP : ∀ x a, ValidRow (P x a)) (x : X) (a : A) :
    (rationalModel P hP).transitionPMF x a = rowPMF (P x a) (hP x a) := by
  apply PMF.ext
  intro z
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [Model.transitionPMF_apply_toReal, rowPMF_toReal]
  rfl

/-- The baseline uses the same observation mapping and original action rows. -/
def baselineRow {X Y A : Type u} [Fintype A]
    (P : X → A → X → ℚ) (q : X → Y) (base : Y → A → ℚ) (x z : X) : ℚ :=
  ∑ a, base (q x) a * P x a z

/-- Remaining safe mass, on the safe alphabet, without runtime matrix powers.
ponytail: direct recursion repeats suffix sums; memoize when larger horizons
make the registered finite checker expensive. -/
def rationalRemaining {S : Type u} [Fintype S] (Q : S → S → ℚ) : ℕ → S → ℚ
  | 0, _ => 1
  | r + 1, i => ∑ j, Q i j * rationalRemaining Q r j

/-- The recursive computation is the existing remaining-survival expression. -/
theorem rationalRemaining_cast {S : Type u} [Fintype S] (Q : S → S → ℚ) :
    ∀ r i, (rationalRemaining Q r i : ℝ) =
      remainingSurvival (fun i j => (Q i j : ℝ)) r i := by
  intro r
  induction r with
  | zero => intro i; simp [rationalRemaining]
  | succ r ih =>
    intro i
    rw [rationalRemaining, Rat.cast_sum, remainingSurvival_succ]
    apply Finset.sum_congr rfl
    intro j _
    rw [Rat.cast_mul, ih]

/-- The exact safe-mass recursion preserves nonnegativity. -/
theorem rationalRemaining_nonneg {S : Type u} [Fintype S] (Q : S → S → ℚ)
    (hQ : ∀ i j, 0 ≤ Q i j) : ∀ r i, 0 ≤ rationalRemaining Q r i := by
  intro r
  induction r with
  | zero => intro i; exact zero_le_one
  | succ r ih =>
    intro i
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hQ i j) (ih j)

/-- Remaining mass on the ambient alphabet; unsafe states have zero mass even
at horizon zero. -/
def sourceRemaining {X : Type u} [Fintype X]
    (B : X → X → ℚ) (safe : X → Bool) (r : ℕ) (x : X) : ℚ :=
  if hx : safe x = true then
    rationalRemaining (fun i j : {x // safe x = true} => B i.val j.val) r ⟨x,hx⟩
  else 0

/-- Exact survival normalizer from the original initial row. -/
def sourceMass {X : Type u} [Fintype X]
    (B : X → X → ℚ) (p0 : X → ℚ) (safe : X → Bool) (T : ℕ) : ℚ :=
  ∑ x, p0 x * sourceRemaining B safe T x

/-- Actual prepared initial table, valid only for positive source mass. -/
def sourceInitial {X : Type u} [Fintype X]
    (B : X → X → ℚ) (p0 : X → ℚ) (safe : X → Bool) (T : ℕ) (x : X) : ℚ :=
  p0 x * sourceRemaining B safe T x / sourceMass B p0 safe T

/-- Total computed target row, with explicit self-loop on null/unsafe rows. -/
def sourceTarget {X : Type u} [Fintype X] [DecidableEq X]
    (B : X → X → ℚ) (safe : X → Bool) (T t : ℕ) (x z : X) : ℚ :=
  let r := T - (t + 1)
  if 0 < sourceRemaining B safe (r+1) x then
    B x z * sourceRemaining B safe r z / sourceRemaining B safe (r+1) x
  else if z = x then 1 else 0

private theorem sum_safe {X : Type u} [Fintype X] (safe : X → Bool) (f : X → ℚ) :
    (∑ x, if safe x = true then f x else 0) = ∑ x : {x // safe x = true}, f x.val := by
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype (Finset.univ.filter (fun x => safe x = true))
    (by intro x; simp) f

/-- The ambient recurrence includes the initial safety test. -/
theorem sourceRemaining_succ {X : Type u} [Fintype X]
    (B : X → X → ℚ) (safe : X → Bool) (r : ℕ) (x : X) :
    sourceRemaining B safe (r+1) x =
      if safe x = true then ∑ z, B x z * sourceRemaining B safe r z else 0 := by
  by_cases hx : safe x = true
  · rw [if_pos hx]
    calc
      sourceRemaining B safe (r+1) x =
          ∑ z : {z // safe z = true}, B x z.val * sourceRemaining B safe r z.val := by
        simp only [sourceRemaining, dif_pos hx, rationalRemaining]
        apply Finset.sum_congr rfl
        intro z _
        rw [dif_pos z.property]
      _ = ∑ z, if safe z = true then B x z * sourceRemaining B safe r z else 0 :=
        (sum_safe safe (fun z => B x z * sourceRemaining B safe r z)).symm
      _ = ∑ z, B x z * sourceRemaining B safe r z := by
        apply Finset.sum_congr rfl
        intro z _
        by_cases hz : safe z = true <;> simp [sourceRemaining, hz]
  · simp [sourceRemaining, hx]

/-- No negative mass enters the source conditioning computation. -/
theorem sourceRemaining_nonneg {X : Type u} [Fintype X]
    (B : X → X → ℚ) (hB : ∀ x z, 0 ≤ B x z) (safe : X → Bool) (r : ℕ) (x : X) :
    0 ≤ sourceRemaining B safe r x := by
  unfold sourceRemaining
  split
  · exact rationalRemaining_nonneg _ (fun (i j : {x // safe x = true}) => hB i.val j.val) _ _
  · exact le_refl 0

/-- Positive normalization validates the computed initial table. -/
theorem sourceInitial_valid {X : Type u} [Fintype X]
    (B : X → X → ℚ) (hB : ∀ x z, 0 ≤ B x z) (p0 : X → ℚ)
    (hp0 : ∀ x, 0 ≤ p0 x) (safe : X → Bool) (T : ℕ)
    (hpos : 0 < sourceMass B p0 safe T) : ValidRow (sourceInitial B p0 safe T) := by
  constructor
  · intro x
    exact div_nonneg (mul_nonneg (hp0 x) (sourceRemaining_nonneg B hB safe T x)) hpos.le
  · simp only [sourceInitial, ← Finset.sum_div]
    exact div_self hpos.ne'

/-- Total computed target rows are probability rows, including null fallbacks. -/
theorem sourceTarget_valid {X : Type u} [Fintype X] [DecidableEq X]
    (B : X → X → ℚ) (hB : ∀ x z, 0 ≤ B x z) (safe : X → Bool) (T t : ℕ) (x : X) :
    ValidRow (sourceTarget B safe T t x) := by
  unfold sourceTarget
  dsimp only
  split
  next hp =>
    constructor
    · intro z
      exact div_nonneg (mul_nonneg (hB x z) (sourceRemaining_nonneg B hB safe _ z)) hp.le
    · simp only [← Finset.sum_div]
      have hx : safe x = true := by
        by_contra hx
        simp [sourceRemaining, hx] at hp
      have heq : (∑ i, B x i * sourceRemaining B safe (T-(t+1)) i) =
          sourceRemaining B safe (T-(t+1)+1) x := by
        simpa only [if_pos hx] using (sourceRemaining_succ B safe (T-(t+1)) x).symm
      rw [heq]
      exact div_self hp.ne'
  next hp =>
    constructor
    · intro z; dsimp only; split <;> norm_num
    · simp

/-- Nonnegativity of the original baseline mixture is computed from its rows. -/
theorem baselineRow_nonneg {X Y A : Type u} [Fintype X] [Fintype A]
    (P : X → A → X → ℚ) (hP : ∀ x a, ValidRow (P x a))
    (q : X → Y) (base : Y → A → ℚ) (hbase : ∀ y, ValidRow (base y)) (x z : X) :
    0 ≤ baselineRow P q base x z :=
  Finset.sum_nonneg fun a _ => mul_nonneg ((hbase (q x)).1 a) ((hP x a).1 z)

/-- Baseline source identity, before killing or normalizing anything. -/
theorem baselineRow_cast {X Y A : Type u} [Fintype X] [Fintype A] [Nonempty A]
    (P : X → A → X → ℚ) (hP : ∀ x a, ValidRow (P x a))
    (q : X → Y) (base : Y → A → ℚ) (hbase : ∀ y, ValidRow (base y)) (x z : X) :
    (baselineRow P q base x z : ℝ) =
      policyMatrix (rationalModel P hP)
        (liftedStationaryPolicy q (fun y => rowPMF (base y) (hbase y))) x z := by
  simp only [baselineRow, Rat.cast_sum, Rat.cast_mul, policyMatrix,
    Model.policyTransition, liftedStationaryPolicy, rowPMF_toReal, rationalModel]

private theorem subtype_map_toReal {X : Type u} (safe : X → Bool)
    (p : PMF {x // safe x = true}) (x : X) :
    ((p.map Subtype.val) x).toReal =
      if hx : safe x = true then (p ⟨x,hx⟩).toReal else 0 := by
  classical
  by_cases hx : safe x = true
  · rw [dif_pos hx]
    exact congrArg ENNReal.toReal
      (pmf_map_injective_atom Subtype.val Subtype.val_injective p ⟨x,hx⟩)
  · rw [dif_neg hx]
    have hz : (p.map Subtype.val) x = 0 := by
      rw [PMF.map_apply]
      have hterm : (fun i : {x // safe x = true} => if x = i.val then p i else 0) =
          (fun _ => 0) := by
        funext i
        have hne : x ≠ i.val := by
          intro heq
          exact hx (heq.symm ▸ i.property)
        simp [hne]
      rw [hterm, tsum_zero]
    rw [hz]
    rfl

/-- The original decidable safety event, also including the initial state. -/
abbrev sourceSafe {X : Type u} (safe : X → Bool) : Set X := {x | safe x = true}

open scoped Classical

noncomputable section SameSource

variable {X Y A : Type u} [Fintype X] [Fintype A] [Nonempty A]
variable (P : X → A → X → ℚ) (hP : ∀ x a, ValidRow (P x a))
variable (q : X → Y) (base : Y → A → ℚ) (hbase : ∀ y, ValidRow (base y))
variable (p0 : X → ℚ) (hp0 : ValidRow p0) (safe : X → Bool)

local notation "B" => baselineRow P q base
local notation "M" => rationalModel P hP
local notation "sigma" => (fun y => rowPMF (base y) (hbase y))
local notation "K" => sourceSafe safe
local notation "Q" => killedMatrix M (liftedStationaryPolicy q sigma) K

local instance semanticSafeFintype : Fintype K :=
  @Subtype.fintype X (Membership.mem K)
    (fun x => Classical.propDecidable (x ∈ K)) inferInstance


private theorem rationalRemaining_instance_irrel {S : Type u} {F G : Fintype S}
    (DQ : S → S → ℚ) (r : ℕ) (x : S) :
    @rationalRemaining S F DQ r x = @rationalRemaining S G DQ r x := by
  cases Subsingleton.elim F G
  rfl

/-- The source's rational safe mass is the actual killed matrix's survival mass. -/
theorem sourceRemaining_eq_actual (r : ℕ) (x : K) :
    (sourceRemaining B safe r x.val : ℝ) = remainingSurvival Q r x := by
  have hx : safe x.val = true := x.property
  unfold sourceRemaining
  rw [dif_pos hx]
  have hcast := rationalRemaining_cast
    (fun i j : K => B i.val j.val) r x
  have heq : (fun i j : K => (B i.val j.val : ℝ)) = Q := by
    funext i j
    exact baselineRow_cast P hP q base hbase i.val j.val
  rw [heq] at hcast
  convert hcast using 1
  exact congrArg (fun z : ℚ => (z : ℝ)) (rationalRemaining_instance_irrel _ _ _)

/-- The computed positive/zero normalizer agrees with the original experiment;
Z=0 therefore cannot be mistaken for an arbitrary conditioned distribution. -/
theorem sourceMass_eq_actual
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A] (T : ℕ) :
    (sourceMass B p0 safe T : ℝ) = actualSurvivalMass M q sigma (rowPMF p0 hp0) K T := by
  rw [actual_survival_mass_eq_initial_remaining_sum]
  unfold sourceMass
  rw [Rat.cast_sum]
  calc
    (∑ x, ((p0 x * sourceRemaining B safe T x : ℚ) : ℝ)) =
        ∑ x, if safe x = true then (p0 x : ℝ) * (sourceRemaining B safe T x : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : safe x = true <;> simp [sourceRemaining, hx]
    _ = ∑ x : K, (p0 x.val : ℝ) * (sourceRemaining B safe T x.val : ℝ) := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype (Finset.univ.filter (fun x => safe x = true))
        (by intro x; simp) _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [sourceRemaining_eq_actual P hP q base hbase]
      simp only [safeInitialRow, rowPMF_toReal]

/-- Positive exact source mass supplies the positivity premise of the original
conditional experiment. -/
theorem actualSource_pos
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A] (T : ℕ)
    (hpos : 0 < sourceMass B p0 safe T) :
    0 < actualSurvivalMass M q sigma (rowPMF p0 hp0) K T := by
  rw [← sourceMass_eq_actual P hP q base hbase p0 hp0 safe T]
  exact_mod_cast hpos

/-- The literal rational initial table is the generated source's actual
remaining-survival tilt, with the same normalizer and unsafe zero mass. -/
theorem sourceInitial_eq_prepared
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A] (T : ℕ)
    (hpos : 0 < sourceMass B p0 safe T) :
    rowPMF (sourceInitial B p0 safe T)
      (sourceInitial_valid B (baselineRow_nonneg P hP q base hbase) p0 hp0.1 safe T hpos) =
      preparedInitial M q sigma (rowPMF p0 hp0) K T
        (actualSource_pos P hP q base hbase p0 hp0 safe T hpos)
        (fun _ x => PMF.pure x) (fun _ x => PMF.pure x) := by
  apply PMF.ext
  intro x
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [rowPMF_toReal]
  change (sourceInitial B p0 safe T x : ℝ) =
    (((windowInitial Q (killedMatrix_nonneg M (liftedStationaryPolicy q sigma) K)
      (safeInitialRow (rowPMF p0 hp0) K) (safeInitialRow_nonneg (rowPMF p0 hp0) K)
      T _).map Subtype.val) x).toReal
  rw [subtype_map_toReal]
  by_cases hx : safe x = true
  · rw [dif_pos hx]
    simp only [windowInitial, FiniteProbabilityRow.ofRealRow_apply_toReal,
      safeInitialRow, rowPMF_toReal]
    have hmass := sourceMass_eq_actual P hP q base hbase p0 hp0 safe T
    rw [actual_survival_mass_eq_initial_remaining_sum] at hmass
    change (sourceInitial B p0 safe T x : ℝ) =
      (p0 x : ℝ) * remainingSurvival Q T ⟨x,hx⟩ / _
    simp only [sourceInitial, Rat.cast_div, Rat.cast_mul]
    rw [sourceRemaining_eq_actual P hP q base hbase safe T ⟨x,hx⟩, hmass]
    rfl
  · rw [dif_neg hx]
    simp [sourceInitial, sourceRemaining, hx]

/-- Every interpreted computed target row is the original source's total
finite-window row, including its declared self-loop fallbacks. -/
theorem sourceTarget_eq_row [DecidableEq X] (T t : ℕ) (x : X) :
    rowPMF (sourceTarget B safe T t x)
      (sourceTarget_valid B (baselineRow_nonneg P hP q base hbase) safe T t x) =
      ambientWindowRow M q sigma K (fun _ i => PMF.pure i) (fun _ x => PMF.pure x)
        (T-(t+1)) x := by
  classical
  let r := T-(t+1)
  by_cases hp : 0 < sourceRemaining B safe (r+1) x
  · have hx : safe x = true := by
      by_contra hx
      simp [sourceRemaining, hx] at hp
    have hden := sourceRemaining_eq_actual P hP q base hbase safe (r+1) ⟨x,hx⟩
    have hp' : 0 < remainingSurvival Q (r+1) ⟨x,hx⟩ := by
      rw [← hden]
      exact_mod_cast hp
    apply PMF.ext
    intro z
    apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
    rw [rowPMF_toReal]
    change ((if 0 < sourceRemaining B safe (r+1) x then
        B x z * sourceRemaining B safe r z / sourceRemaining B safe (r+1) x
        else if z=x then 1 else 0 : ℚ) : ℝ) = _
    rw [if_pos hp, ambientWindowRow, dif_pos (show x ∈ K from hx), subtype_map_toReal]
    by_cases hz : safe z = true
    · rw [dif_pos hz]
      change ((B x z * sourceRemaining B safe r z / sourceRemaining B safe (r+1) x : ℚ) : ℝ) =
        (totalWindowRow Q (killedMatrix_nonneg M (liftedStationaryPolicy q sigma) K)
          (fun _ i => PMF.pure i) r ⟨x,hx⟩ ⟨z,hz⟩).toReal
      rw [totalWindowRow_apply_toReal_of_pos Q
        (killedMatrix_nonneg M (liftedStationaryPolicy q sigma) K) (fun _ i => PMF.pure i)
        r ⟨x,hx⟩ ⟨z,hz⟩ hp']
      simp only [finiteWindowRow, Rat.cast_div, Rat.cast_mul]
      rw [sourceRemaining_eq_actual P hP q base hbase safe r ⟨z,hz⟩, hden,
        baselineRow_cast P hP q base hbase]
      rfl
    · rw [dif_neg hz]
      simp [sourceRemaining, hz]
  · have hnull : ambientWindowRow M q sigma K (fun _ i => PMF.pure i)
        (fun _ x => PMF.pure x) r x = PMF.pure x := by
      unfold ambientWindowRow
      split
      next hx =>
        have hp' : ¬ 0 < remainingSurvival Q (r+1) ⟨x,hx⟩ := by
          rw [← sourceRemaining_eq_actual P hP q base hbase safe (r+1) ⟨x,hx⟩]
          exact_mod_cast hp
        rw [totalWindowRow, dif_neg hp', PMF.pure_map]
      next hx => rfl
    rw [hnull]
    apply PMF.ext
    intro z
    apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
    rw [rowPMF_toReal]
    change ((if 0 < sourceRemaining B safe (r+1) x then
        B x z * sourceRemaining B safe r z / sourceRemaining B safe (r+1) x
        else if z=x then 1 else 0 : ℚ) : ℝ) = _
    rw [if_neg hp, PMF.pure_apply]
    by_cases hzx : z=x <;> simp [hzx]

/-- The exact computed target, interpreted without selecting any policy, is
precisely the complete original baseline experiment conditioned on safety.
This is the source identity consumed by both positive and negative certificates. -/
theorem sourceTargetPath_eq_actual [DecidableEq X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A] (T : ℕ)
    (hpos : 0 < sourceMass B p0 safe T) :
    targetPath
      (rowPMF (sourceInitial B p0 safe T)
        (sourceInitial_valid B (baselineRow_nonneg P hP q base hbase) p0 hp0.1 safe T hpos))
      (fun t x => rowPMF (sourceTarget B safe T t x)
        (sourceTarget_valid B (baselineRow_nonneg P hP q base hbase) safe T t x)) T =
      actualConditionedPrefix M q sigma (rowPMF p0 hp0) K T 0
        (actualSource_pos P hP q base hbase p0 hp0 safe T hpos) := by
  rw [sourceInitial_eq_prepared P hP q base hbase p0 hp0 safe T hpos]
  have hrows : (fun t x => rowPMF (sourceTarget B safe T t x)
        (sourceTarget_valid B (baselineRow_nonneg P hP q base hbase) safe T t x)) =
      conditionedTargetRow M q sigma K T (fun _ i => PMF.pure i) (fun _ x => PMF.pure x) := by
    funext t x
    exact sourceTarget_eq_row P hP q base hbase safe T t x
  rw [hrows]
  change generatedAmbientPrefix M q sigma (rowPMF p0 hp0) K T
    (actualSource_pos P hP q base hbase p0 hp0 safe T hpos)
    (fun _ i => PMF.pure i) (fun _ x => PMF.pure x) T = _
  exact generated_ambient_eq_actual M q sigma (rowPMF p0 hp0) K T 0
    (actualSource_pos P hP q base hbase p0 hp0 safe T hpos)
    (fun _ i => PMF.pure i) (fun _ x => PMF.pure x)

end SameSource

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RationalConditionedSourceCheck
