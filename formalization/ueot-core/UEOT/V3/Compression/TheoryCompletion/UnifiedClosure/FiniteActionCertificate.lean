import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FinitePolicyPath

/-!
# Exact finite action certificates

Only rational finite sums run in the checkers. PMFs interpret the accepted
same table; the interpretation performs no search or choice. Occupancy is
computed from the target path, never supplied by a certificate.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionCertificateCheck

open UEOT.V3.PathError UEOT.V3.FiniteDiscountedControl UEOT.V3.CoreOperationalAssembly
open FiniteActionRealizabilityCheck ConditionedActionTransportCheck
open scoped BigOperators

universe u

/-- Exact finite probability-row validation. -/
def ValidRow {X : Type u} [Fintype X] (r : X → ℚ) : Prop :=
  (∀ x, 0 ≤ r x) ∧ ∑ x, r x = 1

instance {X : Type u} [Fintype X] (r : X → ℚ) : Decidable (ValidRow r) :=
  inferInstanceAs (Decidable ((∀ x, 0 ≤ r x) ∧ ∑ x, r x = 1))

/-- Mathematical interpretation of this exact table, not a selected witness. -/
noncomputable def rowPMF {X : Type u} [Fintype X]
    (r : X → ℚ) (hr : ValidRow r) : PMF X :=
  FiniteProbabilityRow.ofRealRow (fun x => (r x : ℝ))
    (fun x => by exact_mod_cast hr.1 x) (by exact_mod_cast hr.2)

@[simp] theorem rowPMF_toReal {X : Type u} [Fintype X]
    (r : X → ℚ) (hr : ValidRow r) (x : X) :
    (rowPMF r hr x).toReal = (r x : ℝ) :=
  FiniteProbabilityRow.ofRealRow_apply_toReal _ _ _ _

/-- Exact target-history mass. ponytail: enumerate small finite horizons;
use forward state masses if a registered input makes enumeration expensive. -/
def pathMass {X : Type u} (mu : X → ℚ) (R : ℕ → X → X → ℚ) :
    ∀ n, CausalHistory X X n → ℚ
  | 0, x => mu x
  | n + 1, h => pathMass mu R n h.1 * R n (currentState n h.1) h.2

/-- Target occupancy is recomputed from its own finite histories. -/
def occupied {X : Type u} (mu : X → ℚ) (R : ℕ → X → X → ℚ)
    (n : ℕ) (x : X) : Prop :=
  ∃ h : CausalHistory X X n, pathMass mu R n h ≠ 0 ∧ currentState n h = x

instance {X : Type u} [Fintype X] [DecidableEq X]
    (mu : X → ℚ) (R : ℕ → X → X → ℚ) (n : ℕ) (x : X) :
    Decidable (occupied mu R n x) :=
  inferInstanceAs (Decidable (∃ h : CausalHistory X X n,
    pathMass mu R n h ≠ 0 ∧ currentState n h = x))

theorem pathMass_eq {X : Type u} [Fintype X]
    (mu : X → ℚ) (R : ℕ → X → X → ℚ)
    (hmu : ValidRow mu) (hR : ∀ t x, ValidRow (R t x)) :
    ∀ n (h : CausalHistory X X n),
      (pathMass mu R n h : ℝ) =
        (targetPath (rowPMF mu hmu) (fun t x => rowPMF (R t x) (hR t x)) n h).toReal := by
  intro n
  induction n with
  | zero => intro h; exact (rowPMF_toReal mu hmu h).symm
  | succ n ih =>
    rintro ⟨h,z⟩
    change ((pathMass mu R n h * R n (currentState n h) z : ℚ) : ℝ) =
      (pmfExtend (targetPath (rowPMF mu hmu) (fun t x => rowPMF (R t x) (hR t x)) n)
        (fun h => rowPMF (R n (currentState n h)) (hR n (currentState n h))) (h,z)).toReal
    rw [Rat.cast_mul, ih, pmfExtend_apply, ENNReal.toReal_mul, rowPMF_toReal]

theorem occupied_iff {X : Type u} [Fintype X]
    (mu : X → ℚ) (R : ℕ → X → X → ℚ)
    (hmu : ValidRow mu) (hR : ∀ t x, ValidRow (R t x)) (n : ℕ) (x : X) :
    occupied mu R n x ↔
      x ∈ occupiedState (rowPMF mu hmu) (fun t x => rowPMF (R t x) (hR t x)) n := by
  have hne (h : CausalHistory X X n) : pathMass mu R n h ≠ 0 ↔
      targetPath (rowPMF mu hmu) (fun t x => rowPMF (R t x) (hR t x)) n h ≠ 0 := by
    rw [← Rat.cast_ne_zero (α := ℝ), pathMass_eq mu R hmu hR n h]
    exact ENNReal.toReal_ne_zero.trans (and_iff_left (PMF.apply_ne_top _ _))
  simp only [occupied, occupiedState, Set.mem_ofPred_eq, hne]

/-- Check the actual initial table and the same common action table on every
positive target occupancy row. Invalid candidates yield false, not a no-go. -/
def checkPositive {X Y A : Type u} [Fintype X] [Fintype Y] [Fintype A]
    [DecidableEq X] (p mu : X → ℚ) (P : X → A → X → ℚ)
    (R : ℕ → X → X → ℚ) (q : X → Y) (T : ℕ)
    (w : Fin T → Y → A → ℚ) : Bool :=
  decide (p = mu ∧ (∀ t y, ValidRow (w t y)) ∧
    ∀ (t : Fin T) x, occupied mu R t.val x → ∀ z,
      ∑ a, w t (q x) a * P x a z = R t.val x z)

/-- The accepted finite weight table, with an explicit post-horizon action. -/
noncomputable def policy {Y A : Type u} [Fintype A] {T : ℕ}
    (w : Fin T → Y → A → ℚ) (hw : ∀ t y, ValidRow (w t y)) (after : A) :
    ℕ → Y → PMF A :=
  fun n y => if h : n < T then rowPMF (w ⟨n,h⟩ y) (hw ⟨n,h⟩ y) else PMF.pure after

/-- Checker acceptance supplies exactly the initial law and occupied row
identities of its own interpreted table. The full-path consumer is separate. -/
theorem checkPositive_sound_rows
    {X Y A : Type u} [Fintype X] [Fintype Y] [Fintype A] [DecidableEq X]
    (p mu : X → ℚ) (P : X → A → X → ℚ) (R : ℕ → X → X → ℚ)
    (q : X → Y) (T : ℕ) (w : Fin T → Y → A → ℚ)
    (hp : ValidRow p) (hmu : ValidRow mu) (hP : ∀ x a, ValidRow (P x a))
    (hR : ∀ t x, ValidRow (R t x)) (after : A)
    (hcheck : checkPositive p mu P R q T w = true) :
    ∃ hw : ∀ t y, ValidRow (w t y),
      rowPMF p hp = rowPMF mu hmu ∧
      ∀ (t : Fin T) x,
        x ∈ occupiedState (rowPMF mu hmu) (fun t x => rowPMF (R t x) (hR t x)) t.val →
        actionMixture (fun a => rowPMF (P x a) (hP x a)) (policy w hw after t.val (q x)) =
          rowPMF (R t.val x) (hR t.val x) := by
  have hc := of_decide_eq_true hcheck
  rcases hc with ⟨hinit, hw, hrow⟩
  refine ⟨hw, ?_, ?_⟩
  · subst p; rfl
  · intro t x hx
    have hx' := (occupied_iff mu R hmu hR t.val x).mpr hx
    apply PMF.ext
    intro z
    apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
    change realRow (actionMixture (fun a => rowPMF (P x a) (hP x a))
      (policy w hw after t.val (q x))) z = _
    rw [realRow_actionMixture]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, realRow,
      policy, dif_pos t.isLt, rowPMF_toReal]
    exact_mod_cast hrow t x hx' z

/-- A strict finite rational separating functional on one occupied fiber. -/
structure Separation (X Y : Type u) where
  time : ℕ
  observation : Y
  coefficient : X → X → ℚ
  bound : ℚ
  gap : ℚ

/-- The fiber is computed here from (mu,R,q), not accepted from the witness. -/
def fiberScore {X Y : Type u} [Fintype X] [DecidableEq X] [DecidableEq Y]
    (mu : X → ℚ) (R : ℕ → X → X → ℚ) (q : X → Y)
    (c : Separation X Y) (v : X → X → ℚ) : ℚ :=
  ∑ x, if occupied mu R c.time x ∧ q x = c.observation then
    ∑ z, c.coefficient x z * v x z else 0

def checkNegative {X Y A : Type u} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq Y]
    (mu : X → ℚ) (P : X → A → X → ℚ) (R : ℕ → X → X → ℚ)
    (q : X → Y) (T : ℕ) (c : Separation X Y) : Bool :=
  decide (c.time < T ∧ 0 < c.gap ∧
    (∀ a, fiberScore mu R q c (fun x => P x a) ≤ c.bound) ∧
    c.bound + c.gap ≤ fiberScore mu R q c (R c.time))

/-- The real linear functional corresponding to the exact rational check. -/
noncomputable def realFiberScore {X Y : Type u} [Fintype X] [DecidableEq X] [DecidableEq Y]
    (mu : X → ℚ) (R : ℕ → X → X → ℚ) (q : X → Y)
    (c : Separation X Y) (v : X → X → ℝ) : ℝ :=
  ∑ x, if occupied mu R c.time x ∧ q x = c.observation then
    ∑ z, (c.coefficient x z : ℝ) * v x z else 0

@[simp] theorem cast_fiberScore {X Y : Type u} [Fintype X] [DecidableEq X] [DecidableEq Y]
    (mu : X → ℚ) (R : ℕ → X → X → ℚ) (q : X → Y)
    (c : Separation X Y) (v : X → X → ℚ) :
    (fiberScore mu R q c v : ℝ) = realFiberScore mu R q c (fun x z => (v x z : ℝ)) := by
  simp only [fiberScore, realFiberScore, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : occupied mu R c.time x ∧ q x = c.observation
  · simp only [if_pos hx, Rat.cast_sum, Rat.cast_mul]
  · simp only [if_neg hx, Rat.cast_zero]

private theorem realFiberScore_sum {X Y A : Type u} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq Y]
    (mu : X → ℚ) (R : ℕ → X → X → ℚ) (q : X → Y)
    (c : Separation X Y) (v : A → X → X → ℝ) :
    realFiberScore mu R q c (fun x z => ∑ a, v a x z) =
      ∑ a, realFiberScore mu R q c (v a) := by
  unfold realFiberScore
  simp_rw [Finset.mul_sum]
  calc
    _ = ∑ x : X, ∑ a : A,
        if occupied mu R c.time x ∧ q x = c.observation then
          ∑ z, (c.coefficient x z : ℝ) * v a x z else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : occupied mu R c.time x ∧ q x = c.observation
      · simp only [if_pos hx]
        exact Finset.sum_comm
      · simp [hx]
    _ = _ := Finset.sum_comm

private theorem realFiberScore_mul {X Y : Type u} [Fintype X]
    [DecidableEq X] [DecidableEq Y]
    (mu : X → ℚ) (R : ℕ → X → X → ℚ) (q : X → Y)
    (c : Separation X Y) (r : ℝ) (v : X → X → ℝ) :
    realFiberScore mu R q c (fun x z => r * v x z) =
      r * realFiberScore mu R q c v := by
  unfold realFiberScore
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : occupied mu R c.time x ∧ q x = c.observation
  · simp only [if_pos hx]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    ring
  · simp [hx]

/-- A checked rational separator excludes every real action distribution,
not just the rational candidates visited by a search algorithm. -/
theorem checkNegative_sound
    {X Y A : Type u} [Fintype X] [Fintype A] [DecidableEq X] [DecidableEq Y]
    (mu : X → ℚ) (P : X → A → X → ℚ) (R : ℕ → X → X → ℚ)
    (q : X → Y) (T : ℕ) (c : Separation X Y)
    (hP : ∀ x a, ValidRow (P x a)) (hR : ∀ t x, ValidRow (R t x))
    (hcheck : checkNegative mu P R q T c = true) :
    ¬ ∃ sigma : PMF A, ∀ x, occupied mu R c.time x → q x = c.observation →
      actionMixture (fun a => rowPMF (P x a) (hP x a)) sigma =
        rowPMF (R c.time x) (hR c.time x) := by
  have hc := of_decide_eq_true hcheck
  rcases hc with ⟨_, hgap, hbound, htarget⟩
  rintro ⟨sigma, hrows⟩
  have heq : realFiberScore mu R q c (fun x z => (R c.time x z : ℝ)) =
      ∑ a, (sigma a).toReal *
        realFiberScore mu R q c (fun x z => (P x a z : ℝ)) := by
    calc
      _ = realFiberScore mu R q c
          (fun x z => ∑ a, (sigma a).toReal * (P x a z : ℝ)) := by
        unfold realFiberScore
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : occupied mu R c.time x ∧ q x = c.observation
        · simp only [if_pos hx]
          apply Finset.sum_congr rfl
          intro z _
          congr 1
          have he := congrFun (congrArg realRow (hrows x hx.1 hx.2)) z
          rw [realRow_actionMixture] at he
          simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, realRow,
            rowPMF_toReal] using he.symm
        · simp [hx]
      _ = _ := by
        rw [realFiberScore_sum]
        apply Finset.sum_congr rfl
        intro a _
        exact realFiberScore_mul mu R q c _ _
  have hupper : realFiberScore mu R q c (fun x z => (R c.time x z : ℝ)) ≤
      (c.bound : ℝ) := by
    rw [heq]
    calc
      _ ≤ ∑ a, (sigma a).toReal * (c.bound : ℝ) := by
        apply Finset.sum_le_sum
        intro a _
        apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        rw [← cast_fiberScore]
        exact_mod_cast hbound a
      _ = _ := by rw [← Finset.sum_mul, coverage_sum_toReal sigma, one_mul]
  have hlower : (c.bound : ℝ) + (c.gap : ℝ) ≤
      realFiberScore mu R q c (fun x z => (R c.time x z : ℝ)) := by
    rw [← cast_fiberScore]
    exact_mod_cast htarget
  have hg : (0 : ℝ) < (c.gap : ℝ) := by exact_mod_cast hgap
  linarith

/-- Validity proof for exactly the weight table accepted by the Boolean
checker. It carries no alternative strategy or implementation witness. -/
theorem acceptedWeights
    {X Y A : Type u} [Fintype X] [Fintype Y] [Fintype A] [DecidableEq X]
    (p mu : X → ℚ) (P : X → A → X → ℚ) (R : ℕ → X → X → ℚ)
    (q : X → Y) (T : ℕ) (w : Fin T → Y → A → ℚ)
    (hcheck : checkPositive p mu P R q T w = true) :
    ∀ t y, ValidRow (w t y) :=
  (of_decide_eq_true hcheck).2.1

/-- Acceptance certifies the complete actual state path of `policy w` itself.
The model's rational-row identity is an independently proved source interface. -/
theorem checkPositive_sound
    {X Y A : Type u} [Fintype X] [Fintype Y] [Fintype A] [DecidableEq X] [Nonempty A]
    (p mu : X → ℚ) (P : X → A → X → ℚ) (R : ℕ → X → X → ℚ)
    (q : X → Y) (T : ℕ) (w : Fin T → Y → A → ℚ)
    (hp : ValidRow p) (hmu : ValidRow mu) (hP : ∀ x a, ValidRow (P x a))
    (hR : ∀ t x, ValidRow (R t x)) (after : A)
    (M : Model X (fun _ => A))
    (hmodel : ∀ x a, M.transitionPMF x a = rowPMF (P x a) (hP x a))
    (hcheck : checkPositive p mu P R q T w = true) :
    (causalLaw (rowPMF p hp)
      (riskMicroControlKernel q (fun _ => M.transitionPMF)
        (timeObservationPolicy (policy w (acceptedWeights p mu P R q T w hcheck) after))) T).map
      (SourcePolicyPathBridgeCheck.eraseActionHistory T) =
        targetPath (rowPMF mu hmu) (fun t x => rowPMF (R t x) (hR t x)) T := by
  obtain ⟨hw, hinit, hrows⟩ :=
    checkPositive_sound_rows p mu P R q T w hp hmu hP hR after hcheck
  apply FinitePolicyPathCheck.specified_policy_path_of_rows M q
    (policy w (acceptedWeights p mu P R q T w hcheck) after)
    (rowPMF p hp) (rowPMF mu hmu) (fun t x => rowPMF (R t x) (hR t x)) T hinit
  intro t ht x hx
  have htransition : M.transitionPMF x = fun a => rowPMF (P x a) (hP x a) :=
    funext (hmodel x)
  rw [htransition]
  exact hrows ⟨t,ht⟩ x hx

/-- The strict separator is a complete-path no-go for all real, time-varying
current-observation policies. The chosen initial law is arbitrary: no initial
preparation can remove this occupied-fiber obstruction. -/
theorem checkNegative_path_no_go
    {X Y A : Type u} [Fintype X] [Fintype A] [DecidableEq X] [DecidableEq Y] [Nonempty A]
    (mu : X → ℚ) (P : X → A → X → ℚ) (R : ℕ → X → X → ℚ)
    (q : X → Y) (T : ℕ) (c : Separation X Y)
    (hmu : ValidRow mu) (hP : ∀ x a, ValidRow (P x a))
    (hR : ∀ t x, ValidRow (R t x))
    (M : Model X (fun _ => A))
    (hmodel : ∀ x a, M.transitionPMF x a = rowPMF (P x a) (hP x a))
    (hcheck : checkNegative mu P R q T c = true) (p : PMF X) :
    ¬ ∃ sigma : ℕ → Y → PMF A,
      (causalLaw p (riskMicroControlKernel q (fun _ => M.transitionPMF)
        (timeObservationPolicy sigma)) T).map (SourcePolicyPathBridgeCheck.eraseActionHistory T) =
          targetPath (rowPMF mu hmu) (fun t x => rowPMF (R t x) (hR t x)) T := by
  rintro ⟨sigma, hpath⟩
  apply checkNegative_sound mu P R q T c hP hR hcheck
  refine ⟨sigma c.time c.observation, ?_⟩
  intro x hx hq
  have hocc := (occupied_iff mu R hmu hR c.time x).mp hx
  have ht : c.time < T := (of_decide_eq_true hcheck).1
  have hrows := (FinitePolicyPathCheck.specified_policy_path_iff M q sigma p
    (rowPMF mu hmu) (fun t x => rowPMF (R t x) (hR t x)) T).mp hpath
  have hrow := hrows.2 c.time ht x hocc
  have htransition : M.transitionPMF x = fun a => rowPMF (P x a) (hP x a) :=
    funext (hmodel x)
  rw [htransition] at hrow
  simpa only [hq] using hrow

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionCertificateCheck
