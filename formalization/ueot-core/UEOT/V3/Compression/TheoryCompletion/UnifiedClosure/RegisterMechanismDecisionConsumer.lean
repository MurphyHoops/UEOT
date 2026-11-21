import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionSource
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteJointDecisionFastSolver
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteMechanismRegretCertificate

/-!
# The registered H3 fixed-mechanism consumer

The source, seven actions, single wallet and whole-run evaluation are fixed.
The three exact finite computations use the old solver on the NEW joint belief:
S oracle, G oracle, and the (3/4,1/4) lower-bound witness. The deployed program
is the very same returned pair of tables, selected by an independent uniform
four-point seed, once at initialization. Mechanism and world noise are not
arguments of `returned`. No reset or additional learning budget is used.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionConsumer

open scoped BigOperators
open RegisterJointDecisionSource (Act Obs Noise)
open RegisterMechanismDecisionSource
open FiniteJointDecisionBelief FiniteJointDecisionSolver
open FiniteJointDecisionFilteredModel FiniteJointDecisionSupportedPolicy

instance : Nonempty FaultMechanism := ⟨.S⟩

theorem sum_mechanisms {X : Type*} [AddCommMonoid X] (f : FaultMechanism → X) :
    (∑ m, f m) = f .S + f .G := by
  have hu : (Finset.univ : Finset FaultMechanism) = {.S,.G} := by decide
  rw [hu]
  simp

def parameters : Parameters where
  goal := true
  normal := 1/2
  normal_bounds := by norm_num
  tariff := 1
  tariff_pos := by norm_num
  price := 1/4
  price_nonneg := by norm_num
  discount := 1
  discount_bounds := by norm_num

inductive Input where
  | knownS
  | knownG
  | dual
  deriving DecidableEq, Repr

def prior : Input → FaultMechanism → ℚ
  | .knownS, .S => 1
  | .knownS, .G => 0
  | .knownG, .S => 0
  | .knownG, .G => 1
  | .dual, .S => 3/4
  | .dual, .G => 1/4

theorem prior_nonneg (q : Input) (m : FaultMechanism) : 0 ≤ prior q m := by
  cases q <;> cases m <;> norm_num [prior]

theorem prior_total (q : Input) : ∑ m, prior q m = 1 := by
  rw [sum_mechanisms]
  cases q <;> norm_num [prior]

def registeredInfo (q : Input) : Info :=
  initialInfo parameters (prior q) (prior_nonneg q) (prior_total q) ⟨2, by norm_num⟩

def observations : List Obs := [(false,false),(false,true),(true,false),(true,true)]

theorem observations_complete (o : Obs) : o ∈ observations := by
  rcases o with ⟨b,c⟩
  cases b <;> cases c <;> simp [observations]

/-- This is the old cached implementation, whose complete value/table pair is
proved equal to the original solver, including all counterfactual rows. -/
def cachedAt (q : Input) (H : ℕ) : ℚ × Table Act Obs H :=
  FiniteJointDecisionFastSolver.fastSolve (model parameters) observations
    observations_complete H (registeredInfo q)

def cachedResult (q : Input) : ℚ × Table Act Obs 3 := cachedAt q 3

def returnedS : Table Act Obs 3 := (cachedResult .knownS).2
def returnedG : Table Act Obs 3 := (cachedResult .knownG).2

/-- The complete executable return. `seed` is independent controller randomness,
not a hidden source label. Its distribution is fixed before the mechanism run. -/
def returned (seed : Fin 4) : Table Act Obs 3 :=
  if seed.val = 0 then returnedS else returnedG

 theorem cachedAt_eq (q : Input) (H : ℕ) :
    cachedAt q H = (optimalValue (model parameters) H (registeredInfo q),
      solve (model parameters) H (registeredInfo q)) :=
  FiniteJointDecisionFastSolver.fastSolve_eq _ _ _ _ _

 theorem returnedS_eq_solve : returnedS = solve (model parameters) 3 (registeredInfo .knownS) := by
  simp only [returnedS, cachedResult, cachedAt_eq]

 theorem returnedG_eq_solve : returnedG = solve (model parameters) 3 (registeredInfo .knownG) := by
  simp only [returnedG, cachedResult, cachedAt_eq]

/-- Complete actual source value, from the damaged founder with fixed m. -/
def tableJ {H : ℕ} (table : Table Act Obs H) (m : FaultMechanism) : ℚ :=
  sourceValue (source parameters) (gain parameters) parameters.discount table
    (initialWorld parameters.goal m)

/-! ### Pure integer-scaled kernel evaluation (zero compiler-trust axioms) -/

section KernelIntExactEval

open RegisterJointDecisionSource (effective cap)
open RegisterJointDecisionConsumer (Wallet allActions menu menu_nonempty advance charge)

private theorem sum_obs {X : Type*} [AddCommMonoid X] (f : Obs → X) :
    (∑ o : Obs, f o) =
      f (false, false) + f (false, true) + f (true, false) + f (true, true) := by
  rw [Fintype.sum_prod_type]
  have hb : (Finset.univ : Finset Bool) = {false, true} := by decide
  simp [hb, add_assoc]

private theorem sum_noise_params (w : World) (a : Act) (F : Obs → World → ℚ) :
    (∑ z : Noise, (source parameters).chance w z *
        F ((source parameters).observe w a z) ((source parameters).next w a z)) =
      (1 / 2 : ℚ) * F (observe true w a (true, false)) (step true w a (true, false)) +
      (1 / 2 : ℚ) * F (observe true w a (false, false)) (step true w a (false, false)) := by
  rw [show (∑ z : Noise, _) = _ by exact sum_obs _]
  dsimp [source, parameters, RegisterJointDecisionSource.primitiveWeight]
  rw [step_label true w a false true false, observe_label true w a false true false,
      step_label true w a true true false, observe_label true w a true true false]
  ring

private abbrev UBelief := List (World × ℕ)

private def usum : UBelief → ℕ
  | [] => 0
  | (_, u) :: rest => u + usum rest

private def uexpect (U : UBelief) (f : World → ℚ) : ℚ :=
  match U with
  | [] => 0
  | (w, u) :: rest => (u : ℚ) * f w + uexpect rest f

private def uinsert (w : World) (u : ℕ) : UBelief → UBelief
  | [] => [(w, u)]
  | (w', u') :: rest =>
      if w = w' then (w', u' + u) :: rest
      else (w', u') :: uinsert w u rest

private theorem usum_uinsert (w : World) (u : ℕ) (U : UBelief) :
    usum (uinsert w u U) = u + usum U := by
  induction U with
  | nil => simp [uinsert, usum]
  | cons hd tl ih =>
      rcases hd with ⟨w', u'⟩
      dsimp [uinsert]
      split
      · simp [usum]; omega
      · simp [usum, ih]; omega

private theorem uexpect_uinsert (w : World) (u : ℕ) (U : UBelief) (f : World → ℚ) :
    uexpect (uinsert w u U) f = (u : ℚ) * f w + uexpect U f := by
  induction U with
  | nil => simp [uinsert, uexpect]
  | cons hd tl ih =>
      rcases hd with ⟨w', u'⟩
      dsimp [uinsert]
      split
      · next h => subst h; simp [uexpect, Nat.cast_add]; ring
      · simp [uexpect, ih]; ring

private def unext (U : UBelief) (a : Act) (o : Obs) : UBelief :=
  match U with
  | [] => []
  | (w, u) :: rest =>
      let acc := unext rest a o
      let acc1 := if observe true w a (true, false) = o
        then uinsert (step true w a (true, false)) u acc else acc
      if observe true w a (false, false) = o
        then uinsert (step true w a (false, false)) u acc1 else acc1

private theorem usum_unext_cast (U : UBelief) (a : Act) (o : Obs) :
    ((usum (unext U a o) : ℕ) : ℚ) =
      uexpect U (fun w =>
        (if observe true w a (true, false) = o then (1 : ℚ) else 0) +
        (if observe true w a (false, false) = o then (1 : ℚ) else 0)) := by
  induction U with
  | nil => simp [unext, usum, uexpect]
  | cons hd tl ih =>
      rcases hd with ⟨w, u⟩
      dsimp only [unext, uexpect]
      by_cases h1 : observe true w a (true, false) = o <;>
      by_cases h2 : observe true w a (false, false) = o <;>
      simp only [h1, h2, ↓reduceIte, usum_uinsert, Nat.cast_add, ih] <;> ring

private theorem uexpect_unext (U : UBelief) (a : Act) (o : Obs) (f : World → ℚ) :
    uexpect (unext U a o) f =
      uexpect U (fun w =>
        (if observe true w a (true, false) = o then f (step true w a (true, false)) else 0) +
        (if observe true w a (false, false) = o then f (step true w a (false, false)) else 0)) := by
  induction U with
  | nil => simp [unext, uexpect]
  | cons hd tl ih =>
      rcases hd with ⟨w, u⟩
      dsimp only [unext, uexpect]
      by_cases h1 : observe true w a (true, false) = o <;>
      by_cases h2 : observe true w a (false, false) = o <;>
      simp only [h1, h2, ↓reduceIte, uexpect_uinsert, ih] <;> ring

private def Represents (U : UBelief) (b : Belief World) : Prop :=
  0 < usum U ∧ ∀ f : World → ℚ, uexpect U f = (usum U : ℚ) * expect b f

private theorem mass_from_represents {U : UBelief} {b : Belief World}
    (hUb : Represents U b) (a : Act) (o : Obs) :
    2 * (usum U : ℚ) * mass (source parameters) b a o = (usum (unext U a o) : ℚ) := by
  rw [usum_unext_cast, hUb.2]
  have hmass : mass (source parameters) b a o =
      expect b (fun w =>
        (1 / 2 : ℚ) * (if observe true w a (true, false) = o then 1 else 0) +
        (1 / 2 : ℚ) * (if observe true w a (false, false) = o then 1 else 0)) := by
    unfold mass joint expect
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro x _
    have h := sum_noise_params (b.state x) a (fun o' _ => if o' = o then (1 : ℚ) else 0)
    calc
      (∑ z : Noise, if (source parameters).observe (b.state x) a z = o
          then b.weight x * (source parameters).chance (b.state x) z else 0)
        = b.weight x * (∑ z : Noise, (source parameters).chance (b.state x) z *
            (if (source parameters).observe (b.state x) a z = o then 1 else 0)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro z _
          split <;> ring
      _ = b.weight x * ((1 / 2 : ℚ) * (if observe true (b.state x) a (true, false) = o then 1 else 0) +
            (1 / 2 : ℚ) * (if observe true (b.state x) a (false, false) = o then 1 else 0)) := by
          rw [h]
  rw [hmass]
  dsimp [expect]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

private theorem represents_posterior {U : UBelief} {b : Belief World}
    (hUb : Represents U b) (a : Act) (o : Obs) (hpos : 0 < usum (unext U a o)) :
    Represents (unext U a o) (posterior (source parameters) b a o) := by
  refine ⟨hpos, fun f => ?_⟩
  have hm := mass_from_represents hUb a o
  have hS0 : (usum U : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hUb.1)
  have hSno : (usum (unext U a o) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hpos)
  have hmass_ne : mass (source parameters) b a o ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hm
    exact hSno hm.symm
  unfold posterior
  dsimp only
  simp only [hmass_ne, ↓reduceDIte]
  rw [uexpect_unext, hUb.2]
  dsimp [expect, normalizeWeights]
  rw [Fintype.sum_prod_type]
  simp only [div_mul_eq_mul_div, ← Finset.sum_div]
  have hjoint :
      (∑ x : b.Atom, ∑ z : Noise, joint (source parameters) b a o (x, z) *
          f ((source parameters).next (b.state x) a z)) =
        (1 / 2 : ℚ) * expect b (fun w =>
          (if observe true w a (true, false) = o then f (step true w a (true, false)) else 0) +
          (if observe true w a (false, false) = o then f (step true w a (false, false)) else 0)) := by
    dsimp [expect]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    have h := sum_noise_params (b.state x) a (fun o' w' => if o' = o then f w' else 0)
    calc
      (∑ z : Noise, joint (source parameters) b a o (x, z) *
          f ((source parameters).next (b.state x) a z))
        = b.weight x * (∑ z : Noise, (source parameters).chance (b.state x) z *
            (if (source parameters).observe (b.state x) a z = o
              then f ((source parameters).next (b.state x) a z) else 0)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro z _
          unfold joint
          split <;> ring
      _ = (1 / 2 : ℚ) * (b.weight x *
            ((if observe true (b.state x) a (true, false) = o
              then f (step true (b.state x) a (true, false)) else 0) +
             (if observe true (b.state x) a (false, false) = o
              then f (step true (b.state x) a (false, false)) else 0))) := by
          rw [h]
          split <;> split <;> ring
  change (usum U : ℚ) * expect b (fun w =>
      (if observe true w a (true, false) = o then f (step true w a (true, false)) else 0) +
      (if observe true w a (false, false) = o then f (step true w a (false, false)) else 0)) = _
  rw [hjoint, ← hm]
  field_simp [hS0, hmass_ne]

private def gain4 (o : Obs) : ℤ :=
  (if o.1 then 4 else 0) - (if o.2 then 1 else 0)

private theorem gain_eq_gain4 (a : Act) (o : Obs) :
    4 * gain parameters a o = (gain4 o : ℚ) := by
  rcases o with ⟨b₁, b₂⟩
  cases b₁ <;> cases b₂ <;> norm_num [gain, parameters, charge, gain4]

private def capNat (a : Act) : ℕ :=
  if (effective false a).2.isSome then 1 else 0

private theorem cap_eq_capNat (a : Act) : cap a = (capNat a : ℚ) := by
  unfold cap capNat
  split <;> norm_num

private def menuNat (bal : ℕ) : List Act :=
  allActions.filter (fun a => decide (capNat a ≤ bal))

private theorem menuNat_eq_menu (bal : ℕ) :
    menuNat bal = menu parameters.tariff ⟨(bal : ℚ), Nat.cast_nonneg bal⟩ := by
  unfold menuNat menu
  congr 1
  funext a
  have hc : parameters.tariff * cap a = (capNat a : ℚ) := by
    rw [cap_eq_capNat]
    dsimp [parameters]
    ring
  simp only [hc, Nat.cast_le]

private theorem menuNat_nonempty (bal : ℕ) : menuNat bal ≠ [] := by
  rw [menuNat_eq_menu]
  exact menu_nonempty _ _

private def advanceNat (bal : ℕ) (o : Obs) : ℕ :=
  if o.2 then bal - 1 else bal

private theorem advanceNat_eq_advance (bal : ℕ) (a : Act) (o : Obs) :
    (⟨(advanceNat bal o : ℚ), Nat.cast_nonneg _⟩ : Wallet) =
      advance parameters.tariff ⟨(bal : ℚ), Nat.cast_nonneg bal⟩ a o := by
  apply Subtype.ext
  dsimp [advanceNat, advance, parameters, charge]
  rcases o with ⟨b₁, b₂⟩
  cases b₂
  · simp
  · simp only [↓reduceIte]
    cases bal with
    | zero => norm_num
    | succ k =>
        simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
        exact (max_eq_right (Nat.cast_nonneg k)).symm

private inductive CTree : ℕ → Type where
  | chalt : CTree 0
  | cnode {n : ℕ} : Act → CTree n → CTree n → CTree n → CTree n → CTree (n + 1)

private def CTree.child {n : ℕ} (t00 t01 t10 t11 : CTree n) : Obs → CTree n
  | (false, false) => t00
  | (false, true) => t01
  | (true, false) => t10
  | (true, true) => t11

private def CTree.toTable : {n : ℕ} → CTree n → Table Act Obs n
  | 0, .chalt => .halt
  | _ + 1, .cnode a t00 t01 t10 t11 =>
      .node a (fun o => (CTree.child t00 t01 t10 t11 o).toTable)

private def cselectScored {X : Type*} (x : ℤ × X) : List (ℤ × X) → ℤ × X
  | [] => x
  | y :: ys =>
      let best := cselectScored y ys
      if x.1 < best.1 then best else x

private theorem cselectScored_map {X : Type*} (f : Act → ℤ × X) (scoreQ : Act → ℚ)
    (c : ℚ) (hc : 0 < c) (hsc : ∀ a, (f a).1 = c * scoreQ a) :
    ∀ (xs : List Act) (a : Act),
      cselectScored (f a) (xs.map f) = f (selectBest scoreQ a xs) := by
  intro xs
  induction xs with
  | nil => intro a; rfl
  | cons b bs ih =>
      intro a
      simp only [List.map_cons, cselectScored, selectBest, ih]
      have hlt : ((f a).1 < (f (selectBest scoreQ b bs)).1) ↔
          (scoreQ a < scoreQ (selectBest scoreQ b bs)) := by
        rw [← Int.cast_lt (R := ℚ), hsc a, hsc (selectBest scoreQ b bs)]
        constructor <;> intro h <;> nlinarith
      by_cases h : scoreQ a < scoreQ (selectBest scoreQ b bs)
      · have hi : (f a).1 < (f (selectBest scoreQ b bs)).1 := hlt.mpr h
        simp [h, hi]
      · have hi : ¬ ((f a).1 < (f (selectBest scoreQ b bs)).1) := fun h' => h (hlt.mp h')
        simp [h, hi]

private def cchooseScored {X : Type*} (f : Act → ℤ × X) :
    (xs : List Act) → xs ≠ [] → ℤ × X
  | [], h => False.elim (h rfl)
  | x :: rest, _ => cselectScored (f x) (rest.map f)

private def cactionInt {n : ℕ}
    (rec : UBelief × ℕ → ℤ × CTree n) (i : UBelief × ℕ) (a : Act) :
    ℤ × CTree (n + 1) :=
  let stepObs (o : Obs) : ℤ × CTree n :=
    let U' := unext i.1 a o
    let So := usum U'
    if So = 0 then
      (0, (rec (i.1, advanceNat i.2 o)).2)
    else
      let c := rec (U', advanceNat i.2 o)
      (((2 ^ n : ℕ) : ℤ) * (So : ℤ) * gain4 o + c.1, c.2)
  let r00 := stepObs (false, false)
  let r01 := stepObs (false, true)
  let r10 := stepObs (true, false)
  let r11 := stepObs (true, true)
  (r00.1 + r01.1 + r10.1 + r11.1, .cnode a r00.2 r01.2 r10.2 r11.2)

private def csolveInt : (n : ℕ) → UBelief × ℕ → ℤ × CTree n
  | 0, _ => (0, .chalt)
  | n + 1, i =>
      cchooseScored (cactionInt (csolveInt n) i) (menuNat i.2) (menuNat_nonempty i.2)

private theorem cactionInt_spec (n : ℕ)
    (ih : ∀ (U : UBelief) (b : Belief World) (bal : ℕ),
      Represents U b →
      ((csolveInt n (U, bal)).1 : ℚ) =
        4 * (2 ^ n : ℚ) * (usum U : ℚ) *
          optimalValue (model parameters) n (b, ⟨(bal : ℚ), Nat.cast_nonneg bal⟩) ∧
      (csolveInt n (U, bal)).2.toTable =
        solve (model parameters) n (b, ⟨(bal : ℚ), Nat.cast_nonneg bal⟩))
    (U : UBelief) (b : Belief World) (bal : ℕ) (hUb : Represents U b) (a : Act) :
    ((cactionInt (csolveInt n) (U, bal) a).1 : ℚ) =
      4 * (2 ^ (n + 1) : ℚ) * (usum U : ℚ) *
        qValue (model parameters) (optimalValue (model parameters) n)
          (b, ⟨(bal : ℚ), Nat.cast_nonneg bal⟩) a ∧
    (cactionInt (csolveInt n) (U, bal) a).2.toTable =
      .node a (fun o => solve (model parameters) n
        ((model parameters).next (b, ⟨(bal : ℚ), Nat.cast_nonneg bal⟩) a o)) := by
  have hobs (o : Obs) :
      (let U' := unext U a o
       let So := usum U'
       if So = 0 then ((0 : ℤ), (csolveInt n (U, advanceNat bal o)).2)
       else
         let c := csolveInt n (U', advanceNat bal o)
         (((2 ^ n : ℕ) : ℤ) * (So : ℤ) * gain4 o + c.1, c.2)).1 =
        (4 * (2 ^ (n + 1) : ℚ) * (usum U : ℚ) *
          ((model parameters).prob (b, ⟨(bal : ℚ), Nat.cast_nonneg bal⟩) a o *
            ((model parameters).reward (b, ⟨(bal : ℚ), Nat.cast_nonneg bal⟩) a o +
              (model parameters).discount *
                optimalValue (model parameters) n
                  ((model parameters).next (b, ⟨(bal : ℚ), Nat.cast_nonneg bal⟩) a o))) : ℚ) ∧
      (let U' := unext U a o
       let So := usum U'
       if So = 0 then ((0 : ℤ), (csolveInt n (U, advanceNat bal o)).2)
       else
         let c := csolveInt n (U', advanceNat bal o)
         (((2 ^ n : ℕ) : ℤ) * (So : ℤ) * gain4 o + c.1, c.2)).2.toTable =
        solve (model parameters) n
          ((model parameters).next (b, ⟨(bal : ℚ), Nat.cast_nonneg bal⟩) a o) := by
    have hm := mass_from_represents hUb a o
    have hS0 : (usum U : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hUb.1)
    have hadv := advanceNat_eq_advance bal a o
    dsimp only
    by_cases hSo : usum (unext U a o) = 0
    · simp only [hSo, ↓reduceIte, Int.cast_zero]
      have hmz : mass (source parameters) b a o = 0 := by
        rw [hSo, Nat.cast_zero] at hm
        have h2S : 2 * (usum U : ℚ) ≠ 0 := mul_ne_zero (by norm_num) hS0
        exact (mul_eq_zero.mp hm).resolve_left h2S
      have hpost : posterior (source parameters) b a o = b := by simp [posterior, hmz]
      have ⟨_, ht⟩ := ih U b (advanceNat bal o) hUb
      refine ⟨?_, ?_⟩
      · change (0 : ℚ) = 4 * (2 ^ (n + 1) : ℚ) * (usum U : ℚ) * (mass (source parameters) b a o * _)
        simp [hmz]
      · change (csolveInt n (U, advanceNat bal o)).2.toTable =
          solve (model parameters) n (posterior (source parameters) b a o,
            advance parameters.tariff ⟨(bal : ℚ), Nat.cast_nonneg bal⟩ a o)
        rw [hpost, ← hadv, ht]
    · simp only [hSo, ↓reduceIte]
      have hpos : 0 < usum (unext U a o) := Nat.pos_of_ne_zero hSo
      have hrep' := represents_posterior hUb a o hpos
      have ⟨hv, ht⟩ := ih (unext U a o) (posterior (source parameters) b a o)
        (advanceNat bal o) hrep'
      refine ⟨?_, ?_⟩
      · push_cast
        rw [hv, ← gain_eq_gain4 a o, ← hm, hadv]
        change (2 : ℚ) ^ n * (2 * (usum U : ℚ) * mass (source parameters) b a o) *
            (4 * gain parameters a o) +
          4 * (2 : ℚ) ^ n * (2 * (usum U : ℚ) * mass (source parameters) b a o) *
            optimalValue (model parameters) n
              ((model parameters).next (b, ⟨(bal : ℚ), Nat.cast_nonneg bal⟩) a o) =
          4 * (2 : ℚ) ^ (n + 1) * (usum U : ℚ) *
            (mass (source parameters) b a o *
              (gain parameters a o + 1 *
                optimalValue (model parameters) n
                  ((model parameters).next (b, ⟨(bal : ℚ), Nat.cast_nonneg bal⟩) a o)))
        ring
      · change (csolveInt n (unext U a o, advanceNat bal o)).2.toTable =
          solve (model parameters) n (posterior (source parameters) b a o,
            advance parameters.tariff ⟨(bal : ℚ), Nat.cast_nonneg bal⟩ a o)
        rw [← hadv, ht]
  unfold cactionInt
  refine ⟨?_, ?_⟩
  · push_cast
    rw [qValue, sum_obs, mul_add, mul_add, mul_add]
    exact congrArg₂ (· + ·)
      (congrArg₂ (· + ·)
        (congrArg₂ (· + ·) (hobs (false, false)).1 (hobs (false, true)).1)
        (hobs (true, false)).1)
      (hobs (true, true)).1
  · have h00 := (hobs (false, false)).2
    have h01 := (hobs (false, true)).2
    have h10 := (hobs (true, false)).2
    have h11 := (hobs (true, true)).2
    change Table.node a (fun o => (CTree.child _ _ _ _ o).toTable) = _
    congr 1
    funext o
    rcases o with ⟨b₁, b₂⟩
    cases b₁ <;> cases b₂ <;> dsimp only [CTree.child]
    · exact h00
    · exact h01
    · exact h10
    · exact h11

private theorem csolveInt_spec :
    ∀ (n : ℕ) (U : UBelief) (b : Belief World) (bal : ℕ),
      Represents U b →
      ((csolveInt n (U, bal)).1 : ℚ) =
        4 * (2 ^ n : ℚ) * (usum U : ℚ) *
          optimalValue (model parameters) n (b, ⟨(bal : ℚ), Nat.cast_nonneg bal⟩) ∧
      (csolveInt n (U, bal)).2.toTable =
        solve (model parameters) n (b, ⟨(bal : ℚ), Nat.cast_nonneg bal⟩) := by
  intro n
  induction n with
  | zero =>
      intro U b bal _
      exact ⟨by simp [csolveInt], rfl⟩
  | succ n ih =>
      intro U b bal hUb
      have hcpos : (0 : ℚ) < 4 * (2 ^ (n + 1) : ℚ) * (usum U : ℚ) := by
        have hS : (0 : ℚ) < (usum U : ℚ) := Nat.cast_pos.mpr hUb.1
        positivity
      have hsc (a : Act) := (cactionInt_spec n ih U b bal hUb a).1
      have hchooseBest_eq : ∀ (s : Act → ℚ) (xs ys : List Act) (hx : xs ≠ []) (hy : ys ≠ []),
          xs = ys → chooseBest s xs hx = chooseBest s ys hy := by
        intro s xs ys hx hy hxy
        subst hxy
        rfl
      have hchoose : cchooseScored (cactionInt (csolveInt n) (U, bal))
          (menuNat bal) (menuNat_nonempty bal) =
          cactionInt (csolveInt n) (U, bal)
            (chosenAction (model parameters) n (b, ⟨(bal : ℚ), Nat.cast_nonneg bal⟩)) := by
        have hmap : ∀ (xs : List Act) (hne : xs ≠ []),
            cchooseScored (cactionInt (csolveInt n) (U, bal)) xs hne =
              cactionInt (csolveInt n) (U, bal)
                (chooseBest (qValue (model parameters) (optimalValue (model parameters) n)
                  (b, ⟨(bal : ℚ), Nat.cast_nonneg bal⟩)) xs hne) := by
          intro xs hne
          cases xs with
          | nil => exact (hne rfl).elim
          | cons x xs => exact cselectScored_map _ _ _ hcpos hsc xs x
        rw [hmap]
        congr 1
        exact hchooseBest_eq _ _ _ _ _ (menuNat_eq_menu bal)
      dsimp only [csolveInt]
      rw [hchoose]
      have ⟨hv, ht⟩ := cactionInt_spec n ih U b bal hUb
        (chosenAction (model parameters) n (b, ⟨(bal : ℚ), Nat.cast_nonneg bal⟩))
      exact ⟨hv.trans (by rw [optimalValue_succ]), ht.trans (solve_succ _ _ _).symm⟩

private def csourceInt : {n : ℕ} → CTree n → World → ℤ
  | 0, .chalt, _ => 0
  | n + 1, .cnode a t00 t01 t10 t11, w =>
      let oT := observe true w a (true, false)
      let wT := step true w a (true, false)
      let oF := observe true w a (false, false)
      let wF := step true w a (false, false)
      ((2 ^ n : ℕ) : ℤ) * gain4 oT + csourceInt (CTree.child t00 t01 t10 t11 oT) wT +
      (((2 ^ n : ℕ) : ℤ) * gain4 oF + csourceInt (CTree.child t00 t01 t10 t11 oF) wF)

private theorem csourceInt_spec :
    ∀ {n : ℕ} (t : CTree n) (w : World),
      (csourceInt t w : ℚ) =
        4 * (2 ^ n : ℚ) * sourceValue (source parameters) (gain parameters)
          parameters.discount t.toTable w := by
  intro n t
  induction t with
  | chalt => intro w; simp [csourceInt, CTree.toTable, sourceValue]
  | @cnode n a t00 t01 t10 t11 ih00 ih01 ih10 ih11 =>
      intro w
      have ihChild (o : Obs) (w' : World) :
          (csourceInt (CTree.child t00 t01 t10 t11 o) w' : ℚ) =
            4 * (2 ^ n : ℚ) * sourceValue (source parameters) (gain parameters)
              parameters.discount ((CTree.child t00 t01 t10 t11 o).toTable) w' := by
        rcases o with ⟨b₁, b₂⟩
        cases b₁ <;> cases b₂ <;> dsimp [CTree.child]
        · exact ih00 w'
        · exact ih01 w'
        · exact ih10 w'
        · exact ih11 w'
      have hsrc : sourceValue (source parameters) (gain parameters) parameters.discount
          ((CTree.cnode a t00 t01 t10 t11).toTable) w =
          ∑ z : Noise, (source parameters).chance w z *
            (gain parameters a ((source parameters).observe w a z) + parameters.discount *
              sourceValue (source parameters) (gain parameters) parameters.discount
                ((CTree.child t00 t01 t10 t11 ((source parameters).observe w a z)).toTable)
                ((source parameters).next w a z)) := rfl
      rw [hsrc, sum_noise_params w a (fun o' w' =>
        gain parameters a o' + parameters.discount *
          sourceValue (source parameters) (gain parameters) parameters.discount
            ((CTree.child t00 t01 t10 t11 o').toTable) w')]
      unfold csourceInt
      push_cast
      rw [ihChild, ihChild, ← gain_eq_gain4 a (observe true w a (true, false)),
          ← gain_eq_gain4 a (observe true w a (false, false))]
      dsimp [parameters]
      ring

private def initUBelief : Input → UBelief
  | .knownS => [(initialWorld true .S, 1)]
  | .knownG => [(initialWorld true .G, 1)]
  | .dual => [(initialWorld true .S, 3), (initialWorld true .G, 1)]

private theorem represents_initUBelief (q : Input) :
    Represents (initUBelief q) (registeredInfo q).1 := by
  refine ⟨by cases q <;> decide, fun f => ?_⟩
  dsimp [registeredInfo, initialInfo, initialBelief, expect]
  rw [sum_mechanisms]
  cases q <;> (simp [initUBelief, usum, uexpect, prior, parameters]; try ring)

private theorem csolveInt_eq_cachedAt (q : Input) (H : ℕ) :
    ((csolveInt H (initUBelief q, 2)).1 : ℚ) =
      4 * (2 ^ H : ℚ) * (usum (initUBelief q) : ℚ) * (cachedAt q H).1 ∧
    ∀ m, (csourceInt (csolveInt H (initUBelief q, 2)).2 (initialWorld true m) : ℚ) =
      4 * (2 ^ H : ℚ) * tableJ (cachedAt q H).2 m := by
  have ⟨hv, ht⟩ := csolveInt_spec H (initUBelief q) (registeredInfo q).1 2 (represents_initUBelief q)
  have hinfo : ((registeredInfo q).1, (⟨((2 : ℕ) : ℚ), Nat.cast_nonneg 2⟩ : Wallet)) = registeredInfo q := by
    apply Prod.ext rfl
    apply Subtype.ext
    norm_num [registeredInfo, initialInfo]
  rw [hinfo] at hv ht
  refine ⟨?_, ?_⟩
  · rw [cachedAt_eq]
    exact hv
  · intro m
    rw [csourceInt_spec, ht, tableJ, cachedAt_eq]
    rfl

private theorem kernel_int_h3 :
    (csolveInt 3 (initUBelief .knownS, 2)).1 = 41 ∧
    (csolveInt 3 (initUBelief .knownG, 2)).1 = 40 ∧
    (csolveInt 3 (initUBelief .dual, 2)).1 = 160 ∧
    csourceInt (csolveInt 3 (initUBelief .knownS, 2)).2 (initialWorld true .S) = 41 ∧
    csourceInt (csolveInt 3 (initUBelief .knownS, 2)).2 (initialWorld true .G) = 37 ∧
    csourceInt (csolveInt 3 (initUBelief .knownG, 2)).2 (initialWorld true .S) = 40 ∧
    csourceInt (csolveInt 3 (initUBelief .knownG, 2)).2 (initialWorld true .G) = 40 := by
  decide

private theorem kernel_int_h2 :
    (csolveInt 2 (initUBelief .knownS, 2)).1 = 13 ∧
    (csolveInt 2 (initUBelief .knownG, 2)).1 = 13 ∧
    csourceInt (csolveInt 2 (initUBelief .knownS, 2)).2 (initialWorld true .S) = 13 ∧
    csourceInt (csolveInt 2 (initUBelief .knownS, 2)).2 (initialWorld true .G) = 13 := by
  decide

end KernelIntExactEval

/- Small exact computation of ALL legal action scores, through the old solver.
This is not a check of only the deployed path. The separate matrix fields
execute the same returned tables in each actual fixed mechanism.
Both finite evaluations below are proved purely inside the Lean kernel via `decide`
over exact integer-scaled dynamic programming, using zero compiler-trust axioms. -/
theorem exact_cached_data :
    let s := cachedResult .knownS
    let g := cachedResult .knownG
    let b := cachedResult .dual
    s.1 = 41/32 ∧ g.1 = 5/4 ∧ b.1 = 5/4 ∧
      tableJ s.2 .S = 41/32 ∧ tableJ s.2 .G = 37/32 ∧
      tableJ g.2 .S = 5/4 ∧ tableJ g.2 .G = 5/4 := by
  have hs := csolveInt_eq_cachedAt .knownS 3
  have hg := csolveInt_eq_cachedAt .knownG 3
  have hb := csolveInt_eq_cachedAt .dual 3
  have hk := kernel_int_h3
  have h1 : (usum (initUBelief .knownS) : ℚ) = 1 := by decide
  have h2 : (usum (initUBelief .knownG) : ℚ) = 1 := by decide
  have h3 : (usum (initUBelief .dual) : ℚ) = 4 := by decide
  have k1 : ((csolveInt 3 (initUBelief .knownS, 2)).1 : ℚ) = 41 := by exact_mod_cast hk.1
  have k2 : ((csolveInt 3 (initUBelief .knownG, 2)).1 : ℚ) = 40 := by exact_mod_cast hk.2.1
  have k3 : ((csolveInt 3 (initUBelief .dual, 2)).1 : ℚ) = 160 := by exact_mod_cast hk.2.2.1
  have k4 : (csourceInt (csolveInt 3 (initUBelief .knownS, 2)).2 (initialWorld true .S) : ℚ) = 41 := by
    exact_mod_cast hk.2.2.2.1
  have k5 : (csourceInt (csolveInt 3 (initUBelief .knownS, 2)).2 (initialWorld true .G) : ℚ) = 37 := by
    exact_mod_cast hk.2.2.2.2.1
  have k6 : (csourceInt (csolveInt 3 (initUBelief .knownG, 2)).2 (initialWorld true .S) : ℚ) = 40 := by
    exact_mod_cast hk.2.2.2.2.2.1
  have k7 : (csourceInt (csolveInt 3 (initUBelief .knownG, 2)).2 (initialWorld true .G) : ℚ) = 40 := by
    exact_mod_cast hk.2.2.2.2.2.2
  have s1 := hs.1; have g1 := hg.1; have b1 := hb.1
  have sS := hs.2 .S; have sG := hs.2 .G
  have gS := hg.2 .S; have gG := hg.2 .G
  rw [k1, h1] at s1; rw [k2, h2] at g1; rw [k3, h3] at b1
  rw [k4] at sS; rw [k5] at sG; rw [k6] at gS; rw [k7] at gG
  dsimp only [cachedResult]
  refine ⟨by linarith, by linarith, by linarith,
          by linarith, by linarith, by linarith, by linarith⟩

/-- A nondegenerate short-horizon common optimizer. Two ticks can have value
13/16 even though no allowed experiment can yet separate the mechanisms. -/
def commonTwo : Table Act Obs 2 := (cachedAt .knownS 2).2

theorem exact_two_data :
    (cachedAt .knownS 2).1 = 13/16 ∧ (cachedAt .knownG 2).1 = 13/16 ∧
      tableJ commonTwo .S = 13/16 ∧ tableJ commonTwo .G = 13/16 := by
  have hs := csolveInt_eq_cachedAt .knownS 2
  have hg := csolveInt_eq_cachedAt .knownG 2
  have hk := kernel_int_h2
  have h1 : (usum (initUBelief .knownS) : ℚ) = 1 := by decide
  have h2 : (usum (initUBelief .knownG) : ℚ) = 1 := by decide
  have k1 : ((csolveInt 2 (initUBelief .knownS, 2)).1 : ℚ) = 13 := by exact_mod_cast hk.1
  have k2 : ((csolveInt 2 (initUBelief .knownG, 2)).1 : ℚ) = 13 := by exact_mod_cast hk.2.1
  have k3 : (csourceInt (csolveInt 2 (initUBelief .knownS, 2)).2 (initialWorld true .S) : ℚ) = 13 := by
    exact_mod_cast hk.2.2.1
  have k4 : (csourceInt (csolveInt 2 (initUBelief .knownS, 2)).2 (initialWorld true .G) : ℚ) = 13 := by
    exact_mod_cast hk.2.2.2
  have s1 := hs.1; have g1 := hg.1
  have sS := hs.2 .S; have sG := hs.2 .G
  rw [k1, h1] at s1; rw [k2, h2] at g1; rw [k3] at sS; rw [k4] at sG
  dsimp only [commonTwo]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

 theorem short_common_values :
    optimalValue (model parameters) 2 (registeredInfo .knownS) = 13/16 ∧
      optimalValue (model parameters) 2 (registeredInfo .knownG) = 13/16 ∧
      tableJ commonTwo .S = 13/16 ∧ tableJ commonTwo .G = 13/16 := by
  have h := exact_two_data
  simpa only [cachedAt_eq] using h

 theorem oracleS_value : optimalValue (model parameters) 3 (registeredInfo .knownS) = 41/32 := by
  have h := exact_cached_data
  simpa only [cachedResult, cachedAt_eq] using h.1

 theorem oracleG_value : optimalValue (model parameters) 3 (registeredInfo .knownG) = 5/4 := by
  have h := exact_cached_data
  simpa only [cachedResult, cachedAt_eq] using h.2.1

 theorem dual_value : optimalValue (model parameters) 3 (registeredInfo .dual) = 5/4 := by
  have h := exact_cached_data
  simpa only [cachedResult, cachedAt_eq] using h.2.2.1

 theorem returned_matrix :
    tableJ returnedS .S = 41/32 ∧ tableJ returnedS .G = 37/32 ∧
      tableJ returnedG .S = 5/4 ∧ tableJ returnedG .G = 5/4 :=
  exact_cached_data.2.2.2

/-- Menu and wallet evolution depend on actual receipts, never on a hidden
mechanism. Thus every returned row is affordable under either prior. -/
 theorem feasible_same_wallet (P : Parameters) :
    ∀ {H : ℕ} (table : Table Act Obs H) (i j : Info), i.2 = j.2 →
      Feasible (model P) i table → Feasible (model P) j table := by
  intro H
  induction H with
  | zero => intro table i j hw hf; cases table; trivial
  | succ H ih =>
      intro table i j hw hf
      cases table with
      | node a children =>
          constructor
          · change a ∈ RegisterJointDecisionConsumer.menu P.tariff j.2
            have ha := hf.1
            change a ∈ RegisterJointDecisionConsumer.menu P.tariff i.2 at ha
            simpa only [hw] using ha
          · intro o
            apply ih (children o) ((model P).next i a o) ((model P).next j a o)
            · change RegisterJointDecisionConsumer.advance P.tariff i.2 a o =
                RegisterJointDecisionConsumer.advance P.tariff j.2 a o
              rw [hw]
            · exact hf.2 o

 theorem returned_feasible (seed : Fin 4) (q : Input) :
    Feasible (model parameters) (registeredInfo q) (returned seed) := by
  unfold returned
  split
  · rw [returnedS_eq_solve]
    exact feasible_same_wallet parameters _ (registeredInfo .knownS) (registeredInfo q)
      rfl (solve_feasible _ _ _)
  · rw [returnedG_eq_solve]
    exact feasible_same_wallet parameters _ (registeredInfo .knownG) (registeredInfo q)
      rfl (solve_feasible _ _ _)

 theorem returned_prefix_payment (seed : Fin 4) (q : Input) (w : Tape Obs 3)
    (hw : 0 < tapeWeight (model parameters) (registeredInfo q) (returned seed) w) :
    PrepaidAlong (model parameters) (walletContract parameters) (registeredInfo q)
      (returned seed) w ∧ ∀ k,
      (walletContract parameters).balance
          (prefixInfo (model parameters) (registeredInfo q) (returned seed) w k) =
        2 - prefixCost (model parameters) (walletContract parameters) (registeredInfo q)
          (returned seed) w k ∧
      0 ≤ prefixCost (model parameters) (walletContract parameters) (registeredInfo q)
          (returned seed) w k ∧
      prefixCost (model parameters) (walletContract parameters) (registeredInfo q)
          (returned seed) w k ≤ 2 := by
  exact ⟨feasible_prepaid _ _ 3 _ _ (returned_feasible seed q) w,
    feasible_prefix_ledger _ _ 3 _ _ (returned_feasible seed q) (by norm_num [walletContract,
      registeredInfo, initialInfo]) w hw⟩

def rhoJ (m : FaultMechanism) : ℚ := ∑ seed : Fin 4, (1/4) * tableJ (returned seed) m

 theorem rhoJ_eq (m : FaultMechanism) :
    rhoJ m = (1/4) * tableJ returnedS m + (3/4) * tableJ returnedG m := by
  norm_num [rhoJ, Fin.sum_univ_succ, returned]
  ring

 theorem returned_randomized_values : rhoJ .S = 161/128 ∧ rhoJ .G = 157/128 := by
  rw [rhoJ_eq, rhoJ_eq, returned_matrix.1, returned_matrix.2.1,
    returned_matrix.2.2.1, returned_matrix.2.2.2]
  norm_num

noncomputable def oracle : FaultMechanism → ℝ
  | .S => 41/32
  | .G => 5/4

noncomputable def dualWeight : FaultMechanism → ℝ
  | .S => 3/4
  | .G => 1/4

 theorem dualWeight_nonneg (m : FaultMechanism) : 0 ≤ dualWeight m := by
  cases m <;> norm_num [dualWeight]

 theorem dualWeight_total : ∑ m, dualWeight m = 1 := by
  rw [sum_mechanisms]
  norm_num [dualWeight]

/-- Every allowed full-history real-randomized kernel uses the same physical
source and the same private memory transition. No m is passed to actionProb. -/
noncomputable def actualJ (pi : RawCausalPolicy (model parameters))
    (h : pi.Memory) (m : FaultMechanism) : ℝ :=
  rawSourceValue (source parameters) (gain parameters) parameters.discount pi 3 h
    (initialWorld parameters.goal m)

 theorem raw_mixture_identity (pi : RawCausalPolicy (model parameters))
    (h : pi.Memory) (hi : pi.info h = registeredInfo .dual) :
    (∑ m, dualWeight m * actualJ pi h m) =
      rawValue (model parameters) pi 3 h := by
  have he := rawSourceValue_eq_model (source parameters)
    (fun i => RegisterJointDecisionConsumer.menu parameters.tariff i.2)
    (fun i => RegisterJointDecisionConsumer.menu_nonempty parameters.tariff i.2)
    (RegisterJointDecisionConsumer.advance parameters.tariff) (gain parameters)
    parameters.discount parameters.discount_bounds.1 pi 3 h
  change expectReal (pi.info h).1
      (rawSourceValue (source parameters) (gain parameters) parameters.discount pi 3 h) =
    rawValue (model parameters) pi 3 h at he
  rw [← he, hi]
  change (∑ m, dualWeight m * actualJ pi h m) =
    ∑ m, ((prior .dual m : ℚ) : ℝ) * actualJ pi h m
  apply Finset.sum_congr rfl
  intro m _
  cases m <;> norm_num [dualWeight, prior]

/-- The essential full comparison-class bound. The finite computation above
is plugged into the already proved raw supported-history Bayes theorem. -/
 theorem all_shared_weighted_upper (pi : RawCausalPolicy (model parameters))
    (h : pi.Memory) (hi : pi.info h = registeredInfo .dual)
    (hl : SupportedAdmissible (model parameters) pi 3 h) :
    (∑ m, dualWeight m * actualJ pi h m) ≤ 5/4 := by
  rw [raw_mixture_identity pi h hi]
  have hu := rawValue_le_solve (model parameters) pi 3 h hl
  rw [hi, dual_value] at hu
  norm_num at hu ⊢
  exact hu

 theorem all_shared_regret_lower (pi : RawCausalPolicy (model parameters))
    (h : pi.Memory) (hi : pi.info h = registeredInfo .dual)
    (hl : SupportedAdmissible (model parameters) pi 3 h) :
    (3/128 : ℝ) ≤ FiniteMechanismRegretCertificate.worst oracle (actualJ pi h) := by
  have hb := FiniteMechanismRegretCertificate.lower_bound oracle (actualJ pi h)
    dualWeight (5/4) dualWeight_nonneg dualWeight_total
    (all_shared_weighted_upper pi h hi hl)
  rw [sum_mechanisms] at hb
  norm_num [dualWeight, oracle] at hb
  exact hb

 theorem returned_regrets :
    oracle .S - (rhoJ .S : ℝ) = 3/128 ∧ oracle .G - (rhoJ .G : ℝ) = 3/128 := by
  rw [returned_randomized_values.1, returned_randomized_values.2]
  norm_num [oracle]

 theorem returned_worst_regret :
    FiniteMechanismRegretCertificate.worst oracle (fun m => (rhoJ m : ℝ)) = 3/128 := by
  apply le_antisymm
  · apply FiniteMechanismRegretCertificate.worst_le
    intro m
    cases m
    · exact returned_regrets.1.le
    · exact returned_regrets.2.le
  · simpa only [returned_regrets.1] using
      FiniteMechanismRegretCertificate.regret_le_worst oracle (fun m => (rhoJ m : ℝ)) .S

/-- Known-mechanism oracle values are certified over exactly the same legal
information class; only the initialization prior is concentrated on m. -/
 theorem knownS_all_policy_upper (pi : RawCausalPolicy (model parameters))
    (h : pi.Memory) (hi : pi.info h = registeredInfo .knownS)
    (hl : SupportedAdmissible (model parameters) pi 3 h) : actualJ pi h .S ≤ 41/32 := by
  have hu := rawValue_le_solve (model parameters) pi 3 h hl
  have he := rawSourceValue_eq_model (source parameters)
    (fun i => RegisterJointDecisionConsumer.menu parameters.tariff i.2)
    (fun i => RegisterJointDecisionConsumer.menu_nonempty parameters.tariff i.2)
    (RegisterJointDecisionConsumer.advance parameters.tariff) (gain parameters)
    parameters.discount parameters.discount_bounds.1 pi 3 h
  change expectReal (pi.info h).1
      (rawSourceValue (source parameters) (gain parameters) parameters.discount pi 3 h) =
    rawValue (model parameters) pi 3 h at he
  rw [← he, hi] at hu
  rw [oracleS_value] at hu
  change (∑ m, ((prior .knownS m : ℚ) : ℝ) * actualJ pi h m) ≤ ((41/32 : ℚ) : ℝ) at hu
  rw [sum_mechanisms] at hu
  norm_num [prior] at hu ⊢
  exact hu

 theorem knownG_all_policy_upper (pi : RawCausalPolicy (model parameters))
    (h : pi.Memory) (hi : pi.info h = registeredInfo .knownG)
    (hl : SupportedAdmissible (model parameters) pi 3 h) : actualJ pi h .G ≤ 5/4 := by
  have hu := rawValue_le_solve (model parameters) pi 3 h hl
  have he := rawSourceValue_eq_model (source parameters)
    (fun i => RegisterJointDecisionConsumer.menu parameters.tariff i.2)
    (fun i => RegisterJointDecisionConsumer.menu_nonempty parameters.tariff i.2)
    (RegisterJointDecisionConsumer.advance parameters.tariff) (gain parameters)
    parameters.discount parameters.discount_bounds.1 pi 3 h
  change expectReal (pi.info h).1
      (rawSourceValue (source parameters) (gain parameters) parameters.discount pi 3 h) =
    rawValue (model parameters) pi 3 h at he
  rw [← he, hi] at hu
  rw [oracleG_value] at hu
  change (∑ m, ((prior .knownG m : ℚ) : ℝ) * actualJ pi h m) ≤ ((5/4 : ℚ) : ℝ) at hu
  rw [sum_mechanisms] at hu
  norm_num [prior] at hu ⊢
  exact hu

/-- At the frozen rate, the original mode/label pair has mass 1/4 regardless
of the fixed mechanism, state, selected action, or private controller seed. -/
 theorem primitive_quarter (w : World) (z : Noise) :
    (source parameters).chance w z = 1/4 := by
  rcases z with ⟨mode,label⟩
  cases mode <;> norm_num [source, parameters, RegisterJointDecisionSource.primitiveWeight]

 theorem source_tape_uniform : ∀ {H : ℕ} (table : Table Act Obs H) (w : World)
    (noise : Tape Noise H), sourceTapeWeight (source parameters) table w noise = (1/4)^H := by
  intro H
  induction H with
  | zero => intro table w noise; cases table; simp [sourceTapeWeight]
  | succ H ih =>
      intro table w noise
      cases table with
      | node a children =>
          rcases noise with ⟨z,zs⟩
          rw [sourceTapeWeight, primitive_quarter, ih, pow_succ]
          ring

def jointSeedNoiseWeight (m : FaultMechanism) (seed : Fin 4) (noise : Tape Noise 3) : ℚ :=
  (1/4) * sourceTapeWeight (source parameters) (returned seed)
    (initialWorld parameters.goal m) noise

/-- Conditional on EITHER fixed mechanism, every one of 4×4³ complete private
seed/world-noise atoms has the same product mass. In particular m cannot choose
or bias the private seed, and no birth label is used as controller randomness. -/
 theorem seed_noise_independent (m : FaultMechanism) (seed : Fin 4) (noise : Tape Noise 3) :
    jointSeedNoiseWeight m seed noise = 1/256 := by
  rw [jointSeedNoiseWeight, source_tape_uniform]
  norm_num

/-- The model ledger applies to EVERY actual source path of THIS returned
program, because both initial mechanisms and every full primitive tape have
strictly positive mass in the shared joint witness. -/
 theorem returned_actual_prefix_payment (seed : Fin 4) (m : FaultMechanism)
    (noise : Tape Noise 3) :
    let path := observedTape (source parameters) (returned seed)
      (initialWorld parameters.goal m) noise
    PrepaidAlong (model parameters) (walletContract parameters) (registeredInfo .dual)
      (returned seed) path ∧ ∀ k,
      (walletContract parameters).balance
          (prefixInfo (model parameters) (registeredInfo .dual) (returned seed) path k) =
        2 - prefixCost (model parameters) (walletContract parameters) (registeredInfo .dual)
          (returned seed) path k ∧
      0 ≤ prefixCost (model parameters) (walletContract parameters) (registeredInfo .dual)
          (returned seed) path k ∧
      prefixCost (model parameters) (walletContract parameters) (registeredInfo .dual)
          (returned seed) path k ≤ 2 := by
  apply returned_prefix_payment seed .dual
  apply observedTape_supported (source parameters)
    (fun i => RegisterJointDecisionConsumer.menu parameters.tariff i.2)
    (fun i => RegisterJointDecisionConsumer.menu_nonempty parameters.tariff i.2)
    (RegisterJointDecisionConsumer.advance parameters.tariff) (gain parameters)
    parameters.discount parameters.discount_bounds.1 3 (returned seed)
    (registeredInfo .dual).1 (registeredInfo .dual).2 m noise
  · change 0 < prior .dual m
    cases m <;> norm_num [prior]
  · rw [source_tape_uniform]
    norm_num

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionConsumer
