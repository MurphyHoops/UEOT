import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionConsumer
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionExecution

/-!
# Exact free continuation after the one-wallet first successful write

A successful initial root write creates the original healthy root and its real
child at address1, and consumes the entire one-write wallet. Only old idle
requests remain affordable. This module bounds EVERY such finite table and
constructs one receipt-only table attaining the bound, for every fixed source
parameter and every finite horizon. It does not grant the scheduler the hidden
population projection used on the world side of the proof.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionFreeTail

open scoped BigOperators
open RegisterJointDecisionSource
open RegisterJointDecisionConsumer
open FiniteJointDecisionSolver
open FiniteJointDecisionFilteredModel

def Free : {H : ℕ} → Table Act Obs H → Prop
  | _, .halt => True
  | _, .node a children => cap a = 0 ∧ ∀ o, Free (children o)

/-- Health is an analysis-side projection. The implemented schedule below
maintains these two bits using only its known initial condition and receipts. -/
def health (goal : Bool) (s : PackedStore) : Bool × Bool :=
  (packedLookup s 0 == some goal, packedLookup s 1 == some goal)

def selected (x : Bool × Bool) (j : Bool) : Bool := if j then x.2 else x.1
def bitNext (x : Bool × Bool) (j mode : Bool) : Bool × Bool :=
  if mode then x else if j then (x.1,false) else (false,x.2)
def bitObs (x : Bool × Bool) (j mode : Bool) : Obs := (mode && selected x j,false)
def receiptUpdate (x : Bool × Bool) (j : Bool) (o : Obs) : Bool × Bool :=
  if j then (x.1,o.1) else (o.1,x.2)
def choose (x : Bool × Bool) : Bool := !x.1 && x.2

def oneBound (r d : ℚ) : ℕ → ℚ
  | 0 => 0
  | H+1 => r*(1+d*oneBound r d H)
def twoBound (r d : ℚ) : ℕ → ℚ
  | 0 => 0
  | H+1 => r*(1+d*twoBound r d H)+(1-r)*d*oneBound r d H
def bound (r d : ℚ) (H : ℕ) (x : Bool × Bool) : ℚ :=
  if x.1 && x.2 then twoBound r d H else if x.1 || x.2 then oneBound r d H else 0

theorem one_nonneg (r d : ℚ) (hr : 0 ≤ r) (hd : 0 ≤ d) :
    ∀ H, 0 ≤ oneBound r d H := by
  intro H
  induction H with
  | zero => exact le_rfl
  | succ H ih => simp only [oneBound]; positivity

theorem one_increasing (r d : ℚ) (hr : 0 ≤ r) (hd : 0 ≤ d) :
    ∀ H, oneBound r d H ≤ oneBound r d (H+1) := by
  intro H
  induction H with
  | zero => simp [oneBound,hr]
  | succ H ih =>
    simp only [oneBound]
    exact mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left ih hd)) hr

theorem one_wait_bound (r d : ℚ) (hr : 0 ≤ r) (hd : 0 ≤ d ∧ d ≤ 1) (H : ℕ) :
    d*oneBound r d H ≤ oneBound r d (H+1) :=
  (mul_le_of_le_one_left (one_nonneg r d hr hd.1 H) hd.2).trans
    (one_increasing r d hr hd.1 H)

theorem bound_zero (r d : ℚ) (x : Bool × Bool) : bound r d 0 x = 0 := by
  rcases x with ⟨x,y⟩
  cases x <;> cases y <;> simp [bound,oneBound,twoBound]

def bitQ (r d : ℚ) (H : ℕ) (x : Bool × Bool) (j : Bool) : ℚ :=
  r*((if selected x j then 1 else 0)+d*bound r d H x) +
    (1-r)*d*bound r d H (bitNext x j false)

theorem bitQ_le_bound (r d : ℚ) (hr : 0 ≤ r ∧ r ≤ 1)
    (hd : 0 ≤ d ∧ d ≤ 1) (H : ℕ) (x : Bool × Bool) (j : Bool) :
    bitQ r d H x j ≤ bound r d (H+1) x := by
  have hw := one_wait_bound r d hr.1 hd H
  simp only [oneBound] at hw
  rcases x with ⟨x,y⟩
  cases x <;> cases y <;> cases j <;>
    simp [bitQ,selected,bitNext,bound,oneBound,twoBound] <;> nlinarith

theorem bitQ_choose_eq (r d : ℚ) (H : ℕ) (x : Bool × Bool) :
    bitQ r d H x (choose x) = bound r d (H+1) x := by
  rcases x with ⟨x,y⟩
  cases x <;> cases y <;>
    simp [bitQ,choose,selected,bitNext,bound,oneBound,twoBound] <;> ring

theorem receipt_updates_health (x : Bool × Bool) (j mode : Bool) :
    receiptUpdate x j (bitObs x j mode) = bitNext x j mode := by
  rcases x with ⟨x,y⟩
  cases x <;> cases y <;> cases j <;> cases mode <;>
    simp [receiptUpdate,bitObs,selected,bitNext]

theorem effective_no_write (stopped : Bool) (a : Act) (ha : cap a = 0) :
    (effective stopped a).2 = none := by
  cases stopped with
  | true => rfl
  | false =>
    cases a with
    | none => rfl
    | some a =>
      rcases a with ⟨j,act⟩
      cases act with
      | none => rfl
      | some b => simp [cap,effective] at ha

theorem packed_free_observe (goal : Bool) (s : PackedStore) (j mode : Bool) :
    packedObserve goal s (address j) none mode = bitObs (health goal s) j mode := by
  cases j with
  | false =>
    cases h : packedLookup s 0 with
    | none => simp [packedObserve,address,health,bitObs,selected,h]
    | some b =>
      cases b <;> cases goal <;> cases mode <;>
        simp [packedObserve,address,health,bitObs,selected,childBit,h]
  | true =>
    cases h : packedLookup s 1 with
    | none => simp [packedObserve,address,health,bitObs,selected,h]
    | some b =>
      cases b <;> cases goal <;> cases mode <;>
        simp [packedObserve,address,health,bitObs,selected,childBit,h]
    
theorem packed_free_next (goal : Bool) (s : PackedStore) (j mode : Bool)
    (hlen : 2 ≤ s.length) :
    health goal (packedNext goal s (address j) none mode) =
      bitNext (health goal s) j mode := by
  cases s with
  | nil => simp at hlen
  | cons x xs =>
    cases xs with
    | nil => simp at hlen
    | cons y ys =>
      cases x <;> cases y <;> cases goal <;> cases j <;> cases mode <;>
        simp [health,packedNext,packedLookup,address,postBit,childBit,bitNext]

theorem observe_free {Theta : Type} (goal : Bool) (w : World Theta) (a : Act)
    (ha : cap a = 0) (z : Noise) :
    observe goal w a z = bitObs (health goal w.store) (effective w.stopped a).1 z.1 := by
  change packedObserve goal w.store (address (effective w.stopped a).1)
    (effective w.stopped a).2 z.1 = _
  rw [effective_no_write w.stopped a ha]
  exact packed_free_observe goal w.store _ _

theorem step_health {Theta : Type} (goal : Bool) (w : World Theta) (a : Act)
    (ha : cap a = 0) (hlen : 2 ≤ w.store.length) (z : Noise) :
    health goal (step goal w a z).store =
      bitNext (health goal w.store) (effective w.stopped a).1 z.1 := by
  change health goal (packedNext goal w.store (address (effective w.stopped a).1)
    (effective w.stopped a).2 z.1) = _
  rw [effective_no_write w.stopped a ha]
  exact packed_free_next goal w.store _ _ hlen

/-- Expand the literal mode/label source; labels are integrated, not selected. -/
theorem sourceValue_modes {Theta : Type} (P : Family Theta) (H : ℕ)
    (a : Act) (cs : Obs → Table Act Obs H) (w : World Theta) :
    sourceValue (source P) (gain P) P.discount (.node a cs) w =
      P.normal w.theta *
        (gain P a (observe P.goal w a (true,false)) + P.discount *
          sourceValue (source P) (gain P) P.discount
            (cs (observe P.goal w a (true,false))) (step P.goal w a (true,false))) +
      (1-P.normal w.theta) *
        (gain P a (observe P.goal w a (false,false)) + P.discount *
          sourceValue (source P) (gain P) P.discount
            (cs (observe P.goal w a (false,false))) (step P.goal w a (false,false))) := by
  simp only [sourceValue,source,Fintype.sum_prod_type,Fintype.sum_bool,primitiveWeight]
  simp only [step,observe,Bool.false_eq_true,if_true,if_false]
  ring

theorem free_bound_one_step {Theta : Type} (P : Family Theta) (H : ℕ)
    (a : Act) (w : World Theta) (ha : cap a = 0) (hlen : 2 ≤ w.store.length) :
    (∑ z : Noise, primitiveWeight P.normal w z *
      (gain P a (observe P.goal w a z) + P.discount *
        bound (P.normal (step P.goal w a z).theta) P.discount H
          (health P.goal (step P.goal w a z).store))) =
      bitQ (P.normal w.theta) P.discount H (health P.goal w.store)
        (effective w.stopped a).1 := by
  simp_rw [theta_preserved,step_health P.goal w a ha hlen,observe_free P.goal w a ha]
  simp [primitiveWeight,Fintype.sum_prod_type,gain,charge,bitObs,bitQ,bitNext]
  ring

/-- A stronger world-side bound: even a competing table chosen knowing theta
cannot exceed this free continuation value. Our attaining table below does not
know theta, which proves that extra theta information has zero control value
inside this post-success, exhausted-wallet regime. -/
theorem free_table_upper {Theta : Type} (P : Family Theta) :
    ∀ (H : ℕ) (table : Table Act Obs H) (w : World Theta),
      Free table → 2 ≤ w.store.length →
      sourceValue (source P) (gain P) P.discount table w ≤
        bound (P.normal w.theta) P.discount H (health P.goal w.store) := by
  intro H
  induction H with
  | zero =>
    intro table w hf hlen
    cases table
    simp [sourceValue,bound_zero]
  | succ H ih =>
    intro table w hf hlen
    cases table with
    | node a cs =>
      obtain ⟨ha,hcs⟩ := hf
      calc
        sourceValue (source P) (gain P) P.discount (.node a cs) w ≤
            ∑ z : Noise, primitiveWeight P.normal w z *
              (gain P a (observe P.goal w a z) + P.discount *
                bound (P.normal (step P.goal w a z).theta) P.discount H
                  (health P.goal (step P.goal w a z).store)) := by
          apply Finset.sum_le_sum
          intro z hz
          apply mul_le_mul_of_nonneg_left _ (primitiveWeight_nonneg P.normal P.normal_bounds w z)
          apply add_le_add le_rfl
          apply mul_le_mul_of_nonneg_left _ P.discount_bounds.1
          exact ih (cs (observe P.goal w a z)) (step P.goal w a z)
            (hcs _) (by rw [step_length]; omega)
        _ = bitQ (P.normal w.theta) P.discount H (health P.goal w.store)
            (effective w.stopped a).1 := free_bound_one_step P H a w ha hlen
        _ ≤ bound (P.normal w.theta) P.discount (H+1) (health P.goal w.store) :=
          bitQ_le_bound _ _ (P.normal_bounds w.theta) P.discount_bounds H _ _

def freeSchedule : (H : ℕ) → (Bool × Bool) → Table Act Obs H
  | 0, _ => .halt
  | H+1, x => .node (some (choose x,none))
      (fun o => freeSchedule H (receiptUpdate x (choose x) o))

theorem freeSchedule_free : ∀ (H : ℕ) (x : Bool × Bool), Free (freeSchedule H x) := by
  intro H
  induction H with
  | zero => intro x; trivial
  | succ H ih =>
    intro x
    refine ⟨?_,fun o => ih _⟩
    simp [cap,effective]

theorem freeSchedule_feasible {Theta : Type} (P : Family Theta) :
    ∀ (H : ℕ) (x : Bool × Bool) (i : Info Theta),
      Feasible (model P) i (freeSchedule H x) := by
  intro H
  induction H with
  | zero => intros; trivial
  | succ H ih =>
    intro x i
    refine ⟨?_,fun o => ih _ _⟩
    change some (choose x,none) ∈ menu P.tariff i.2
    cases h : choose x <;> simp [menu,allActions,cap,effective,i.2.property]

theorem freeSchedule_attains {Theta : Type} (P : Family Theta) :
    ∀ (H : ℕ) (w : World Theta), w.stopped = false → 2 ≤ w.store.length →
      sourceValue (source P) (gain P) P.discount
        (freeSchedule H (health P.goal w.store)) w =
          bound (P.normal w.theta) P.discount H (health P.goal w.store) := by
  intro H
  induction H with
  | zero =>
    intro w hs hlen
    simp [freeSchedule,sourceValue,bound_zero]
  | succ H ih =>
    intro w hs hlen
    let x := health P.goal w.store
    let a : Act := some (choose x,none)
    have ha : cap a = 0 := by simp [a,cap,effective]
    have hstate (z : Noise) :
        health P.goal (step P.goal w a z).store =
          receiptUpdate x (choose x) (observe P.goal w a z) := by
      rw [step_health P.goal w a ha hlen,observe_free P.goal w a ha]
      simp only [a,effective,hs,Bool.false_eq_true,if_false,Option.getD_some]
      exact (receipt_updates_health x (choose x) z.1).symm
    change (∑ z : Noise, primitiveWeight P.normal w z *
      (gain P a (observe P.goal w a z) + P.discount *
        sourceValue (source P) (gain P) P.discount
          (freeSchedule H (receiptUpdate x (choose x) (observe P.goal w a z)))
          (step P.goal w a z))) = _
    calc
      _ = ∑ z : Noise, primitiveWeight P.normal w z *
          (gain P a (observe P.goal w a z) + P.discount *
            bound (P.normal (step P.goal w a z).theta) P.discount H
              (health P.goal (step P.goal w a z).store)) := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [← hstate z,ih]
        · simp [step,hs,a]
        · rw [step_length]; omega
      _ = bitQ (P.normal w.theta) P.discount H x (choose x) := by
        rw [free_bound_one_step P H a w ha hlen]
        simp [a,effective,hs,x]
      _ = bound (P.normal w.theta) P.discount (H+1) x := bitQ_choose_eq _ _ _ _

/-- The actual menu/advance functions force every row of a feasible zero-wallet
table to be free; even the zero-mass receipt defaults cannot grant a write. -/
theorem feasible_zero_wallet_free {Theta : Type} (P : Family Theta) :
    ∀ (H : ℕ) (i : Info Theta) (table : Table Act Obs H),
      i.2.val = 0 → Feasible (model P) i table → Free table := by
  intro H
  induction H with
  | zero => intro i table hz hf; cases table; trivial
  | succ H ih =>
    intro i table hz hf
    cases table with
    | node a cs =>
      refine ⟨?_,fun o => ?_⟩
      · exact insufficient_prepaid_no_write P.tariff i.2 (by rw [hz]; exact P.tariff_pos)
          a hf.1
      · apply ih ((model P).next i a o) (cs o) _ (hf.2 o)
        change max 0 (i.2.val-charge P.tariff o) = 0
        rw [hz]
        exact max_eq_left (by linarith [charge_nonneg P o])

theorem twoBound_small (r d : ℚ) :
    twoBound r d 1 = r ∧ twoBound r d 2 = r+d*r ∧
      twoBound r d 3 = r+d*r+d^2*(2*r^2-r^3) := by
  simp [twoBound,oneBound]
  constructor <;> ring

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionFreeTail

