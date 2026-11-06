import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionConsumer
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionNativeLaw

/-!
# Fixed local and common fault mechanisms on the same decision source

S is the old source without modification. G first performs that same transaction;
on a fault tick it then damages the relevant bit of every existing result slot.
The new map preserves empty slots and adds no observation or controlled action.
Both sources share the seven-action, request-cap, actual-fee, wallet and clock
protocol. A mechanism is a hidden, persistent world parameter, never a policy
argument. A common public normal rate is fixed for the whole experiment.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionSource

open scoped BigOperators
open RegisterJointDecisionSource (Act Obs Noise PackedStore effective address cap
  packedLookup packedNext packedObserve postBit childBit primitiveWeight)
open RegisterJointDecisionExecution (Execution prepend)
open RegisterJointDecisionConsumer (Wallet menu menu_nonempty mem_menu_prepay advance charge)
open FiniteJointDecisionBelief FiniteJointDecisionSolver
open FiniteJointDecisionFilteredModel FiniteJointDecisionSupportedPolicy

inductive FaultMechanism where
  | S
  | G
  deriving DecidableEq, Repr

instance : Fintype FaultMechanism where
  elems := {.S, .G}
  complete := by intro m; cases m <;> simp

abbrev World := RegisterJointDecisionSource.World FaultMechanism

/-- World-side environmental damage, not an added controller permission. -/
def damagePacked (goal : Bool) (s : PackedStore) : PackedStore :=
  s.map (Option.map (fun _ => !goal))

/-- The order is fixed: old transaction, then common damage on a G fault. -/
def step (goal : Bool) (w : World) (a : Act) (z : Noise) : World :=
  let u := RegisterJointDecisionSource.step goal w a z
  if w.theta = .G ∧ z.1 = false then {u with store := damagePacked goal u.store} else u

/-- Both receipt fields still come from the SAME original transaction. -/
def observe (goal : Bool) (w : World) (a : Act) (z : Noise) : Obs :=
  RegisterJointDecisionSource.observe goal w a z

def initialWorld (goal : Bool) (m : FaultMechanism) : World :=
  ⟨m, [some (!goal)], false⟩

@[simp] theorem step_S (goal : Bool) (w : World) (a : Act) (z : Noise)
    (hm : w.theta = .S) :
    step goal w a z = RegisterJointDecisionSource.step goal w a z := by
  simp [step, hm]

@[simp] theorem step_normal (goal : Bool) (w : World) (a : Act) (label : Bool) :
    step goal w a (true,label) = RegisterJointDecisionSource.step goal w a (true,label) := by
  simp [step]

@[simp] theorem step_G_fault (goal : Bool) (w : World) (a : Act) (label : Bool)
    (hm : w.theta = .G) :
    (step goal w a (false,label)).store =
      damagePacked goal (RegisterJointDecisionSource.step goal w a (false,label)).store := by
  simp [step, hm]

@[simp] theorem theta_preserved (goal : Bool) (w : World) (a : Act) (z : Noise) :
    (step goal w a z).theta = w.theta := by
  unfold step
  split <;> rfl

@[simp] theorem stopped_step (goal : Bool) (w : World) (a : Act) (z : Noise) :
    (step goal w a z).stopped = (w.stopped || a.isNone) := by
  unfold step
  split <;> rfl

@[simp] theorem step_length (goal : Bool) (w : World) (a : Act) (z : Noise) :
    (step goal w a z).store.length = w.store.length + 1 := by
  unfold step
  split <;> simp [damagePacked]

theorem step_label (goal : Bool) (w : World) (a : Act) (mode l₁ l₂ : Bool) :
    step goal w a (mode,l₁) = step goal w a (mode,l₂) := rfl

theorem observe_label (goal : Bool) (w : World) (a : Act) (mode l₁ l₂ : Bool) :
    observe goal w a (mode,l₁) = observe goal w a (mode,l₂) := rfl

@[simp] theorem observe_fault (goal : Bool) (w : World) (a : Act) (label : Bool) :
    observe goal w a (false,label) = (false,false) := by
  dsimp only [observe, RegisterJointDecisionSource.observe]
  unfold packedObserve
  split <;> simp [childBit]

/-- All common-damage maps preserve existence, chronology and failed slots. -/
@[simp] theorem damagePacked_length (goal : Bool) (s : PackedStore) :
    (damagePacked goal s).length = s.length := by simp [damagePacked]

@[simp] theorem damagePacked_lookup (goal : Bool) (s : PackedStore) (j : ℕ) :
    packedLookup (damagePacked goal s) j = (packedLookup s j).map (fun _ => !goal) := by
  simp only [damagePacked, packedLookup, List.getElem?_map]
  cases h : s[j]? with
  | none => simp [h]
  | some op => cases op <;> simp [h]

/-- Public parameters are shared across the two fixed mechanisms. -/
structure Parameters where
  goal : Bool
  normal : ℚ
  normal_bounds : 0 ≤ normal ∧ normal ≤ 1
  tariff : ℚ
  tariff_pos : 0 < tariff
  price : ℚ
  price_nonneg : 0 ≤ price
  discount : ℚ
  discount_bounds : 0 ≤ discount ∧ discount ≤ 1

abbrev Info := Belief World × Wallet

def source (P : Parameters) : Source World Act Obs Noise where
  chance := primitiveWeight (fun _ => P.normal)
  nonneg := RegisterJointDecisionSource.primitiveWeight_nonneg _ (fun _ => P.normal_bounds)
  total := RegisterJointDecisionSource.primitiveWeight_sum_one _
  next := step P.goal
  observe := observe P.goal

def gain (P : Parameters) (_a : Act) (o : Obs) : ℚ :=
  (if o.1 then 1 else 0) - P.price * charge P.tariff o

def model (P : Parameters) : Model Info Act Obs :=
  filteredModel (source P) (fun i => menu P.tariff i.2)
    (fun i => menu_nonempty P.tariff i.2)
    (advance P.tariff) (gain P) P.discount P.discount_bounds.1

/-- All information updates use the joint world belief, not separate mechanism
and body marginals. The world itself remains behind the Source interface. -/
def initialBelief (goal : Bool) (prior : FaultMechanism → ℚ)
    (hn : ∀ m, 0 ≤ prior m) (ht : ∑ m, prior m = 1) : Belief World where
  Atom := FaultMechanism
  atoms := inferInstance
  state := initialWorld goal
  weight := prior
  nonneg := hn
  total := ht

def initialInfo (P : Parameters) (prior : FaultMechanism → ℚ)
    (hn : ∀ m, 0 ≤ prior m) (ht : ∑ m, prior m = 1) (wallet : Wallet) : Info :=
  (initialBelief P.goal prior hn ht, wallet)

/-- A causal controller can compute this from its own complete permitted
history. Neither a hidden field nor the true mechanism is an input. -/
def historyInfo (P : Parameters) (initial : Info) (h : List (Act × Obs)) : Info :=
  FiniteJointDecisionSupportedPolicy.historyInfo (model P) initial h

theorem joint_posterior_identity (P : Parameters) (b : Belief World) (a : Act)
    (o : Obs) (f : World → ℚ) :
    mass (source P) b a o * expect (posterior (source P) b a o) f =
      ∑ x : b.Atom × Noise, joint (source P) b a o x * f ((source P).next (b.state x.1) a x.2) :=
  posterior_identity (source P) b a o f

theorem receipt_witness (P : Parameters) (b : Belief World) (a : Act) (o : Obs)
    (ho : 0 < mass (source P) b a o) :
    ∃ x : b.Atom × Noise, observe P.goal (b.state x.1) a x.2 = o := by
  by_contra hn
  push Not at hn
  have hz : mass (source P) b a o = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    simp [joint, source, hn x]
  linarith

theorem supported_charge_le_cap (P : Parameters) (b : Belief World) (a : Act) (o : Obs)
    (ho : 0 < mass (source P) b a o) : charge P.tariff o ≤ P.tariff * cap a := by
  obtain ⟨x, hx⟩ := receipt_witness P b a o ho
  have hf := RegisterJointDecisionSource.feeUnit_le_cap P.goal (b.state x.1) a x.2
  change (if (observe P.goal (b.state x.1) a x.2).2 then 1 else 0 : ℚ) ≤ cap a at hf
  rw [hx] at hf
  calc
    charge P.tariff o = P.tariff * (if o.2 then 1 else 0) := by
      unfold charge
      cases o.2 <;> simp
    _ ≤ P.tariff * cap a := mul_le_mul_of_nonneg_left hf P.tariff_pos.le

/-- The original request cap is checked BEFORE a primitive result, and all
supported successors subtract that same actual fee from the same wallet. -/
def walletContract (P : Parameters) : WalletContract (model P) where
  balance := fun i => i.2.val
  prepay := fun _ a => P.tariff * cap a
  cost := fun _ _ o => charge P.tariff o
  prepay_nonneg := fun _ a => mul_nonneg P.tariff_pos.le (RegisterJointDecisionConsumer.cap_nonneg a)
  affordable := fun i a ha => mem_menu_prepay P.tariff i.2 a ha
  cost_nonneg := by intro i a ha o ho; unfold charge; split <;> linarith [P.tariff_pos]
  cost_le_prepay := fun i a _ o ho => supported_charge_le_cap P i.1 a o ho
  balance_next := by
    intro i a ha o ho
    change max 0 (i.2.val - charge P.tariff o) = i.2.val - charge P.tariff o
    apply max_eq_right
    exact sub_nonneg.mpr ((supported_charge_le_cap P i.1 a o ho).trans
      (mem_menu_prepay P.tariff i.2 a ha))

/-- Actual table execution branches only on the original permitted receipt. -/
def packedExecute (goal : Bool) :
    {H : ℕ} → Table Act Obs H → World → (Fin H → Noise) → Execution World Obs
  | _, .halt, w, _ => ⟨w, [], []⟩
  | H+1, .node a children, w, z =>
      let o := observe goal w a (z 0)
      prepend a o o (packedExecute goal (children o) (step goal w a (z 0)) (fun j => z j.succ))

@[simp] theorem packedExecute_theta (goal : Bool) :
    ∀ {H : ℕ} (table : Table Act Obs H) (w : World) (z : Fin H → Noise),
      (packedExecute goal table w z).finalWorld.theta = w.theta := by
  intro H
  induction H with
  | zero => intro table w z; cases table; rfl
  | succ H ih =>
      intro table w z
      cases table with
      | node a children =>
          exact (ih _ _ _).trans (theta_preserved goal w a (z 0))

theorem packedExecute_length (goal : Bool) :
    ∀ {H : ℕ} (table : Table Act Obs H) (w : World) (z : Fin H → Noise),
      (packedExecute goal table w z).records.length = H ∧
      (packedExecute goal table w z).history.length = H ∧
      (packedExecute goal table w z).finalWorld.store.length = w.store.length + H := by
  intro H
  induction H with
  | zero => intro table w z; cases table; simp [packedExecute]
  | succ H ih =>
      intro table w z
      cases table with
      | node a children =>
          have h := ih (children (observe goal w a (z 0))) (step goal w a (z 0)) (fun j => z j.succ)
          simp only [packedExecute, prepend, List.length_cons]
          exact ⟨by omega, by omega, by have ht := h.2.2; rw [step_length] at ht; omega⟩

/-- Conservative extension: S's entire computation is the original source. -/
theorem packedExecute_S (goal : Bool) :
    ∀ {H : ℕ} (table : Table Act Obs H) (w : World) (z : Fin H → Noise),
      w.theta = .S → packedExecute goal table w z =
        RegisterJointDecisionExecution.packedExecute goal table w z := by
  intro H
  induction H with
  | zero => intro table w z hm; cases table; rfl
  | succ H ih =>
      intro table w z hm
      cases table with
      | node a children =>
          simp only [packedExecute, RegisterJointDecisionExecution.packedExecute, observe]
          rw [step_S goal w a (z 0) hm, ih _ _ _ hm]

/-- Joint filtering transports the source value for every exact table. -/
theorem value_eq_source (P : Parameters) (H : ℕ) (table : Table Act Obs H) (i : Info) :
    value (model P) i table = expect i.1 (sourceValue (source P) (gain P) P.discount table) :=
  FiniteJointDecisionFilteredModel.value_eq_source (source P)
    (fun j => menu P.tariff j.2) (fun j => menu_nonempty P.tariff j.2)
    (advance P.tariff) (gain P) P.discount P.discount_bounds.1 H table i.1 i.2

/-- The pre-existing full-history theorem now consumes the NEW joint source.
Admissibility is required only on positive source-supported prefixes. -/
theorem all_actual_causal_le_returned (P : Parameters)
    (pi : RawCausalPolicy (model P)) (H : ℕ) (h : pi.Memory)
    (hh : SupportedAdmissible (model P) pi H h) :
    expectReal (pi.info h).1 (rawSourceValue (source P) (gain P) P.discount pi H h) ≤
      (expect (pi.info h).1 (sourceValue (source P) (gain P) P.discount
        (solve (model P) H (pi.info h))) : ℝ) :=
  supported_actual_causal_le_returned (source P) (fun j => menu P.tariff j.2)
    (fun j => menu_nonempty P.tariff j.2) (advance P.tariff) (gain P)
    P.discount P.discount_bounds.1 pi H h hh

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionSource
