import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionSource
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteJointDecisionBelief
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteJointDecisionSolverExecution
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteJointDecisionFilteredModel

/-!
# One-source, one-wallet Register decision consumer

Only the public prior, public parameters and actual birth/charge receipts enter
the filter. The packed physical population is a hidden variable in that belief,
not a real-population oracle. A requested write is prepaid before its possibly
free fault/None outcome. Actual supported balances never use the off-path clamp.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionConsumer

open scoped BigOperators
open RegisterJointDecisionSource
open FiniteJointDecisionBelief
open FiniteJointDecisionSolver
open FiniteJointDecisionFilteredModel

structure Family (Theta : Type) where
  goal : Bool
  normal : Theta → ℚ
  normal_bounds : ∀ theta, 0 ≤ normal theta ∧ normal theta ≤ 1
  tariff : ℚ
  tariff_pos : 0 < tariff
  price : ℚ
  price_nonneg : 0 ≤ price
  discount : ℚ
  discount_bounds : 0 ≤ discount ∧ discount ≤ 1

abbrev Wallet := {q : ℚ // 0 ≤ q}
abbrev Info (Theta : Type) := Belief (World Theta) × Wallet

def source {Theta : Type} (P : Family Theta) : Source (World Theta) Act Obs Noise where
  chance := primitiveWeight P.normal
  nonneg := primitiveWeight_nonneg P.normal P.normal_bounds
  total := primitiveWeight_sum_one P.normal
  next := step P.goal
  observe := observe P.goal

/-- This exact public menu contains real child-address requests even when that
address does not exist. There is no successful-lookup filter. -/
def allActions : List Act :=
  [none, some (false, none), some (true, none),
    some (false, some false), some (false, some true),
    some (true, some false), some (true, some true)]

def menu (tariff : ℚ) (wallet : Wallet) : List Act :=
  allActions.filter (fun a => decide (tariff * cap a ≤ wallet.val))

theorem stop_mem_menu (tariff : ℚ) (wallet : Wallet) : none ∈ menu tariff wallet := by
  simp [menu, allActions, cap, effective, wallet.property]

theorem menu_nonempty (tariff : ℚ) (wallet : Wallet) : menu tariff wallet ≠ [] := by
  intro h
  have hn := stop_mem_menu tariff wallet
  rw [h] at hn
  exact List.not_mem_nil hn

theorem mem_menu_prepay (tariff : ℚ) (wallet : Wallet) (a : Act)
    (ha : a ∈ menu tariff wallet) : tariff * cap a ≤ wallet.val := by
  exact of_decide_eq_true (List.mem_filter.mp ha).2

def charge (tariff : ℚ) (o : Obs) : ℚ := if o.2 then tariff else 0

def gain {Theta : Type} (P : Family Theta) (_a : Act) (o : Obs) : ℚ :=
  (if o.1 then 1 else 0) - P.price * charge P.tariff o

/-- Only impossible observation branches can need the clamp. On every
supported feasible branch the source-derived prepayment bound proves equality
with literal subtraction. -/
def advance (tariff : ℚ) (wallet : Wallet) (_a : Act) (o : Obs) : Wallet :=
  ⟨max 0 (wallet.val - charge tariff o), le_max_left _ _⟩

def model {Theta : Type} (P : Family Theta) : Model (Info Theta) Act Obs :=
  filteredModel (source P) (fun i => menu P.tariff i.2)
    (fun i => menu_nonempty P.tariff i.2)
    (advance P.tariff) (gain P) P.discount P.discount_bounds.1

theorem charge_nonneg {Theta : Type} (P : Family Theta) (o : Obs) :
    0 ≤ charge P.tariff o := by unfold charge; split <;> linarith [P.tariff_pos]

theorem cap_nonneg (a : Act) : 0 ≤ cap a := by unfold cap; split <;> norm_num

/-- Positive receipt probability supplies an actual primitive branch; no hidden
state is supplied to the algorithm by this world-side existence proof. -/
theorem receipt_witness {Theta : Type} (P : Family Theta) (b : Belief (World Theta))
    (a : Act) (o : Obs) (ho : 0 < mass (source P) b a o) :
    ∃ x : b.Atom × Noise, observe P.goal (b.state x.1) a x.2 = o := by
  by_contra hn
  push Not at hn
  have hz : mass (source P) b a o = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    simp [joint, source, hn x]
  linarith

theorem supported_charge_le_cap {Theta : Type} (P : Family Theta)
    (b : Belief (World Theta)) (a : Act) (o : Obs)
    (ho : 0 < mass (source P) b a o) : charge P.tariff o ≤ P.tariff * cap a := by
  obtain ⟨x, hx⟩ := receipt_witness P b a o ho
  have hf := feeUnit_le_cap P.goal (b.state x.1) a x.2
  unfold feeUnit at hf
  rw [hx] at hf
  calc
    charge P.tariff o = P.tariff * (if o.2 then 1 else 0) := by
      unfold charge
      cases o.2 <;> simp
    _ ≤ P.tariff * cap a := mul_le_mul_of_nonneg_left hf P.tariff_pos.le

/-- The full wallet contract is derived from native charges and the public
pre-outcome menu. It is not an assumed resource certificate on an optimum. -/
def walletContract {Theta : Type} (P : Family Theta) : WalletContract (model P) where
  balance := fun i => i.2.val
  prepay := fun _ a => P.tariff * cap a
  cost := fun _ _ o => charge P.tariff o
  prepay_nonneg := fun _ a => mul_nonneg P.tariff_pos.le (cap_nonneg a)
  affordable := fun i a ha => mem_menu_prepay P.tariff i.2 a ha
  cost_nonneg := fun _ _ _ o _ => charge_nonneg P o
  cost_le_prepay := fun i a _ o ho => supported_charge_le_cap P i.1 a o ho
  balance_next := by
    intro i a ha o ho
    change max 0 (i.2.val - charge P.tariff o) = i.2.val - charge P.tariff o
    apply max_eq_right
    exact sub_nonneg.mpr ((supported_charge_le_cap P i.1 a o ho).trans
      (mem_menu_prepay P.tariff i.2 a ha))

def initialBelief {Theta : Type} [Fintype Theta] (P : Family Theta)
    (prior : Theta → ℚ) (hn : ∀ t, 0 ≤ prior t) (ht : ∑ t, prior t = 1) :
    Belief (World Theta) where
  Atom := Theta
  atoms := inferInstance
  state := fun t => ⟨t, [some (!P.goal)], false⟩
  weight := prior
  nonneg := hn
  total := ht

/-- Actual executable return for any finite horizon, not an existential
replacement of the table produced by the solver. -/
def returned {Theta : Type} (P : Family Theta) (H : ℕ) (i : Info Theta) : Table Act Obs H :=
  solve (model P) H i

theorem returned_feasible {Theta : Type} (P : Family Theta) (H : ℕ) (i : Info Theta) :
    Feasible (model P) i (returned P H i) := solve_feasible (model P) H i

theorem returned_prefix_payment {Theta : Type} (P : Family Theta) (H : ℕ) (i : Info Theta)
    (w : Tape Obs H) (hw : 0 < tapeWeight (model P) i (returned P H i) w) :
    PrepaidAlong (model P) (walletContract P) i (returned P H i) w ∧ ∀ k,
      (walletContract P).balance (prefixInfo (model P) i (returned P H i) w k) =
        i.2.val - prefixCost (model P) (walletContract P) i (returned P H i) w k ∧
      0 ≤ prefixCost (model P) (walletContract P) i (returned P H i) w k ∧
      prefixCost (model P) (walletContract P) i (returned P H i) w k ≤ i.2.val :=
  returned_table_prefix_payment (model P) (walletContract P) H i i.2.property w hw

theorem insufficient_prepaid_no_write (tariff : ℚ) (wallet : Wallet)
    (h : wallet.val < tariff) (a : Act) (ha : a ∈ menu tariff wallet) : cap a = 0 := by
  have hp := mem_menu_prepay tariff wallet a ha
  by_cases hc : (effective false a).2.isSome = true
  · have hcap : cap a = 1 := by simp [cap, hc]
    rw [hcap, mul_one] at hp
    exact (not_le_of_gt h hp).elim
  · simp [cap, hc]

@[simp] theorem horizon_zero_value {Theta : Type} (P : Family Theta) (i : Info Theta) :
    value (model P) i (returned P 0 i) = 0 := rfl

/-- The computed optimum is the expected payoff of THIS returned table on
the actual persistent-theta primitive, with its hidden population retained. -/
theorem returned_actual_value {Theta : Type} (P : Family Theta) (H : ℕ) (i : Info Theta) :
    value (model P) i (returned P H i) =
      expect i.1 (sourceValue (source P) (gain P) P.discount (returned P H i)) :=
  value_eq_source (source P) (fun j => menu P.tariff j.2)
    (fun j => menu_nonempty P.tariff j.2) (advance P.tariff) (gain P)
    P.discount P.discount_bounds.1 H (returned P H i) i.1 i.2

/-- Every supported ACTUAL initial atom and primitive-noise path inherits
the returned table's exact prefix ledger, not only an expected-budget bound. -/
theorem returned_actual_prefix_payment {Theta : Type} (P : Family Theta) (H : ℕ)
    (i : Info Theta) (x : i.1.Atom) (noise : Tape Noise H)
    (hx : 0 < i.1.weight x)
    (hn : 0 < sourceTapeWeight (source P) (returned P H i) (i.1.state x) noise) :
    let path := observedTape (source P) (returned P H i) (i.1.state x) noise
    PrepaidAlong (model P) (walletContract P) i (returned P H i) path ∧ ∀ k,
      (walletContract P).balance (prefixInfo (model P) i (returned P H i) path k) =
        i.2.val - prefixCost (model P) (walletContract P) i (returned P H i) path k ∧
      0 ≤ prefixCost (model P) (walletContract P) i (returned P H i) path k ∧
      prefixCost (model P) (walletContract P) i (returned P H i) path k ≤ i.2.val := by
  apply returned_prefix_payment
  exact observedTape_supported (source P) (fun j => menu P.tariff j.2)
    (fun j => menu_nonempty P.tariff j.2) (advance P.tariff) (gain P)
    P.discount P.discount_bounds.1 H (returned P H i) i.1 i.2 x noise hx hn

/-- Arbitrary-memory real-randomized competitors use the same permitted
history, original joint primitive and full fees. -/
theorem returned_actual_optimal {Theta : Type} (P : Family Theta)
    (pi : CausalPolicy (model P)) (H : ℕ) (h : pi.Memory) :
    expectReal (pi.info h).1 (sourceCausalValue (source P) (gain P) P.discount pi H h) ≤
      (expect (pi.info h).1 (sourceValue (source P) (gain P) P.discount
        (returned P H (pi.info h))) : ℝ) :=
  actual_causal_le_returned (source P) (fun j => menu P.tariff j.2)
    (fun j => menu_nonempty P.tariff j.2) (advance P.tariff) (gain P)
    P.discount P.discount_bounds.1 pi H h

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionConsumer
