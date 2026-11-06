import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismExperimentPaths
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionFreeTail

/-!
# Zero-information source boundaries at every finite horizon

The root-only relation forgets hidden backup slots; it does not equate worlds.
The low-wallet result uses pre-outcome request caps, not realized fault fees.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismExperimentZero

open RegisterJointDecisionSource (Act Obs Noise PackedStore cap packedLookup effective address
  packedNext packedObserve postBit childBit)
open RegisterJointDecisionExecution (prepend)
open RegisterMechanismDecisionSource
open RegisterMechanismExperimentPaths
open RegisterJointDecisionValueBounds (AllDamaged)
open FiniteJointDecisionSolver (Table)

/-- This relation is used only inside the proof. It is not a sensor. -/
def SameBody (w v : World) : Prop := w.store = v.store ∧ w.stopped = v.stopped

def SameRoot (w v : World) : Prop :=
  packedLookup w.store 0 = packedLookup v.store 0 ∧ w.stopped = v.stopped

theorem observe_eq_of_sameBody (goal : Bool) (w v : World) (a : Act) (z : Noise)
    (h : SameBody w v) : observe goal w a z = observe goal v a z := by
  simp only [observe, RegisterJointDecisionSource.observe]
  rw [h.1,h.2]

theorem normal_sameBody (goal : Bool) (w v : World) (a : Act) (label : Bool)
    (h : SameBody w v) : SameBody (step goal w a (true,label)) (step goal v a (true,label)) := by
  simp only [SameBody, step_normal, RegisterJointDecisionSource.step]
  exact ⟨by rw [h.1,h.2], by rw [h.2]⟩

/-- With root dispatch, its own old fault already damages precisely this bit.
G's extra environmental damage cannot change the root recurrence. -/
theorem root_lookup_step (goal : Bool) (w : World) (a : Act) (z : Noise)
    (ha : (effective w.stopped a).1 = false) :
    packedLookup (step goal w a z).store 0 =
      (packedLookup w.store 0).map (fun bit => postBit goal bit (effective w.stopped a).2 z.1) := by
  rcases w with ⟨m,s,stopped⟩
  rcases z with ⟨mode,label⟩
  have hq : effective stopped a = (false,(effective stopped a).2) := Prod.ext ha rfl
  cases s with
  | nil =>
      cases m <;> cases mode <;>
        simp [step, RegisterJointDecisionSource.step, hq, address, packedNext,
          packedLookup, damagePacked]
  | cons op s =>
      cases op with
      | none =>
          cases m <;> cases mode <;>
            simp [step, RegisterJointDecisionSource.step, hq, address, packedNext,
              packedLookup, damagePacked]
      | some bit =>
          cases m <;> cases mode <;>
            simp [step, RegisterJointDecisionSource.step, hq, address, packedNext,
              packedLookup, damagePacked, postBit]

theorem observe_eq_of_sameRoot (goal : Bool) (w v : World) (a : Act) (z : Noise)
    (h : SameRoot w v) (ha : (effective w.stopped a).1 = false) :
    observe goal w a z = observe goal v a z := by
  unfold observe RegisterJointDecisionSource.observe
  rw [← h.2]
  simp only [address, ha, Bool.false_eq_true, if_false, packedObserve]
  rw [h.1]

theorem root_sameRoot (goal : Bool) (w v : World) (a : Act) (z : Noise)
    (h : SameRoot w v) (ha : (effective w.stopped a).1 = false) :
    SameRoot (step goal w a z) (step goal v a z) := by
  have hv : (effective v.stopped a).1 = false := by rw [← h.2]; exact ha
  constructor
  · rw [root_lookup_step goal w a z ha, root_lookup_step goal v a z hv, h.1, h.2]
  · simp only [stopped_step, h.2]

/-- All executed dispatches are to root. Once committed stop is set, even a
later syntactic request is physically the original root idle. -/
def RootOnly : {H : ℕ} → Bool → Table Act Obs H → Prop
  | _, _, .halt => True
  | _, stopped, .node a children =>
      (effective stopped a).1 = false ∧
        ∀ o, RootOnly (stopped || a.isNone) (children o)

theorem root_only_same_history (goal : Bool) :
    ∀ {H : ℕ} (t : Table Act Obs H) (w v : World) (z : Fin H → Noise),
      SameRoot w v → RootOnly w.stopped t →
      (packedExecute goal t w z).history = (packedExecute goal t v z).history := by
  intro H
  induction H with
  | zero => intro t w v z h hr; simp
  | succ H ih =>
      intro t w v z h hr
      cases t with
      | node a children =>
          have ho := observe_eq_of_sameRoot goal w v a (z 0) h hr.1
          simp only [packedExecute,prepend]
          rw [ho]
          apply congrArg (List.cons (a,observe goal v a (z 0)))
          apply ih
          · exact root_sameRoot goal w v a (z 0) h hr.1
          · simpa only [stopped_step] using hr.2 (observe goal v a (z 0))

theorem root_only_initial_history (goal : Bool) {H : ℕ} (t : Table Act Obs H)
    (z : Fin H → Noise) (hr : RootOnly false t) :
    (packedExecute goal t (initialWorld goal .S) z).history =
      (packedExecute goal t (initialWorld goal .G) z).history :=
  root_only_same_history goal t _ _ z ⟨rfl,rfl⟩ hr

/-- The permitted path when every tick delivers the actual 00 receipt. -/
def zeroHistory : {H : ℕ} → Table Act Obs H → List (Act × Obs)
  | _, .halt => []
  | _, .node a children => (a,(false,false)) :: zeroHistory (children (false,false))

/-- All-fault paths agree for every table, even in arbitrary initial worlds.
They supply a positive common mass, not a regret lower bound. -/
theorem all_fault_history (goal : Bool) :
    ∀ {H : ℕ} (t : Table Act Obs H) (w : World) (z : Fin H → Noise),
      (∀ j, (z j).1 = false) → (packedExecute goal t w z).history = zeroHistory t := by
  intro H
  induction H with
  | zero => intro t w z hz; cases t; rfl
  | succ H ih =>
      intro t w z hz
      cases t with
      | node a children =>
          have ho : observe goal w a (z 0) = (false,false) := by
            rw [← Prod.mk.eta (z 0), hz 0]
            exact observe_fault goal w a (z 0).2
          simp only [packedExecute,prepend,zeroHistory]
          rw [ho]
          exact congrArg (List.cons (a,(false,false))) (ih _ _ _ (fun j => hz j.succ))

theorem all_normal_same_history (goal : Bool) :
    ∀ {H : ℕ} (t : Table Act Obs H) (w v : World) (z : Fin H → Noise),
      SameBody w v → (∀ j, (z j).1 = true) →
      (packedExecute goal t w z).history = (packedExecute goal t v z).history := by
  intro H
  induction H with
  | zero => intro t w v z h hz; simp
  | succ H ih =>
      intro t w v z h hz
      cases t with
      | node a children =>
          have ho := observe_eq_of_sameBody goal w v a (z 0) h
          have hs : SameBody (step goal w a (z 0)) (step goal v a (z 0)) := by
            rw [← Prod.mk.eta (z 0), hz 0]
            exact normal_sameBody goal w v a (z 0).2 h
          simp only [packedExecute,prepend]
          rw [ho]
          exact congrArg (List.cons (a,observe goal v a (z 0)))
            (ih _ _ _ _ hs (fun j => hz j.succ))

theorem damagePacked_eq_of_damaged (goal : Bool) (s : PackedStore)
    (h : AllDamaged goal s) : damagePacked goal s = s := by
  induction s with
  | nil => rfl
  | cons op s ih =>
      have ht : AllDamaged goal s := fun b hb => h b (by simp [hb])
      cases op with
      | none => simpa [damagePacked] using congrArg (List.cons none) (ih ht)
      | some b =>
          have hb : b ≠ goal := h b (by simp)
          have he : !goal = b := by cases goal <;> cases b <;> simp_all
          simp only [damagePacked, List.map_cons, Option.map_some]
          rw [he]
          exact congrArg (List.cons (some b)) (ih ht)

/-- A cap-zero request cannot incur a write fee. The real old primitive proves
no birth and preserves damage; G adds only an idempotent damage map. -/
theorem damaged_free_step (goal : Bool) (w : World) (a : Act) (z : Noise)
    (hw : AllDamaged goal w.store) (ha : cap a = 0) :
    observe goal w a z = (false,false) ∧ AllDamaged goal (step goal w a z).store := by
  have hf : RegisterJointDecisionSource.feeUnit goal w a z = 0 := by
    have hn := RegisterJointDecisionSource.feeUnit_nonneg goal w a z
    have hl := RegisterJointDecisionSource.feeUnit_le_cap goal w a z
    rw [ha] at hl
    exact le_antisymm hl hn
  obtain ⟨hb,hs⟩ := RegisterJointDecisionValueBounds.no_fee_preserves_damaged goal w a z hw hf
  have ho : observe goal w a z = (false,false) := by
    change (RegisterJointDecisionSource.observe goal w a z) = (false,false)
    unfold RegisterJointDecisionSource.feeUnit at hf
    unfold RegisterJointDecisionSource.birthUnit at hb
    cases hx : (RegisterJointDecisionSource.observe goal w a z).1 <;>
      cases hy : (RegisterJointDecisionSource.observe goal w a z).2 <;> simp_all
  refine ⟨ho, ?_⟩
  unfold step
  split
  · simpa only [damagePacked_eq_of_damaged goal _ hs] using hs
  · exact hs

/-- The prepay contract as a predicate on the actual allowed history. It
checks requests before reading the following receipt and then charges the
literal paid-write flag. This is the same cap/cost ledger used by WalletContract. -/
def PrepaidHistory (tariff : ℚ) : ℚ → List (Act × Obs) → Prop
  | _, [] => True
  | wallet, (a,o) :: rest => tariff * cap a ≤ wallet ∧
      PrepaidHistory tariff (wallet - RegisterJointDecisionConsumer.charge tariff o) rest

theorem cap_zero_of_insufficient (tariff wallet : ℚ) (a : Act)
    (hB : wallet < tariff) (ha : tariff * cap a ≤ wallet) : cap a = 0 := by
  by_cases hc : (effective false a).2.isSome = true
  · have hcap : cap a = 1 := by simp [cap,hc]
    rw [hcap,mul_one] at ha
    exact (not_le_of_gt hB ha).elim
  · simp [cap,hc]

/-- Every actually prepaid run from a damaged founder with B<c has only 00
receipts, at arbitrary finite H. Failed writes cannot evade the initial cap. -/
theorem insufficient_wallet_zero_history (goal : Bool) (tariff : ℚ) :
    ∀ {H : ℕ} (t : Table Act Obs H) (w : World) (z : Fin H → Noise) (wallet : ℚ),
      AllDamaged goal w.store → wallet < tariff →
      PrepaidHistory tariff wallet (packedExecute goal t w z).history →
      (packedExecute goal t w z).history = zeroHistory t := by
  intro H
  induction H with
  | zero => intro t w z wallet hw hB hp; cases t; rfl
  | succ H ih =>
      intro t w z wallet hw hB hp
      cases t with
      | node a children =>
          have ha : tariff * cap a ≤ wallet := hp.1
          obtain ⟨ho,hs⟩ := damaged_free_step goal w a (z 0) hw
            (cap_zero_of_insufficient tariff wallet a hB ha)
          have ht : PrepaidHistory tariff wallet
              (packedExecute goal (children (false,false)) (step goal w a (z 0))
                (fun j => z j.succ)).history := by
            simpa only [packedExecute,prepend,PrepaidHistory,ho,
              RegisterJointDecisionConsumer.charge, Bool.false_eq_true, if_false, sub_zero] using hp.2
          simp only [packedExecute,prepend,zeroHistory]
          rw [ho]
          exact congrArg (List.cons (a,(false,false))) (ih _ _ _ wallet hs hB ht)

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismExperimentZero
