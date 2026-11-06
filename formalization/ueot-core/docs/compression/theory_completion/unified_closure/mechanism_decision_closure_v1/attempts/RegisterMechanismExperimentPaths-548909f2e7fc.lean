import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionSource

/-!
# Source-path limits of allowed mechanism experiments

All source states in this file are world-side proof variables. Tables consume
only their own action and the two receipt bits. The equalities include failure
and missing-address receipts; the complete native worlds need not agree.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismExperimentPaths

open RegisterJointDecisionSource (Act Obs Noise PackedStore cap packedLookup effective address
  packedNext packedObserve postBit childBit)
open RegisterJointDecisionExecution (Execution prepend)
open RegisterMechanismDecisionSource
open FiniteJointDecisionSolver (Table)

/-- The local source's two relevant output fields, before any private selection. -/
def firstReceipt (goal : Bool) (m : FaultMechanism) (a : Act) (mode : Bool) : Obs :=
  observe goal (initialWorld goal m) a (mode, false)

def firstWorld (goal : Bool) (m : FaultMechanism) (a : Act) (mode : Bool) : World :=
  step goal (initialWorld goal m) a (mode, false)

def secondReceipt (goal : Bool) (m : FaultMechanism) (a b : Act) (x y : Bool) : Obs :=
  observe goal (firstWorld goal m a x) b (y, false)

def secondWorld (goal : Bool) (m : FaultMechanism) (a b : Act) (x y : Bool) : World :=
  step goal (firstWorld goal m a x) b (y, false)

def thirdReceipt (goal : Bool) (m : FaultMechanism) (a b c : Act) (x y z : Bool) : Obs :=
  observe goal (secondWorld goal m a b x y) c (z, false)

/-- The first allowed receipt agrees for EVERY request and mode. -/
theorem first_receipt_eq : ∀ (goal : Bool) (a : Act) (mode : Bool),
    firstReceipt goal .S a mode = firstReceipt goal .G a mode := by decide

/-- Even the full menu has the same second receipt, for every common pair of
requests and modes. The child1 allocation phase is included by the real list. -/
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem second_receipt_eq : ∀ (goal : Bool) (a b : Act) (x y : Bool),
    secondReceipt goal .S a b x y = secondReceipt goal .G a b x y := by decide

/-- The first potentially different receipt is the third one; its mode word
must be normal/fault/normal. This is a finite identity of the actual primitive,
not an assumption on the final returned strategy or its visited actions. -/
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem third_receipt_eq_unless_NFN : ∀ (goal : Bool) (a b c : Act) (x y z : Bool),
    ¬(x = true ∧ y = false ∧ z = true) →
      thirdReceipt goal .S a b c x y z = thirdReceipt goal .G a b c x y z := by decide

@[simp] theorem zero_history (goal : Bool) (t : Table Act Obs 0) (w : World)
    (z : Fin 0 → Noise) : (packedExecute goal t w z).history = [] := by
  cases t
  rfl

/-- Every primitive birth label is erased only from the allowed history, never
from the native record. Its actual use is independent of the controller. -/
theorem history_label_irrelevant (goal : Bool) :
    ∀ {H : ℕ} (t : Table Act Obs H) (w : World) (z z' : Fin H → Noise),
      (∀ j, (z j).1 = (z' j).1) →
      (packedExecute goal t w z).history = (packedExecute goal t w z').history := by
  intro H
  induction H with
  | zero => intro t w z z' hz; simp
  | succ H ih =>
      intro t w z z' hz
      cases t with
      | node a children =>
          have ho : observe goal w a (z 0) = observe goal w a (z' 0) := by
            rcases h0 : z 0 with ⟨mode,label⟩
            rcases h1 : z' 0 with ⟨mode',label'⟩
            have hm := hz 0
            simp only [h0,h1] at hm
            subst mode'
            rfl
          have hs : step goal w a (z 0) = step goal w a (z' 0) := by
            rcases h0 : z 0 with ⟨mode,label⟩
            rcases h1 : z' 0 with ⟨mode',label'⟩
            have hm := hz 0
            simp only [h0,h1] at hm
            subst mode'
            rfl
          simp only [packedExecute, prepend]
          rw [ho, hs]
          exact congrArg (List.cons (a, observe goal w a (z' 0)))
            (ih _ _ _ _ (fun j => hz j.succ))

/-- H1 equality is pathwise under the same independent private seed/table. -/
theorem history_one_eq (goal : Bool) (t : Table Act Obs 1) (z : Fin 1 → Noise) :
    (packedExecute goal t (initialWorld goal .S) z).history =
      (packedExecute goal t (initialWorld goal .G) z).history := by
  cases t with
  | node a children =>
      simp only [packedExecute, prepend, zero_history]
      have ho := first_receipt_eq goal a (z 0).1
      exact congrArg (fun o => [(a,o)]) ho

/-- H2 equality is pathwise even for adaptive tables over ALL seven actions. -/
theorem history_two_eq (goal : Bool) (t : Table Act Obs 2) (z : Fin 2 → Noise) :
    (packedExecute goal t (initialWorld goal .S) z).history =
      (packedExecute goal t (initialWorld goal .G) z).history := by
  cases t with
  | node a children =>
      have h0 := first_receipt_eq goal a (z 0).1
      change observe goal (initialWorld goal .S) a (z 0) =
        observe goal (initialWorld goal .G) a (z 0) at h0
      simp only [packedExecute, prepend]
      rw [h0]
      cases hc : children (observe goal (initialWorld goal .G) a (z 0)) with
      | node b grandchildren =>
          simp only [packedExecute, prepend, zero_history]
          have h1 := second_receipt_eq goal a b (z 0).1 (z 1).1
          exact congrArg (fun o => (a,observe goal (initialWorld goal .G) a (z 0)) :: [(b,o)]) h1

/-- The H3 all-table coupling bound is independent of its probabilities,
wallet or payoff. Imposing legality therefore cannot weaken this upper bound. -/
theorem history_three_eq_unless_NFN (goal : Bool) (t : Table Act Obs 3)
    (z : Fin 3 → Noise)
    (hmode : ¬((z 0).1 = true ∧ (z 1).1 = false ∧ (z 2).1 = true)) :
    (packedExecute goal t (initialWorld goal .S) z).history =
      (packedExecute goal t (initialWorld goal .G) z).history := by
  cases t with
  | node a children =>
      have h0 := first_receipt_eq goal a (z 0).1
      change observe goal (initialWorld goal .S) a (z 0) =
        observe goal (initialWorld goal .G) a (z 0) at h0
      simp only [packedExecute, prepend]
      rw [h0]
      cases hc : children (observe goal (initialWorld goal .G) a (z 0)) with
      | node b grandchildren =>
          have h1 := second_receipt_eq goal a b (z 0).1 (z 1).1
          change observe goal (step goal (initialWorld goal .S) a (z 0)) b (z 1) =
            observe goal (step goal (initialWorld goal .G) a (z 0)) b (z 1) at h1
          simp only [packedExecute, prepend]
          rw [h1]
          cases hd : grandchildren
              (observe goal (step goal (initialWorld goal .G) a (z 0)) b (z 1)) with
          | node c greatgrandchildren =>
              simp only [packedExecute, prepend, zero_history]
              have h2 := third_receipt_eq_unless_NFN goal a b c
                (z 0).1 (z 1).1 (z 2).1 hmode
              exact congrArg (fun o =>
                (a,observe goal (initialWorld goal .G) a (z 0)) ::
                (b,observe goal (step goal (initialWorld goal .G) a (z 0)) b (z 1)) :: [(c,o)]) h2

/-- The actual three-step separation protocol. Middle idle is not committed
stop; it preserves the ability to dispatch child1 on the final tick. -/
def separationTable (goal : Bool) : Table Act Obs 3 :=
  .node (some (false, some goal)) (fun _ =>
    .node (some (false, none)) (fun _ =>
      .node (some (true, none)) (fun _ => .halt)))

def separationHistory (goal : Bool) : List (Act × Obs) :=
  [(some (false, some goal), (true,true)), (some (false,none), (false,false)),
    (some (true,none), (true,false))]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem separation_event_S : ∀ (goal : Bool) (z : Fin 3 → Noise),
    (packedExecute goal (separationTable goal) (initialWorld goal .S) z).history =
      separationHistory goal ↔ (z 0).1 = true ∧ (z 1).1 = false ∧ (z 2).1 = true := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem separation_event_G : ∀ (goal : Bool) (z : Fin 3 → Noise),
    (packedExecute goal (separationTable goal) (initialWorld goal .G) z).history ≠
      separationHistory goal := by decide

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismExperimentPaths
