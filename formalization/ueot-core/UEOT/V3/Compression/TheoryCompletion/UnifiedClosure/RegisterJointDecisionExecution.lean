import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionSource
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteJointDecisionSolver

/-!
# Actual execution of the returned outer decision table

These interpreters consume the table stored at each node. Only the permitted
birth/payment receipt chooses a child row. The original full Store and complete
transaction record stay on the world side. Source mode and label are sampled
tape inputs, never arguments to the table selector. The theorem is for every
finite horizon, every table and every tape, so it applies to THIS solver output
without substituting an existential optimal policy.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionExecution

open RegisterJointDecisionSource
open RegisterMechanismPurpose
open RegisterTimestampedBirthSource (ClockedRecord ClockedOrganism)
open FiniteJointDecisionSolver (Table)
open scoped BigOperators

structure Execution (W R : Type*) where
  finalWorld : W
  history : List (Act × Obs)
  records : List R

def prepend {W R : Type*} (a : Act) (o : Obs) (r : R) (tail : Execution W R) :
    Execution W R := ⟨tail.finalWorld, (a,o) :: tail.history, r :: tail.records⟩

def packedExecute {Theta : Type*} (goal : Bool) :
    {H : ℕ} → Table Act Obs H → World Theta → (Fin H → Noise) → Execution (World Theta) Obs
  | _, .halt, w, _ => ⟨w, [], []⟩
  | H+1, .node a children, w, z =>
      let o := observe goal w a (z 0)
      prepend a o o
        (packedExecute goal (children o) (step goal w a (z 0)) (fun j => z j.succ))

noncomputable def nativeExecute {Theta : Type*} {n : ℕ} (i : Fin n) (m : Mechanism) :
    {H : ℕ} → Table Act Obs H → NativeWorld Theta n → (Fin H → Noise) →
      Execution (NativeWorld Theta n) (Option (ClockedRecord n))
  | _, .halt, w, _ => ⟨w, [], []⟩
  | H+1, .node a children, w, z =>
      let r := nativeTransaction i m w a (z 0)
      let o := nativeObs r
      prepend a o r
        (nativeExecute i m (children o) (nativeStep i m w a (z 0)) (fun j => z j.succ))

def eraseExecution {Theta : Type*} {n : ℕ} (i : Fin n)
    (x : Execution (NativeWorld Theta n) (Option (ClockedRecord n))) :
    Execution (World Theta) Obs :=
  ⟨projectWorld i x.finalWorld, x.history, x.records.map nativeObs⟩

theorem erase_prepend {Theta : Type*} {n : ℕ} (i : Fin n) (a : Act)
    (r : Option (ClockedRecord n))
    (x : Execution (NativeWorld Theta n) (Option (ClockedRecord n))) :
    eraseExecution i (prepend a (nativeObs r) r x) =
      prepend a (nativeObs r) (nativeObs r) (eraseExecution i x) := rfl

/-- Pathwise source implementation for this exact finite table. This includes
the final physical population, every visible action/receipt, and the projections
of all literal transactions, without discarding fault or None records. -/
theorem nativeExecute_project {Theta : Type*} {n : ℕ} (i : Fin n) (m : Mechanism) :
    ∀ {H : ℕ} (table : Table Act Obs H) (w : NativeWorld Theta n) (z : Fin H → Noise),
      Aligned m.goal w.store →
      eraseExecution i (nativeExecute i m table w z) =
        packedExecute m.goal table (projectWorld i w) z := by
  intro H
  induction H with
  | zero =>
      intro table w z hw
      cases table
      rfl
  | succ H ih =>
      intro table w z hw
      cases table with
      | node a children =>
          simp only [nativeExecute, packedExecute, erase_prepend]
          rw [nativeObservation_project i m w a (z 0) hw]
          rw [ih (children (observe m.goal (projectWorld i w) a (z 0)))
            (nativeStep i m w a (z 0)) (fun j => z j.succ)
            (nativeStep_aligned i m w a (z 0) hw)]
          rw [nativeStep_project i m w a (z 0) hw]

/-- The protected original programs remain protected and aligned after the
whole run, irrespective of births, faults, stopping and address validity. -/
theorem nativeExecute_aligned {Theta : Type*} {n : ℕ} (i : Fin n) (m : Mechanism) :
    ∀ {H : ℕ} (table : Table Act Obs H) (w : NativeWorld Theta n) (z : Fin H → Noise),
      Aligned m.goal w.store →
      Aligned m.goal (nativeExecute i m table w z).finalWorld.store := by
  intro H
  induction H with
  | zero => intro table w z hw; cases table; exact hw
  | succ H ih =>
      intro table w z hw
      cases table with
      | node a children =>
          exact ih _ _ _ (nativeStep_aligned i m w a (z 0) hw)

theorem packedExecute_theta {Theta : Type*} (goal : Bool) :
    ∀ {H : ℕ} (table : Table Act Obs H) (w : World Theta) (z : Fin H → Noise),
      (packedExecute goal table w z).finalWorld.theta = w.theta := by
  intro H
  induction H with
  | zero => intro table w z; cases table; rfl
  | succ H ih =>
      intro table w z
      cases table with
      | node a children => exact ih _ _ _

theorem packedExecute_length {Theta : Type*} (goal : Bool) :
    ∀ {H : ℕ} (table : Table Act Obs H) (w : World Theta) (z : Fin H → Noise),
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

theorem nativeExecute_length {Theta : Type*} {n : ℕ} (i : Fin n) (m : Mechanism)
    {H : ℕ} (table : Table Act Obs H) (w : NativeWorld Theta n) (z : Fin H → Noise)
    (hw : Aligned m.goal w.store) :
    (nativeExecute i m table w z).records.length = H ∧
      (nativeExecute i m table w z).history.length = H ∧
      (nativeExecute i m table w z).finalWorld.store.length = w.store.length + H := by
  have h := packedExecute_length m.goal table (projectWorld i w) z
  rw [← nativeExecute_project i m table w z hw] at h
  simpa only [eraseExecution, projectWorld, project, List.length_map] using h

/-- The native and computational interpreters emit exactly the same legal
observation history; complete world records are not silently exposed. -/
theorem native_history_eq {Theta : Type*} {n : ℕ} (i : Fin n) (m : Mechanism)
    {H : ℕ} (table : Table Act Obs H) (w : NativeWorld Theta n) (z : Fin H → Noise)
    (hw : Aligned m.goal w.store) :
    (nativeExecute i m table w z).history = (packedExecute m.goal table (projectWorld i w) z).history :=
  congrArg Execution.history (nativeExecute_project i m table w z hw)

def receiptFee (o : Obs) : ℚ := if o.2 then 1 else 0
def receiptBirth (o : Obs) : ℚ := if o.1 then 1 else 0

def packedPayoff (pricedWrite discount : ℚ) : List Obs → ℚ
  | [] => 0
  | o :: os => receiptBirth o - pricedWrite * receiptFee o + discount * packedPayoff pricedWrite discount os

noncomputable def actualPayoff {n : ℕ} (price discount : ℚ) : List (Option (ClockedRecord n)) → ℝ
  | [] => 0
  | r :: rs => nativePayoff price r + (discount : ℝ) * actualPayoff price discount rs

theorem primitive_fee_receipt {n : ℕ} (i : Fin n) (m : Mechanism)
    (s : RegisterPopulationHistorySource.Store n) (q : RegisterPopulationHistorySource.Request) :
    nativeFee (RegisterPopulationHistorySource.transaction i m s q) =
      (receiptFee (nativeObs (RegisterPopulationHistorySource.transaction i m s q)) : ℝ) * m.writeCost := by
  unfold RegisterPopulationHistorySource.transaction
  cases hp : RegisterPopulationHistorySource.lookup s q.parent with
  | none => simp [nativeFee, nativeObs, receiptFee]
  | some p =>
      simp only [Option.map_some, primitive_fee]
      cases q.mode <;> cases q.action <;>
        simp [nativeObs, receiptFee, RegisterTimestampedBirthSource.step,
          RegisterFaultJointRecord.modeRecordStep, RegisterJointRecord.recordStep]

/-- Every recorded fee equals its own permitted paid-write receipt times the
public tariff, with zero fees at all missing and preempted transactions. -/
theorem native_fees_from_receipts {Theta : Type*} {n : ℕ} (i : Fin n) (m : Mechanism) :
    ∀ {H : ℕ} (table : Table Act Obs H) (w : NativeWorld Theta n) (z : Fin H → Noise),
      (nativeExecute i m table w z).records.map nativeFee =
        ((nativeExecute i m table w z).records.map nativeObs).map
          (fun o => (receiptFee o : ℝ) * m.writeCost) := by
  intro H
  induction H with
  | zero => intro table w z; cases table; rfl
  | succ H ih =>
      intro table w z
      cases table with
      | node a children =>
          simp only [nativeExecute, prepend, List.map_cons]
          rw [show nativeFee (nativeTransaction i m w a (z 0)) =
            (receiptFee (nativeObs (nativeTransaction i m w a (z 0))) : ℝ) * m.writeCost from
              primitive_fee_receipt i m w.store (request w.stopped a (z 0)), ih]

/-- Exact sum on every execution prefix of this table; it is not merely an
expected-cost bound and includes unsuccessful paid writes. -/
theorem prefix_cost_eq {Theta : Type*} {n : ℕ} (i : Fin n) (m : Mechanism)
    {H : ℕ} (table : Table Act Obs H) (w : NativeWorld Theta n) (z : Fin H → Noise)
    (hw : Aligned m.goal w.store) (k : ℕ) :
    (((nativeExecute i m table w z).records.map nativeFee).take k).sum =
      ((((packedExecute m.goal table (projectWorld i w) z).records.map
        (fun o => (receiptFee o : ℝ) * m.writeCost))).take k).sum := by
  rw [native_fees_from_receipts]
  have h := congrArg Execution.records (nativeExecute_project i m table w z hw)
  change (nativeExecute i m table w z).records.map nativeObs = _ at h
  rw [h]

/-- Full finite payoff identity for every exact table, not just the optimal
value or an existence witness. The terminal payoff is zero in both interpreters. -/
theorem table_payoff_eq {Theta : Type*} {n : ℕ} (i : Fin n) (m : Mechanism)
    (price tariff discount : ℚ) (hc : (m.writeCost : ℝ) = (tariff : ℝ)) :
    ∀ {H : ℕ} (table : Table Act Obs H) (w : NativeWorld Theta n) (z : Fin H → Noise),
      Aligned m.goal w.store →
      actualPayoff price discount (nativeExecute i m table w z).records =
        (packedPayoff (price * tariff) discount
          (packedExecute m.goal table (projectWorld i w) z).records : ℝ) := by
  intro H
  induction H with
  | zero => intro table w z hw; cases table; simp [nativeExecute, packedExecute, actualPayoff, packedPayoff]
  | succ H ih =>
      intro table w z hw
      cases table with
      | node a children =>
          simp only [nativeExecute, packedExecute, prepend, actualPayoff, packedPayoff]
          rw [nativeObservation_project i m w a (z 0) hw,
            nativePayoff_project i m price w a (z 0) hw,
            ih (children (observe m.goal (projectWorld i w) a (z 0)))
              (nativeStep i m w a (z 0)) (fun j => z j.succ)
              (nativeStep_aligned i m w a (z 0) hw),
            nativeStep_project i m w a (z 0) hw, hc]
          simp only [Rat.cast_add, Rat.cast_sub, Rat.cast_mul]
          rfl

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionExecution
