import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionSource

/-!
# Complete original Store implementation of the fixed S/G source

The extra G fault acts only on a physical register. All original records,
identities, genealogy, protected programs, other bits, and dispatch clocks are
retained. In particular, a missing request still appends None and does not cancel
the environmental fault. The same receipt-only table is interpreted natively;
the hidden mechanism is used by the world transition and never by the selector.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionNative

open scoped BigOperators
open RegisterMechanismDecisionSource
open RegisterJointDecisionSource (Act Obs Noise Aligned project projectWorld nativeObs
  nativeFee nativePayoff request)
open RegisterJointDecisionExecution (Execution prepend eraseExecution erase_prepend
  receiptFee packedPayoff actualPayoff)
open RegisterTimestampedBirthSource (ClockedOrganism ClockedRecord)
open RegisterMechanismPurpose (Mechanism)
open FiniteJointDecisionSolver (Table Model)
open FiniteJointDecisionBelief (Source Belief)
open FiniteJointDecisionSupportedPolicy (RawCausalPolicy rawSourceValue)

abbrev NativeWorld (n : ℕ) := RegisterJointDecisionSource.NativeWorld FaultMechanism n

/-- No clock, ancestry or protected program is changed by common damage. -/
def damageOrganism {n : ℕ} (i : Fin n) (goal : Bool) (p : ClockedOrganism n) : ClockedOrganism n :=
  {p with organism := {p.organism with physical := Function.update p.organism.physical i (!goal)}}

def damageStore {n : ℕ} (i : Fin n) (goal : Bool)
    (s : RegisterPopulationHistorySource.Store n) : RegisterPopulationHistorySource.Store n :=
  s.map (Option.map (damageOrganism i goal))

@[simp] theorem damageOrganism_bit {n : ℕ} (i : Fin n) (goal : Bool) (p : ClockedOrganism n) :
    (damageOrganism i goal p).organism.physical i = !goal := by
  simp [damageOrganism]

theorem damageOrganism_other_bit {n : ℕ} (i j : Fin n) (goal : Bool)
    (p : ClockedOrganism n) (hji : j ≠ i) :
    (damageOrganism i goal p).organism.physical j = p.organism.physical j := by
  simp [damageOrganism, hji]

/-- The complete nonphysical fields remain those of the original transaction. -/
theorem damageOrganism_metadata {n : ℕ} (i : Fin n) (goal : Bool) (p : ClockedOrganism n) :
    (damageOrganism i goal p).identity = p.identity ∧
    (damageOrganism i goal p).clock = p.clock ∧
    (damageOrganism i goal p).organism.history = p.organism.history ∧
    (damageOrganism i goal p).organism.program = p.organism.program := by
  exact ⟨rfl, rfl, rfl, rfl⟩

@[simp] theorem damageStore_length {n : ℕ} (i : Fin n) (goal : Bool)
    (s : RegisterPopulationHistorySource.Store n) :
    (damageStore i goal s).length = s.length := by simp [damageStore]

theorem damageStore_lookup {n : ℕ} (i : Fin n) (goal : Bool)
    (s : RegisterPopulationHistorySource.Store n) (j : ℕ) :
    RegisterPopulationHistorySource.lookup (damageStore i goal s) j =
      (RegisterPopulationHistorySource.lookup s j).map (damageOrganism i goal) := by
  simp only [damageStore, RegisterPopulationHistorySource.lookup, List.getElem?_map]
  cases h : s[j]? with
  | none => simp [h]
  | some op => cases op <;> simp [h]

theorem damageStore_metadata {n : ℕ} (i : Fin n) (goal : Bool)
    (s : RegisterPopulationHistorySource.Store n) :
    (damageStore i goal s).map (Option.map (fun p =>
      (p.identity, p.clock, p.organism.history, p.organism.program))) =
    s.map (Option.map (fun p =>
      (p.identity, p.clock, p.organism.history, p.organism.program))) := by
  simp [damageStore, damageOrganism, List.map_map, Function.comp_def, Option.map_map]

theorem project_damageStore {n : ℕ} (i : Fin n) (goal : Bool)
    (s : RegisterPopulationHistorySource.Store n) :
    project i (damageStore i goal s) = damagePacked goal (project i s) := by
  simp [project, damageStore, damagePacked, damageOrganism, List.map_map,
    Function.comp_def, Option.map_map]

theorem aligned_damageStore {n : ℕ} (i : Fin n) (goal : Bool)
    (s : RegisterPopulationHistorySource.Store n) (hs : Aligned goal s) :
    Aligned goal (damageStore i goal s) := by
  intro p hp
  obtain ⟨op, hop, heq⟩ := List.mem_map.mp hp
  cases op with
  | none => cases heq
  | some q =>
      have heq' : damageOrganism i goal q = p := Option.some.inj heq
      rw [← heq']
      exact hs q hop

/-- Old source first, then G damage. The post-map does not alter the record. -/
noncomputable def nativeStep {n : ℕ} (i : Fin n) (m : Mechanism)
    (w : NativeWorld n) (a : Act) (z : Noise) : NativeWorld n :=
  let u := RegisterJointDecisionSource.nativeStep i m w a z
  if w.theta = .G ∧ z.1 = false then {u with store := damageStore i m.goal u.store} else u

noncomputable def nativeTransaction {n : ℕ} (i : Fin n) (m : Mechanism)
    (w : NativeWorld n) (a : Act) (z : Noise) : Option (ClockedRecord n) :=
  RegisterJointDecisionSource.nativeTransaction i m w a z

@[simp] theorem nativeStep_S {n : ℕ} (i : Fin n) (m : Mechanism)
    (w : NativeWorld n) (a : Act) (z : Noise) (hm : w.theta = .S) :
    nativeStep i m w a z = RegisterJointDecisionSource.nativeStep i m w a z := by
  simp [nativeStep, hm]

@[simp] theorem nativeStep_normal {n : ℕ} (i : Fin n) (m : Mechanism)
    (w : NativeWorld n) (a : Act) (label : Bool) :
    nativeStep i m w a (true,label) =
      RegisterJointDecisionSource.nativeStep i m w a (true,label) := by
  simp [nativeStep]

/-- The new packed transition is derived from the original complete Store. -/
theorem nativeStep_project {n : ℕ} (i : Fin n) (m : Mechanism)
    (w : NativeWorld n) (a : Act) (z : Noise) (hw : Aligned m.goal w.store) :
    projectWorld i (nativeStep i m w a z) = step m.goal (projectWorld i w) a z := by
  have hbase := RegisterJointDecisionSource.nativeStep_project i m w a z hw
  unfold nativeStep step
  change (projectWorld i (if w.theta = .G ∧ z.1 = false then
      { RegisterJointDecisionSource.nativeStep i m w a z with
        store := damageStore i m.goal (RegisterJointDecisionSource.nativeStep i m w a z).store }
      else RegisterJointDecisionSource.nativeStep i m w a z)) =
    if w.theta = .G ∧ z.1 = false then
      { RegisterJointDecisionSource.step m.goal (projectWorld i w) a z with
        store := damagePacked m.goal (RegisterJointDecisionSource.step m.goal (projectWorld i w) a z).store }
      else RegisterJointDecisionSource.step m.goal (projectWorld i w) a z
  split_ifs with h
  · calc
      _ = {projectWorld i (RegisterJointDecisionSource.nativeStep i m w a z) with
          store := damagePacked m.goal (projectWorld i
            (RegisterJointDecisionSource.nativeStep i m w a z)).store} := by
            simp only [projectWorld, project_damageStore]
      _ = _ := congrArg (fun v : World => {v with store := damagePacked m.goal v.store}) hbase
  · exact hbase

theorem nativeStep_aligned {n : ℕ} (i : Fin n) (m : Mechanism)
    (w : NativeWorld n) (a : Act) (z : Noise) (hw : Aligned m.goal w.store) :
    Aligned m.goal (nativeStep i m w a z).store := by
  unfold nativeStep
  split
  · exact aligned_damageStore i m.goal _ (RegisterJointDecisionSource.nativeStep_aligned i m w a z hw)
  · exact RegisterJointDecisionSource.nativeStep_aligned i m w a z hw

theorem nativeObservation_project {n : ℕ} (i : Fin n) (m : Mechanism)
    (w : NativeWorld n) (a : Act) (z : Noise) (hw : Aligned m.goal w.store) :
    nativeObs (nativeTransaction i m w a z) = observe m.goal (projectWorld i w) a z :=
  RegisterJointDecisionSource.nativeObservation_project i m w a z hw

theorem nativeFee_project {n : ℕ} (i : Fin n) (m : Mechanism)
    (w : NativeWorld n) (a : Act) (z : Noise) :
    nativeFee (nativeTransaction i m w a z) =
      (if (observe m.goal (projectWorld i w) a z).2 then 1 else 0 : ℝ) * m.writeCost := by
  exact RegisterJointDecisionSource.fee_project i m w.store (request w.stopped a z)

theorem nativePayoff_eq_pricedReceipt {n : ℕ} (i : Fin n) (m : Mechanism)
    (price tariff : ℚ) (hc : (m.writeCost : ℝ) = (tariff : ℝ))
    (w : NativeWorld n) (a : Act) (z : Noise) (hw : Aligned m.goal w.store) :
    nativePayoff price (nativeTransaction i m w a z) =
      (RegisterJointDecisionNativeLaw.pricedReceipt price tariff a
        (observe m.goal (projectWorld i w) a z) : ℝ) :=
  RegisterJointDecisionNativeLaw.nativePayoff_eq_pricedReceipt i m price tariff hc w a z hw

/-- A missing dispatch still takes a tick, appends None and suffers G damage. -/
theorem native_G_missing_fault {n : ℕ} (i : Fin n) (m : Mechanism)
    (w : NativeWorld n) (a : Act) (label : Bool) (hm : w.theta = .G)
    (hn : RegisterPopulationHistorySource.lookup w.store
      (request w.stopped a (false,label)).parent = none) :
    nativeTransaction i m w a (false,label) = none ∧
    (nativeStep i m w a (false,label)).store = damageStore i m.goal (w.store ++ [none]) := by
  have h := RegisterPopulationHistorySource.invalid_request i m w.store
    (request w.stopped a (false,label)) hn
  refine ⟨h.1, ?_⟩
  simp only [nativeStep, hm, and_self, if_true, RegisterJointDecisionSource.nativeStep]
  rw [h.2.2]

/-- The selector consumes the SAME table and only the original two-bit receipt. -/
noncomputable def nativeExecute {n : ℕ} (i : Fin n) (m : Mechanism) :
    {H : ℕ} → Table Act Obs H → NativeWorld n → (Fin H → Noise) →
      Execution (NativeWorld n) (Option (ClockedRecord n))
  | _, .halt, w, _ => ⟨w, [], []⟩
  | H+1, .node a children, w, z =>
      let r := nativeTransaction i m w a (z 0)
      let o := nativeObs r
      prepend a o r (nativeExecute i m (children o) (nativeStep i m w a (z 0)) (fun j => z j.succ))

/-- All finite horizons, every table and every full primitive tape. Complete
world-side records are preserved, while their controller projection commutes. -/
theorem nativeExecute_project {n : ℕ} (i : Fin n) (m : Mechanism) :
    ∀ {H : ℕ} (table : Table Act Obs H) (w : NativeWorld n) (z : Fin H → Noise),
      Aligned m.goal w.store →
      eraseExecution i (nativeExecute i m table w z) =
        packedExecute m.goal table (projectWorld i w) z := by
  intro H
  induction H with
  | zero => intro table w z hw; cases table; rfl
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

theorem nativeExecute_aligned {n : ℕ} (i : Fin n) (m : Mechanism) :
    ∀ {H : ℕ} (table : Table Act Obs H) (w : NativeWorld n) (z : Fin H → Noise),
      Aligned m.goal w.store → Aligned m.goal (nativeExecute i m table w z).finalWorld.store := by
  intro H
  induction H with
  | zero => intro table w z hw; cases table; exact hw
  | succ H ih =>
      intro table w z hw
      cases table with
      | node a children => exact ih _ _ _ (nativeStep_aligned i m w a (z 0) hw)

theorem nativeExecute_length {n : ℕ} (i : Fin n) (m : Mechanism)
    {H : ℕ} (table : Table Act Obs H) (w : NativeWorld n) (z : Fin H → Noise)
    (hw : Aligned m.goal w.store) :
    (nativeExecute i m table w z).records.length = H ∧
    (nativeExecute i m table w z).history.length = H ∧
    (nativeExecute i m table w z).finalWorld.store.length = w.store.length + H := by
  have h := packedExecute_length m.goal table (projectWorld i w) z
  rw [← nativeExecute_project i m table w z hw] at h
  simpa only [eraseExecution, projectWorld, project, List.length_map] using h

theorem native_history_eq {n : ℕ} (i : Fin n) (m : Mechanism)
    {H : ℕ} (table : Table Act Obs H) (w : NativeWorld n) (z : Fin H → Noise)
    (hw : Aligned m.goal w.store) :
    (nativeExecute i m table w z).history =
      (packedExecute m.goal table (projectWorld i w) z).history :=
  congrArg Execution.history (nativeExecute_project i m table w z hw)

theorem native_fees_from_receipts {n : ℕ} (i : Fin n) (m : Mechanism) :
    ∀ {H : ℕ} (table : Table Act Obs H) (w : NativeWorld n) (z : Fin H → Noise),
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
              RegisterJointDecisionExecution.primitive_fee_receipt i m w.store
                (request w.stopped a (z 0)), ih]

theorem prefix_cost_eq {n : ℕ} (i : Fin n) (m : Mechanism)
    {H : ℕ} (table : Table Act Obs H) (w : NativeWorld n) (z : Fin H → Noise)
    (hw : Aligned m.goal w.store) (k : ℕ) :
    (((nativeExecute i m table w z).records.map nativeFee).take k).sum =
      ((((packedExecute m.goal table (projectWorld i w) z).records.map
        (fun o => (receiptFee o : ℝ) * m.writeCost))).take k).sum := by
  rw [native_fees_from_receipts]
  have h := congrArg Execution.records (nativeExecute_project i m table w z hw)
  change (nativeExecute i m table w z).records.map nativeObs = _ at h
  rw [h]

/-- Every literal native payoff uses the birth and full charge of its record. -/
theorem table_payoff_eq {n : ℕ} (i : Fin n) (m : Mechanism)
    (price tariff discount : ℚ) (hc : (m.writeCost : ℝ) = (tariff : ℝ)) :
    ∀ {H : ℕ} (table : Table Act Obs H) (w : NativeWorld n) (z : Fin H → Noise),
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
            nativePayoff_eq_pricedReceipt i m price tariff hc w a (z 0) hw,
            ih (children (observe m.goal (projectWorld i w) a (z 0)))
              (nativeStep i m w a (z 0)) (fun j => z j.succ)
              (nativeStep_aligned i m w a (z 0) hw),
            nativeStep_project i m w a (z 0) hw]
          simp only [RegisterJointDecisionNativeLaw.pricedReceipt,
            RegisterJointDecisionExecution.receiptBirth, receiptFee]
          push_cast
          cases hb : (observe m.goal (projectWorld i w) a (z 0)).1 <;>
            cases hf : (observe m.goal (projectWorld i w) a (z 0)).2 <;>
              simp [hb, hf] <;> ring

/-- A raw real causal kernel on permitted memory, executed against full Store.
Only the world transition receives the mechanism. Private policy randomness is
supplied independently, through actionProb on the allowed memory alone. -/
noncomputable def rawNativeCausalValue {n : ℕ} {I : Type*}
    (K : Source World Act Obs Noise) (i : Fin n) (m : Mechanism)
    (price d : ℚ) {N : Model I Act Obs} (pi : RawCausalPolicy N) :
    ℕ → pi.Memory → NativeWorld n → ℝ
  | 0, _, _ => 0
  | H+1, h, w =>
      ∑ a, pi.actionProb h a * ∑ z, (K.chance (projectWorld i w) z : ℝ) *
        (nativePayoff price (nativeTransaction i m w a z) + (d : ℝ) *
          rawNativeCausalValue K i m price d pi H
            (pi.advance h a (nativeObs (nativeTransaction i m w a z))) (nativeStep i m w a z))

/-- This whole-process identity has no all-counterfactual-menu premise.
Combined with C1 it covers every supported-legal real full-history competitor. -/
theorem rawNativeCausalValue_eq_packed {n : ℕ} {M : Type*}
    (K : Source World Act Obs Noise) (i : Fin n) (m : Mechanism)
    (hnext : K.next = step m.goal) (hobs : K.observe = observe m.goal)
    (price tariff d : ℚ) (hc : (m.writeCost : ℝ) = (tariff : ℝ))
    {N : Model (Belief World × M) Act Obs} (pi : RawCausalPolicy N) :
    ∀ H (h : pi.Memory) (w : NativeWorld n), Aligned m.goal w.store →
      rawNativeCausalValue K i m price d pi H h w =
        rawSourceValue K (RegisterJointDecisionNativeLaw.pricedReceipt price tariff) d pi H h
          (projectWorld i w) := by
  intro H
  induction H with
  | zero => intros; rfl
  | succ H ih =>
      intro h w hw
      simp only [rawNativeCausalValue, rawSourceValue]
      apply Finset.sum_congr rfl
      intro a ha
      apply congrArg (fun t : ℝ => pi.actionProb h a * t)
      apply Finset.sum_congr rfl
      intro z hz
      apply congrArg (fun t : ℝ => (K.chance (projectWorld i w) z : ℝ) * t)
      rw [nativePayoff_eq_pricedReceipt i m price tariff hc w a z hw,
        nativeObservation_project i m w a z hw,
        ih _ _ (nativeStep_aligned i m w a z hw), nativeStep_project i m w a z hw]
      simp only [hnext, hobs]

/-- Literal preservation of actual child source and fresh address allocation. -/
theorem native_child_is_actual {n : ℕ} (i : Fin n) (m : Mechanism)
    (w : NativeWorld n) (a : Act) (z : Noise) (c : ClockedOrganism n)
    (hc : (nativeTransaction i m w a z).bind ClockedRecord.child = some c) :
    ∃ p : ClockedOrganism n,
      RegisterPopulationHistorySource.lookup w.store (request w.stopped a z).parent = some p ∧
      (RegisterFaultJointRecord.modeRecordStep i m p.organism
        (request w.stopped a z).action z.1 z.2).transaction.child = some c.organism ∧
      c.organism.program = p.organism.program ∧
      (request w.stopped a z).parent < w.store.length :=
  RegisterJointDecisionSource.native_child_is_actual i m w a z c hc

theorem native_child_fresh {n : ℕ} (i : Fin n) (m : Mechanism)
    (w : NativeWorld n) (a : Act) (z : Noise) (c : ClockedOrganism n)
    (hc : (nativeTransaction i m w a z).bind ClockedRecord.child = some c) :
    RegisterPopulationHistorySource.childID i m w.store (request w.stopped a z) = some w.store.length ∧
    RegisterPopulationHistorySource.lookup w.store w.store.length = none ∧
    (request w.stopped a z).parent < w.store.length :=
  RegisterJointDecisionSource.native_child_fresh i m w a z c hc

/-- G changes no allocation, failed slot, identity, lineage, program or clock
beyond the original selected transaction. In particular, undispatched clocks do
not advance merely because their physical bits receive common damage. -/
theorem nativeStep_metadata {n : ℕ} (i : Fin n) (m : Mechanism)
    (w : NativeWorld n) (a : Act) (z : Noise) :
    (nativeStep i m w a z).store.map (Option.map (fun p =>
      (p.identity, p.clock, p.organism.history, p.organism.program))) =
    (RegisterJointDecisionSource.nativeStep i m w a z).store.map
      (Option.map (fun p => (p.identity, p.clock, p.organism.history, p.organism.program))) := by
  unfold nativeStep
  split
  · exact damageStore_metadata i m.goal _
  · rfl

/-- Faults never produce newborns in either mechanism; the None allocation is
an actual source fact, even if the dispatched address is absent. -/
theorem native_fault_no_child {n : ℕ} (i : Fin n) (m : Mechanism)
    (w : NativeWorld n) (a : Act) (label : Bool) :
    (nativeTransaction i m w a (false,label)).bind ClockedRecord.child = none := by
  unfold nativeTransaction RegisterJointDecisionSource.nativeTransaction
    RegisterPopulationHistorySource.transaction
  cases hp : RegisterPopulationHistorySource.lookup w.store
    (request w.stopped a (false,label)).parent <;> rfl

/-- A successful newborn in the result Store is the original allocated child.
A common fault cannot alter a newborn because the fault branch has no birth. -/
theorem native_new_slot_is_actual_child {n : ℕ} (i : Fin n) (m : Mechanism)
    (w : NativeWorld n) (a : Act) (z : Noise) :
    RegisterPopulationHistorySource.lookup (nativeStep i m w a z).store w.store.length =
      (nativeTransaction i m w a z).bind ClockedRecord.child := by
  have hnew := RegisterPopulationHistorySource.next_new_slot i m w.store
    (request w.stopped a z)
  rcases z with ⟨mode,label⟩
  cases mode with
  | true =>
      simpa only [nativeStep_normal, RegisterJointDecisionSource.nativeStep] using hnew
  | false =>
      have hnone : RegisterPopulationHistorySource.child i m w.store
          (request w.stopped a (false,label)) = none := native_fault_no_child i m w a label
      by_cases hm : w.theta = .G
      · simp only [nativeStep, hm, and_self, if_true, RegisterJointDecisionSource.nativeStep]
        rw [damageStore_lookup, hnew, hnone]
        exact (native_fault_no_child i m w a label).symm
      · simpa only [nativeStep, hm, false_and, if_false, RegisterJointDecisionSource.nativeStep]
          using hnew

/-- The original S native interpreter is preserved, including complete
records, identities, labels and None entries, for every table and noise tape. -/
theorem nativeExecute_S {n : ℕ} (i : Fin n) (m : Mechanism) :
    ∀ {H : ℕ} (table : Table Act Obs H) (w : NativeWorld n) (z : Fin H → Noise),
      w.theta = .S → nativeExecute i m table w z =
        RegisterJointDecisionExecution.nativeExecute i m table w z := by
  intro H
  induction H with
  | zero => intro table w z hm; cases table; rfl
  | succ H ih =>
      intro table w z hm
      cases table with
      | node a children =>
          simp only [nativeExecute, RegisterJointDecisionExecution.nativeExecute, nativeTransaction]
          rw [nativeStep_S i m w a (z 0) hm]
          rw [ih _ (RegisterJointDecisionSource.nativeStep i m w a (z 0)) _ (by exact hm)]

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionNative
