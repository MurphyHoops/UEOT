import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionNative
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionConsumer
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionNativeConsumer

/-!
# THIS independent-seed return on the original complete Store

The complete returned tables, the uniform private seed, both fixed mechanisms,
and every primitive mode/label tape are the same objects used in the value and
payment theorems. Native prepayment tests the request cap before executing each
transaction and then subtracts that original record's actual fee. No new policy
or world observation is substituted in this bridge.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionNativeConsumer

open scoped BigOperators
open RegisterMechanismDecisionSource RegisterMechanismDecisionConsumer
open RegisterMechanismDecisionNative
open RegisterJointDecisionSource (Act Obs Noise Aligned projectWorld nativeObs nativeFee nativePayoff cap
  initialStore initial_aligned)
open RegisterJointDecisionExecution (Execution eraseExecution actualPayoff packedPayoff receiptBirth receiptFee)
open RegisterJointDecisionConsumer (charge menu menu_nonempty advance mem_menu_prepay)
open RegisterJointDecisionNativeConsumer (tapeVector tapeList)
open RegisterMechanismPurpose (Mechanism)
open FiniteJointDecisionBelief FiniteJointDecisionSolver
open FiniteJointDecisionFilteredModel FiniteJointDecisionSupportedPolicy

noncomputable def nativeMechanism : Mechanism := ⟨true, 1⟩

def nativeFounder (m : FaultMechanism) : NativeWorld 1 :=
  ⟨m, initialStore true false, false⟩

@[simp] theorem founder_project (m : FaultMechanism) :
    projectWorld (0 : Fin 1) (nativeFounder m) = initialWorld true m := rfl

 theorem packed_records_tape :
    ∀ {H : ℕ} (table : Table Act Obs H) (w : World) (noise : Tape Noise H),
      (packedExecute true table w (tapeVector noise)).records =
        tapeList (observedTape (source parameters) table w noise) := by
  intro H
  induction H with
  | zero => intro table w noise; cases table; rfl
  | succ H ih =>
      intro table w noise
      cases table with
      | node a children =>
          rcases noise with ⟨z, rest⟩
          change observe true w a z ::
              (packedExecute true (children (observe true w a z))
                (step true w a z) (tapeVector rest)).records =
            observe true w a z :: tapeList (observedTape (source parameters)
              (children (observe true w a z)) (step true w a z) rest)
          rw [ih]

 theorem native_records_tape {H : ℕ} (table : Table Act Obs H) (w : NativeWorld 1)
    (noise : Tape Noise H) (hw : Aligned true w.store) :
    (nativeExecute 0 nativeMechanism table w (tapeVector noise)).records.map nativeObs =
      tapeList (observedTape (source parameters) table (projectWorld 0 w) noise) := by
  have h := congrArg Execution.records
    (nativeExecute_project 0 nativeMechanism table w (tapeVector noise) hw)
  change (nativeExecute 0 nativeMechanism table w (tapeVector noise)).records.map nativeObs =
    (packedExecute true table (projectWorld 0 w) (tapeVector noise)).records at h
  exact h.trans (packed_records_tape table (projectWorld 0 w) noise)

 theorem packed_payoff_tape :
    ∀ {H : ℕ} (i : Info) (table : Table Act Obs H) (w : World) (noise : Tape Noise H),
      packedPayoff (1/4) 1 (packedExecute true table w (tapeVector noise)).records =
        tapePayoff (model parameters) i table (observedTape (source parameters) table w noise) := by
  intro H
  induction H with
  | zero => intro i table w noise; cases table; rfl
  | succ H ih =>
      intro i table w noise
      cases table with
      | node a children =>
          rcases noise with ⟨z, rest⟩
          let o := observe true w a z
          change receiptBirth o - (1/4) * receiptFee o +
              1 * packedPayoff (1/4) 1
                (packedExecute true (children o) (step true w a z) (tapeVector rest)).records =
            gain parameters a o + 1 * tapePayoff (model parameters)
              ((model parameters).next i a o) (children o)
              (observedTape (source parameters) (children o) (step true w a z) rest)
          rw [ih ((model parameters).next i a o)]
          have hg : receiptBirth o - (1/4) * receiptFee o = gain parameters a o := by
            cases ho : o.2 <;> simp [receiptBirth, receiptFee, gain, charge, parameters, ho]
          rw [hg]

 theorem native_payoff_tape {H : ℕ} (i : Info) (table : Table Act Obs H) (w : NativeWorld 1)
    (noise : Tape Noise H) (hw : Aligned true w.store) :
    actualPayoff (1/4) 1 (nativeExecute 0 nativeMechanism table w (tapeVector noise)).records =
      (tapePayoff (model parameters) i table
        (observedTape (source parameters) table (projectWorld 0 w) noise) : ℝ) := by
  rw [table_payoff_eq 0 nativeMechanism (1/4) 1 1 (by norm_num [nativeMechanism])
    table w (tapeVector noise) hw]
  norm_num only [mul_one]
  exact congrArg (fun q : ℚ => (q : ℝ)) (packed_payoff_tape i table (projectWorld 0 w) noise)

/-- An actual expectation of the complete native records over all 4^H original
mode/label tapes, with the mechanism fixed before the run. -/
noncomputable def nativeJ {H : ℕ} (table : Table Act Obs H) (m : FaultMechanism) : ℝ :=
  ∑ noise : Tape Noise H,
    (sourceTapeWeight (source parameters) table (initialWorld true m) noise : ℝ) *
      actualPayoff (1/4) 1
        (nativeExecute 0 nativeMechanism table (nativeFounder m) (tapeVector noise)).records

 theorem nativeJ_eq_trace {H : ℕ} (i : Info) (table : Table Act Obs H) (m : FaultMechanism) :
    nativeJ table m =
      (sourceTraceExpectation (source parameters) table (tapePayoff (model parameters) i table)
        (initialWorld true m) : ℝ) := by
  rw [sourceTrace_eq_noiseExpectation]
  simp only [nativeJ, Rat.cast_sum, Rat.cast_mul]
  apply Finset.sum_congr rfl
  intro noise hn
  rw [native_payoff_tape i table (nativeFounder m) noise (initial_aligned true false), founder_project]

noncomputable def expectedNativeJ {H : ℕ} (q : Input) (table : Table Act Obs H) : ℝ :=
  ∑ m, (prior q m : ℝ) * nativeJ table m

 theorem expectedNativeJ_eq_value {H : ℕ} (q : Input) (table : Table Act Obs H)
    (ht : Feasible (model parameters) (registeredInfo q) table) :
    expectedNativeJ q table = (value (model parameters) (registeredInfo q) table : ℝ) := by
  calc
    expectedNativeJ q table =
        (expect (registeredInfo q).1 (sourceTraceExpectation (source parameters) table
          (tapePayoff (model parameters) (registeredInfo q) table)) : ℝ) := by
      change (∑ m, (prior q m : ℝ) * nativeJ table m) =
        ((∑ m, prior q m * sourceTraceExpectation (source parameters) table
          (tapePayoff (model parameters) (registeredInfo q) table) (initialWorld true m) : ℚ) : ℝ)
      simp only [Rat.cast_sum, Rat.cast_mul]
      apply Finset.sum_congr rfl
      intro m hm
      rw [nativeJ_eq_trace (registeredInfo q)]
    _ = (traceExpectation (model parameters) (registeredInfo q) table
        (tapePayoff (model parameters) (registeredInfo q) table) : ℝ) := by
      congr 1
      exact (traceExpectation_eq_source (source parameters)
        (fun j => menu parameters.tariff j.2) (fun j => menu_nonempty parameters.tariff j.2)
        (advance parameters.tariff) (gain parameters) parameters.discount
        parameters.discount_bounds.1 H table (registeredInfo q).1 (registeredInfo q).2
        (tapePayoff (model parameters) (registeredInfo q) table)).symm
    _ = (value (model parameters) (registeredInfo q) table : ℝ) := by
      change (tapeExpectation (model parameters) (registeredInfo q) table : ℝ) = _
      exact congrArg (fun q : ℚ => (q : ℝ))
        (tapeExpectation_eq_value (model parameters) H (registeredInfo q) table ht)

/-- Each seed executes the exact returned table, in either actual mechanism. -/
 theorem returned_nativeJ (seed : Fin 4) (m : FaultMechanism) :
    nativeJ (returned seed) m = (tableJ (returned seed) m : ℝ) := by
  cases m with
  | S =>
      have h := expectedNativeJ_eq_value .knownS (returned seed) (returned_feasible seed .knownS)
      rw [RegisterMechanismDecisionSource.value_eq_source] at h
      change (∑ m, (prior .knownS m : ℝ) * nativeJ (returned seed) m) =
        ((∑ m, prior .knownS m * tableJ (returned seed) m : ℚ) : ℝ) at h
      rw [sum_mechanisms, sum_mechanisms] at h
      norm_num [prior] at h
      exact h
  | G =>
      have h := expectedNativeJ_eq_value .knownG (returned seed) (returned_feasible seed .knownG)
      rw [RegisterMechanismDecisionSource.value_eq_source] at h
      change (∑ m, (prior .knownG m : ℝ) * nativeJ (returned seed) m) =
        ((∑ m, prior .knownG m * tableJ (returned seed) m : ℚ) : ℝ) at h
      rw [sum_mechanisms, sum_mechanisms] at h
      norm_num [prior] at h
      exact h

noncomputable def nativeRhoJ (m : FaultMechanism) : ℝ :=
  ∑ seed : Fin 4, (1/4 : ℝ) * nativeJ (returned seed) m

 theorem nativeRhoJ_eq (m : FaultMechanism) : nativeRhoJ m = (rhoJ m : ℝ) := by
  simp only [nativeRhoJ, rhoJ, Rat.cast_sum, Rat.cast_mul, Rat.cast_div,
    Rat.cast_one, Rat.cast_ofNat, returned_nativeJ]

 theorem returned_native_values : nativeRhoJ .S = 161/128 ∧ nativeRhoJ .G = 157/128 := by
  rw [nativeRhoJ_eq, nativeRhoJ_eq, returned_randomized_values.1, returned_randomized_values.2]
  norm_num

 theorem returned_native_regret :
    FiniteMechanismRegretCertificate.worst oracle nativeRhoJ = 3/128 := by
  rw [show nativeRhoJ = fun m => (rhoJ m : ℝ) from funext nativeRhoJ_eq]
  exact returned_worst_regret

 theorem prefixCost_receipts :
    ∀ {H : ℕ} (i : Info) (table : Table Act Obs H) (path : Tape Obs H) (k : ℕ),
      prefixCost (model parameters) (walletContract parameters) i table path k =
        (((tapeList path).map (charge 1)).take k).sum := by
  intro H
  induction H with
  | zero => intro i table path k; cases table; simp [prefixCost, tapeList]
  | succ H ih =>
      intro i table path k
      cases table with
      | node a children =>
          rcases path with ⟨o, rest⟩
          cases k with
          | zero => simp [prefixCost]
          | succ k =>
              change charge 1 o + prefixCost (model parameters) (walletContract parameters)
                  ((model parameters).next i a o) (children o) rest k =
                charge 1 o + (((tapeList rest).map (charge 1)).take k).sum
              rw [ih]

private theorem cast_prefix_sum (f : Obs → ℚ) : ∀ (os : List Obs) (k : ℕ),
    (((os.map (fun o => (f o : ℝ))).take k).sum) = ((((os.map f).take k).sum) : ℝ) := by
  intro os k
  induction k generalizing os with
  | zero => simp
  | succ k ih =>
      cases os with
      | nil => simp
      | cons o os =>
          simpa only [List.map_cons, List.take_succ_cons, List.sum_cons, Rat.cast_add] using
            congrArg (fun v : ℝ => (f o : ℝ) + v) (ih os)

 theorem native_prefix_cost {H : ℕ} (i : Info) (table : Table Act Obs H) (w : NativeWorld 1)
    (noise : Tape Noise H) (hw : Aligned true w.store) (k : ℕ) :
    (((nativeExecute 0 nativeMechanism table w (tapeVector noise)).records.map nativeFee).take k).sum =
      (prefixCost (model parameters) (walletContract parameters) i table
        (observedTape (source parameters) table (projectWorld 0 w) noise) k : ℝ) := by
  rw [native_fees_from_receipts, native_records_tape table w noise hw, prefixCost_receipts]
  have hf : (fun o : Obs => (receiptFee o : ℝ) * nativeMechanism.writeCost) =
      (fun o : Obs => (charge 1 o : ℝ)) := by
    funext o
    cases ho : o.2 <;> simp [receiptFee, charge, nativeMechanism, ho]
  rw [hf]
  exact cast_prefix_sum (charge 1) _ k

/-- The cap test precedes the actual transaction, including every fault and
None branch. The recursion subtracts each original record's literal fee. -/
noncomputable def NativePrepaid :
    {H : ℕ} → ℝ → Table Act Obs H → NativeWorld 1 → Tape Noise H → Prop
  | 0, _, .halt, _, _ => True
  | H+1, budget, .node a children, w, (z, rest) =>
      (cap a : ℝ) ≤ budget ∧
      NativePrepaid (budget - nativeFee (nativeTransaction 0 nativeMechanism w a z))
        (children (nativeObs (nativeTransaction 0 nativeMechanism w a z)))
        (nativeStep 0 nativeMechanism w a z) rest

 theorem native_fee_charge (w : NativeWorld 1) (a : Act) (z : Noise) :
    nativeFee (nativeTransaction 0 nativeMechanism w a z) =
      (charge 1 (observe true (projectWorld 0 w) a z) : ℝ) := by
  rw [nativeFee_project]
  cases ho : (observe true (projectWorld 0 w) a z).2 <;>
    simp [charge, nativeMechanism, ho]

 theorem native_prepaid_of_supported :
    ∀ {H : ℕ} (i : Info) (table : Table Act Obs H) (w : NativeWorld 1)
      (noise : Tape Noise H), Aligned true w.store → Feasible (model parameters) i table →
      0 < tapeWeight (model parameters) i table
        (observedTape (source parameters) table (projectWorld 0 w) noise) →
      NativePrepaid (i.2.val : ℝ) table w noise := by
  intro H
  induction H with
  | zero => intro i table w noise hw ht hs; cases table; trivial
  | succ H ih =>
      intro i table w noise hw ht hs
      cases table with
      | node a children =>
          rcases noise with ⟨z, rest⟩
          let o := observe true (projectWorld 0 w) a z
          have hpos : 0 < (model parameters).prob i a o ∧
              0 < tapeWeight (model parameters) ((model parameters).next i a o) (children o)
                (observedTape (source parameters) (children o)
                  (step true (projectWorld 0 w) a z) rest) := by
            change 0 < (model parameters).prob i a o * _ at hs
            rcases mul_pos_iff.mp hs with hp | hp
            · exact hp
            · exact ((not_lt_of_ge ((model parameters).prob_nonneg i a ht.1 o)) hp.1).elim
          have hbal := (walletContract parameters).balance_next i a ht.1 o hpos.1
          have hbalR : (((model parameters).next i a o).2.val : ℝ) =
              (i.2.val : ℝ) - (charge 1 o : ℝ) := by exact_mod_cast hbal
          change (cap a : ℝ) ≤ (i.2.val : ℝ) ∧ _
          refine ⟨?_, ?_⟩
          · have hc := mem_menu_prepay parameters.tariff i.2 a ht.1
            norm_num [parameters] at hc
            exact_mod_cast hc
          · rw [nativeObservation_project 0 nativeMechanism w a z hw,
              native_fee_charge, ← hbalR]
            apply ih ((model parameters).next i a o) (children o) (nativeStep 0 nativeMechanism w a z)
              rest (nativeStep_aligned 0 nativeMechanism w a z hw) (ht.2 o)
            rw [nativeStep_project 0 nativeMechanism w a z hw]
            exact hpos.2

 theorem returned_observed_support (seed : Fin 4) (m : FaultMechanism) (noise : Tape Noise 3) :
    0 < tapeWeight (model parameters) (registeredInfo .dual) (returned seed)
      (observedTape (source parameters) (returned seed) (initialWorld true m) noise) := by
  apply observedTape_supported (source parameters)
    (fun i => menu parameters.tariff i.2) (fun i => menu_nonempty parameters.tariff i.2)
    (advance parameters.tariff) (gain parameters) parameters.discount parameters.discount_bounds.1
    3 (returned seed) (registeredInfo .dual).1 (registeredInfo .dual).2 m noise
  · change 0 < prior .dual m
    cases m <;> norm_num [prior]
  · rw [source_tape_uniform]
    norm_num

/-- Every seed, both fixed mechanisms, every one of 64 complete primitive
noise tapes, and every prefix use the same cap and literal original-fee wallet. -/
 theorem returned_native_payment (seed : Fin 4) (m : FaultMechanism) (noise : Tape Noise 3) :
    NativePrepaid 2 (returned seed) (nativeFounder m) noise ∧ ∀ k,
      let paid := (((nativeExecute 0 nativeMechanism (returned seed) (nativeFounder m)
        (tapeVector noise)).records.map nativeFee).take k).sum
      let path := observedTape (source parameters) (returned seed) (initialWorld true m) noise
      (((prefixInfo (model parameters) (registeredInfo .dual) (returned seed) path k).2.val : ℝ) =
        2 - paid) ∧ 0 ≤ paid ∧ paid ≤ 2 := by
  refine ⟨?_, ?_⟩
  · exact native_prepaid_of_supported (registeredInfo .dual) (returned seed) (nativeFounder m)
      noise (initial_aligned true false) (returned_feasible seed .dual)
      (returned_observed_support seed m noise)
  · intro k
    dsimp only
    rw [native_prefix_cost (registeredInfo .dual) (returned seed) (nativeFounder m) noise
      (initial_aligned true false) k, founder_project]
    have hk := (returned_actual_prefix_payment seed m noise).2 k
    exact ⟨by exact_mod_cast hk.1, by exact_mod_cast hk.2.1, by exact_mod_cast hk.2.2⟩

noncomputable def nativeRawJ (pi : RawCausalPolicy (model parameters))
    (h : pi.Memory) (m : FaultMechanism) : ℝ :=
  rawNativeCausalValue (source parameters) 0 nativeMechanism (1/4) 1 pi 3 h (nativeFounder m)

 theorem nativeRawJ_eq_actualJ (pi : RawCausalPolicy (model parameters))
    (h : pi.Memory) (m : FaultMechanism) : nativeRawJ pi h m = actualJ pi h m := by
  exact rawNativeCausalValue_eq_packed (source parameters) 0 nativeMechanism rfl rfl
    (1/4) 1 1 (by norm_num [nativeMechanism]) pi 3 h (nativeFounder m) (initial_aligned true false)

/-- The complete real-history comparison bound is now a native-Store bound,
with no hidden mechanism/label passed to the control action kernel. -/
 theorem all_native_regret_lower (pi : RawCausalPolicy (model parameters))
    (h : pi.Memory) (hi : pi.info h = registeredInfo .dual)
    (hl : SupportedAdmissible (model parameters) pi 3 h) :
    (3/128 : ℝ) ≤ FiniteMechanismRegretCertificate.worst oracle (nativeRawJ pi h) := by
  rw [show nativeRawJ pi h = actualJ pi h from funext (nativeRawJ_eq_actualJ pi h)]
  exact all_shared_regret_lower pi h hi hl

/-- Full original identity/record retention accompanies this same return. -/
 theorem returned_native_population (seed : Fin 4) (m : FaultMechanism) (noise : Tape Noise 3) :
    eraseExecution 0 (nativeExecute 0 nativeMechanism (returned seed) (nativeFounder m) (tapeVector noise)) =
      packedExecute true (returned seed) (initialWorld true m) (tapeVector noise) ∧
    (nativeExecute 0 nativeMechanism (returned seed) (nativeFounder m) (tapeVector noise)).records.length = 3 ∧
    (nativeExecute 0 nativeMechanism (returned seed) (nativeFounder m) (tapeVector noise)).history.length = 3 ∧
    (nativeExecute 0 nativeMechanism (returned seed) (nativeFounder m) (tapeVector noise)).finalWorld.store.length = 4 := by
  refine ⟨nativeExecute_project 0 nativeMechanism (returned seed) (nativeFounder m)
    (tapeVector noise) (initial_aligned true false), ?_⟩
  exact nativeExecute_length 0 nativeMechanism (returned seed) (nativeFounder m)
    (tapeVector noise) (initial_aligned true false)

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionNativeConsumer
