import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionNativeLaw
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionConsumer
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionOptimality

/-!
# THIS returned table on the original finite population Store

The original transaction interpreter receives every requested address, including
missing addresses, and retains every complete record.  The scheduler receives
only the registered birth/payment receipt.  The results below join the finite
noise law, its `Fin H` interpreter, actual finite-horizon J, pre-outcome payment,
and supported real randomized competitors.  No payoff or optimality identity is
accepted as an input certificate.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionNativeConsumer

open scoped BigOperators
open RegisterJointDecisionSource RegisterJointDecisionExecution
open RegisterJointDecisionNativeLaw RegisterJointDecisionConsumer
open FiniteJointDecisionBelief FiniteJointDecisionSolver
open FiniteJointDecisionFilteredModel FiniteJointDecisionSupportedPolicy
open RegisterMechanismPurpose (Mechanism)

/-- The native public mechanism has precisely the frozen positive tariff. -/
noncomputable def mechanism {Theta : Type} (P : Family Theta) : Mechanism :=
  ⟨P.goal, ⟨(P.tariff : ℝ), by exact_mod_cast P.tariff_pos.le⟩⟩

@[simp] theorem mechanism_tariff {Theta : Type} (P : Family Theta) :
    ((mechanism P).writeCost : ℝ) = (P.tariff : ℝ) := rfl

@[simp] theorem mechanism_goal {Theta : Type} (P : Family Theta) :
    (mechanism P).goal = P.goal := rfl

/-- A structural conversion, with no reordering, resampling, or dropped tick. -/
def tapeVector {X : Type*} : {H : ℕ} → Tape X H → Fin H → X
  | 0, _, j => Fin.elim0 j
  | H+1, (x, xs), j => Fin.cases x (tapeVector xs) j

def tapeList {X : Type*} : {H : ℕ} → Tape X H → List X
  | 0, _ => []
  | H+1, (x, xs) => x :: tapeList xs

theorem packed_records_tape {Theta : Type} (P : Family Theta) :
    ∀ {H : ℕ} (table : Table Act Obs H) (w : World Theta) (noise : Tape Noise H),
      (packedExecute P.goal table w (tapeVector noise)).records =
        tapeList (observedTape (source P) table w noise) := by
  intro H
  induction H with
  | zero => intro table w noise; cases table; rfl
  | succ H ih =>
      intro table w noise
      cases table with
      | node a children =>
          rcases noise with ⟨z, rest⟩
          change observe P.goal w a z ::
              (packedExecute P.goal (children (observe P.goal w a z))
                (step P.goal w a z) (tapeVector rest)).records =
            observe P.goal w a z ::
              tapeList (observedTape (source P) (children (observe P.goal w a z))
                (step P.goal w a z) rest)
          rw [ih]

/-- The allowed observations from the actual full records are exactly the
observation tape used by the exact filter and by the wallet proof. -/
theorem native_records_tape {Theta : Type} {n : ℕ} (P : Family Theta) (j : Fin n)
    {H : ℕ} (table : Table Act Obs H) (w : NativeWorld Theta n) (noise : Tape Noise H)
    (hw : Aligned P.goal w.store) :
    (nativeExecute j (mechanism P) table w (tapeVector noise)).records.map nativeObs =
      tapeList (observedTape (source P) table (projectWorld j w) noise) := by
  have h := congrArg Execution.records
    (nativeExecute_project j (mechanism P) table w (tapeVector noise) hw)
  change (nativeExecute j (mechanism P) table w (tapeVector noise)).records.map nativeObs =
    (packedExecute P.goal table (projectWorld j w) (tapeVector noise)).records at h
  exact h.trans (packed_records_tape P table (projectWorld j w) noise)

theorem packed_payoff_tape {Theta : Type} (P : Family Theta) :
    ∀ {H : ℕ} (i : Info Theta) (table : Table Act Obs H) (w : World Theta)
      (noise : Tape Noise H),
      packedPayoff (P.price * P.tariff) P.discount
        (packedExecute P.goal table w (tapeVector noise)).records =
      tapePayoff (model P) i table (observedTape (source P) table w noise) := by
  intro H
  induction H with
  | zero => intro i table w noise; cases table; rfl
  | succ H ih =>
      intro i table w noise
      cases table with
      | node a children =>
          rcases noise with ⟨z, rest⟩
          let o := observe P.goal w a z
          change receiptBirth o - (P.price * P.tariff) * receiptFee o +
              P.discount * packedPayoff (P.price * P.tariff) P.discount
                (packedExecute P.goal (children o) (step P.goal w a z) (tapeVector rest)).records =
            gain P a o + P.discount * tapePayoff (model P)
              ((model P).next i a o) (children o)
              (observedTape (source P) (children o) (step P.goal w a z) rest)
          rw [ih ((model P).next i a o)]
          have hg : receiptBirth o - (P.price * P.tariff) * receiptFee o = gain P a o := by
            cases ho : o.2 <;> simp [receiptBirth, receiptFee, gain, charge, ho]
          rw [hg]

/-- Literal original-record J equals the payoff of the same table on its
allowed observation tape, path by path.  The terminal payoff is zero. -/
theorem native_payoff_tape {Theta : Type} {n : ℕ} (P : Family Theta) (j : Fin n)
    {H : ℕ} (i : Info Theta) (table : Table Act Obs H) (w : NativeWorld Theta n)
    (noise : Tape Noise H) (hw : Aligned P.goal w.store) :
    actualPayoff P.price P.discount
      (nativeExecute j (mechanism P) table w (tapeVector noise)).records =
      (tapePayoff (model P) i table
        (observedTape (source P) table (projectWorld j w) noise) : ℝ) := by
  rw [table_payoff_eq j (mechanism P) P.price P.tariff P.discount rfl
    table w (tapeVector noise) hw, mechanism_goal,
    packed_payoff_tape P i table (projectWorld j w) noise]

/-- The noise law is the registered persistent-theta source, already identified
with the original mode PMF times the fair birth-label PMF in NativeLaw. -/
noncomputable def nativeJ {Theta : Type} {n : ℕ} (P : Family Theta) (j : Fin n)
    {H : ℕ} (table : Table Act Obs H) (w : NativeWorld Theta n) : ℝ :=
  ∑ noise : Tape Noise H,
    (sourceTapeWeight (source P) table (projectWorld j w) noise : ℝ) *
      actualPayoff P.price P.discount
        (nativeExecute j (mechanism P) table w (tapeVector noise)).records

theorem nativeJ_eq_trace {Theta : Type} {n : ℕ} (P : Family Theta) (j : Fin n)
    {H : ℕ} (i : Info Theta) (table : Table Act Obs H) (w : NativeWorld Theta n)
    (hw : Aligned P.goal w.store) :
    nativeJ P j table w =
      (sourceTraceExpectation (source P) table (tapePayoff (model P) i table)
        (projectWorld j w) : ℝ) := by
  rw [sourceTrace_eq_noiseExpectation]
  simp only [nativeJ, Rat.cast_sum, Rat.cast_mul]
  apply Finset.sum_congr rfl
  intro noise hn
  rw [native_payoff_tape P j i table w noise hw]

/-- A world-side realization supplies the literal original Store for each
finite prior atom.  It is not an observation or an argument to `returned`.
Only program alignment and the already defined physical projection are required. -/
structure Realization {Theta : Type} {n : ℕ} (P : Family Theta) (j : Fin n)
    (b : Belief (World Theta)) where
  world : b.Atom → NativeWorld Theta n
  aligned : ∀ x, Aligned P.goal (world x).store
  projects : ∀ x, projectWorld j (world x) = b.state x

noncomputable def expectedNativeJ {Theta : Type} {n : ℕ} (P : Family Theta) (j : Fin n)
    {H : ℕ} (i : Info Theta) (R : Realization P j i.1) (table : Table Act Obs H) : ℝ :=
  ∑ x, (i.1.weight x : ℝ) * nativeJ P j table (R.world x)

/-- The entire finite population experiment, including actual failed records,
has exactly the value of this particular feasible table. -/
theorem expectedNativeJ_eq_value {Theta : Type} {n : ℕ} (P : Family Theta) (j : Fin n)
    {H : ℕ} (i : Info Theta) (R : Realization P j i.1) (table : Table Act Obs H)
    (ht : Feasible (model P) i table) :
    expectedNativeJ P j i R table = (value (model P) i table : ℝ) := by
  calc
    expectedNativeJ P j i R table =
        (expect i.1 (sourceTraceExpectation (source P) table
          (tapePayoff (model P) i table)) : ℝ) := by
      simp only [expectedNativeJ, expect, Rat.cast_sum, Rat.cast_mul]
      apply Finset.sum_congr rfl
      intro x hx
      rw [nativeJ_eq_trace P j i table (R.world x) (R.aligned x), R.projects x]
    _ = (traceExpectation (model P) i table (tapePayoff (model P) i table) : ℝ) := by
      congr 1
      exact (traceExpectation_eq_source (source P) (fun q => menu P.tariff q.2)
        (fun q => menu_nonempty P.tariff q.2) (advance P.tariff) (gain P)
        P.discount P.discount_bounds.1 H table i.1 i.2 (tapePayoff (model P) i table)).symm
    _ = (value (model P) i table : ℝ) := by
      change (tapeExpectation (model P) i table : ℝ) = _
      exact congrArg (fun q : ℚ => (q : ℝ)) (tapeExpectation_eq_value (model P) H i table ht)

/-- The return object itself, rather than an existential optimizing substitute,
is executed on the original Store and attains its reported optimal value. -/
theorem returned_native_value {Theta : Type} {n : ℕ} (P : Family Theta) (j : Fin n)
    (H : ℕ) (i : Info Theta) (R : Realization P j i.1) :
    expectedNativeJ P j i R (returned P H i) = (optimalValue (model P) H i : ℝ) :=
  expectedNativeJ_eq_value P j i R (returned P H i) (returned_feasible P H i)

theorem prefixCost_receipts {Theta : Type} (P : Family Theta) :
    ∀ {H : ℕ} (i : Info Theta) (table : Table Act Obs H) (path : Tape Obs H) (k : ℕ),
      prefixCost (model P) (walletContract P) i table path k =
        (((tapeList path).map (charge P.tariff)).take k).sum := by
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
              change charge P.tariff o +
                  prefixCost (model P) (walletContract P) ((model P).next i a o) (children o) rest k =
                charge P.tariff o + (((tapeList rest).map (charge P.tariff)).take k).sum
              rw [ih]

private theorem cast_prefix_sum (f : Obs → ℚ) : ∀ (os : List Obs) (k : ℕ),
    (((os.map (fun o => (f o : ℝ))).take k).sum) =
      ((((os.map f).take k).sum) : ℝ) := by
  intro os k
  induction k generalizing os with
  | zero => simp
  | succ k ih =>
      cases os with
      | nil => simp
      | cons o os =>
          simpa only [List.map_cons, List.take_succ_cons, List.sum_cons, Rat.cast_add] using
            (congrArg (fun v : ℝ => (f o : ℝ) + v) (ih os))

/-- Every original transaction fee, including unsuccessful paid writes, equals
the corresponding increment of the exact filtered-model wallet ledger. -/
theorem native_prefix_cost {Theta : Type} {n : ℕ} (P : Family Theta) (j : Fin n)
    {H : ℕ} (i : Info Theta) (table : Table Act Obs H) (w : NativeWorld Theta n)
    (noise : Tape Noise H) (hw : Aligned P.goal w.store) (k : ℕ) :
    (((nativeExecute j (mechanism P) table w (tapeVector noise)).records.map nativeFee).take k).sum =
      (prefixCost (model P) (walletContract P) i table
        (observedTape (source P) table (projectWorld j w) noise) k : ℝ) := by
  rw [native_fees_from_receipts, native_records_tape P j table w noise hw, prefixCost_receipts]
  have hf : (fun o : Obs => (receiptFee o : ℝ) * (mechanism P).writeCost) =
      (fun o : Obs => (charge P.tariff o : ℝ)) := by
    funext o
    cases ho : o.2 <;> simp [receiptFee, charge, ho]
  rw [hf]
  exact cast_prefix_sum (charge P.tariff) _ k

/-- Prepayment in the actual original interpreter: the request cap is checked
before the transaction.  The next balance subtracts its literal actual fee. -/
noncomputable def NativePrepaid {Theta : Type} {n : ℕ} (P : Family Theta) (j : Fin n) :
    {H : ℕ} → ℝ → Table Act Obs H → NativeWorld Theta n → Tape Noise H → Prop
  | 0, _, .halt, _, _ => True
  | H+1, budget, .node a children, w, (z, rest) =>
      ((P.tariff * cap a : ℚ) : ℝ) ≤ budget ∧
      NativePrepaid P j (budget - nativeFee (nativeTransaction j (mechanism P) w a z))
        (children (nativeObs (nativeTransaction j (mechanism P) w a z)))
        (nativeStep j (mechanism P) w a z) rest

theorem native_fee_charge {Theta : Type} {n : ℕ} (P : Family Theta) (j : Fin n)
    (w : NativeWorld Theta n) (a : Act) (z : Noise) (_hw : Aligned P.goal w.store) :
    nativeFee (nativeTransaction j (mechanism P) w a z) =
      (charge P.tariff (observe P.goal (projectWorld j w) a z) : ℝ) := by
  rw [nativeFee_project j (mechanism P) w a z]
  cases ho : (observe P.goal (projectWorld j w) a z).2 <;>
    simp [feeUnit, charge, ho]

theorem native_prepaid_of_supported {Theta : Type} {n : ℕ} (P : Family Theta) (j : Fin n) :
    ∀ {H : ℕ} (i : Info Theta) (table : Table Act Obs H) (w : NativeWorld Theta n)
      (noise : Tape Noise H), Aligned P.goal w.store → Feasible (model P) i table →
      0 < tapeWeight (model P) i table (observedTape (source P) table (projectWorld j w) noise) →
      NativePrepaid P j (i.2.val : ℝ) table w noise := by
  intro H
  induction H with
  | zero => intro i table w noise hw ht hs; cases table; trivial
  | succ H ih =>
      intro i table w noise hw ht hs
      cases table with
      | node a children =>
          rcases noise with ⟨z, rest⟩
          let o := observe P.goal (projectWorld j w) a z
          have hpos : 0 < (model P).prob i a o ∧
              0 < tapeWeight (model P) ((model P).next i a o) (children o)
                (observedTape (source P) (children o) (step P.goal (projectWorld j w) a z) rest) := by
            change 0 < (model P).prob i a o * _ at hs
            rcases mul_pos_iff.mp hs with hp | hp
            · exact hp
            · exact ((not_lt_of_ge ((model P).prob_nonneg i a ht.1 o)) hp.1).elim
          have hbal := (walletContract P).balance_next i a ht.1 o hpos.1
          have hbalR : (((model P).next i a o).2.val : ℝ) =
              (i.2.val : ℝ) - (charge P.tariff o : ℝ) := by exact_mod_cast hbal
          change ((P.tariff * cap a : ℚ) : ℝ) ≤ (i.2.val : ℝ) ∧ _
          refine ⟨by exact_mod_cast mem_menu_prepay P.tariff i.2 a ht.1, ?_⟩
          rw [nativeObservation_project j (mechanism P) w a z hw,
            native_fee_charge P j w a z hw, ← hbalR]
          apply ih ((model P).next i a o) (children o) (nativeStep j (mechanism P) w a z) rest
            (nativeStep_aligned j (mechanism P) w a z hw) (ht.2 o)
          rw [nativeStep_project j (mechanism P) w a z hw]
          exact hpos.2

/-- Every supported actual initial atom and full primitive tape satisfies
native pre-outcome payment and a literal original-fee ledger at every prefix. -/
theorem returned_native_payment {Theta : Type} {n : ℕ} (P : Family Theta) (j : Fin n)
    (H : ℕ) (i : Info Theta) (R : Realization P j i.1) (x : i.1.Atom)
    (noise : Tape Noise H) (hx : 0 < i.1.weight x)
    (hn : 0 < sourceTapeWeight (source P) (returned P H i) (i.1.state x) noise) :
    NativePrepaid P j (i.2.val : ℝ) (returned P H i) (R.world x) noise ∧
      ∀ k, let paid := (((nativeExecute j (mechanism P) (returned P H i) (R.world x)
          (tapeVector noise)).records.map nativeFee).take k).sum
        let path := observedTape (source P) (returned P H i) (i.1.state x) noise
        (((prefixInfo (model P) i (returned P H i) path k).2.val : ℝ) = (i.2.val : ℝ) - paid) ∧
          0 ≤ paid ∧ paid ≤ (i.2.val : ℝ) := by
  have hs := observedTape_supported (source P) (fun q => menu P.tariff q.2)
    (fun q => menu_nonempty P.tariff q.2) (advance P.tariff) (gain P)
    P.discount P.discount_bounds.1 H (returned P H i) i.1 i.2 x noise hx hn
  refine ⟨?_, ?_⟩
  · apply native_prepaid_of_supported P j i (returned P H i) (R.world x) noise
      (R.aligned x) (returned_feasible P H i)
    rw [R.projects x]
    exact hs
  · intro k
    dsimp only
    rw [native_prefix_cost P j i (returned P H i) (R.world x) noise (R.aligned x) k,
      R.projects x]
    have hk := (returned_actual_prefix_payment P H i x noise hx hn).2 k
    exact ⟨by exact_mod_cast hk.1, by exact_mod_cast hk.2.1, by exact_mod_cast hk.2.2⟩

noncomputable def expectedRawNativeJ {Theta : Type} {n : ℕ} (P : Family Theta) (j : Fin n)
    (pi : RawCausalPolicy (model P)) (H : ℕ) (h : pi.Memory)
    (R : Realization P j (pi.info h).1) : ℝ :=
  ∑ x, ((pi.info h).1.weight x : ℝ) *
    rawNativeCausalValue (source P) j (mechanism P) P.price P.discount pi H h (R.world x)

theorem expectedRawNativeJ_eq_source {Theta : Type} {n : ℕ} (P : Family Theta) (j : Fin n)
    (pi : RawCausalPolicy (model P)) (H : ℕ) (h : pi.Memory)
    (R : Realization P j (pi.info h).1) :
    expectedRawNativeJ P j pi H h R =
      expectReal (pi.info h).1 (rawSourceValue (source P) (gain P) P.discount pi H h) := by
  unfold expectedRawNativeJ expectReal
  apply Finset.sum_congr rfl
  intro x hx
  rw [rawNativeCausalValue_eq_packed (source P) j (mechanism P) rfl rfl
    P.price P.tariff P.discount rfl pi H h (R.world x) (R.aligned x), R.projects x]
  rfl

/-- ALL real causal policies using the same permitted history and satisfying
the same prepaid menu on positive-probability prefixes are bounded by the
actual original-Store J of THIS returned table.  No conditions are imposed on
their impossible observation branches. -/
theorem returned_native_optimal {Theta : Type} {n : ℕ} (P : Family Theta) (j : Fin n)
    (pi : RawCausalPolicy (model P)) (H : ℕ) (h : pi.Memory)
    (R : Realization P j (pi.info h).1)
    (hh : SupportedAdmissible (model P) pi H h) :
    expectedRawNativeJ P j pi H h R ≤
      expectedNativeJ P j (pi.info h) R (returned P H (pi.info h)) := by
  rw [expectedRawNativeJ_eq_source, returned_native_value]
  calc
    _ = rawValue (model P) pi H h :=
      rawSourceValue_eq_model (source P) (fun q => menu P.tariff q.2)
        (fun q => menu_nonempty P.tariff q.2) (advance P.tariff) (gain P)
        P.discount P.discount_bounds.1 pi H h
    _ ≤ _ := rawValue_le_solve (model P) pi H h hh

/-- The concrete once-drawn source starts at the original allocated founder,
with its original identity/history/clock; only its physical register is damaged. -/
def nativeInitial {Theta : Type} (P : Family Theta) (theta : Theta) : NativeWorld Theta 1 :=
  ⟨theta, initialStore P.goal (!P.goal), false⟩

def initialRealization {Theta : Type} [Fintype Theta] (P : Family Theta)
    (prior : Theta → ℚ) (hn : ∀ t, 0 ≤ prior t) (ht : ∑ t, prior t = 1) :
    Realization P (0 : Fin 1) (initialBelief P prior hn ht) where
  world := nativeInitial P
  aligned := fun _ => initial_aligned P.goal (!P.goal)
  projects := by
    intro theta
    change World.mk theta (project (0 : Fin 1) (initialStore P.goal (!P.goal))) false =
      World.mk theta [some (!P.goal)] false
    rw [initial_project]

/-- Concrete prior initialization, with theta drawn only once, consumes the
realization rather than leaving it as an uninstantiated physical bridge. -/
theorem initial_returned_native_value {Theta : Type} [Fintype Theta] (P : Family Theta)
    (prior : Theta → ℚ) (hn : ∀ t, 0 ≤ prior t) (ht : ∑ t, prior t = 1)
    (wallet : Wallet) (H : ℕ) :
    let i : Info Theta := (initialBelief P prior hn ht, wallet)
    (∑ theta, (prior theta : ℝ) *
      nativeJ P (0 : Fin 1) (returned P H i) (nativeInitial P theta)) =
        (optimalValue (model P) H i : ℝ) := by
  exact returned_native_value P (0 : Fin 1) H (initialBelief P prior hn ht, wallet)
    (initialRealization P prior hn ht)

/-- The nontrivial all-horizon source boundary is the payoff of the actual
returned policy executed on the original Store with the one-tariff wallet. -/
theorem initial_returned_native_boundary {Theta : Type} [Fintype Theta] (P : Family Theta)
    (prior : Theta → ℚ) (hn : ∀ t, 0 ≤ prior t) (ht : ∑ t, prior t = 1)
    (H : ℕ)
    (hp : RegisterJointDecisionValueBounds.geometric P.discount H ≤ P.price * P.tariff) :
    let i := RegisterJointDecisionOptimality.initialInfo P prior hn ht
    (∑ theta, (prior theta : ℝ) *
      nativeJ P (0 : Fin 1) (returned P (H+1) i) (nativeInitial P theta)) =
        ((max 0 (RegisterJointDecisionOptimality.priorRepairScore P prior H) : ℚ) : ℝ) := by
  dsimp only [RegisterJointDecisionOptimality.initialInfo]
  rw [initial_returned_native_value P prior hn ht ⟨P.tariff, P.tariff_pos.le⟩ (H+1)]
  exact congrArg (fun q : ℚ => (q : ℝ))
    (RegisterJointDecisionOptimality.optimal_initial_value P prior hn ht H hp)

/-- Full native Store execution is retained: one record, one request/receipt
pair and one allocated Store slot per frozen tick, also after stopping. -/
theorem returned_native_population {Theta : Type} {n : ℕ} (P : Family Theta) (j : Fin n)
    (H : ℕ) (i : Info Theta) (R : Realization P j i.1) (x : i.1.Atom) (noise : Tape Noise H) :
    eraseExecution j (nativeExecute j (mechanism P) (returned P H i) (R.world x) (tapeVector noise)) =
      packedExecute P.goal (returned P H i) (i.1.state x) (tapeVector noise) ∧
    (nativeExecute j (mechanism P) (returned P H i) (R.world x) (tapeVector noise)).records.length = H ∧
    (nativeExecute j (mechanism P) (returned P H i) (R.world x) (tapeVector noise)).history.length = H ∧
    (nativeExecute j (mechanism P) (returned P H i) (R.world x) (tapeVector noise)).finalWorld.store.length =
      (R.world x).store.length + H := by
  refine ⟨?_, nativeExecute_length j (mechanism P) (returned P H i) (R.world x)
    (tapeVector noise) (R.aligned x)⟩
  rw [nativeExecute_project j (mechanism P) (returned P H i) (R.world x)
    (tapeVector noise) (R.aligned x), mechanism_goal, R.projects x]

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionNativeConsumer
