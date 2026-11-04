import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionFreeTail
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionExpectedBounds

/-!
# Exact Bayes decision boundary for the actual one-write-wallet population

For H+1 protocol decisions, a single initial write tariff in the wallet, and
price-times-tariff at least the H-step birth ceiling, the entire optimal value
has an explicit parameter formula.  The source parameter is drawn once.  The
root action cannot depend on it; after success a receipt-only free scheduler
attains the world-side continuation upper bound for every parameter at once.

The proof compares EVERY feasible table, then inherits the generic actual-source
upper bound for all real randomized full-history policies.  It is not merely
the value of one repair example or a policy-class inclusion inequality.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionOptimality

open scoped BigOperators
open RegisterJointDecisionSource RegisterJointDecisionConsumer
open RegisterJointDecisionValueBounds RegisterJointDecisionExpectedBounds
open RegisterJointDecisionFreeTail
open FiniteJointDecisionBelief FiniteJointDecisionSolver FiniteJointDecisionFilteredModel

def initialWorld {Theta : Type} (P : Family Theta) (theta : Theta) : World Theta :=
  ⟨theta, [some (!P.goal)], false⟩

def successfulWorld {Theta : Type} (P : Family Theta) (theta : Theta) : World Theta :=
  ⟨theta, [some P.goal, some P.goal], false⟩

def failedWorld {Theta : Type} (P : Family Theta) (theta : Theta) : World Theta :=
  ⟨theta, [some (!P.goal), none], false⟩

def correctAction (goal : Bool) : Act := some (false, some goal)

def initialInfo {Theta : Type} [Fintype Theta] (P : Family Theta)
    (prior : Theta → ℚ) (hn : ∀ t, 0 ≤ prior t) (ht : ∑ t, prior t = 1) : Info Theta :=
  (initialBelief P prior hn ht, ⟨P.tariff, P.tariff_pos.le⟩)

def repairScore {Theta : Type} (P : Family Theta) (H : ℕ) (theta : Theta) : ℚ :=
  P.normal theta * (1 - P.price * P.tariff +
    P.discount * twoBound (P.normal theta) P.discount H)

def priorRepairScore {Theta : Type} [Fintype Theta] (P : Family Theta)
    (prior : Theta → ℚ) (H : ℕ) : ℚ := ∑ theta, prior theta * repairScore P H theta

/-- Successful repair creates the real root and child; failures retain their
actual failure slot and may leave the write wallet unspent. -/
theorem initial_correct_normal {Theta : Type} (P : Family Theta) (theta : Theta) (label : Bool) :
    observe P.goal (initialWorld P theta) (correctAction P.goal) (true, label) = (true, true) ∧
      step P.goal (initialWorld P theta) (correctAction P.goal) (true, label) = successfulWorld P theta := by
  cases hg : P.goal <;>
    simp [initialWorld, successfulWorld, correctAction, observe, step, effective, address,
      packedObserve, packedNext, packedLookup, postBit, childBit, hg]

theorem initial_correct_fault {Theta : Type} (P : Family Theta) (theta : Theta) (label : Bool) :
    observe P.goal (initialWorld P theta) (correctAction P.goal) (false, label) = (false, false) ∧
      step P.goal (initialWorld P theta) (correctAction P.goal) (false, label) = failedWorld P theta := by
  cases hg : P.goal <;>
    simp [initialWorld, failedWorld, correctAction, observe, step, effective, address,
      packedObserve, packedNext, packedLookup, postBit, childBit, hg]

theorem successful_health {Theta : Type} (P : Family Theta) (theta : Theta) :
    health P.goal (successfulWorld P theta).store = (true, true) := by
  simp [health, successfulWorld, packedLookup]

theorem failed_damaged {Theta : Type} (P : Family Theta) (theta : Theta) :
    AllDamaged P.goal (failedWorld P theta).store := by
  cases hg : P.goal <;> simp [AllDamaged, failedWorld, hg]

/-- Any different first request has no birth and leaves a damaged population.
This includes genuine invalid child-address requests and paid wrong writes. -/
theorem initial_other_step {Theta : Type} (P : Family Theta) (theta : Theta)
    (a : Act) (ha : a ≠ correctAction P.goal) (z : Noise) :
    birthUnit P.goal (initialWorld P theta) a z = 0 ∧
      AllDamaged P.goal (step P.goal (initialWorld P theta) a z).store := by
  rcases z with ⟨mode, label⟩
  cases a with
  | none =>
      cases hg : P.goal <;> cases mode <;>
        simp [initialWorld, correctAction, birthUnit, observe, step, effective, address,
          packedObserve, packedNext, packedLookup, postBit, childBit, AllDamaged, hg]
  | some q =>
      rcases q with ⟨j, act⟩
      cases j <;> cases act with
      | none =>
          cases hg : P.goal <;> cases mode <;>
            simp [initialWorld, correctAction, birthUnit, observe, step, effective, address,
              packedObserve, packedNext, packedLookup, postBit, childBit, AllDamaged, hg]
      | some bit =>
          cases bit <;> cases hg : P.goal <;> cases mode <;>
            simp_all [initialWorld, correctAction, birthUnit, observe, step, effective, address,
              packedObserve, packedNext, packedLookup, postBit, childBit, AllDamaged]

theorem initial_other_nonpos {Theta : Type} (P : Family Theta) (H : ℕ)
    (a : Act) (children : Obs → Table Act Obs H) (theta : Theta)
    (ha : a ≠ correctAction P.goal) (hp : geometric P.discount H ≤ P.price * P.tariff) :
    sourceValue (source P) (gain P) P.discount (.node a children) (initialWorld P theta) ≤ 0 := by
  apply Finset.sum_nonpos
  intro z hz
  apply mul_nonpos_of_nonneg_of_nonpos
    (primitiveWeight_nonneg P.normal P.normal_bounds (initialWorld P theta) z)
  obtain ⟨hb, hw⟩ := initial_other_step P theta a ha z
  have htail := source_allDamaged_nonpos P
    (children (observe P.goal (initialWorld P theta) a z))
    (step P.goal (initialWorld P theta) a z) hw hp
  have hgain : gain P a (observe P.goal (initialWorld P theta) a z) ≤ 0 := by
    rw [gain_eq_receipt,
      show RegisterJointDecisionExecution.receiptBirth
        (observe P.goal (initialWorld P theta) a z) = 0 from hb]
    have hc := mul_nonneg (mul_nonneg P.price_nonneg P.tariff_pos.le)
      (receiptFee_nonneg (observe P.goal (initialWorld P theta) a z))
    linarith
  exact add_nonpos hgain (mul_nonpos_of_nonneg_of_nonpos P.discount_bounds.1 htail)

/-- Upper bound on ANY first-repair continuation with its exhausted wallet.
The failure branch is retained and is bounded by the actual high-price no-go. -/
theorem initial_repair_upper {Theta : Type} (P : Family Theta) (H : ℕ)
    (children : Obs → Table Act Obs H) (theta : Theta)
    (hf : Free (children (true, true)))
    (hp : geometric P.discount H ≤ P.price * P.tariff) :
    sourceValue (source P) (gain P) P.discount
      (.node (correctAction P.goal) children) (initialWorld P theta) ≤ repairScore P H theta := by
  have hs := free_table_upper P H (children (true, true)) (successfulWorld P theta) hf
    (by simp [successfulWorld])
  rw [successful_health] at hs
  change sourceValue (source P) (gain P) P.discount (children (true, true))
    (successfulWorld P theta) ≤ twoBound (P.normal theta) P.discount H at hs
  have hfault := source_allDamaged_nonpos P (children (false, false))
    (failedWorld P theta) (failed_damaged P theta) hp
  have hnormal := initial_correct_normal P theta false
  have hfailed := initial_correct_fault P theta false
  rw [sourceValue_modes, hnormal.1, hnormal.2, hfailed.1, hfailed.2]
  simp only [gain, charge, ite_true, Bool.false_eq_true, ite_false,
    mul_zero, sub_zero, zero_add]
  have hsuccess := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hs P.discount_bounds.1) (P.normal_bounds theta).1
  have hfailure := mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (sub_nonneg.mpr (P.normal_bounds theta).2) P.discount_bounds.1) hfault
  dsimp only [initialWorld, repairScore]
  nlinarith

/-- A concrete attaining policy: repair root0 now, then use receipt-only free
dispatch after success, or stop paid intervention after a failed first tick. -/
def repairThenFree (goal : Bool) (H : ℕ) : Table Act Obs (H + 1) :=
  .node (correctAction goal) (fun o => if o.1 then freeSchedule H (true, true) else stopTable H)

theorem repairThenFree_source {Theta : Type} (P : Family Theta) (H : ℕ) (theta : Theta) :
    sourceValue (source P) (gain P) P.discount (repairThenFree P.goal H) (initialWorld P theta) =
      repairScore P H theta := by
  have hs := freeSchedule_attains P H (successfulWorld P theta) rfl (by simp [successfulWorld])
  rw [successful_health] at hs
  change sourceValue (source P) (gain P) P.discount (freeSchedule H (true, true))
    (successfulWorld P theta) = twoBound (P.normal theta) P.discount H at hs
  have hf := source_stop_zero P H (failedWorld P theta) (failed_damaged P theta)
  have hnormal := initial_correct_normal P theta false
  have hfailed := initial_correct_fault P theta false
  unfold repairThenFree
  rw [sourceValue_modes, hnormal.1, hnormal.2, hfailed.1, hfailed.2]
  dsimp only
  simp only [ite_true, Bool.false_eq_true, ite_false]
  rw [hs, hf]
  simp [gain, charge, repairScore, initialWorld]

theorem stopTable_feasible {Theta : Type} (P : Family Theta) :
    ∀ (H : ℕ) (i : Info Theta), Feasible (model P) i (stopTable H) := by
  intro H
  induction H with
  | zero => intros; trivial
  | succ H ih => intro i; exact ⟨stop_mem_menu P.tariff i.2, fun o => ih _⟩

theorem repairThenFree_feasible {Theta : Type} [Fintype Theta] (P : Family Theta)
    (prior : Theta → ℚ) (hn : ∀ t, 0 ≤ prior t) (ht : ∑ t, prior t = 1) (H : ℕ) :
    Feasible (model P) (initialInfo P prior hn ht) (repairThenFree P.goal H) := by
  refine ⟨?_, ?_⟩
  · change correctAction P.goal ∈ menu P.tariff ⟨P.tariff, P.tariff_pos.le⟩
    cases hg : P.goal <;> simp [menu, allActions, correctAction, cap, effective, hg]
  · intro o
    dsimp only
    split
    · exact freeSchedule_feasible P H (true, true) _
    · exact stopTable_feasible P H _

theorem consumer_value_eq_source {Theta : Type} (P : Family Theta) {H : ℕ}
    (i : Info Theta) (table : Table Act Obs H) :
    value (model P) i table = expect i.1 (sourceValue (source P) (gain P) P.discount table) :=
  value_eq_source (source P) (fun i => menu P.tariff i.2)
    (fun i => menu_nonempty P.tariff i.2) (advance P.tariff) (gain P)
    P.discount P.discount_bounds.1 H table i.1 i.2

/-- Averaging occurs only after the full fixed-theta source execution. -/
theorem initial_repair_value {Theta : Type} [Fintype Theta] (P : Family Theta)
    (prior : Theta → ℚ) (hn : ∀ t, 0 ≤ prior t) (ht : ∑ t, prior t = 1) (H : ℕ) :
    value (model P) (initialInfo P prior hn ht) (repairThenFree P.goal H) =
      priorRepairScore P prior H := by
  rw [consumer_value_eq_source]
  change (∑ theta, prior theta * sourceValue (source P) (gain P) P.discount
    (repairThenFree P.goal H) (initialWorld P theta)) = _
  simp_rw [repairThenFree_source]
  rfl

theorem initial_stop_value {Theta : Type} [Fintype Theta] (P : Family Theta)
    (prior : Theta → ℚ) (hn : ∀ t, 0 ≤ prior t) (ht : ∑ t, prior t = 1) (H : ℕ) :
    value (model P) (initialInfo P prior hn ht) (stopTable H) = 0 := by
  rw [consumer_value_eq_source]
  change (∑ theta, prior theta * sourceValue (source P) (gain P) P.discount
    (stopTable H) (initialWorld P theta)) = 0
  apply Finset.sum_eq_zero
  intro theta htheta
  rw [source_stop_zero P H (initialWorld P theta) (allDamaged_initial P.goal), mul_zero]

theorem initial_table_upper {Theta : Type} [Fintype Theta] (P : Family Theta)
    (prior : Theta → ℚ) (hn : ∀ t, 0 ≤ prior t) (ht : ∑ t, prior t = 1)
    (H : ℕ) (table : Table Act Obs (H + 1))
    (hf : Feasible (model P) (initialInfo P prior hn ht) table)
    (hp : geometric P.discount H ≤ P.price * P.tariff) :
    value (model P) (initialInfo P prior hn ht) table ≤ max 0 (priorRepairScore P prior H) := by
  cases table with
  | node a children =>
      by_cases ha : a = correctAction P.goal
      · subst a
        have hz : (((model P).next (initialInfo P prior hn ht)
            (correctAction P.goal) (true, true)).2).val = 0 := by
          simp [model, filteredModel, initialInfo, advance, charge]
        have hfree := feasible_zero_wallet_free P H
          ((model P).next (initialInfo P prior hn ht) (correctAction P.goal) (true, true))
          (children (true, true)) hz (hf.2 (true, true))
        rw [consumer_value_eq_source]
        change (∑ theta, prior theta * sourceValue (source P) (gain P) P.discount
          (.node (correctAction P.goal) children) (initialWorld P theta)) ≤ _
        calc
          _ ≤ priorRepairScore P prior H := by
            apply Finset.sum_le_sum
            intro theta htheta
            exact mul_le_mul_of_nonneg_left (initial_repair_upper P H children theta hfree hp) (hn theta)
          _ ≤ max 0 (priorRepairScore P prior H) := le_max_right _ _
      · rw [consumer_value_eq_source]
        change (∑ theta, prior theta * sourceValue (source P) (gain P) P.discount
          (.node a children) (initialWorld P theta)) ≤ _
        calc
          _ ≤ 0 := Finset.sum_nonpos fun theta _ =>
            mul_nonpos_of_nonneg_of_nonpos (hn theta) (initial_other_nonpos P H a children theta ha hp)
          _ ≤ max 0 (priorRepairScore P prior H) := le_max_left _ _

/-- Main source-specific parameter theorem.  This is the exact value of the
actual returned optimum over the entire permitted finite process. -/
theorem optimal_initial_value {Theta : Type} [Fintype Theta] (P : Family Theta)
    (prior : Theta → ℚ) (hn : ∀ t, 0 ≤ prior t) (ht : ∑ t, prior t = 1)
    (H : ℕ) (hp : geometric P.discount H ≤ P.price * P.tariff) :
    optimalValue (model P) (H + 1) (initialInfo P prior hn ht) =
      max 0 (priorRepairScore P prior H) := by
  apply le_antisymm
  · exact initial_table_upper P prior hn ht H _
      (solve_feasible (model P) (H + 1) (initialInfo P prior hn ht)) hp
  · apply max_le
    · have h := value_le_solve (model P) (H + 1) (initialInfo P prior hn ht)
        (stopTable (H + 1)) (stopTable_feasible P (H + 1) _)
      rw [initial_stop_value] at h
      exact h
    · have h := value_le_solve (model P) (H + 1) (initialInfo P prior hn ht)
        (repairThenFree P.goal H) (repairThenFree_feasible P prior hn ht H)
      rw [initial_repair_value] at h
      exact h

theorem positive_value_iff {Theta : Type} [Fintype Theta] (P : Family Theta)
    (prior : Theta → ℚ) (hn : ∀ t, 0 ≤ prior t) (ht : ∑ t, prior t = 1)
    (H : ℕ) (hp : geometric P.discount H ≤ P.price * P.tariff) :
    0 < optimalValue (model P) (H + 1) (initialInfo P prior hn ht) ↔
      0 < priorRepairScore P prior H := by
  rw [optimal_initial_value P prior hn ht H hp]
  simp

/-- Prepayment below one tariff excludes writes at every row; actual receipts
can only reduce the same wallet, including the total zero-mass defaults. -/
theorem feasible_small_wallet_free {Theta : Type} (P : Family Theta) :
    ∀ (H : ℕ) (i : Info Theta) (table : Table Act Obs H),
      i.2.val < P.tariff → Feasible (model P) i table → Free table := by
  intro H
  induction H with
  | zero => intro i table hi hf; cases table; trivial
  | succ H ih =>
      intro i table hi hf
      cases table with
      | node a children =>
          refine ⟨insufficient_prepaid_no_write P.tariff i.2 hi a hf.1, ?_⟩
          intro o
          have hw : (((model P).next i a o).2).val ≤ i.2.val := by
            change max 0 (i.2.val - charge P.tariff o) ≤ i.2.val
            exact max_le i.2.property (sub_le_self _ (charge_nonneg P o))
          exact ih ((model P).next i a o) (children o) (hw.trans_lt hi) (hf.2 o)

theorem free_damaged_value_zero {Theta : Type} (P : Family Theta) :
    ∀ (H : ℕ) (table : Table Act Obs H) (w : World Theta),
      Free table → AllDamaged P.goal w.store →
      sourceValue (source P) (gain P) P.discount table w = 0 := by
  intro H
  induction H with
  | zero => intro table w hf hw; cases table; rfl
  | succ H ih =>
      intro table w hf hw
      cases table with
      | node a children =>
          apply Finset.sum_eq_zero
          intro z hz
          have hfee : feeUnit P.goal w a z = 0 :=
            le_antisymm (by simpa [hf.1] using feeUnit_le_cap P.goal w a z)
              (feeUnit_nonneg P.goal w a z)
          have hkeep := no_fee_preserves_damaged P.goal w a z hw hfee
          have hgain : gain P a (observe P.goal w a z) = 0 := by
            rw [gain_eq_receipt,
              show RegisterJointDecisionExecution.receiptBirth (observe P.goal w a z) = 0 from hkeep.1,
              show RegisterJointDecisionExecution.receiptFee (observe P.goal w a z) = 0 from hfee]
            ring
          change primitiveWeight P.normal w z * (gain P a (observe P.goal w a z) +
            P.discount * sourceValue (source P) (gain P) P.discount
              (children (observe P.goal w a z)) (step P.goal w a z)) = 0
          rw [hgain, ih _ _ (hf.2 _) hkeep.2]
          ring

/-- Exact budget impossibility for every finite horizon, every prior on a
damaged population, and every nonnegative registered price. -/
theorem insufficient_wallet_optimal_zero {Theta : Type} (P : Family Theta)
    (H : ℕ) (i : Info Theta) (hi : i.2.val < P.tariff)
    (hw : ∀ x, i.1.weight x ≠ 0 → AllDamaged P.goal (i.1.state x).store) :
    optimalValue (model P) H i = 0 := by
  change value (model P) i (solve (model P) H i) = 0
  rw [consumer_value_eq_source]
  have hf := feasible_small_wallet_free P H i (solve (model P) H i) hi (solve_feasible (model P) H i)
  apply Finset.sum_eq_zero
  intro x hx
  by_cases hz : i.1.weight x = 0
  · simp [hz]
  · rw [free_damaged_value_zero P H _ (i.1.state x) hf (hw x hz), mul_zero]

def normalMean {Theta : Type} [Fintype Theta] (P : Family Theta) (prior : Theta → ℚ) : ℚ :=
  ∑ theta, prior theta * P.normal theta

def continuationMoment {Theta : Type} [Fintype Theta] (P : Family Theta)
    (prior : Theta → ℚ) (H : ℕ) : ℚ :=
  ∑ theta, prior theta * P.normal theta * twoBound (P.normal theta) P.discount H

theorem priorRepairScore_expansion {Theta : Type} [Fintype Theta] (P : Family Theta)
    (prior : Theta → ℚ) (H : ℕ) :
    priorRepairScore P prior H = normalMean P prior * (1 - P.price * P.tariff) +
      P.discount * continuationMoment P prior H := by
  unfold priorRepairScore repairScore normalMean continuationMoment
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro theta htheta
  ring

/-- A source-derived price boundary, with both directions and its exact
high-price scope. Increasing the priced tariff past this threshold gives zero
optimal net value; below it repair and receipt-directed continuation are useful. -/
theorem positive_price_boundary {Theta : Type} [Fintype Theta] (P : Family Theta)
    (prior : Theta → ℚ) (hn : ∀ t, 0 ≤ prior t) (ht : ∑ t, prior t = 1)
    (H : ℕ) (hp : geometric P.discount H ≤ P.price * P.tariff)
    (hm : 0 < normalMean P prior) :
    0 < optimalValue (model P) (H + 1) (initialInfo P prior hn ht) ↔
      P.price * P.tariff < 1 +
        P.discount * continuationMoment P prior H / normalMean P prior := by
  rw [positive_value_iff P prior hn ht H hp, priorRepairScore_expansion]
  constructor
  · intro h
    have hb : (P.price * P.tariff - 1) * normalMean P prior <
        P.discount * continuationMoment P prior H := by nlinarith
    have hd := (lt_div_iff₀ hm).mpr hb
    linarith
  · intro h
    have hd : P.price * P.tariff - 1 <
        P.discount * continuationMoment P prior H / normalMean P prior := by linarith
    have hb := (lt_div_iff₀ hm).mp hd
    nlinarith

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionOptimality
