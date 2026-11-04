import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionExecution

/-!
# Source-specific finite-horizon impossibility and high-price bounds

These are pathwise bounds for every outer decision table on the real Register
source. They do not follow from policy-class containment. Starting without a
healthy resident, paying at least the entire remaining discounted birth ceiling
cannot improve net payoff. A failed paid intervention does not create a free
healthy parent, extra wallet or source redraw.

Only the known-goal source family is used. The estimate is a sufficient
high-price region, not a necessary threshold for all priors or budgets.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionValueBounds

open RegisterJointDecisionSource RegisterJointDecisionExecution
open RegisterMechanismPurpose (Mechanism)
open FiniteJointDecisionSolver (Table)
open scoped BigOperators

def geometric (d : ℚ) : ℕ → ℚ
  | 0 => 0
  | H+1 => 1 + d * geometric d H

theorem geometric_nonneg (d : ℚ) (hd : 0 ≤ d) : ∀ H, 0 ≤ geometric d H := by
  intro H
  induction H with
  | zero => exact le_rfl
  | succ H ih => exact add_nonneg zero_le_one (mul_nonneg hd ih)

theorem geometric_mono (d : ℚ) (hd : 0 ≤ d) : ∀ H, geometric d H ≤ geometric d (H+1) := by
  intro H
  induction H with
  | zero => simp [geometric]
  | succ H ih =>
      have h := mul_le_mul_of_nonneg_left ih hd
      change 1 + d * geometric d H ≤ 1 + d * geometric d (H+1)
      linarith

theorem geometric_eq_sum (d : ℚ) : ∀ H, geometric d H = ∑ t ∈ Finset.range H, d ^ t := by
  intro H
  induction H with
  | zero => simp [geometric]
  | succ H ih =>
      rw [geometric, Finset.sum_range_succ']
      simp only [pow_succ, ← Finset.sum_mul, ← ih]
      ring

def AllDamaged (goal : Bool) (s : PackedStore) : Prop :=
  ∀ bit, some bit ∈ s → bit ≠ goal

theorem allDamaged_initial (goal : Bool) : AllDamaged goal [some (!goal)] := by
  intro bit hb
  simp only [List.mem_cons, List.not_mem_nil, or_false, Option.some.injEq] at hb
  subst bit
  cases goal <;> decide

private theorem lookup_mem (s : PackedStore) (j : ℕ) (bit : Bool)
    (h : packedLookup s j = some bit) : some bit ∈ s := by
  unfold packedLookup at h
  cases hs : s[j]? with
  | none => simp [hs] at h
  | some op =>
      cases op with
      | none => simp [hs] at h
      | some b =>
          have hb : b = bit := by simpa [hs] using h
          subst b
          exact List.mem_of_getElem? hs

private theorem allDamaged_set (goal : Bool) (s : PackedStore) (hs : AllDamaged goal s)
    (j : ℕ) (bit : Bool) (hb : bit ≠ goal) : AllDamaged goal (s.set j (some bit)) := by
  induction s generalizing j with
  | nil => simp [AllDamaged]
  | cons op s ih =>
      cases j with
      | zero =>
          intro b h
          simp only [List.set_cons_zero, List.mem_cons] at h
          rcases h with h | h
          · exact (Option.some.inj h).symm ▸ hb
          · exact hs b (by simp [h])
      | succ j =>
          intro b h
          simp only [List.set_cons_succ, List.mem_cons] at h
          rcases h with h | h
          · exact hs b (by simp [h])
          · exact ih (fun b h => hs b (by simp [h])) j b h

private theorem allDamaged_append_none (goal : Bool) (s : PackedStore) (hs : AllDamaged goal s) :
    AllDamaged goal (s ++ [none]) := by
  intro bit hb
  simp only [List.mem_append, List.mem_singleton, Option.some_ne_none, or_false] at hb
  exact hs bit hb

/-- No charge at a damaged population means no actual birth and no newly
healthy resident. This is derived from dispatch/invalid-address/fault branches. -/
theorem packed_no_charge {goal : Bool} {s : PackedStore} (hs : AllDamaged goal s)
    (j : ℕ) (a : RegisterRepairSource.Action) (mode : Bool)
    (hf : (packedObserve goal s j a mode).2 = false) :
    (packedObserve goal s j a mode).1 = false ∧
      AllDamaged goal (packedNext goal s j a mode) := by
  cases hp : packedLookup s j with
  | none =>
      refine ⟨by simp [packedObserve, hp], ?_⟩
      simpa [packedNext, hp] using allDamaged_append_none goal s hs
  | some bit =>
      have hb := hs bit (lookup_mem s j bit hp)
      cases mode with
      | false =>
          have hn : (!goal) ≠ goal := by cases goal <;> decide
          refine ⟨by simp [packedObserve, hp, childBit], ?_⟩
          simpa [packedNext, hp, postBit, childBit] using
            allDamaged_append_none goal _ (allDamaged_set goal s hs j (!goal) hn)
      | true =>
          cases a with
          | none =>
              refine ⟨by simp [packedObserve, hp, childBit, hb], ?_⟩
              simpa [packedNext, hp, postBit, childBit, hb] using
                allDamaged_append_none goal _ (allDamaged_set goal s hs j bit hb)
          | some b =>
              simp [packedObserve, hp] at hf

theorem no_fee_preserves_damaged {Theta : Type*} (goal : Bool) (w : World Theta)
    (a : Act) (z : Noise) (hw : AllDamaged goal w.store) (hf : feeUnit goal w a z = 0) :
    birthUnit goal w a z = 0 ∧ AllDamaged goal (step goal w a z).store := by
  have hpaid : (observe goal w a z).2 = false := by
    unfold feeUnit at hf
    cases h : (observe goal w a z).2 <;> simp_all
  have h := packed_no_charge hw (address (effective w.stopped a).1) (effective w.stopped a).2 z.1 hpaid
  exact ⟨by simp [birthUnit, observe, h.1], h.2⟩

theorem receiptBirth_le_one (o : Obs) : receiptBirth o ≤ 1 := by
  unfold receiptBirth
  split <;> norm_num

theorem receiptFee_nonneg (o : Obs) : 0 ≤ receiptFee o := by
  unfold receiptFee
  split <;> norm_num

/-- A finite process can create at most one child per tick, and all registered
fees are retained with their nonnegative price. No source-probability premise
or optimistic reward certificate is used in this ceiling. -/
theorem payoff_le_geometric {Theta : Type*} (goal : Bool) (price d : ℚ)
    (hp : 0 ≤ price) (hd : 0 ≤ d) :
    ∀ {H : ℕ} (table : Table Act Obs H) (w : World Theta) (z : Fin H → Noise),
      packedPayoff price d (packedExecute goal table w z).records ≤ geometric d H := by
  intro H
  induction H with
  | zero => intro table w z; cases table; simp [packedExecute, packedPayoff, geometric]
  | succ H ih =>
      intro table w z
      cases table with
      | node a children =>
          let o := observe goal w a (z 0)
          have htail := mul_le_mul_of_nonneg_left
            (ih (children o) (step goal w a (z 0)) (fun j => z j.succ)) hd
          have hb := receiptBirth_le_one o
          have hc := mul_nonneg hp (receiptFee_nonneg o)
          change receiptBirth o - price * receiptFee o +
            d * packedPayoff price d (packedExecute goal (children o) (step goal w a (z 0)) (fun j => z j.succ)).records ≤
              1 + d * geometric d H
          linarith

/-- Source-specific arbitrary-horizon no-go. Starting with no healthy resident,
a priced write at least as expensive as the whole remaining birth ceiling
cannot yield positive net payoff, for ANY exact table and ANY primitive tape. -/
theorem allDamaged_payoff_nonpos {Theta : Type*} (goal : Bool) (price d : ℚ) (hd : 0 ≤ d) :
    ∀ {H : ℕ} (table : Table Act Obs H) (w : World Theta) (z : Fin H → Noise),
      AllDamaged goal w.store → geometric d H ≤ price →
      packedPayoff price d (packedExecute goal table w z).records ≤ 0 := by
  intro H
  induction H with
  | zero => intro table w z hw hp; cases table; simp [packedExecute, packedPayoff]
  | succ H ih =>
      intro table w z hw hp
      cases table with
      | node a children =>
          let o := observe goal w a (z 0)
          by_cases hf : feeUnit goal w a (z 0) = 0
          · have hkeep := no_fee_preserves_damaged goal w a (z 0) hw hf
            have htail := ih (children o) (step goal w a (z 0)) (fun j => z j.succ)
              hkeep.2 ((geometric_mono d hd H).trans hp)
            have hb : receiptBirth o = 0 := hkeep.1
            have hfee : receiptFee o = 0 := hf
            change receiptBirth o - price * receiptFee o +
              d * packedPayoff price d (packedExecute goal (children o) (step goal w a (z 0)) (fun j => z j.succ)).records ≤ 0
            rw [hb, hfee]
            simpa using mul_nonpos_of_nonneg_of_nonpos hd htail
          · have hfee : receiptFee o = 1 := by
              unfold feeUnit at hf
              unfold receiptFee o
              cases ho : (observe goal w a (z 0)).2 <;> simp_all
            have hp0 := (geometric_nonneg d hd (H+1)).trans hp
            have htail := mul_le_mul_of_nonneg_left
              (payoff_le_geometric goal price d hp0 hd (children o)
                (step goal w a (z 0)) (fun j => z j.succ)) hd
            have hb := receiptBirth_le_one o
            change receiptBirth o - price * receiptFee o +
              d * packedPayoff price d (packedExecute goal (children o) (step goal w a (z 0)) (fun j => z j.succ)).records ≤ 0
            rw [hfee]
            simp only [geometric] at hp
            linarith

def stopTable : (H : ℕ) → Table Act Obs H
  | 0 => .halt
  | H+1 => .node none (fun _ => stopTable H)

/-- Stopping is a real remaining-idle run, not deletion of future ticks.
In this damaged family its payoff is exactly zero while the Store still grows
by H retained failure slots. -/
theorem stopTable_payoff_zero {Theta : Type*} (goal : Bool) (price d : ℚ) :
    ∀ (H : ℕ) (w : World Theta) (z : Fin H → Noise), AllDamaged goal w.store →
      packedPayoff price d (packedExecute goal (stopTable H) w z).records = 0 := by
  intro H
  induction H with
  | zero => intros; rfl
  | succ H ih =>
      intro w z hw
      have hf : feeUnit goal w none (z 0) = 0 := by
        have h := feeUnit_le_cap goal w none (z 0)
        have hz := feeUnit_nonneg goal w none (z 0)
        simp [cap, effective] at h
        linarith
      have hk := no_fee_preserves_damaged goal w none (z 0) hw hf
      simp only [stopTable, packedExecute, prepend, packedPayoff]
      rw [show receiptBirth (observe goal w none (z 0)) = 0 from hk.1,
        show receiptFee (observe goal w none (z 0)) = 0 from hf,
        ih (step goal w none (z 0)) (fun j => z j.succ) hk.2]
      ring

/-- The all-table no-go is a claim about literal original transactions and
their actual net payoff, via the same complete native Store execution. -/
theorem native_high_price_nonpos {Theta : Type*} {n : ℕ} (i : Fin n) (m : Mechanism)
    (price tariff d : ℚ) (hc : (m.writeCost : ℝ) = (tariff : ℝ)) (hd : 0 ≤ d)
    {H : ℕ} (table : Table Act Obs H) (w : NativeWorld Theta n) (z : Fin H → Noise)
    (hw : Aligned m.goal w.store) (hb : AllDamaged m.goal (project i w.store))
    (hp : geometric d H ≤ price * tariff) :
    actualPayoff price d (nativeExecute i m table w z).records ≤ 0 := by
  rw [table_payoff_eq i m price tariff d hc table w z hw]
  exact_mod_cast allDamaged_payoff_nonpos m.goal (price * tariff) d hd
    table (projectWorld i w) z hb hp

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionValueBounds
