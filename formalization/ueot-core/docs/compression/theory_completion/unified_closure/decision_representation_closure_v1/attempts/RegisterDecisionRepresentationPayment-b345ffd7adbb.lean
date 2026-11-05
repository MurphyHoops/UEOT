import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterDecisionRepresentationNative

/-!
# Literal prefix payment by the direct compact Store interpreter

The request cap is checked before each actual transaction. Summing the fees of
the original records gives the wallet obtained from the receipt-only summary
at every prefix, including fault, failed write, missing-slot and stop ticks.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterDecisionRepresentationPayment

open scoped BigOperators
open RegisterJointDecisionSource RegisterJointDecisionExecution
open RegisterJointDecisionConsumer RegisterJointDecisionNativeConsumer
open RegisterDecisionObserver RegisterDecisionRepresentationModel RegisterDecisionRepresentationNative
open FiniteJointDecisionBelief FiniteJointDecisionSolver
open FiniteJointDecisionFilteredModel FiniteJointDecisionDAG
open RegisterMechanismPurpose (Mechanism)

variable {Theta : Type} [Fintype Theta]

/-- A direct cursor prepayment predicate, with the cap before the outcome.
The real original fee, not an expected fee, updates the budget. -/
noncomputable def GraphPrepaid {n : ℕ} (P : Family Theta) (j : Fin n)
    (M : Model Stat Act Obs) (G : Graph Stat Act Obs) :
    (H : ℕ) → ℝ → Stat → Option ℕ → NativeWorld Theta n → Tape Noise H → Prop
  | 0, _, _, _, _, _ => True
  | H+1, budget, st, cursor, w, (z, rest) =>
      let a := controllerAction M G (H+1) st cursor
      let record := nativeTransaction j (mechanism P) w a z
      let o := nativeObs record
      ((P.tariff * cap a : ℚ) : ℝ) ≤ budget ∧
        GraphPrepaid P j M G H (budget - nativeFee record) (M.next st a o)
          (controllerNext M G (H+1) st cursor a o) (nativeStep j (mechanism P) w a z) rest

theorem graphPrepaid_eq {n : ℕ} (P : Family Theta) (j : Fin n)
    (M : Model Stat Act Obs) (G : Graph Stat Act Obs) :
    ∀ H budget st cursor (w : NativeWorld Theta n) (noise : Tape Noise H),
      GraphPrepaid P j M G H budget st cursor w noise ↔
        NativePrepaid P j budget (denote M G H st cursor) w noise := by
  intro H
  induction H with
  | zero => intros; rfl
  | succ H ih =>
      intro budget st cursor w noise
      rcases noise with ⟨z, rest⟩
      simp only [GraphPrepaid, denote, NativePrepaid, ih]

/-- The execution summary and old filter have exactly the same public
balance at every prefix, including total off-path defaults. -/
theorem packed_summary_wallet (P : Family Theta) (initial : Wallet) :
    ∀ {H : ℕ} (table : Table Act Obs H) (i : Info Theta) (st : Stat)
      (w : World Theta) (noise : Tape Noise H), i.2 = wallet P.tariff initial st → ∀ k,
      wallet P.tariff initial
          (summarizeFrom P.goal st ((packedExecute P.goal table w (tapeVector noise)).history.take k)) =
        (prefixInfo (RegisterJointDecisionConsumer.model P) i table
          (observedTape (source P) table w noise) k).2 := by
  intro H
  induction H with
  | zero =>
      intro table i st w noise hb k
      cases table
      simpa only [packedExecute, List.take_nil, summarizeFrom_nil, prefixInfo] using hb.symm
  | succ H ih =>
      intro table i st w noise hb k
      cases table with
      | node a children =>
          rcases noise with ⟨z, rest⟩
          cases k with
          | zero => simpa only [List.take_zero, summarizeFrom_nil, prefixInfo] using hb.symm
          | succ k =>
              let o := observe P.goal w a z
              change wallet P.tariff initial
                (summarizeFrom P.goal (updateStat P.goal st a o)
                  ((packedExecute P.goal (children o) (step P.goal w a z)
                    (tapeVector rest)).history.take k)) =
                (prefixInfo (RegisterJointDecisionConsumer.model P)
                  ((RegisterJointDecisionConsumer.model P).next i a o) (children o)
                  (observedTape (source P) (children o) (step P.goal w a z) rest) k).2
              apply ih (children o) _ (updateStat P.goal st a o) _ rest _ k
              change advance P.tariff i.2 a o = wallet P.tariff initial (updateStat P.goal st a o)
              rw [hb, wallet_next]

theorem native_summary_wallet {n : ℕ} (P : Family Theta) (j : Fin n) (initial : Wallet)
    {H : ℕ} (table : Table Act Obs H) (i : Info Theta) (st : Stat)
    (w : NativeWorld Theta n) (noise : Tape Noise H) (hw : Aligned P.goal w.store)
    (hb : i.2 = wallet P.tariff initial st) (k : ℕ) :
    wallet P.tariff initial
        (summarizeFrom P.goal st ((nativeExecute j (mechanism P) table w
          (tapeVector noise)).history.take k)) =
      (prefixInfo (RegisterJointDecisionConsumer.model P) i table
        (observedTape (source P) table (projectWorld j w) noise) k).2 := by
  rw [native_history_eq j (mechanism P) table w (tapeVector noise) hw]
  exact packed_summary_wallet P initial table i st (projectWorld j w) noise hb k

/-- Actual supported primitive tapes of THIS compact controller are prepaid
and keep a nonnegative literal balance at every prefix. This is pathwise, not
an average-budget guarantee, and it does not require an optimal graph. -/
theorem graph_native_payment {n : ℕ} (P : Family Theta) (j : Fin n)
    (prior : Theta → ℚ) (hn : ∀ t, 0 ≤ prior t) (ht : ∑ t, prior t = 1)
    (initial : Wallet) (G : Graph Stat Act Obs) (H : ℕ)
    (i : Info Theta) (R : Realization P j i.1) (st : Stat) (cursor : Option ℕ)
    (hb : i.2 = wallet P.tariff initial st) (x : i.1.Atom) (noise : Tape Noise H)
    (hx : 0 < i.1.weight x)
    (hz : 0 < primitiveTapeWeight P.normal (i.1.state x).theta noise) :
    let M := RegisterDecisionRepresentationModel.model P prior hn ht initial
    GraphPrepaid P j M G H (i.2.val : ℝ) st cursor (R.world x) noise ∧
      ∀ k, let execution := nativeRun j (mechanism P) M G H st cursor (R.world x) (tapeVector noise)
        let paid := ((execution.records.map nativeFee).take k).sum
        let summary := summarizeFrom P.goal st (execution.history.take k)
        ((wallet P.tariff initial summary).val : ℝ) = (i.2.val : ℝ) - paid ∧
          0 ≤ paid ∧ paid ≤ (i.2.val : ℝ) := by
  let M := RegisterDecisionRepresentationModel.model P prior hn ht initial
  let table := denote M G H st cursor
  have hf : Feasible (RegisterJointDecisionConsumer.model P) i table :=
    feasible_transfer_wallet P prior hn ht initial i st hb table (denote_feasible M G H st cursor)
  have hsource : 0 < sourceTapeWeight (source P) table (i.1.state x) noise := by
    rw [sourceTapeWeight_eq]; exact hz
  have hs := observedTape_supported (source P) (fun q => menu P.tariff q.2)
    (fun q => menu_nonempty P.tariff q.2) (advance P.tariff) (gain P)
    P.discount P.discount_bounds.1 H table i.1 i.2 x noise hx hsource
  refine ⟨?_, ?_⟩
  · apply (graphPrepaid_eq P j M G H (i.2.val : ℝ) st cursor (R.world x) noise).2
    apply native_prepaid_of_supported P j i table (R.world x) noise (R.aligned x) hf
    rw [R.projects x]
    exact hs
  · intro k
    dsimp only
    rw [nativeRun_eq, native_summary_wallet P j initial table i st (R.world x)
      noise (R.aligned x) hb k,
      native_prefix_cost P j i table (R.world x) noise (R.aligned x) k, R.projects x]
    have hk := feasible_prefix_ledger (RegisterJointDecisionConsumer.model P)
      (walletContract P) H i table hf i.2.property _ hs k
    exact ⟨by exact_mod_cast hk.1, by exact_mod_cast hk.2.1, by exact_mod_cast hk.2.2⟩

/-- In the registered initial experiment the public balance starts at B0;
the source theta and actual full Store remain on the world side. -/
theorem initial_graph_native_payment (P : Family Theta)
    (prior : Theta → ℚ) (hn : ∀ t, 0 ≤ prior t) (ht : ∑ t, prior t = 1)
    (initial : Wallet) (G : Graph Stat Act Obs) (H : ℕ) (cursor : Option ℕ)
    (theta : Theta) (noise : Tape Noise H) (hx : 0 < prior theta)
    (hz : 0 < primitiveTapeWeight P.normal theta noise) :
    let M := RegisterDecisionRepresentationModel.model P prior hn ht initial
    GraphPrepaid P (0 : Fin 1) M G H (initial.val : ℝ) (initialStat P.goal) cursor
        (nativeInitial P theta) noise ∧
      ∀ k, let execution := nativeRun (0 : Fin 1) (mechanism P) M G H (initialStat P.goal)
          cursor (nativeInitial P theta) (tapeVector noise)
        let paid := ((execution.records.map nativeFee).take k).sum
        let summary := summarizeFrom P.goal (initialStat P.goal) (execution.history.take k)
        ((wallet P.tariff initial summary).val : ℝ) = (initial.val : ℝ) - paid ∧
          0 ≤ paid ∧ paid ≤ (initial.val : ℝ) :=
  graph_native_payment P (0 : Fin 1) prior hn ht initial G H
    (initialBelief P prior hn ht, initial) (initialRealization P prior hn ht)
    (initialStat P.goal) cursor (initial_relation P prior hn ht initial).balance theta noise hx hz

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterDecisionRepresentationPayment
