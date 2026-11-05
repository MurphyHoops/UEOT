import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterDecisionObserver
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionNativeLaw

/-!
# Reachable failures and genuine mergers of decision representations

All histories below use only the old root0 / child1 menu. Their receipt laws
are computed from the same original packed primitive; the native execution
lemmas retain the actual Store, None allocations and genealogical metadata.
The address2 request appears ONLY in the explicitly enlarged-protocol witness.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterDecisionRepresentationWitnesses

open scoped BigOperators
open RegisterJointDecisionSource RegisterJointDecisionExecution
open RegisterDecisionObserver
open FiniteJointDecisionSolver (Table)

def rootWrite : Act := some (false, some true)
def rootIdle : Act := some (false, none)
def childIdle : Act := some (true, none)

def sequenceTable : (actions : List Act) → Table Act Obs actions.length
  | [] => .halt
  | a :: actions => .node a (fun _ => sequenceTable actions)

def rootThree : Table Act Obs 3 := sequenceTable [rootWrite, rootIdle, rootIdle]
def mergeTableA : Table Act Obs 3 := sequenceTable [rootWrite, rootIdle, childIdle]
def mergeTableB : Table Act Obs 3 := sequenceTable [rootWrite, childIdle, rootIdle]

def initial : World Unit := ⟨(), [some false], false⟩
def nativeInitial : NativeWorld Unit 1 := ⟨(), initialStore true false, false⟩

def insufficientA : History :=
  [(rootWrite, (true,true)), (rootIdle, (true,false)), (rootIdle, (false,false))]
def insufficientB : History :=
  [(rootWrite, (true,true)), (rootIdle, (false,false)), (rootIdle, (false,false))]
def mergeA : History :=
  [(rootWrite, (true,true)), (rootIdle, (false,false)), (childIdle, (true,false))]
def mergeB : History :=
  [(rootWrite, (true,true)), (childIdle, (true,false)), (rootIdle, (false,false))]

def bodyAfterThree : Local := ⟨false, some true, false, false⟩

/-- The source histories are reachable at the same elapsed time. B's final
zero receipt occurs for BOTH hidden modes, so it is not another fault sample. -/
theorem insufficient_histories_actual (l0 l1 l2 : Bool) :
    (packedExecute true rootThree initial ![(true,l0),(true,l1),(false,l2)]).history = insufficientA ∧
    (packedExecute true rootThree initial ![(true,l0),(false,l1),(true,l2)]).history = insufficientB ∧
    (packedExecute true rootThree initial ![(true,l0),(false,l1),(false,l2)]).history = insufficientB := by
  exact ⟨rfl, rfl, rfl⟩

theorem insufficient_counts_and_same_body :
    summarize true insufficientA = ⟨3,2,1,1,bodyAfterThree⟩ ∧
    summarize true insufficientB = ⟨3,1,1,1,bodyAfterThree⟩ := by
  exact ⟨rfl, rfl⟩

theorem insufficient_same_time_wallet_body :
    (summarize true insufficientA).elapsed = (summarize true insufficientB).elapsed ∧
    (summarize true insufficientA).paidCount = (summarize true insufficientB).paidCount ∧
    (summarize true insufficientA).q = (summarize true insufficientB).q ∧
    (summarize true insufficientA).s ≠ (summarize true insufficientB).s := by
  decide

/-- Exact fixed-theta expectation for one future actual birth. Hidden labels
are summed, not selected; their original fair law is the factor in primitiveWeight. -/
def nextBirth (r : ℚ) (w : World Unit) (a : Act) : ℚ :=
  ∑ z : Noise, primitiveWeight (fun _ : Unit => r) w z * birthUnit true w a z

/-- Original-source integral of a continuation on a specified legal history.
Actions here are externally fixed history entries; only receipts filter the
same primitive. For terminal 1 this is the actual history likelihood. -/
def historyIntegral (r : ℚ) (terminal : World Unit → ℚ) : World Unit → History → ℚ
  | w, [] => terminal w
  | w, (a,o) :: h =>
      ∑ z : Noise, primitiveWeight (fun _ : Unit => r) w z *
        if observe true w a z = o then historyIntegral r terminal (step true w a z) h else 0

def historyMassAt (r : ℚ) (h : History) : ℚ := historyIntegral r (fun _ => 1) initial h
def birthAfterMassAt (r : ℚ) (h : History) (a : Act) : ℚ :=
  historyIntegral r (fun w => nextBirth r w a) initial h

noncomputable def nativeHistoryIntegral (r : ℚ) (tariff : NNReal)
    (terminal : World Unit → ℚ) : NativeWorld Unit 1 → History → ℚ
  | w, [] => terminal (projectWorld 0 w)
  | w, (a,o) :: h =>
      ∑ z : Noise, primitiveWeight (fun _ : Unit => r) (projectWorld 0 w) z *
        if nativeObs (nativeTransaction 0 ⟨true,tariff⟩ w a z) = o then
          nativeHistoryIntegral r tariff terminal (nativeStep 0 ⟨true,tariff⟩ w a z) h else 0

/-- The witness likelihoods are transported from the ORIGINAL Store and its
actual receipt, not posited as probabilities of a newly manufactured source. -/
theorem native_history_integral_eq (r : ℚ) (tariff : NNReal) (terminal : World Unit → ℚ) :
    ∀ (h : History) (w : NativeWorld Unit 1), Aligned true w.store →
      nativeHistoryIntegral r tariff terminal w h =
        historyIntegral r terminal (projectWorld 0 w) h := by
  intro h
  induction h with
  | nil => intro w hw; rfl
  | cons e h ih =>
      rcases e with ⟨a,o⟩
      intro w hw
      simp only [nativeHistoryIntegral, historyIntegral]
      apply Finset.sum_congr rfl
      intro z hz
      rw [nativeObservation_project 0 ⟨true,tariff⟩ w a z hw]
      split_ifs with ho
      · rw [ih _ (nativeStep_aligned 0 ⟨true,tariff⟩ w a z hw),
          nativeStep_project 0 ⟨true,tariff⟩ w a z hw]
      · rfl

theorem insufficient_likelihoods (r : ℚ) :
    historyMassAt r insufficientA = r^2*(1-r) ∧
    historyMassAt r insufficientB = r*(1-r) := by
  constructor <;>
    simp [historyMassAt, historyIntegral, insufficientA, insufficientB,
      rootWrite, rootIdle, initial, observe, step, effective, address,
      packedObserve, packedNext, packedLookup, postBit, childBit,
      primitiveWeight, Fintype.sum_prod_type, Fintype.sum_bool] <;> ring

theorem insufficient_joint_next_birth (r : ℚ) :
    birthAfterMassAt r insufficientA childIdle = r^3*(1-r) ∧
    birthAfterMassAt r insufficientB childIdle = r^2*(1-r) := by
  constructor <;>
    simp [birthAfterMassAt, historyIntegral, nextBirth, birthUnit,
      insufficientA, insufficientB, rootWrite, rootIdle, childIdle, initial,
      observe, step, effective, address, packedObserve, packedNext, packedLookup,
      postBit, childBit, primitiveWeight, Fintype.sum_prod_type, Fintype.sum_bool] <;> ring

def equalPriorMass (h : History) : ℚ :=
  (historyMassAt (1/4) h + historyMassAt (3/4) h) / 2
def lowPosterior (h : History) : ℚ :=
  historyMassAt (1/4) h / (historyMassAt (1/4) h + historyMassAt (3/4) h)
def conditionalNextBirth (h : History) (a : Act) : ℚ :=
  (birthAfterMassAt (1/4) h a + birthAfterMassAt (3/4) h a) /
    (historyMassAt (1/4) h + historyMassAt (3/4) h)

/-- Same current body, time and exhausted wallet; different actual future
birth law. Both conditioning events have strictly positive source mass. -/
theorem body_wallet_time_is_insufficient :
    equalPriorMass insufficientA = 3/32 ∧ equalPriorMass insufficientB = 3/16 ∧
    0 < equalPriorMass insufficientA ∧ 0 < equalPriorMass insufficientB ∧
    lowPosterior insufficientA = 1/4 ∧ lowPosterior insufficientB = 1/2 ∧
    conditionalNextBirth insufficientA childIdle = 5/8 ∧
    conditionalNextBirth insufficientB childIdle = 1/2 := by
  have h0 := insufficient_likelihoods (1/4)
  have h1 := insufficient_likelihoods (3/4)
  have hb0 := insufficient_joint_next_birth (1/4)
  have hb1 := insufficient_joint_next_birth (3/4)
  norm_num [equalPriorMass, lowPosterior, conditionalNextBirth, h0.1, h0.2,
    h1.1, h1.2, hb0.1, hb0.2, hb1.1, hb1.2]

def mergedWorldA : World Unit :=
  (packedExecute true mergeTableA initial ![(true,false),(false,false),(true,false)]).finalWorld
def mergedWorldB : World Unit :=
  (packedExecute true mergeTableB initial ![(true,false),(true,false),(false,false)]).finalWorld

theorem merge_histories_actual (l0 l1 l2 : Bool) :
    (packedExecute true mergeTableA initial ![(true,l0),(false,l1),(true,l2)]).history = mergeA ∧
    (packedExecute true mergeTableB initial ![(true,l0),(true,l1),(false,l2)]).history = mergeB := by
  exact ⟨rfl, rfl⟩

theorem merge_same_complete_summary :
    summarize true mergeA = ⟨3,2,1,1,bodyAfterThree⟩ ∧
    summarize true mergeB = ⟨3,2,1,1,bodyAfterThree⟩ := by
  exact ⟨rfl, rfl⟩

theorem merge_different_actual_tails :
    mergedWorldA.store = [some false, some true, none, some true] ∧
    mergedWorldB.store = [some false, some true, some true, none] ∧
    mergedWorldA.store ≠ mergedWorldB.store := by
  decide

theorem merge_likelihoods (r : ℚ) :
    historyMassAt r mergeA = r^2*(1-r) ∧ historyMassAt r mergeB = r^2*(1-r) := by
  constructor <;>
    simp [historyMassAt, historyIntegral, mergeA, mergeB, rootWrite, rootIdle,
      childIdle, initial, observe, step, effective, address,
      packedObserve, packedNext, packedLookup, postBit, childBit,
      primitiveWeight, Fintype.sum_prod_type, Fintype.sum_bool] <;> ring

theorem merge_both_positive_same_posterior :
    equalPriorMass mergeA = 3/32 ∧ equalPriorMass mergeB = 3/32 ∧
    0 < equalPriorMass mergeA ∧ 0 < equalPriorMass mergeB ∧
    lowPosterior mergeA = 1/4 ∧ lowPosterior mergeB = 1/4 := by
  have h0 := merge_likelihoods (1/4)
  have h1 := merge_likelihoods (3/4)
  norm_num [equalPriorMass, lowPosterior, h0.1, h0.2, h1.1, h1.2]

/-- Every old action has the same literal receipt at the same next hidden
mode. The mode weights are the same after these two positive histories. -/
theorem merge_old_menu_receipt (a : Act) (z : Noise) :
    observe true mergedWorldA a z = observe true mergedWorldB a z := by
  rcases z with ⟨mode,label⟩
  cases a with
  | none => cases mode <;> rfl
  | some q =>
      rcases q with ⟨j,act⟩
      cases j <;> cases act with
      | none => cases mode <;> rfl
      | some bit => cases bit <;> cases mode <;> rfl

theorem merge_old_menu_joint_summary (a : Act) (z : Noise) :
    (observe true mergedWorldA a z,
      updateStat true (summarize true mergeA) a (observe true mergedWorldA a z)) =
    (observe true mergedWorldB a z,
      updateStat true (summarize true mergeB) a (observe true mergedWorldB a z)) := by
  rw [merge_same_complete_summary.1, merge_same_complete_summary.2,
    merge_old_menu_receipt]

/-- Original complete executions retain DIFFERENT allocated slots and owners
even when their control keys merge. No identity is reconstructed from a key. -/
theorem native_merge_keeps_distinct_records (tariff : NNReal) (l0 l1 l2 : Bool) :
    let sa := (nativeExecute 0 ⟨true,tariff⟩ mergeTableA nativeInitial
      ![(true,l0),(false,l1),(true,l2)]).finalWorld.store
    let sb := (nativeExecute 0 ⟨true,tariff⟩ mergeTableB nativeInitial
      ![(true,l0),(true,l1),(false,l2)]).finalWorld.store
    RegisterPopulationHistorySource.lookup sa 2 = none ∧
    (RegisterPopulationHistorySource.lookup sa 3).map (fun p => p.identity) =
      some [(0,false),(1,l0),(3,l2)] ∧
    (RegisterPopulationHistorySource.lookup sb 2).map (fun p => p.identity) =
      some [(0,false),(1,l0),(2,l1)] ∧
    RegisterPopulationHistorySource.lookup sb 3 = none := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Enlarging the menu to address2 invalidates this quotient. These worlds
were produced by legal old-menu histories, not invented unreachable states. -/
theorem dispatch2_breaks_merge (mode : Bool) :
    packedObserve true mergedWorldA.store 2 none mode = (false,false) ∧
    packedObserve true mergedWorldB.store 2 none mode = (mode,false) := by
  cases mode <;> exact ⟨rfl,rfl⟩

theorem dispatch2_birth_laws (r : ℚ) :
    (∑ z : Noise, primitiveWeight (fun _ : Unit => r) mergedWorldA z *
      if (packedObserve true mergedWorldA.store 2 none z.1).1 then 1 else 0) = 0 ∧
    (∑ z : Noise, primitiveWeight (fun _ : Unit => r) mergedWorldB z *
      if (packedObserve true mergedWorldB.store 2 none z.1).1 then 1 else 0) = r := by
  simp only [dispatch2_breaks_merge, primitiveWeight]
  simp [Fintype.sum_prod_type, Fintype.sum_bool]
  ring

/-- The same distinction is present in the original dispatcher. A's address2
request is a real None transaction; B can create a real child from that slot. -/
theorem native_dispatch2_boundary (tariff : NNReal) (l0 l1 l2 label : Bool) :
    let sa := (nativeExecute 0 ⟨true,tariff⟩ mergeTableA nativeInitial
      ![(true,l0),(false,l1),(true,l2)]).finalWorld.store
    let sb := (nativeExecute 0 ⟨true,tariff⟩ mergeTableB nativeInitial
      ![(true,l0),(true,l1),(false,l2)]).finalWorld.store
    RegisterPopulationHistorySource.transaction 0 ⟨true,tariff⟩ sa ⟨2,none,true,label⟩ = none ∧
    nativeObs (RegisterPopulationHistorySource.transaction 0 ⟨true,tariff⟩ sb
      ⟨2,none,true,label⟩) = (true,false) := by
  exact ⟨rfl,rfl⟩

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterDecisionRepresentationWitnesses
