import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterDecisionRepresentationModel
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteJointDecisionDAG
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionNativeConsumer

/-!
# THIS checked compact controller on the original Store

The interpreters below recurse through the finite horizon with one node cursor.
They do not expand a table. Only the action and receipt update their public
summary. The equality to `denote` is a proof used to reuse the original native
source, full-history optimality and prefix-payment theorems.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterDecisionRepresentationNative

open scoped BigOperators
open RegisterJointDecisionSource RegisterJointDecisionExecution
open RegisterJointDecisionConsumer RegisterJointDecisionNativeConsumer
open RegisterDecisionObserver RegisterDecisionRepresentationModel
open FiniteJointDecisionBelief FiniteJointDecisionSolver
open FiniteJointDecisionFilteredModel FiniteJointDecisionSupportedPolicy
open FiniteJointDecisionRefinement FiniteJointDecisionDAG
open RegisterMechanismPurpose (Mechanism)
open RegisterTimestampedBirthSource (ClockedRecord)

/-- Executable packed interpreter, reading only one node at a time. The
world is passed to the primitive, never to `controllerAction`. -/
def packedRun {Theta : Type} (goal : Bool) (M : Model Stat Act Obs) (G : Graph Stat Act Obs) :
    (H : ℕ) → Stat → Option ℕ → World Theta → (Fin H → Noise) → Execution (World Theta) Obs
  | 0, _, _, w, _ => ⟨w, [], []⟩
  | H+1, st, cursor, w, noise =>
      let a := controllerAction M G (H+1) st cursor
      let o := observe goal w a (noise 0)
      prepend a o o (packedRun goal M G H (M.next st a o)
        (controllerNext M G (H+1) st cursor a o) (step goal w a (noise 0))
        (fun j => noise j.succ))

/-- The original population interpreter uses the identical node cursor. Its
literal record retains all programs, identities, lineage, clocks and None. -/
noncomputable def nativeRun {Theta : Type} {n : ℕ} (j : Fin n) (m : Mechanism)
    (M : Model Stat Act Obs) (G : Graph Stat Act Obs) :
    (H : ℕ) → Stat → Option ℕ → NativeWorld Theta n → (Fin H → Noise) →
      Execution (NativeWorld Theta n) (Option (ClockedRecord n))
  | 0, _, _, w, _ => ⟨w, [], []⟩
  | H+1, st, cursor, w, noise =>
      let a := controllerAction M G (H+1) st cursor
      let record := nativeTransaction j m w a (noise 0)
      let o := nativeObs record
      prepend a o record (nativeRun j m M G H (M.next st a o)
        (controllerNext M G (H+1) st cursor a o) (nativeStep j m w a (noise 0))
        (fun k => noise k.succ))

theorem packedRun_eq {Theta : Type} (goal : Bool) (M : Model Stat Act Obs) (G : Graph Stat Act Obs) :
    ∀ H st cursor (w : World Theta) (noise : Fin H → Noise),
      packedRun goal M G H st cursor w noise =
        packedExecute goal (denote M G H st cursor) w noise := by
  intro H
  induction H with
  | zero => intros; rfl
  | succ H ih => intros; simp only [packedRun, denote, packedExecute, ih]

theorem nativeRun_eq {Theta : Type} {n : ℕ} (j : Fin n) (m : Mechanism)
    (M : Model Stat Act Obs) (G : Graph Stat Act Obs) :
    ∀ H st cursor (w : NativeWorld Theta n) (noise : Fin H → Noise),
      nativeRun j m M G H st cursor w noise =
        nativeExecute j m (denote M G H st cursor) w noise := by
  intro H
  induction H with
  | zero => intros; rfl
  | succ H ih => intros; simp only [nativeRun, denote, nativeExecute, ih]

theorem nativeRun_project {Theta : Type} {n : ℕ} (j : Fin n) (m : Mechanism)
    (M : Model Stat Act Obs) (G : Graph Stat Act Obs)
    (H : ℕ) (st : Stat) (cursor : Option ℕ) (w : NativeWorld Theta n) (noise : Fin H → Noise)
    (hw : Aligned m.goal w.store) :
    eraseExecution j (nativeRun j m M G H st cursor w noise) =
      packedRun m.goal M G H st cursor (projectWorld j w) noise := by
  rw [nativeRun_eq, packedRun_eq, nativeExecute_project j m _ w noise hw]

/-- Independent-of-policy finite primitive law: theta is used once and kept
fixed throughout the tape. The label is still sampled at every actual tick. -/
def primitiveTapeWeight {Theta : Type} (r : Theta → ℚ) (theta : Theta) :
    {H : ℕ} → Tape Noise H → ℚ
  | 0, _ => 1
  | _+1, (z, rest) => ((if z.1 then r theta else 1-r theta) / 2) *
      primitiveTapeWeight r theta rest

theorem sourceTapeWeight_eq {Theta : Type} (P : Family Theta) :
    ∀ {H : ℕ} (table : Table Act Obs H) (w : World Theta) (noise : Tape Noise H),
      sourceTapeWeight (source P) table w noise = primitiveTapeWeight P.normal w.theta noise := by
  intro H
  induction H with
  | zero => intro table w noise; cases table; rfl
  | succ H ih =>
      intro table w noise
      cases table with
      | node a children =>
          rcases noise with ⟨z, rest⟩
          simp only [sourceTapeWeight, primitiveTapeWeight, ih]
          rfl

noncomputable def nativeGraphJ {Theta : Type} {n : ℕ} (P : Family Theta) (j : Fin n)
    (M : Model Stat Act Obs) (G : Graph Stat Act Obs) (H : ℕ)
    (st : Stat) (cursor : Option ℕ) (w : NativeWorld Theta n) : ℝ :=
  ∑ noise : Tape Noise H, (primitiveTapeWeight P.normal w.theta noise : ℝ) *
    actualPayoff P.price P.discount
      (nativeRun j (mechanism P) M G H st cursor w (tapeVector noise)).records

theorem nativeGraphJ_eq {Theta : Type} {n : ℕ} (P : Family Theta) (j : Fin n)
    (M : Model Stat Act Obs) (G : Graph Stat Act Obs) (H : ℕ)
    (st : Stat) (cursor : Option ℕ) (w : NativeWorld Theta n) :
    nativeGraphJ P j M G H st cursor w = nativeJ P j (denote M G H st cursor) w := by
  simp only [nativeGraphJ, nativeJ, nativeRun_eq, sourceTapeWeight_eq]
  rfl

noncomputable def expectedGraphJ {Theta : Type} {n : ℕ} (P : Family Theta) (j : Fin n)
    (M : Model Stat Act Obs) (G : Graph Stat Act Obs) (H : ℕ)
    (i : Info Theta) (R : Realization P j i.1) (st : Stat) (cursor : Option ℕ) : ℝ :=
  ∑ x, (i.1.weight x : ℝ) * nativeGraphJ P j M G H st cursor (R.world x)

theorem expectedGraphJ_eq {Theta : Type} {n : ℕ} (P : Family Theta) (j : Fin n)
    (M : Model Stat Act Obs) (G : Graph Stat Act Obs) (H : ℕ)
    (i : Info Theta) (R : Realization P j i.1) (st : Stat) (cursor : Option ℕ) :
    expectedGraphJ P j M G H i R st cursor =
      expectedNativeJ P j i R (denote M G H st cursor) := by
  simp only [expectedGraphJ, expectedNativeJ, nativeGraphJ_eq]

variable {Theta : Type} [Fintype Theta]

/-- Exact value of THIS graph, with actual native population records. The
graph certificate covers all legal alternatives, not just the chosen edges. -/
theorem checked_native_value {n : ℕ} (P : Family Theta) (j : Fin n)
    (prior : Theta → ℚ) (hn : ∀ t, 0 ≤ prior t) (ht : ∑ t, prior t = 1)
    (initial : Wallet) (G : Graph Stat Act Obs)
    (hg : Good (RegisterDecisionRepresentationModel.model P prior hn ht initial) G)
    (H : ℕ) (root : Fin G.size) (hr : (G[root.val]).remaining = H)
    (i : Info Theta) (R : Realization P j i.1)
    (hi : Rel P prior initial i (G[root.val]).state) :
    expectedGraphJ P j (RegisterDecisionRepresentationModel.model P prior hn ht initial)
      G H i R (G[root.val]).state (some root.val) = ((G[root.val]).value : ℝ) := by
  let M := RegisterDecisionRepresentationModel.model P prior hn ht initial
  have hf := denote_feasible M G H (G[root.val]).state (some root.val)
  have hfold := feasible_transfer_wallet P prior hn ht initial i (G[root.val]).state hi.balance _ hf
  rw [expectedGraphJ_eq, expectedNativeJ_eq_value P j i R _ hfold]
  rw [value_transfer (refinement P prior hn ht initial) i (G[root.val]).state hi _
    (feasible_supported M _ _ hf), denote_value_eq_node M G hg H root hr]

/-- The comparison class remains all legal permitted full-history kernels,
with arbitrary real randomization, memory and unsupported off-path defaults. -/
theorem checked_native_optimal {n : ℕ} (P : Family Theta) (j : Fin n)
    (prior : Theta → ℚ) (hn : ∀ t, 0 ≤ prior t) (ht : ∑ t, prior t = 1)
    (initial : Wallet) (G : Graph Stat Act Obs)
    (hg : Good (RegisterDecisionRepresentationModel.model P prior hn ht initial) G)
    (H : ℕ) (root : Fin G.size) (hr : (G[root.val]).remaining = H)
    (pi : RawCausalPolicy (RegisterJointDecisionConsumer.model P)) (h : pi.Memory)
    (R : Realization P j (pi.info h).1)
    (hi : Rel P prior initial (pi.info h) (G[root.val]).state)
    (ha : SupportedAdmissible (RegisterJointDecisionConsumer.model P) pi H h) :
    expectedRawNativeJ P j pi H h R ≤
      expectedGraphJ P j (RegisterDecisionRepresentationModel.model P prior hn ht initial)
        G H (pi.info h) R (G[root.val]).state (some root.val) := by
  rw [checked_native_value P j prior hn ht initial G hg H root hr (pi.info h) R hi]
  have hbound := returned_native_optimal P j pi H h R ha
  rw [returned_native_value] at hbound
  rw [optimalValue_transfer (refinement P prior hn ht initial) H (pi.info h)
    (G[root.val]).state hi,
    ← node_value_eq_optimal (RegisterDecisionRepresentationModel.model P prior hn ht initial)
      G hg H root hr] at hbound
  exact hbound

/-- The original known damaged founder instantiates the physical relation;
it is not left as a premise of the final consumer. -/
theorem initial_checked_native_value (P : Family Theta)
    (prior : Theta → ℚ) (hn : ∀ t, 0 ≤ prior t) (ht : ∑ t, prior t = 1)
    (initial : Wallet) (G : Graph Stat Act Obs)
    (hg : Good (RegisterDecisionRepresentationModel.model P prior hn ht initial) G)
    (H : ℕ) (root : Fin G.size) (hr : (G[root.val]).remaining = H)
    (hs : (G[root.val]).state = initialStat P.goal) :
    (∑ theta, (prior theta : ℝ) *
      nativeGraphJ P (0 : Fin 1) (RegisterDecisionRepresentationModel.model P prior hn ht initial)
        G H (initialStat P.goal) (some root.val) (nativeInitial P theta)) =
      ((G[root.val]).value : ℝ) := by
  have hv := checked_native_value P (0 : Fin 1) prior hn ht initial G hg H root hr
    (initialBelief P prior hn ht, initial) (initialRealization P prior hn ht)
    (by rw [hs]; exact initial_relation P prior hn ht initial)
  simpa only [expectedGraphJ, initialBelief, initialRealization, hs] using hv

/-- The full actual world keeps advancing after stop, including None slots;
compression affects only controller memory, not identity or population state. -/
theorem nativeRun_population {n : ℕ} (P : Family Theta) (j : Fin n)
    (M : Model Stat Act Obs) (G : Graph Stat Act Obs) (H : ℕ)
    (st : Stat) (cursor : Option ℕ) (w : NativeWorld Theta n) (noise : Fin H → Noise)
    (hw : Aligned P.goal w.store) :
    (nativeRun j (mechanism P) M G H st cursor w noise).records.length = H ∧
    (nativeRun j (mechanism P) M G H st cursor w noise).history.length = H ∧
    (nativeRun j (mechanism P) M G H st cursor w noise).finalWorld.store.length = w.store.length + H := by
  rw [nativeRun_eq]
  exact nativeExecute_length j (mechanism P) _ w noise hw

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterDecisionRepresentationNative
