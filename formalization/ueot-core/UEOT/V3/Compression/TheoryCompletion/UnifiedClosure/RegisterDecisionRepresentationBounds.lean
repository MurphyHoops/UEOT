import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterDecisionObserver
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteJointDecisionDAG

/-!
# A source-specific bound on the actual array of unique decision nodes

The counted object is the actual Graph array, not an ideal set which ignores
implementation copies. Its node-key injectivity and executable horizon check
inject every stored node into four bounded count coordinates and the 24 local
states. The source observer proves the count invariant from initialization and
every update. No posterior atom carrier or full native Store is counted as a
single free object: rational bit lengths, arithmetic, temporary data, metadata
and serialization costs require their own measurements.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterDecisionRepresentationBounds

open RegisterDecisionObserver RegisterJointDecisionSource
open FiniteJointDecisionDAG

def CountBound (st : Stat) : Prop := st.s + st.f ≤ st.elapsed ∧ st.paidCount ≤ st.elapsed

instance (st : Stat) : Decidable (CountBound st) := inferInstanceAs
  (Decidable (st.s + st.f ≤ st.elapsed ∧ st.paidCount ≤ st.elapsed))

theorem initial_count_bound (goal : Bool) : CountBound (initialStat goal) := by
  simp [CountBound, initialStat]

theorem update_count_bound (goal : Bool) (st : Stat) (a : Act) (o : Obs)
    (hs : CountBound st) : CountBound (updateStat goal st a o) := by
  have hi := increments_le_one goal st.q a o
  have hp : (if o.2 then 1 else 0 : ℕ) ≤ 1 := by cases o.2 <;> simp
  dsimp [CountBound, updateStat] at hs ⊢
  omega

theorem summarizeFrom_count_bound (goal : Bool) :
    ∀ (h : History) (st : Stat), CountBound st → CountBound (summarizeFrom goal st h) := by
  intro h
  induction h with
  | nil => intro st hs; exact hs
  | cons e h ih =>
      rcases e with ⟨a,o⟩
      intro st hs
      exact ih _ (update_count_bound goal st a o hs)

theorem summarize_count_bound (goal : Bool) (h : History) : CountBound (summarize goal h) :=
  summarizeFrom_count_bound goal h (initialStat goal) (initial_count_bound goal)

theorem summarizeFrom_elapsed (goal : Bool) :
    ∀ (h : History) (st : Stat),
      (summarizeFrom goal st h).elapsed = st.elapsed + h.length := by
  intro h
  induction h with
  | nil => intro st; simp [summarizeFrom]
  | cons e h ih =>
      rcases e with ⟨a,o⟩
      intro st
      rw [summarizeFrom_cons, ih]
      simp only [updateStat, List.length_cons]
      omega

theorem summarize_elapsed (goal : Bool) (h : History) :
    (summarize goal h).elapsed = h.length := by
  simpa [summarize, initialStat] using summarizeFrom_elapsed goal h (initialStat goal)

/-- Remaining time is not a fifth independent unbounded coordinate. -/
def InHorizon (H : ℕ) (key : ℕ × Stat) : Prop :=
  key.1 + key.2.elapsed = H ∧ CountBound key.2

instance (H : ℕ) (key : ℕ × Stat) : Decidable (InHorizon H key) := inferInstanceAs
  (Decidable (key.1 + key.2.elapsed = H ∧ CountBound key.2))

theorem initial_in_horizon (goal : Bool) (H : ℕ) :
    InHorizon H (H,initialStat goal) := by
  exact ⟨by simp [initialStat], initial_count_bound goal⟩

theorem update_in_horizon (goal : Bool) (H n : ℕ) (st : Stat) (a : Act) (o : Obs)
    (hs : InHorizon H (n+1,st)) : InHorizon H (n,updateStat goal st a o) := by
  refine ⟨?_,update_count_bound goal st a o hs.2⟩
  have ht := hs.1
  change (n+1)+st.elapsed = H at ht
  change n + (st.elapsed + 1) = H
  omega

theorem history_in_horizon (goal : Bool) (H n : ℕ) (h : History)
    (ht : n + h.length = H) : InHorizon H (n,summarize goal h) := by
  exact ⟨by simpa [summarize_elapsed] using ht, summarize_count_bound goal h⟩

def localEquiv : Local ≃ Bool × Option Bool × Bool × Bool where
  toFun q := (q.root,q.child,q.stopped,q.fresh)
  invFun q := ⟨q.1,q.2.1,q.2.2.1,q.2.2.2⟩
  left_inv q := by cases q; rfl
  right_inv q := by rcases q with ⟨root,child,stopped,fresh⟩; rfl

theorem local_card : Fintype.card Local = 24 := by
  rw [Fintype.card_congr localEquiv]
  norm_num

abbrev Code (H : ℕ) := Fin (H+1) × Fin (H+1) × Fin (H+1) × Fin (H+1) × Local

theorem code_card (H : ℕ) : Fintype.card (Code H) = 24*(H+1)^4 := by
  simp only [Code, Fintype.card_prod, Fintype.card_fin, local_card]
  ring

def encode (H : ℕ) (key : ℕ × Stat) (h : InHorizon H key) : Code H := by
  have ht := h.1
  have hs := h.2.1
  have hk := h.2.2
  exact (⟨key.2.elapsed,by omega⟩, ⟨key.2.s,by omega⟩,
    ⟨key.2.f,by omega⟩, ⟨key.2.paidCount,by omega⟩, key.2.q)

theorem encode_injective (H : ℕ) (x y : ℕ × Stat) (hx : InHorizon H x) (hy : InHorizon H y)
    (he : encode H x hx = encode H y hy) : x = y := by
  have ht : x.2.elapsed = y.2.elapsed := congrArg (fun c : Code H => c.1.val) he
  have hs : x.2.s = y.2.s := congrArg (fun c : Code H => c.2.1.val) he
  have hf : x.2.f = y.2.f := congrArg (fun c : Code H => c.2.2.1.val) he
  have hk : x.2.paidCount = y.2.paidCount := congrArg (fun c : Code H => c.2.2.2.1.val) he
  have hq : x.2.q = y.2.q := congrArg (fun c : Code H => c.2.2.2.2) he
  have hn : x.1 = y.1 := by have hx' := hx.1; have hy' := hy.1; omega
  rcases x with ⟨nx,⟨tx,sx,fx,kx,qx⟩⟩
  rcases y with ⟨ny,⟨ty,sy,fy,ky,qy⟩⟩
  dsimp only at hn ht hs hf hk hq
  cases hn
  cases ht
  cases hs
  cases hf
  cases hk
  cases hq
  rfl

/-- An executable condition on ALL actual stored rows, including any row
which is outside the selected policy's execution subgraph. -/
def boundCheck {A O : Type} (H : ℕ) (G : Graph Stat A O) : Bool :=
  decide (∀ j : Fin G.size, InHorizon H ((G[j]).remaining,(G[j]).state))

theorem boundCheck_sound {A O : Type} (H : ℕ) (G : Graph Stat A O)
    (h : boundCheck H G = true) :
    ∀ j : Fin G.size, InHorizon H ((G[j]).remaining,(G[j]).state) := by
  exact of_decide_eq_true h

/-- The source-specific O(H^4) bound is on the actual Graph.size. Key
injectivity rules out counting an ideal quotient while storing duplicate rows. -/
theorem actual_graph_node_bound {A O : Type} (H : ℕ) (G : Graph Stat A O)
    (hunique : Function.Injective
      (fun j : Fin G.size => ((G[j]).remaining,(G[j]).state)))
    (hb : boundCheck H G = true) : G.size ≤ 24*(H+1)^4 := by
  let enc : Fin G.size → Code H := fun j =>
    encode H ((G[j]).remaining,(G[j]).state) (boundCheck_sound H G hb j)
  have hi : Function.Injective enc := by
    intro i j hij
    apply hunique
    exact encode_injective H _ _ _ _ hij
  have hc := Fintype.card_le_of_injective enc hi
  simpa only [Fintype.card_fin, code_card] using hc

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterDecisionRepresentationBounds
