import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Discrete Preference Cochain Obstruction on Finite Graphs & Condorcet 3-Cycle Non-Integrability

Pure-kernel Lean 4 formalization complementing `UEOT.V3.AlignmentGlobalExactness` (`P-ALI-01`,
which proves global exactness for `C¹` one-forms on connected smooth manifolds) with the
**discrete graph-cochain theory** on arbitrary connected simple graphs `G : SimpleGraph V`
(including finite graphs `[Fintype V]` and complete pairwise comparison graphs `⊤ : SimpleGraph V`):

1. **Discrete 1-Forms and Coboundary `d0`**:
   - `DiscreteOneForm V`: antisymmetric pairwise comparison / preference 1-cochain
     `ω : V → V → ℝ` satisfying `ω u v = - ω v u`.
   - `d0 Φ`: discrete coboundary `(d0 Φ) u v = Φ v - Φ u` of a scalar potential `Φ : V → ℝ`.
   - `IsExactOn G ω`: existence of a scalar potential `Φ : V → ℝ` such that `ω u v = (d0 Φ) u v`
     on all edges `G.Adj u v`; `IsExact ω`: global exactness `ω = d0 Φ` (equivalent to
     `IsExactOn ⊤ ω`).

2. **Walk Sums, Cycle Decomposition & Discrete Global Exactness**:
   - `walkSum ω p` and `cycleSum ω c`: discrete line integral along a `SimpleGraph.Walk`.
   - `closedWalkSums_iff_zeroSimpleCycleSums`: vanishing on all closed walks `G.Walk u u`
     is equivalent to vanishing on all simple cycles `c.IsCycle`.
   - `discrete_exact_iff_zero_cycle_sum` (and `discrete_exact_iff_closed_walk_sum`,
     `finite_graph_discrete_exact_iff_zero_cycle_sum`, `complete_discrete_exact_iff_zero_cycle_sum`):
     on any connected simple graph `G`, `IsExactOn G ω ↔ ZeroSimpleCycleSums G ω`, proved in the
     reverse direction by fixing a basepoint `v₀`, constructing the potential
     `Φ x := walkSum ω (chosenWalk x)`, and deriving edge consistency from path reversal
     and concatenation.

3. **Condorcet 3-Alternative Cycle Non-Integrability (`condorcet_3cycle_nonintegrable`)**:
   - Concrete skew-symmetric 1-form `condorcetThreeCycleForm` on `Fin 3` with
     `ω 0 1 = 1`, `ω 1 2 = 1`, `ω 2 0 = 1`.
   - Proves `cycleSum = 3 ≠ 0` on the simple 3-cycle `0 → 1 → 2 → 0`, yielding both:
     - `¬ IsExactOn (⊤ : SimpleGraph (Fin 3)) condorcetThreeCycleForm` (and `¬ IsExact`), and
     - `¬ ∃ Φ : Fin 3 → ℝ, ∀ u v : Fin 3, 0 < condorcetThreeCycleForm u v → Φ u < Φ v`
       (no strict scalar preference potential exists).

## Pure-Kernel Guarantee
Axioms strictly `⊆ {propext, Classical.choice, Quot.sound}`; zero `sorryAx`; zero custom
`axiom`, `opaque`, `unsafe`, or `native_decide`; zero dependency on any physics frontier module.
-/

namespace UEOTPhysicsUnification.DiscretePreferenceCochainObstruction

/-! ## 1. Discrete 1-Forms and Coboundary `d0` -/

/-- A discrete 1-form (antisymmetric 1-cochain) on a vertex type `V`, assigning
skew-symmetric real weights `ω u v = - ω v u` to ordered vertex pairs. -/
structure DiscreteOneForm (V : Type*) where
  toFun : V → V → ℝ
  skew : ∀ u v : V, toFun u v = - toFun v u

instance {V : Type*} : CoeFun (DiscreteOneForm V) (fun _ => V → V → ℝ) :=
  ⟨DiscreteOneForm.toFun⟩

@[ext]
theorem DiscreteOneForm.ext {V : Type*} {ω₁ ω₂ : DiscreteOneForm V}
    (h : ∀ u v, ω₁ u v = ω₂ u v) : ω₁ = ω₂ := by
  cases ω₁
  cases ω₂
  simp only [DiscreteOneForm.mk.injEq]
  funext u v
  exact h u v

@[simp]
theorem DiscreteOneForm.skew_diag {V : Type*} (ω : DiscreteOneForm V) (u : V) :
    ω u u = 0 := by
  have h := ω.skew u u
  linarith

/-- Discrete coboundary operator `d0 : (V → ℝ) → DiscreteOneForm V`,
given by `(d0 Φ) u v = Φ v - Φ u`. -/
def d0 {V : Type*} (Φ : V → ℝ) : DiscreteOneForm V where
  toFun u v := Φ v - Φ u
  skew u v := by ring

@[simp]
theorem d0_apply {V : Type*} (Φ : V → ℝ) (u v : V) : d0 Φ u v = Φ v - Φ u := rfl

/-- A discrete 1-form `ω` is exact on a simple graph `G` if there exists a scalar potential
`Φ : V → ℝ` whose coboundary `d0 Φ` agrees with `ω` on every edge of `G`. -/
def IsExactOn {V : Type*} (G : SimpleGraph V) (ω : DiscreteOneForm V) : Prop :=
  ∃ Φ : V → ℝ, ∀ ⦃u v : V⦄, G.Adj u v → ω u v = (d0 Φ) u v

/-- Global exactness on all pairs of vertices (`ω = d0 Φ`). -/
def IsExact {V : Type*} (ω : DiscreteOneForm V) : Prop :=
  ∃ Φ : V → ℝ, ω = d0 Φ

theorem isExact_iff_isExactOn_top {V : Type*} (ω : DiscreteOneForm V) :
    IsExact ω ↔ IsExactOn (⊤ : SimpleGraph V) ω := by
  constructor
  · rintro ⟨Φ, rfl⟩
    exact ⟨Φ, fun _ _ _ => rfl⟩
  · rintro ⟨Φ, hΦ⟩
    refine ⟨Φ, DiscreteOneForm.ext fun u v => ?_⟩
    by_cases huv : u = v
    · subst huv
      simp
    · exact hΦ huv

/-! ## 2. Walk Sums, Reversal, Concatenation, and Cycle Decomposition -/

/-- Discrete line integral (sum of 1-form values) along a graph walk `p : G.Walk u v`. -/
def walkSum {V : Type*} {G : SimpleGraph V} (ω : DiscreteOneForm V) :
    {u v : V} → G.Walk u v → ℝ
  | _, _, .nil => 0
  | u, _, .cons (v := v) _ p => ω u v + walkSum ω p

/-- Cycle sum along a closed walk `c : G.Walk u u`. -/
abbrev cycleSum {V : Type*} {G : SimpleGraph V} (ω : DiscreteOneForm V) {u : V}
    (c : G.Walk u u) : ℝ :=
  walkSum ω c

@[simp]
theorem walkSum_nil {V : Type*} {G : SimpleGraph V} (ω : DiscreteOneForm V) (u : V) :
    walkSum ω (.nil : G.Walk u u) = 0 := rfl

@[simp]
theorem walkSum_cons {V : Type*} {G : SimpleGraph V} (ω : DiscreteOneForm V)
    {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    walkSum ω (.cons h p) = ω u v + walkSum ω p := rfl

@[simp]
theorem walkSum_append {V : Type*} {G : SimpleGraph V} (ω : DiscreteOneForm V)
    {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    walkSum ω (p.append q) = walkSum ω p + walkSum ω q := by
  induction p with
  | nil => simp
  | cons h p ih =>
      simp only [SimpleGraph.Walk.cons_append, walkSum_cons, ih]
      ring

@[simp]
theorem walkSum_reverse {V : Type*} {G : SimpleGraph V} (ω : DiscreteOneForm V)
    {u v : V} (p : G.Walk u v) :
    walkSum ω p.reverse = - walkSum ω p := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
      simp only [SimpleGraph.Walk.reverse_cons, walkSum_append, walkSum_cons, walkSum_nil,
        add_zero, ih]
      have hsk := ω.skew u v
      linarith

theorem walkSum_exact_on {V : Type*} {G : SimpleGraph V} (ω : DiscreteOneForm V)
    {Φ : V → ℝ} (hΦ : ∀ ⦃x y : V⦄, G.Adj x y → ω x y = (d0 Φ) x y)
    {u v : V} (p : G.Walk u v) :
    walkSum ω p = Φ v - Φ u := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
      simp only [walkSum_cons, hΦ h, d0_apply, ih]
      ring

/-- Vanishing of `cycleSum` on every closed walk `G.Walk u u`. -/
def ClosedWalkSums {V : Type*} (G : SimpleGraph V) (ω : DiscreteOneForm V) : Prop :=
  ∀ (u : V) (c : G.Walk u u), cycleSum ω c = 0

/-- Vanishing of `cycleSum` on every simple cycle `c.IsCycle`. -/
def ZeroSimpleCycleSums {V : Type*} (G : SimpleGraph V) (ω : DiscreteOneForm V) : Prop :=
  ∀ (u : V) (c : G.Walk u u), c.IsCycle → cycleSum ω c = 0

private theorem walkSum_backtrack_eq_zero {V : Type*} {G : SimpleGraph V}
    (ω : DiscreteOneForm V) {u v : V} (hadj : G.Adj u v) (p : G.Walk v u)
    (hp : p.IsPath) (hedge : s(u, v) ∈ p.edges) :
    walkSum ω (.cons hadj p) = 0 := by
  cases p with
  | nil => simp at hedge
  | @cons _ w' _ h' q =>
      by_cases hw : w' = u
      · subst hw
        have hqnil : q.Nil := SimpleGraph.Walk.isPath_iff_nil.mp hp.of_cons
        cases q with
        | nil =>
            simp only [walkSum_cons, walkSum_nil, add_zero]
            have hsk := ω.skew w' v
            linarith
        | cons _ _ => exact absurd hqnil SimpleGraph.Walk.not_nil_cons
      · exfalso
        have hmem : v ∉ q.support := (SimpleGraph.Walk.cons_isPath_iff h' q).mp hp |>.2
        simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at hedge
        rcases hedge with h_eq | h_in_q
        · rw [Sym2.eq_iff] at h_eq
          rcases h_eq with ⟨huv, _⟩ | ⟨huw, _⟩
          · exact hadj.ne huv
          · exact hw huw.symm
        · exact hmem (SimpleGraph.Walk.snd_mem_support_of_mem_edges q h_in_q)

private theorem walkSum_eq_zero_of_zeroSimpleCycleSums_aux
    {V : Type*} {G : SimpleGraph V} (ω : DiscreteOneForm V)
    (hcyc : ZeroSimpleCycleSums G ω) :
    ∀ (n : ℕ) (u : V) (c : G.Walk u u), c.length ≤ n → walkSum ω c = 0 := by
  intro n
  induction n with
  | zero =>
      intro u c hc
      have hnil : c.Nil := SimpleGraph.Walk.length_eq_zero_iff.mp (Nat.le_zero.mp hc)
      cases c with
      | nil => simp
      | cons _ _ => exact absurd hnil SimpleGraph.Walk.not_nil_cons
  | succ n ih =>
      intro u c hc
      cases c with
      | nil => simp
      | @cons _ v _ hadj p =>
          simp only [SimpleGraph.Walk.length_cons] at hc
          by_cases hp : p.IsPath
          · by_cases hedge : s(u, v) ∈ p.edges
            · exact walkSum_backtrack_eq_zero ω hadj p hp hedge
            · have hc_cyc : (SimpleGraph.Walk.cons hadj p).IsCycle :=
                (SimpleGraph.Walk.cons_isCycle_iff p hadj).mpr ⟨hp, hedge⟩
              exact hcyc u (SimpleGraph.Walk.cons hadj p) hc_cyc
          · have hnot : ¬ ∀ (w : V) (sub : G.Walk w w), sub.IsSubwalk p → sub.Nil := by
              rwa [← SimpleGraph.Walk.isPath_iff_isSubwalk_imp_nil]
            push Not at hnot
            rcases hnot with ⟨w, sub, hsub, hnonnil⟩
            rcases hsub with ⟨q₁, q₂, rfl⟩
            have hsub_pos : 0 < sub.length :=
              Nat.pos_of_ne_zero (mt SimpleGraph.Walk.length_eq_zero_iff.mp hnonnil)
            have hlen_p : ((q₁.append sub).append q₂).length ≤ n := by omega
            simp only [SimpleGraph.Walk.length_append] at hlen_p
            have hsub_zero : walkSum ω sub = 0 := ih w sub (by omega)
            let c' : G.Walk u u := .cons hadj (q₁.append q₂)
            have hc'_len : c'.length ≤ n := by
              simp only [c', SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_append]
              omega
            have hc'_zero : walkSum ω c' = 0 := ih u c' hc'_len
            simp only [c', walkSum_cons, walkSum_append] at hc'_zero
            simp only [walkSum_cons, walkSum_append, hsub_zero]
            linarith

/-- Vanishing of `cycleSum` on all closed walks is equivalent to vanishing on all simple cycles. -/
theorem closedWalkSums_iff_zeroSimpleCycleSums {V : Type*} (G : SimpleGraph V)
    (ω : DiscreteOneForm V) :
    ClosedWalkSums G ω ↔ ZeroSimpleCycleSums G ω := by
  constructor
  · intro hclosed u c _
    exact hclosed u c
  · intro hcyc u c
    exact walkSum_eq_zero_of_zeroSimpleCycleSums_aux ω hcyc c.length u c le_rfl

/-! ## 3. Path Independence & Discrete Global Exactness (`discrete_exact_iff_zero_cycle_sum`) -/

/-- Under `ClosedWalkSums G ω`, the walk sum between any two vertices is independent of the
chosen walk (discrete counterpart of `AlignmentGlobalExactness.pathIndependent`). -/
theorem discrete_pathIndependent {V : Type*} {G : SimpleGraph V} (ω : DiscreteOneForm V)
    (hclosed : ClosedWalkSums G ω) {u v : V} (p q : G.Walk u v) :
    walkSum ω p = walkSum ω q := by
  have hloop := hclosed u (p.append q.reverse)
  rw [cycleSum, walkSum_append, walkSum_reverse] at hloop
  linarith

theorem exactOn_closedWalkSums {V : Type*} {G : SimpleGraph V} (ω : DiscreteOneForm V)
    (hex : IsExactOn G ω) : ClosedWalkSums G ω := by
  rcases hex with ⟨Φ, hΦ⟩
  intro u c
  rw [cycleSum, walkSum_exact_on ω hΦ c]
  ring

theorem closedWalkSums_exactOn {V : Type*} {G : SimpleGraph V} (hG : G.Connected)
    (ω : DiscreteOneForm V) (hclosed : ClosedWalkSums G ω) : IsExactOn G ω := by
  let v₀ : V := Classical.choice hG.nonempty
  let chosenWalk : ∀ x : V, G.Walk v₀ x := fun x => Classical.choice (hG v₀ x)
  let Φ : V → ℝ := fun x => walkSum ω (chosenWalk x)
  refine ⟨Φ, fun u v huv => ?_⟩
  have hpi : walkSum ω (chosenWalk v) = walkSum ω ((chosenWalk u).append (.cons huv .nil)) :=
    discrete_pathIndependent ω hclosed (chosenWalk v) ((chosenWalk u).append (.cons huv .nil))
  simp only [walkSum_append, walkSum_cons, walkSum_nil, add_zero] at hpi
  dsimp [Φ, d0]
  linarith

/-- **Discrete Global Exactness Theorem (Closed Walks)**:
On any connected simple graph `G`, `ω` is exact on `G` iff every closed walk sum vanishes. -/
theorem discrete_exact_iff_closed_walk_sum {V : Type*} {G : SimpleGraph V}
    (hG : G.Connected) (ω : DiscreteOneForm V) :
    IsExactOn G ω ↔ ClosedWalkSums G ω :=
  ⟨exactOn_closedWalkSums ω, closedWalkSums_exactOn hG ω⟩

/-- **Discrete Global Exactness Theorem (Simple Cycles)**:
On any connected simple graph `G` (and in particular any connected finite graph `[Fintype V]`),
a discrete 1-form `ω` is exact (`∃ Φ, ∀ u v, G.Adj u v → ω u v = Φ v - Φ u`) if and only if
every simple cycle sum vanishes. -/
theorem discrete_exact_iff_zero_cycle_sum {V : Type*} {G : SimpleGraph V}
    (hG : G.Connected) (ω : DiscreteOneForm V) :
    IsExactOn G ω ↔ ZeroSimpleCycleSums G ω := by
  rw [discrete_exact_iff_closed_walk_sum hG ω, closedWalkSums_iff_zeroSimpleCycleSums]

/-- Explicit finite-graph specialization of `discrete_exact_iff_zero_cycle_sum`. -/
theorem finite_graph_discrete_exact_iff_zero_cycle_sum {V : Type*} [Fintype V]
    {G : SimpleGraph V} (hG : G.Connected) (ω : DiscreteOneForm V) :
    IsExactOn G ω ↔ ZeroSimpleCycleSums G ω :=
  discrete_exact_iff_zero_cycle_sum hG ω

/-- Global exactness on all vertex pairs (`ω = d0 Φ`) iff all simple cycles on the complete
graph `⊤ : SimpleGraph V` have zero sum. -/
theorem complete_discrete_exact_iff_zero_cycle_sum {V : Type*} [Nonempty V]
    (ω : DiscreteOneForm V) :
    IsExact ω ↔ ZeroSimpleCycleSums (⊤ : SimpleGraph V) ω := by
  rw [isExact_iff_isExactOn_top]
  exact discrete_exact_iff_zero_cycle_sum SimpleGraph.connected_top ω

/-- Any closed walk with nonzero `cycleSum` immediately obstructs exactness on `G`. -/
theorem not_isExactOn_of_nonzero_cycle_sum {V : Type*} {G : SimpleGraph V}
    {ω : DiscreteOneForm V} {u : V} (c : G.Walk u u) (hc : cycleSum ω c ≠ 0) :
    ¬ IsExactOn G ω := by
  intro hex
  exact hc (exactOn_closedWalkSums ω hex u c)

/-- Along any walk whose darts all have strictly positive `ω` value, any strict order
potential `Φ` (`∀ x y, 0 < ω x y → Φ x < Φ y`) must strictly increase from start to end
provided the walk is non-empty. -/
theorem strict_potential_walk_lt {V : Type*} {G : SimpleGraph V}
    {ω : DiscreteOneForm V} {Φ : V → ℝ}
    (hΦ : ∀ x y : V, 0 < ω x y → Φ x < Φ y) :
    ∀ {u v : V} (p : G.Walk u v), ¬ p.Nil →
      (∀ d ∈ p.darts, 0 < ω d.fst d.snd) → Φ u < Φ v
  | _, _, .nil, hnil, _ => absurd SimpleGraph.Walk.nil_nil hnil
  | u, _, .cons (v := v) h₁ .nil, _, hpos => by
      have h0 : 0 < ω u v := hpos ⟨(u, v), h₁⟩ (by simp)
      exact hΦ u v h0
  | u, w, .cons (v := v) h₁ (.cons h₂ q), _, hpos => by
      have h0 : 0 < ω u v := hpos ⟨(u, v), h₁⟩ (by simp)
      have htail : Φ v < Φ w :=
        strict_potential_walk_lt hΦ (.cons h₂ q) SimpleGraph.Walk.not_nil_cons
          (fun d hd => hpos d (List.mem_cons_of_mem _ hd))
      exact lt_trans (hΦ u v h0) htail

/-- Any non-empty closed walk with strictly positive step weights `0 < ω d.fst d.snd`
rules out *any* strict scalar order potential `Φ : V → ℝ`, not merely additive coboundaries. -/
theorem no_strict_potential_of_positive_cycle {V : Type*} {G : SimpleGraph V}
    {ω : DiscreteOneForm V} {u : V} (c : G.Walk u u) (hc_ne : ¬ c.Nil)
    (hpos : ∀ d ∈ c.darts, 0 < ω d.fst d.snd) :
    ¬ ∃ Φ : V → ℝ, ∀ x y : V, 0 < ω x y → Φ x < Φ y := by
  rintro ⟨Φ, hΦ⟩
  have hlt : Φ u < Φ u := strict_potential_walk_lt hΦ c hc_ne hpos
  exact lt_irrefl (Φ u) hlt

/-! ## 4. Condorcet 3-Cycle Non-Integrability (`condorcet_3cycle_nonintegrable`) -/

/-- Pairwise preference weight matrix for a Condorcet 3-alternative cycle
`0 → 1 → 2 → 0` on `Fin 3`. -/
def condorcetWeight (u v : Fin 3) : ℝ :=
  if (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 0) then 1
  else if (u = 1 ∧ v = 0) ∨ (u = 2 ∧ v = 1) ∨ (u = 0 ∧ v = 2) then -1
  else 0

/-- Antisymmetric discrete 1-form realizing the Condorcet 3-alternative cycle on `Fin 3`. -/
def condorcetThreeCycleForm : DiscreteOneForm (Fin 3) where
  toFun := condorcetWeight
  skew u v := by
    fin_cases u <;> fin_cases v <;> simp [condorcetWeight, Fin.ext_iff]

@[simp]
theorem condorcetThreeCycleForm_apply (u v : Fin 3) :
    condorcetThreeCycleForm u v = condorcetWeight u v := rfl

/-- The directed 3-cycle `0 → 1 → 2 → 0` in the complete graph `⊤ : SimpleGraph (Fin 3)`. -/
def condorcetCycleWalk : (⊤ : SimpleGraph (Fin 3)).Walk 0 0 :=
  .cons (by decide : (⊤ : SimpleGraph (Fin 3)).Adj 0 1)
    (.cons (by decide : (⊤ : SimpleGraph (Fin 3)).Adj 1 2)
      (.cons (by decide : (⊤ : SimpleGraph (Fin 3)).Adj 2 0) .nil))

theorem condorcetCycleWalk_isCycle : condorcetCycleWalk.IsCycle := by
  have h01 : (⊤ : SimpleGraph (Fin 3)).Adj 0 1 := by decide
  have h12 : (⊤ : SimpleGraph (Fin 3)).Adj 1 2 := by decide
  have h20 : (⊤ : SimpleGraph (Fin 3)).Adj 2 0 := by decide
  change (SimpleGraph.Walk.cons h01 (.cons h12 (.cons h20 .nil))).IsCycle
  rw [SimpleGraph.Walk.cons_isCycle_iff]
  refine ⟨?_, ?_⟩
  · rw [SimpleGraph.Walk.isPath_def]
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil]
    decide
  · simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.mem_cons,
      List.not_mem_nil, or_false, Sym2.eq_iff]
    decide

theorem condorcetCycleWalk_sum :
    cycleSum condorcetThreeCycleForm condorcetCycleWalk = 3 := by
  norm_num [cycleSum, walkSum, condorcetCycleWalk, condorcetWeight]

/-- **Condorcet 3-Cycle Non-Integrability Obstruction**:
For the concrete 3-alternative cycle `0 → 1 → 2 → 0` (`ω 0 1 = ω 1 2 = ω 2 0 = 1`):
1. `condorcetCycleWalk` is a simple cycle with `cycleSum = 3 ≠ 0`;
2. `condorcetThreeCycleForm` is neither exact on `⊤ : SimpleGraph (Fin 3)` (`¬ IsExactOn ⊤ ω`)
   nor globally exact (`¬ IsExact ω`);
3. No strict scalar preference potential `Φ : Fin 3 → ℝ` (`∀ u v, 0 < ω u v → Φ u < Φ v`) exists. -/
theorem condorcet_3cycle_nonintegrable :
    cycleSum condorcetThreeCycleForm condorcetCycleWalk = 3 ∧
      condorcetCycleWalk.IsCycle ∧
      ¬ IsExactOn (⊤ : SimpleGraph (Fin 3)) condorcetThreeCycleForm ∧
      ¬ IsExact condorcetThreeCycleForm ∧
      ¬ ∃ Φ : Fin 3 → ℝ, ∀ u v : Fin 3, 0 < condorcetThreeCycleForm u v → Φ u < Φ v := by
  have hsum : cycleSum condorcetThreeCycleForm condorcetCycleWalk = 3 :=
    condorcetCycleWalk_sum
  have hne : cycleSum condorcetThreeCycleForm condorcetCycleWalk ≠ 0 := by
    rw [hsum]
    norm_num
  have hnot_exact_on : ¬ IsExactOn (⊤ : SimpleGraph (Fin 3)) condorcetThreeCycleForm :=
    not_isExactOn_of_nonzero_cycle_sum condorcetCycleWalk hne
  have hnot_exact : ¬ IsExact condorcetThreeCycleForm := by
    rw [isExact_iff_isExactOn_top]
    exact hnot_exact_on
  have hnot_strict : ¬ ∃ Φ : Fin 3 → ℝ,
      ∀ u v : Fin 3, 0 < condorcetThreeCycleForm u v → Φ u < Φ v := by
    apply no_strict_potential_of_positive_cycle condorcetCycleWalk
    · simp [condorcetCycleWalk]
    · intro d hd
      simp only [condorcetCycleWalk, SimpleGraph.Walk.darts_cons, SimpleGraph.Walk.darts_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl <;> norm_num [condorcetWeight]
  exact ⟨hsum, condorcetCycleWalk_isCycle, hnot_exact_on, hnot_exact, hnot_strict⟩

end UEOTPhysicsUnification.DiscretePreferenceCochainObstruction
