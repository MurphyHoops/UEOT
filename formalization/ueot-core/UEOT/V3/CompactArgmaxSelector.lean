import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Measurable argmax selector on a compact metric action space

Mathlib at the pinned UEOT toolchain does not expose the general measurable
selection theorem used in the paper proof of P-CTL-02. This module proves the
special case needed there from first principles.

For a jointly continuous real objective on X × A, with A compact metric and
nonempty, a fixed dense sequence supplies shrinking closed balls that meet the
argmax set. The first admissible dense center is chosen measurably at each
scale. Consecutive centers have a summable distance bound, hence converge; the
limit is measurable and remains in the closed argmax set.

No measurable selector or argmax theorem is assumed as an input.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology

noncomputable section

namespace UEOT.V3.CompactArgmaxSelector

variable {X A : Type*}
variable [MetricSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X]
variable [MetricSpace A] [CompactSpace A] [Nonempty A]
variable [MeasurableSpace A] [BorelSpace A]

def radius (n : ℕ) : ℝ := (1 : ℝ) / 4 / 2 ^ n

lemma radius_pos (n : ℕ) : 0 < radius n := by
  unfold radius
  exact div_pos (by norm_num) (pow_pos (by norm_num) n)

lemma summable_radius : Summable (radius : ℕ → ℝ) := by
  have h :
      (radius : ℕ → ℝ) = fun n => (1 / 2 : ℝ) / 2 / 2 ^ n := by
    funext n
    simp [radius]
    ring
  rw [h]
  exact summable_geometric_two' (1 / 2 : ℝ)

def globalMax (q : X → A → ℝ) (x : X) : ℝ :=
  sSup (q x '' (Set.univ : Set A))

def localMax (q : X → A → ℝ) (n k : ℕ) (x : X) : ℝ :=
  sSup (q x '' Metric.closedBall (denseSeq A k) (radius n))

lemma continuous_globalMax {q : X → A → ℝ}
    (hq : Continuous ↿q) :
    Continuous (globalMax q) := by
  change Continuous fun x => sSup (q x '' (Set.univ : Set A))
  exact isCompact_univ.continuous_sSup (f := q) hq

lemma compact_closedBall (c : A) (r : ℝ) :
    IsCompact (Metric.closedBall c r) :=
  Metric.isClosed_closedBall.isCompact

lemma continuous_localMax {q : X → A → ℝ}
    (hq : Continuous ↿q) (n k : ℕ) :
    Continuous (localMax q n k) := by
  change Continuous fun x =>
    sSup (q x '' Metric.closedBall (denseSeq A k) (radius n))
  exact (compact_closedBall (denseSeq A k) (radius n)).continuous_sSup
    (f := q) hq

lemma exists_global_argmax {q : X → A → ℝ}
    (hq : Continuous ↿q) (x : X) :
    ∃ a : A, globalMax q x = q x a ∧
      ∀ b : A, q x b ≤ q x a := by
  obtain ⟨a, _ha, hmax, hge⟩ :=
    isCompact_univ.exists_sSup_image_eq_and_ge Set.univ_nonempty
      (show Continuous (q x) from hq.comp (.prodMk_right x)).continuousOn
  exact ⟨a, by simpa [globalMax] using hmax, fun b => hge b (by simp)⟩

lemma hit_iff_exists_argmax_in_closedBall {q : X → A → ℝ}
    (hq : Continuous ↿q) (n k : ℕ) (x : X) :
    localMax q n k x = globalMax q x ↔
      ∃ a ∈ Metric.closedBall (denseSeq A k) (radius n),
        q x a = globalMax q x := by
  constructor
  · intro hhit
    have hcompact := compact_closedBall (denseSeq A k) (radius n)
    have hnonempty : (Metric.closedBall (denseSeq A k) (radius n)).Nonempty :=
      ⟨denseSeq A k, by simp [radius_pos n |>.le]⟩
    obtain ⟨a, ha, hlocal, _⟩ :=
      hcompact.exists_sSup_image_eq_and_ge hnonempty
        (show Continuous (q x) from hq.comp (.prodMk_right x)).continuousOn
    refine ⟨a, ha, ?_⟩
    rw [← hhit]
    simpa [localMax] using hlocal.symm
  · rintro ⟨a, ha, haMax⟩
    have hcompact := compact_closedBall (denseSeq A k) (radius n)
    have hnonempty : (Metric.closedBall (denseSeq A k) (radius n)).Nonempty := ⟨a, ha⟩
    obtain ⟨b, hb, hlocal, hge⟩ :=
      hcompact.exists_sSup_image_eq_and_ge hnonempty
        (show Continuous (q x) from hq.comp (.prodMk_right x)).continuousOn
    obtain ⟨g, hgMax, hgGe⟩ := exists_global_argmax hq x
    have hab : q x a ≤ q x b := hge a ha
    have hbg : q x b ≤ q x g := hgGe b
    have hag : q x a = q x g := by
      simpa [haMax, hgMax]
    have hba : q x b = q x a := le_antisymm (hag ▸ hbg) hab
    calc
      localMax q n k x = q x b := by simpa [localMax] using hlocal
      _ = q x a := hba
      _ = globalMax q x := haMax

lemma exists_hit {q : X → A → ℝ}
    (hq : Continuous ↿q) (n : ℕ) (x : X) :
    ∃ k : ℕ, localMax q n k x = globalMax q x := by
  obtain ⟨a, haMax, _⟩ := exists_global_argmax hq x
  obtain ⟨k, hk⟩ :=
    (denseRange_denseSeq A).exists_dist_lt a (radius_pos n)
  refine ⟨k, (hit_iff_exists_argmax_in_closedBall hq n k x).2 ?_⟩
  refine ⟨a, ?_, haMax.symm⟩
  exact Metric.mem_closedBall'.2 (by simpa [dist_comm] using hk.le)

lemma measurableSet_hit {q : X → A → ℝ}
    (hq : Continuous ↿q) (n k : ℕ) :
    MeasurableSet {x : X | localMax q n k x = globalMax q x} := by
  exact measurableSet_eq_fun
    (continuous_localMax hq n k).measurable
    (continuous_globalMax hq).measurable

structure Approximation (q : X → A → ℝ) (n : ℕ) where
  index : X → ℕ
  measurable_index : Measurable index
  hit : ∀ x, localMax q n (index x) x = globalMax q x

noncomputable def initialApproximation {q : X → A → ℝ}
    (hq : Continuous ↿q) : Approximation q 0 := by
  classical
  let idx : X → ℕ := fun x => Nat.find (exists_hit hq 0 x)
  refine
    { index := idx
      measurable_index := ?_
      hit := ?_ }
  · unfold idx
    exact measurable_find
      (fun x => exists_hit hq 0 x)
      (fun k => measurableSet_hit hq 0 k)
  · intro x
    exact Nat.find_spec (exists_hit hq 0 x)

lemma exists_next_hit {q : X → A → ℝ}
    (hq : Continuous ↿q) {n : ℕ} (s : Approximation q n) (x : X) :
    ∃ k : ℕ,
      localMax q (n + 1) k x = globalMax q x ∧
        dist (denseSeq A k) (denseSeq A (s.index x)) <
          radius (n + 1) + radius n := by
  obtain ⟨z, hzBall, hzMax⟩ :=
    (hit_iff_exists_argmax_in_closedBall hq n (s.index x) x).1 (s.hit x)
  obtain ⟨k, hk⟩ :=
    (denseRange_denseSeq A).exists_dist_lt z (radius_pos (n + 1))
  refine ⟨k, ?_, ?_⟩
  · apply (hit_iff_exists_argmax_in_closedBall hq (n + 1) k x).2
    refine ⟨z, ?_, hzMax⟩
    exact Metric.mem_closedBall'.2 (by simpa [dist_comm] using hk.le)
  · have hzPrev : dist z (denseSeq A (s.index x)) ≤ radius n := by
      simpa [dist_comm] using (Metric.mem_closedBall'.1 hzBall)
    calc
      dist (denseSeq A k) (denseSeq A (s.index x))
          ≤ dist (denseSeq A k) z + dist z (denseSeq A (s.index x)) :=
            dist_triangle _ _ _
      _ < radius (n + 1) + radius n :=
        add_lt_add_of_lt_of_le (by simpa [dist_comm] using hk) hzPrev

lemma measurableSet_nextPredicate {q : X → A → ℝ}
    (hq : Continuous ↿q) {n : ℕ} (s : Approximation q n) (k : ℕ) :
    MeasurableSet
      {x : X |
        localMax q (n + 1) k x = globalMax q x ∧
          dist (denseSeq A k) (denseSeq A (s.index x)) <
            radius (n + 1) + radius n} := by
  have hDense : Measurable (denseSeq A) :=
    measurable_of_countable (denseSeq A)
  have hPrev : Measurable fun x : X => denseSeq A (s.index x) :=
    hDense.comp s.measurable_index
  have hDist :
      Measurable fun x : X => dist (denseSeq A k) (denseSeq A (s.index x)) :=
    Measurable.dist measurable_const hPrev
  exact (measurableSet_hit hq (n + 1) k).inter
    (measurableSet_lt hDist measurable_const)

noncomputable def nextApproximation {q : X → A → ℝ}
    (hq : Continuous ↿q) {n : ℕ} (s : Approximation q n) :
    Approximation q (n + 1) := by
  classical
  let idx : X → ℕ := fun x =>
    Nat.find (exists_next_hit hq s x)
  refine
    { index := idx
      measurable_index := ?_
      hit := ?_ }
  · unfold idx
    exact measurable_find
      (fun x => exists_next_hit hq s x)
      (fun k => measurableSet_nextPredicate hq s k)
  · intro x
    exact (Nat.find_spec (exists_next_hit hq s x)).1

noncomputable def approximations {q : X → A → ℝ}
    (hq : Continuous ↿q) : (n : ℕ) → Approximation q n
  | 0 => initialApproximation hq
  | n + 1 => nextApproximation hq (approximations hq n)

noncomputable def center {q : X → A → ℝ}
    (hq : Continuous ↿q) (n : ℕ) (x : X) : A :=
  denseSeq A ((approximations hq n).index x)

lemma measurable_center {q : X → A → ℝ}
    (hq : Continuous ↿q) (n : ℕ) :
    Measurable (center hq n) := by
  exact (measurable_of_countable (denseSeq A)).comp
    (approximations hq n).measurable_index

lemma center_hit {q : X → A → ℝ}
    (hq : Continuous ↿q) (n : ℕ) (x : X) :
    localMax q n ((approximations hq n).index x) x = globalMax q x :=
  (approximations hq n).hit x

lemma dist_center_succ_lt {q : X → A → ℝ}
    (hq : Continuous ↿q) (n : ℕ) (x : X) :
    dist (center hq (n + 1) x) (center hq n x) <
      radius (n + 1) + radius n := by
  change
    dist
      (denseSeq A ((approximations hq (n + 1)).index x))
      (denseSeq A ((approximations hq n).index x)) <
      radius (n + 1) + radius n
  simp only [approximations]
  exact (Nat.find_spec
    (exists_next_hit hq (approximations hq n) x)).2

lemma summable_radius_add_succ :
    Summable fun n => radius (n + 1) + radius n := by
  exact (summable_radius.comp_injective Nat.succ_injective).add summable_radius

lemma cauchy_center {q : X → A → ℝ}
    (hq : Continuous ↿q) (x : X) :
    CauchySeq fun n => center hq n x := by
  apply cauchySeq_of_dist_le_of_summable
    (fun n => radius (n + 1) + radius n)
  · intro n
    simpa [dist_comm] using (dist_center_succ_lt hq n x).le
  · exact summable_radius_add_succ

noncomputable def selector {q : X → A → ℝ}
    (hq : Continuous ↿q) (x : X) : A :=
  Classical.choose (cauchySeq_tendsto_of_complete (cauchy_center hq x))

lemma center_tendsto_selector {q : X → A → ℝ}
    (hq : Continuous ↿q) (x : X) :
    Tendsto (fun n => center hq n x) atTop (𝓝 (selector hq x)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete (cauchy_center hq x))

lemma measurable_selector {q : X → A → ℝ}
    (hq : Continuous ↿q) :
    Measurable (selector hq) := by
  apply measurable_of_tendsto_metrizable (fun n => measurable_center hq n)
  exact tendsto_pi_nhds.mpr (fun x => center_tendsto_selector hq x)

noncomputable def argmaxWitness {q : X → A → ℝ}
    (hq : Continuous ↿q) (n : ℕ) (x : X) : A :=
  Classical.choose <|
    (hit_iff_exists_argmax_in_closedBall hq n
      ((approximations hq n).index x) x).1 (center_hit hq n x)

lemma argmaxWitness_mem {q : X → A → ℝ}
    (hq : Continuous ↿q) (n : ℕ) (x : X) :
    argmaxWitness hq n x ∈
      Metric.closedBall (center hq n x) (radius n) := by
  exact (Classical.choose_spec <|
    (hit_iff_exists_argmax_in_closedBall hq n
      ((approximations hq n).index x) x).1 (center_hit hq n x)).1

lemma argmaxWitness_max {q : X → A → ℝ}
    (hq : Continuous ↿q) (n : ℕ) (x : X) :
    q x (argmaxWitness hq n x) = globalMax q x := by
  exact (Classical.choose_spec <|
    (hit_iff_exists_argmax_in_closedBall hq n
      ((approximations hq n).index x) x).1 (center_hit hq n x)).2

lemma argmaxWitness_tendsto_selector {q : X → A → ℝ}
    (hq : Continuous ↿q) (x : X) :
    Tendsto (fun n => argmaxWitness hq n x) atTop (𝓝 (selector hq x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨Nc, hNc⟩ :=
    (Metric.tendsto_atTop.mp (center_tendsto_selector hq x))
      (ε / 2) (half_pos hε)
  have hr0 : Tendsto (radius : ℕ → ℝ) atTop (𝓝 (0 : ℝ)) :=
    summable_radius.tendsto_atTop_zero
  obtain ⟨Nr, hNr⟩ :=
    (Metric.tendsto_atTop.mp hr0) (ε / 2) (half_pos hε)
  refine ⟨max Nc Nr, ?_⟩
  intro n hn
  have hnC : Nc ≤ n := le_trans (le_max_left _ _) hn
  have hnR : Nr ≤ n := le_trans (le_max_right _ _) hn
  have hc : dist (center hq n x) (selector hq x) < ε / 2 :=
    hNc n hnC
  have hr : radius n < ε / 2 := by
    have h := hNr n hnR
    simpa [Real.dist_eq, abs_of_pos (radius_pos n)] using h
  have hwc :
      dist (argmaxWitness hq n x) (center hq n x) ≤ radius n := by
    simpa [Metric.mem_closedBall] using (argmaxWitness_mem hq n x)
  calc
    dist (argmaxWitness hq n x) (selector hq x)
        ≤ dist (argmaxWitness hq n x) (center hq n x) +
            dist (center hq n x) (selector hq x) :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hwc.trans_lt hr) hc
    _ = ε := by ring

lemma selector_attains_max {q : X → A → ℝ}
    (hq : Continuous ↿q) (x : X) :
    globalMax q x = q x (selector hq x) := by
  have hqcont : Continuous (q x) :=
    hq.comp (.prodMk_right x)
  have hlim :
      Tendsto (fun n => q x (argmaxWitness hq n x)) atTop
        (𝓝 (q x (selector hq x))) :=
    hqcont.continuousAt.tendsto.comp (argmaxWitness_tendsto_selector hq x)
  have hlim' :
      Tendsto (fun _ : ℕ => globalMax q x) atTop
        (𝓝 (q x (selector hq x))) := by
    simpa only [argmaxWitness_max] using hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim'

theorem measurable_argmax_selector {q : X → A → ℝ}
    (hq : Continuous ↿q) :
    ∃ π : X → A,
      Measurable π ∧
      ∀ x, q x (π x) = globalMax q x ∧
        ∀ a, q x a ≤ q x (π x) := by
  refine ⟨selector hq, measurable_selector hq, ?_⟩
  intro x
  have hsel := selector_attains_max hq x
  obtain ⟨a, ha, hge⟩ := exists_global_argmax hq x
  refine ⟨hsel.symm, ?_⟩
  intro b
  calc
    q x b ≤ q x a := hge b
    _ = globalMax q x := ha.symm
    _ = q x (selector hq x) := hsel

end UEOT.V3.CompactArgmaxSelector
