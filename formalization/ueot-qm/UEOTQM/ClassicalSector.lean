import UEOTQM.Mixture
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Finite classical states and purification obstruction

The allowed state space is the entire finite probability simplex. Composite
systems use the entire simplex on the product and discarding is the actual
finite marginal. These are an explicit classical interpretation, not consequences
that the generic Core is claimed to force. Purity is defined as convex extremality.
-/

namespace UEOTQM.Classical

open scoped BigOperators _root_.Classical

noncomputable section

universe u v w

abbrev State (X : Type u) [Fintype X] := Mixture.Weights X

/-- All bounded classical response functions are allowed in this interpretation. -/
structure Effect (X : Type u) where
  response : X → ℝ
  nonneg : ∀ x, 0 ≤ response x
  le_one : ∀ x, response x ≤ 1

variable {X : Type u} {Y : Type v} {B : Type w}
  [Fintype X] [Fintype Y] [Fintype B]

@[ext] theorem state_ext {p q : State X}
    (h : ∀ x, p.weight x = q.weight x) : p = q := by
  cases p
  cases q
  congr
  exact funext h

/-- The classical state/effect pairing is the actual finite expectation. -/
def evaluate (p : State X) (e : Effect X) : ℝ :=
  ∑ x, p.weight x * e.response x

theorem evaluate_nonneg (p : State X) (e : Effect X) : 0 ≤ evaluate p e :=
  Finset.sum_nonneg fun x _ => mul_nonneg (p.nonneg x) (e.nonneg x)

theorem evaluate_le_one (p : State X) (e : Effect X) : evaluate p e ≤ 1 := by
  calc
    evaluate p e ≤ ∑ x, p.weight x :=
      Finset.sum_le_sum fun x _ => mul_le_of_le_one_right (p.nonneg x) (e.le_one x)
    _ = 1 := p.sum_one

def indicator (x : X) : Effect X where
  response z := if z = x then 1 else 0
  nonneg z := by split_ifs <;> norm_num
  le_one z := by split_ifs <;> norm_num

@[simp] theorem evaluate_indicator (p : State X) (x : X) :
    evaluate p (indicator x) = p.weight x := by
  simp [evaluate, indicator]

theorem all_effects_separate (p q : State X) :
    (∀ e : Effect X, evaluate p e = evaluate q e) ↔ p = q := by
  constructor
  · intro h
    exact state_ext fun x => by simpa using h (indicator x)
  · rintro rfl
    intro e
    rfl

def dirac (x : X) : State X := by
  classical
  exact ⟨fun z => if z = x then 1 else 0,
    fun z => by split_ifs <;> norm_num, by simp⟩

@[simp] theorem dirac_weight (x z : X) :
    (dirac x).weight z = if z = x then 1 else 0 := by
  classical
  rfl

@[simp] theorem evaluate_dirac (x : X) (e : Effect X) :
    evaluate (dirac x) e = e.response x := by
  simp [evaluate, dirac_weight]

def mix (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (p q : State X) : State X where
  weight x := t * p.weight x + (1-t) * q.weight x
  nonneg x := add_nonneg (mul_nonneg ht0 (p.nonneg x))
    (mul_nonneg (sub_nonneg.mpr ht1) (q.nonneg x))
  sum_one := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      p.sum_one, q.sum_one]
    ring

@[simp] theorem mix_weight (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (p q : State X) (x : X) :
    (mix t ht0 ht1 p q).weight x = t*p.weight x + (1-t)*q.weight x := rfl

def halfMix (p q : State X) : State X := mix (1/2) (by norm_num) (by norm_num) p q

@[simp] theorem halfMix_weight (p q : State X) (x : X) :
    (halfMix p q).weight x = (p.weight x + q.weight x) / 2 := by
  simp only [halfMix, mix_weight]
  ring

def pushforward (f : X → Y) (p : State X) : State Y := by
  classical
  refine ⟨fun y => ∑ x, if f x = y then p.weight x else 0, ?_, ?_⟩
  · intro y
    exact Finset.sum_nonneg fun x _ => by split_ifs <;> simp_all [p.nonneg]
  · rw [Finset.sum_comm]
    simpa using p.sum_one

@[simp] theorem pushforward_weight (f : X → Y) (p : State X) (y : Y) :
    (pushforward f p).weight y = ∑ x, if f x = y then p.weight x else 0 := by
  classical
  rfl

theorem pushforward_dirac (f : X → Y) (x : X) :
    pushforward f (dirac x) = dirac (f x) := by
  classical
  apply state_ext
  intro y
  simp only [pushforward_weight, dirac_weight]
  calc
    (∑ z, if f z = y then (if z = x then (1 : ℝ) else 0) else 0) =
        ∑ z, if z = x then (if f x = y then (1 : ℝ) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : z = x
      · subst z; simp
      · simp [hz]
    _ = if y = f x then 1 else 0 := by simp [eq_comm]

theorem pushforward_halfMix (f : X → Y) (p q : State X) :
    pushforward f (halfMix p q) = halfMix (pushforward f p) (pushforward f q) := by
  classical
  apply state_ext
  intro y
  simp only [pushforward_weight, halfMix_weight]
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> ring

def marginalLeft (p : State (X × B)) : State X where
  weight x := ∑ b, p.weight (x,b)
  nonneg x := Finset.sum_nonneg fun b _ => p.nonneg (x,b)
  sum_one := by rw [← Fintype.sum_prod_type]; exact p.sum_one

@[simp] theorem marginalLeft_weight (p : State (X × B)) (x : X) :
    (marginalLeft p).weight x = ∑ b, p.weight (x,b) := rfl

theorem marginalLeft_eq_pushforward (p : State (X × B)) :
    marginalLeft p = pushforward Prod.fst p := by
  classical
  apply state_ext
  intro x
  change (∑ b, p.weight (x,b)) = ∑ z : X × B, if z.1 = x then p.weight z else 0
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp

theorem marginalLeft_dirac (x : X) (b : B) :
    marginalLeft (dirac (x,b)) = dirac x := by
  rw [marginalLeft_eq_pushforward, pushforward_dirac]

theorem marginalLeft_halfMix (p q : State (X × B)) :
    marginalLeft (halfMix p q) = halfMix (marginalLeft p) (marginalLeft q) := by
  rw [marginalLeft_eq_pushforward, pushforward_halfMix]
  rw [← marginalLeft_eq_pushforward, ← marginalLeft_eq_pushforward]

/-- Convex extremality in the whole allowed simplex, not in a reachable subset. -/
def IsPure (p : State X) : Prop :=
  ∀ (q r : State X) (t : ℝ), 0 < t → t < 1 →
    (∀ x, p.weight x = t*q.weight x + (1-t)*r.weight x) → q = p ∧ r = p

theorem dirac_isPure (x : X) : IsPure (dirac x) := by
  classical
  intro q r t ht0 ht1 heq
  have hz : ∀ y, y ≠ x → q.weight y = 0 ∧ r.weight y = 0 := by
    intro y hy
    have h := heq y
    simp only [dirac_weight, if_neg hy] at h
    have hq := mul_nonneg (le_of_lt ht0) (q.nonneg y)
    have hr := mul_nonneg (sub_nonneg.mpr (le_of_lt ht1)) (r.nonneg y)
    have hh := (add_eq_zero_iff_of_nonneg hq hr).mp h.symm
    exact ⟨(mul_eq_zero.mp hh.1).resolve_left (ne_of_gt ht0),
      (mul_eq_zero.mp hh.2).resolve_left (ne_of_gt (sub_pos.mpr ht1))⟩
  have hqx : q.weight x = 1 := by
    calc
      q.weight x = ∑ y, q.weight y := by
        symm
        exact Finset.sum_eq_single x (fun y _ hy => (hz y hy).1) (by simp)
      _ = 1 := q.sum_one
  have hrx : r.weight x = 1 := by
    calc
      r.weight x = ∑ y, r.weight y := by
        symm
        exact Finset.sum_eq_single x (fun y _ hy => (hz y hy).2) (by simp)
      _ = 1 := r.sum_one
  constructor
  · apply state_ext
    intro y
    by_cases hy : y = x
    · subst y; simp [hqx]
    · simp [hy, (hz y hy).1]
  · apply state_ext
    intro y
    by_cases hy : y = x
    · subst y; simp [hrx]
    · simp [hy, (hz y hy).2]

theorem dirac_ne {x y : X} (hxy : x ≠ y) : dirac x ≠ dirac y := by
  classical
  intro h
  have hh := congrArg (fun p : State X => p.weight x) h
  simp [hxy] at hh

theorem halfMix_not_pure {x y : X} (hxy : x ≠ y) :
    ¬ IsPure (halfMix (dirac x) (dirac y)) := by
  intro hp
  have h := hp (dirac x) (dirac y) (1/2) (by norm_num) (by norm_num)
    (fun z => by simp only [halfMix_weight]; ring)
  exact dirac_ne hxy (h.1.trans h.2.symm)

/-- Actual conditional row at an event of mass one half. The input is only
the event mass, not purity or any desired extension obstruction. -/
def halfRow (p : State (X × B)) (x : X)
    (hx : (marginalLeft p).weight x = 1/2) : State (X × B) := by
  classical
  refine ⟨fun z => if z.1 = x then 2 * p.weight z else 0, ?_, ?_⟩
  · intro z
    split_ifs
    · exact mul_nonneg (by norm_num) (p.nonneg z)
    · exact le_rfl
  · calc
      (∑ z : X × B, if z.1 = x then 2*p.weight z else 0) =
          2 * ∑ b, p.weight (x,b) := by
        rw [Fintype.sum_prod_type, Finset.sum_comm]
        simp [Finset.mul_sum]
      _ = 1 := by
        change 2 * (marginalLeft p).weight x = 1
        rw [hx]
        norm_num

@[simp] theorem halfRow_weight (p : State (X × B)) (x : X)
    (hx : (marginalLeft p).weight x = 1/2) (z : X × B) :
    (halfRow p x hx).weight z = if z.1 = x then 2*p.weight z else 0 := by
  classical
  rfl

theorem marginalLeft_halfRow (p : State (X × B)) (x : X)
    (hx : (marginalLeft p).weight x = 1/2) :
    marginalLeft (halfRow p x hx) = dirac x := by
  classical
  apply state_ext
  intro z
  by_cases hz : z = x
  · subst z
    simp only [marginalLeft_weight, halfRow_weight, dirac_weight, ite_true]
    rw [← Finset.mul_sum]
    change 2 * (marginalLeft p).weight x = 1
    rw [hx]
    norm_num
  · simp [marginalLeft_weight, halfRow_weight, hz]

/-- A classical two-point mixture has no pure extension in ANY finite
auxiliary carrier. No nonempty-ancilla hypothesis is needed for this denial. -/
theorem no_pure_extension_halfMix {x y : X} (hxy : x ≠ y) :
    ¬ ∃ p : State (X × B), IsPure p ∧
      marginalLeft p = halfMix (dirac x) (dirac y) := by
  classical
  rintro ⟨p, hp, hm⟩
  have hx : (marginalLeft p).weight x = 1/2 := by
    rw [hm]
    simp [hxy]
  have hy : (marginalLeft p).weight y = 1/2 := by
    rw [hm]
    simp [Ne.symm hxy]
  let p0 := halfRow p x hx
  let p1 := halfRow p y hy
  have hz : ∀ z : X × B, z.1 ≠ x → z.1 ≠ y → p.weight z = 0 := by
    intro z hxz hyz
    have hmz : (marginalLeft p).weight z.1 = 0 := by
      rw [hm]
      simp [hxz, hyz]
    have hle : p.weight z ≤ (marginalLeft p).weight z.1 := by
      change p.weight (z.1,z.2) ≤ ∑ b, p.weight (z.1,b)
      exact Finset.single_le_sum (fun b _ => p.nonneg (z.1,b)) (Finset.mem_univ z.2)
    exact le_antisymm (hmz ▸ hle) (p.nonneg z)
  have hdecomp : ∀ z, p.weight z = (1/2)*p0.weight z + (1-1/2)*p1.weight z := by
    intro z
    dsimp [p0, p1]
    simp only [halfRow_weight]
    by_cases hxz : z.1 = x
    · have hyz : z.1 ≠ y := by simpa [hxz] using hxy
      simp only [if_pos hxz, if_neg hyz]
      ring
    · by_cases hyz : z.1 = y
      · simp only [if_neg hxz, if_pos hyz]
        ring
      · simp [hxz, hyz, hz z hxz hyz]
  have heq := (hp p0 p1 (1/2) (by norm_num) (by norm_num) hdecomp).1
  have hm0 : marginalLeft p0 = dirac x := marginalLeft_halfRow p x hx
  rw [heq, hm] at hm0
  have hf := congrArg (fun q : State X => q.weight y) hm0
  simp [Ne.symm hxy] at hf

/-- Dropping purity leaves a valid ordinary extension whenever an auxiliary
point is supplied. This keeps extension existence distinct from purification. -/
def attach (p : State X) (b : B) : State (X × B) :=
  pushforward (fun x => (x,b)) p

theorem marginalLeft_attach (p : State X) (b : B) :
    marginalLeft (attach p b) = p := by
  classical
  apply state_ext
  intro x
  simp only [marginalLeft_weight, attach, pushforward_weight]
  rw [Finset.sum_comm]
  calc
    _ = ∑ y, if y = x then p.weight y else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y = x
      · subst y; simp
      · simp [Prod.mk.injEq, hy]
    _ = p.weight x := by simp

theorem dirac_has_pure_extension (x : X) (b : B) :
    ∃ p : State (X × B), IsPure p ∧ marginalLeft p = dirac x :=
  ⟨dirac (x,b), dirac_isPure (x,b), marginalLeft_dirac x b⟩

end

end UEOTQM.Classical
