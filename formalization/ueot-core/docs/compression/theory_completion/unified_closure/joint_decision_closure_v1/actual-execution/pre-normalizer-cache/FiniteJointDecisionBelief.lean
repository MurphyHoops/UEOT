import Mathlib

/-!
# Finite rational filtering of one joint source

A belief has an explicitly finite atom enumeration, even when the hidden world
has an infinite ambient type.  Atoms retain the source index and all unobserved
state; observing a receipt conditions the SAME joint primitive, never independent
transition/observation/cost marginals.  All operations below are computable.
The zero-probability branch returns the prior as a documented off-path default.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteJointDecisionBelief

open scoped BigOperators

universe uW uA uO uZ

structure Belief (W : Type uW) where
  Atom : Type
  atoms : Fintype Atom
  state : Atom → W
  weight : Atom → ℚ
  nonneg : ∀ x, 0 ≤ weight x
  total : ∑ x, weight x = 1

attribute [instance] Belief.atoms

structure Source (W : Type uW) (A : Type uA) (O : Type uO) (Z : Type uZ)
    [Fintype Z] where
  chance : W → Z → ℚ
  nonneg : ∀ w z, 0 ≤ chance w z
  total : ∀ w, ∑ z, chance w z = 1
  next : W → A → Z → W
  observe : W → A → Z → O

variable {W : Type uW} {A : Type uA} {O : Type uO} {Z : Type}
variable [Fintype Z] [Fintype O] [DecidableEq O]

def expect (b : Belief W) (f : W → ℚ) : ℚ := ∑ x, b.weight x * f (b.state x)

@[simp] theorem expect_const (b : Belief W) (c : ℚ) : expect b (fun _ => c) = c := by
  rw [expect, ← Finset.sum_mul, b.total, one_mul]

def joint (K : Source W A O Z) (b : Belief W) (a : A) (o : O)
    (x : b.Atom × Z) : ℚ :=
  if K.observe (b.state x.1) a x.2 = o then b.weight x.1 * K.chance (b.state x.1) x.2 else 0

def mass (K : Source W A O Z) (b : Belief W) (a : A) (o : O) : ℚ :=
  ∑ x : b.Atom × Z, joint K b a o x

theorem joint_nonneg (K : Source W A O Z) (b : Belief W) (a : A) (o : O)
    (x : b.Atom × Z) : 0 ≤ joint K b a o x := by
  unfold joint
  split
  · exact mul_nonneg (b.nonneg _) (K.nonneg _ _)
  · exact le_rfl

theorem mass_nonneg (K : Source W A O Z) (b : Belief W) (a : A) (o : O) :
    0 ≤ mass K b a o := Finset.sum_nonneg fun x _ => joint_nonneg K b a o x

theorem mass_total (K : Source W A O Z) (b : Belief W) (a : A) :
    ∑ o, mass K b a o = 1 := by
  unfold mass
  rw [Finset.sum_comm]
  have hrow (x : b.Atom × Z) : (∑ o, joint K b a o x) =
      b.weight x.1 * K.chance (b.state x.1) x.2 := by simp [joint]
  simp_rw [hrow]
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, K.total, mul_one]
  exact b.total

theorem joint_zero (K : Source W A O Z) (b : Belief W) (a : A) (o : O)
    (h : mass K b a o = 0) (x : b.Atom × Z) : joint K b a o x = 0 := by
  apply le_antisymm
  · have hx : joint K b a o x ≤ mass K b a o :=
      Finset.single_le_sum (fun y _ => joint_nonneg K b a o y) (Finset.mem_univ x)
    simpa [h] using hx
  · exact joint_nonneg K b a o x

/-- Bayes update on (source index, hidden actual state), with an explicit
zero-mass default.  The enlarged finite atom type retains each primitive branch. -/
def posterior (K : Source W A O Z) (b : Belief W) (a : A) (o : O) : Belief W :=
  if h : mass K b a o = 0 then b else
  { Atom := b.Atom × Z
    atoms := inferInstance
    state := fun x => K.next (b.state x.1) a x.2
    weight := fun x => joint K b a o x / mass K b a o
    nonneg := fun x => div_nonneg (joint_nonneg K b a o x) (mass_nonneg K b a o)
    total := by
      rw [← Finset.sum_div]
      change mass K b a o / mass K b a o = 1
      exact div_self h }

/-- Exact joint-mass identity; it also holds at impossible observations. -/
theorem posterior_identity (K : Source W A O Z) (b : Belief W) (a : A) (o : O)
    (f : W → ℚ) :
    mass K b a o * expect (posterior K b a o) f =
      ∑ x : b.Atom × Z, joint K b a o x * f (K.next (b.state x.1) a x.2) := by
  by_cases h : mass K b a o = 0
  · simp only [h, zero_mul]
    symm
    exact Finset.sum_eq_zero fun x _ => by rw [joint_zero K b a o h x, zero_mul]
  · rw [posterior, dif_neg h]
    dsimp only [expect]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    field_simp

/-- Disintegration is derived from one joint primitive, including the
correlation of receipt, next state, fee and birth. -/
theorem total_expectation (K : Source W A O Z) (b : Belief W) (a : A)
    (f : O → W → ℚ) :
    (∑ o, mass K b a o * expect (posterior K b a o) (f o)) =
      ∑ x : b.Atom × Z, b.weight x.1 * K.chance (b.state x.1) x.2 *
        f (K.observe (b.state x.1) a x.2) (K.next (b.state x.1) a x.2) := by
  simp_rw [posterior_identity]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp [joint, ite_mul]

theorem expect_add (b : Belief W) (f g : W → ℚ) :
    expect b (fun w => f w + g w) = expect b f + expect b g := by
  simp [expect, mul_add, Finset.sum_add_distrib]

theorem expect_mul (b : Belief W) (c : ℚ) (f : W → ℚ) :
    expect b (fun w => c * f w) = c * expect b f := by
  simp only [expect, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Every positive posterior atom has an actual old atom and a compatible
primitive branch; zero observations do not manufacture support. -/
theorem posterior_supported (K : Source W A O Z) (b : Belief W) (a : A) (o : O)
    (h : mass K b a o ≠ 0) (P : W → Prop)
    (hp : ∀ x z, b.weight x ≠ 0 → K.chance (b.state x) z ≠ 0 →
      K.observe (b.state x) a z = o → P (K.next (b.state x) a z)) :
    ∀ x, (posterior K b a o).weight x ≠ 0 → P ((posterior K b a o).state x) := by
  rw [posterior, dif_neg h]
  intro x hx
  have hj : joint K b a o x ≠ 0 := by
    intro hz
    exact hx (by simp [hz])
  have ho : K.observe (b.state x.1) a x.2 = o := by
    by_contra hn
    exact hj (by simp [joint, hn])
  have hm : b.weight x.1 * K.chance (b.state x.1) x.2 ≠ 0 := by simpa [joint, ho] using hj
  exact hp x.1 x.2 (mul_ne_zero_iff.mp hm).1 (mul_ne_zero_iff.mp hm).2 ho

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteJointDecisionBelief
