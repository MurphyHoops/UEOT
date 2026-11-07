import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativePopulation
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteSourceGrowthControl

/-!
# Marked ancestry of actual source records

The left hand side is a sum over the records returned by `descendants`, whose
edges contain the real retained identity or new child identity and parent
pointer.  The right hand side is a finite marked Doob law.  `false` means
retention and `true` means strict new birth.  These marks are never conflated.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeLineage

open scoped BigOperators
open CoreRegenerativeSource CoreRegenerativeFeedback CoreRegenerativePopulation
open SourceCohortFeedback
open FiniteSourceGrowthControl.SourceConsumer
open UEOT.V3.Compression.PositiveEigenstructure

abbrev Mark := Bool × Kind

theorem retained_markedPath (t : ℕ) (old : Member) (status : Status) (body : Body) :
    markedPath (retainedMember t old status body) =
      markedPath old ++ [(false, diagnostic body)] := by
  simp [markedPath, retainedMember]

theorem newborn_markedPath (t : ℕ) (old : Member) (body : Body) :
    markedPath (newbornMember t old body) =
      markedPath old ++ [(true, diagnostic body)] := by
  simp [markedPath, newbornMember]

/-- Recursive value of the two real output slots, with their actual ancestry records. -/
def pathValue (p : Parameters) :
    (T : ℕ) → ℕ → Member → NoiseTree T → (List Mark → ℝ) → ℝ
  | 0, _, old, _, F => sourceValue p (diagnostic old.body) * F (markedPath old)
  | T + 1, t, old, w, F =>
    let r := programStep old.body w.1
    optionValue (fun body => pathValue p T (t + 1)
      (retainedMember t old r.status body) w.2.1 F) r.retained +
    optionValue (fun body => pathValue p T (t + 1)
      (newbornMember t old body) w.2.2 F) r.newborn

/-- The recursive quantity is exactly the weighted sum over actual descendant records. -/
theorem pathValue_eq_actual_descendants (p : Parameters) (T t : ℕ)
    (old : Member) (w : NoiseTree T) (F : List Mark → ℝ) :
    pathValue p T t old w F =
      ((descendants T t old w).map
        (fun m => sourceValue p (diagnostic m.body) * F (markedPath m))).sum := by
  induction T generalizing t old with
  | zero => simp [pathValue, descendants]
  | succ T ih =>
      simp only [pathValue, descendants, List.map_append, List.sum_append]
      generalize programStep old.body w.1 = r
      cases hr : r.retained <;> cases hb : r.newborn <;>
        simp [optionValue, ih]

def pathMean (p : Parameters) (T t : ℕ) (old : Member) (F : List Mark → ℝ) : ℝ :=
  expect (treeWeight p T) (fun w => pathValue p T t old w F)

theorem pathMean_eq_actual_descendants (p : Parameters) (T t : ℕ)
    (old : Member) (F : List Mark → ℝ) :
    pathMean p T t old F =
      ∑ w : NoiseTree T, treeWeight p T w *
        ((descendants T t old w).map
          (fun m => sourceValue p (diagnostic m.body) * F (markedPath m))).sum := by
  simp [pathMean, expect, pathValue_eq_actual_descendants]

theorem expect_option_path (p : Parameters) (T t : ℕ) (f : Body → Member)
    (o : Option Body) (F : List Mark → ℝ) :
    expect (treeWeight p T)
      (fun w => optionValue (fun body => pathValue p T t (f body) w F) o) =
      optionValue (fun body => pathMean p T t (f body) F) o := by
  cases o <;> simp [optionValue, pathMean, expect]

theorem pathMean_zero (p : Parameters) (t : ℕ) (old : Member) (F : List Mark → ℝ) :
    pathMean p 0 t old F = sourceValue p (diagnostic old.body) * F (markedPath old) := by
  simp [pathMean, expect, treeWeight, pathValue, NoiseTree]

theorem pathMean_succ (p : Parameters) (T t : ℕ) (old : Member) (F : List Mark → ℝ) :
    pathMean p (T + 1) t old F = ∑ z : Noise, noiseWeight p z *
      (optionValue (fun body => pathMean p T (t + 1)
        (retainedMember t old (programStep old.body z).status body) F)
          (programStep old.body z).retained +
      optionValue (fun body => pathMean p T (t + 1)
        (newbornMember t old body) F) (programStep old.body z).newborn) := by
  calc
    _ = ∑ z : Noise, noiseWeight p z *
        expect (productWeight (treeWeight p T) (treeWeight p T))
          (fun v =>
            optionValue (fun body => pathValue p T (t + 1)
              (retainedMember t old (programStep old.body z).status body) v.1 F)
                (programStep old.body z).retained +
            optionValue (fun body => pathValue p T (t + 1)
              (newbornMember t old body) v.2 F) (programStep old.body z).newborn) := by
      simp only [pathMean, expect, treeWeight, pathValue, productWeight]
      change (∑ w : Noise × (NoiseTree T × NoiseTree T),
        noiseWeight p w.1 * (treeWeight p T w.2.1 * treeWeight p T w.2.2) *
          (optionValue (fun body => pathValue p T (t + 1)
            (retainedMember t old (programStep old.body w.1).status body) w.2.1 F)
              (programStep old.body w.1).retained +
          optionValue (fun body => pathValue p T (t + 1)
            (newbornMember t old body) w.2.2 F) (programStep old.body w.1).newborn)) = _
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z _
      congr 1
      have h := product_expect_add (treeWeight p T) (treeWeight p T)
        (fun v => optionValue (fun body => pathValue p T (t + 1)
          (retainedMember t old (programStep old.body z).status body) v F)
            (programStep old.body z).retained)
        (fun v => optionValue (fun body => pathValue p T (t + 1)
          (newbornMember t old body) v F) (programStep old.body z).newborn)
      simpa only [treeWeight_total, mul_one, one_mul, expect_option_path] using h

def markedMeanRow (p : Parameters) (i : Kind) (mark : Bool) (j : Kind) : ℝ :=
  (if mark then birthRate p (programAction true i)
    else survivalRate p (programAction true i)) * damageWeight p j

theorem markedMeanRow_sum (p : Parameters) (i j : Kind) :
    (∑ mark : Bool, markedMeanRow p i mark j) = programRow p true i j := by
  simp [markedMeanRow, programRow, row, countRate]
  ring

theorem retainedCount_test (a : Action) (z : Noise) (f : Kind → ℝ) :
    (∑ j : Kind, (retainedCount a z j : ℝ) * f j) =
      (if retains a z then f z.2.1 else 0) := by
  cases hr : retains a z <;> cases hdp : z.2.1 <;>
    simp [retainedCount, hr, hdp]

theorem newbornCount_test (a : Action) (z : Noise) (f : Kind → ℝ) :
    (∑ j : Kind, (newbornCount a z j : ℝ) * f j) =
      (if births a z then f z.2.2 else 0) := by
  cases hb : births a z <;> cases hdc : z.2.2 <;>
    simp [newbornCount, hb, hdc]

theorem noise_expected_retained (p : Parameters) (a : Action) (f : Kind → ℝ) :
    (∑ z : Noise, noiseWeight p z * (if retains a z then f z.2.1 else 0)) =
      ∑ j : Kind, (survivalRate p a * damageWeight p j) * f j := by
  simp_rw [← retainedCount_test a _ f, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = retainedMean p a j * f j := by
      rw [retainedMean, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = _ := by rw [retainedMean_eq]

theorem noise_expected_newborn (p : Parameters) (a : Action) (f : Kind → ℝ) :
    (∑ z : Noise, noiseWeight p z * (if births a z then f z.2.2 else 0)) =
      ∑ j : Kind, (birthRate p a * damageWeight p j) * f j := by
  simp_rw [← newbornCount_test a _ f, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = newbornMean p a j * f j := by
      rw [newbornMean, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = _ := by rw [newbornMean_eq]

theorem noise_expected_marked (p : Parameters) (i : Kind) (f : Bool → Kind → ℝ) :
    (∑ z : Noise, noiseWeight p z *
      ((if retains (programAction true i) z then f false z.2.1 else 0) +
       (if births (programAction true i) z then f true z.2.2 else 0))) =
      ∑ mark : Bool, ∑ j : Kind, markedMeanRow p i mark j * f mark j := by
  simp only [mul_add, Finset.sum_add_distrib]
  rw [noise_expected_retained, noise_expected_newborn]
  simp [markedMeanRow, add_comm]

/-- A finite path functional generated by the proved marked first moments. -/
def lineageMass (p : Parameters) : ℕ → Kind → List Mark → (List Mark → ℝ) → ℝ
  | 0, i, prefix, F => sourceValue p i * F prefix
  | T + 1, i, prefix, F => ∑ mark : Bool, ∑ j : Kind,
      markedMeanRow p i mark j * lineageMass p T j (prefix ++ [(mark, j)]) F

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeLineage
