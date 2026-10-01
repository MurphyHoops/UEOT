import UEOT.V3.Compression.TopologyChangingGoaInvariantUniquenessIsolation
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Finite deterministic functional-graph classification for Track S

This module gives a structural interpretation of the canonical Track-S residual
isolation certificate for arbitrary finite deterministic maps. It separates the
transient functional-graph part from the recurrent periodic core, proves that
zero-mass residual injectivity is equivalent to having exactly one recurrent
periodic orbit, and then combines that classification with the general finite-
Markov uniqueness theorem to identify unique invariant semantics with the same
functional-graph condition.

The module also records the sharp deterministic Dobrushin dichotomy: a constant
map has coefficient zero, while any deterministic map with two distinct images
has coefficient one. Thus one-step contraction cannot distinguish most
deterministic recurrent structures, whereas the residual conorm does.

This is post-FINAL, uncounted Track-S research.
-/

namespace UEOT.V3.Compression.TopologyChangingGoaFunctionalGraphClassification

open Function
open UEOT.V3
open UEOT.V3.Compression.TopologyChangingGoaSpectralIsolation
open UEOT.V3.Compression.TopologyChangingGoaRestrictedResidualAdapter
open UEOT.V3.Compression.TopologyChangingGoaL1ResidualConorm

universe u
noncomputable section
variable {S : Type u} [Fintype S] [Nonempty S]
noncomputable local instance : DecidableEq S := Classical.decEq S
local instance : MeasurableSpace S := ⊤

def detKernel (f : S → S) : Matrix S S ℝ :=
  fun i j => if j = f i then 1 else 0

theorem detKernel_stochastic (f : S → S) :
    detKernel f ∈ Matrix.rowStochastic ℝ S := by
  rw [Matrix.mem_rowStochastic_iff_sum]
  constructor
  · intro i j
    by_cases h : j = f i <;> simp [detKernel, h]
  · intro i
    simp [detKernel]

theorem vecMul_detKernel (f : S → S) (v : S → ℝ) (y : S) :
    Matrix.vecMul v (detKernel f) y =
      ∑ x ∈ Finset.univ.filter (fun x => f x = y), v x := by
  rw [Matrix.vecMul_apply_eq_sum]
  classical
  simp only [detKernel]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : f x = y
  · simp [h]
  · have h' : y ≠ f x := Ne.symm h
    simp [h, h']

theorem iterate_card_mem_periodicPts (f : S → S) (x : S) :
    f^[Fintype.card S] x ∈ periodicPts f := by
  let g : Fin (Fintype.card S + 1) → S := fun i => f^[i.1] x
  have hcard : Fintype.card S < Fintype.card (Fin (Fintype.card S + 1)) := by
    simp
  obtain ⟨i, j, hij, hg⟩ := Fintype.exists_ne_map_eq_of_card_lt g hcard
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · let p := j.1 - i.1
    have hp : 0 < p := Nat.sub_pos_of_lt hijlt
    have hper : IsPeriodicPt f p (f^[i.1] x) := by
      unfold IsPeriodicPt IsFixedPt
      calc
        f^[p] (f^[i.1] x) = f^[p + i.1] x := by rw [iterate_add_apply]
        _ = f^[j.1] x := by
          congr
          exact Nat.sub_add_cancel hijlt.le
        _ = f^[i.1] x := hg.symm
    have hi_card : i.1 ≤ Fintype.card S := Nat.le_of_lt_succ i.2
    have htarget : f^[Fintype.card S] x =
        f^[(Fintype.card S - i.1)] (f^[i.1] x) := by
      rw [← iterate_add_apply]
      congr
      exact (Nat.sub_add_cancel hi_card).symm
    rw [htarget]
    exact mk_mem_periodicPts hp (hper.apply_iterate _)
  · let p := i.1 - j.1
    have hp : 0 < p := Nat.sub_pos_of_lt hjilt
    have hper : IsPeriodicPt f p (f^[j.1] x) := by
      unfold IsPeriodicPt IsFixedPt
      calc
        f^[p] (f^[j.1] x) = f^[p + j.1] x := by rw [iterate_add_apply]
        _ = f^[i.1] x := by
          congr
          exact Nat.sub_add_cancel hjilt.le
        _ = f^[j.1] x := hg
    have hj_card : j.1 ≤ Fintype.card S := Nat.le_of_lt_succ j.2
    have htarget : f^[Fintype.card S] x =
        f^[(Fintype.card S - j.1)] (f^[j.1] x) := by
      rw [← iterate_add_apply]
      congr
      exact (Nat.sub_add_cancel hj_card).symm
    rw [htarget]
    exact mk_mem_periodicPts hp (hper.apply_iterate _)

theorem periodicPts_subset_range_iterate_card (f : S → S) :
    periodicPts f ⊆ Set.range (f^[Fintype.card S]) := by
  intro y hy
  let N := Nat.factorial (Fintype.card S)
  have hNpos : 0 < N := Nat.factorial_pos _
  have hyN : IsPeriodicPt f N y := isPeriodicPt_factorial_card_of_mem_periodicPts hy
  let M := N * Fintype.card S
  have hcardM : Fintype.card S ≤ M := by
    dsimp [M]
    have hNge : 1 ≤ N := hNpos
    simpa using Nat.mul_le_mul_right (Fintype.card S) hNge
  refine ⟨f^[M - Fintype.card S] y, ?_⟩
  rw [← iterate_add_apply]
  have hadd : Fintype.card S + (M - Fintype.card S) = M :=
    Nat.add_sub_of_le hcardM
  rw [hadd]
  dsimp [M]
  rw [mul_comm]
  change f^[Fintype.card S * N] y = y
  rw [iterate_mul]
  exact (hyN.iterate _).eq

theorem range_iterate_card_eq_periodicPts (f : S → S) :
    Set.range (f^[Fintype.card S]) = periodicPts f := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, rfl⟩
    exact iterate_card_mem_periodicPts f x
  · exact periodicPts_subset_range_iterate_card f

private theorem residual_zero_coord_eq_fiber_sum
    (f : S → S) (v : S → ℝ)
    (hres : signedResidual (detKernel f) v = 0) (y : S) :
    v y = ∑ x ∈ Finset.univ.filter (fun x => f x = y), v x := by
  have hy := congrFun hres y
  unfold signedResidual at hy
  change Matrix.vecMul v (detKernel f) y - v y = 0 at hy
  rw [vecMul_detKernel] at hy
  linarith

private theorem residual_zero_vanishes_outside_range
    (f : S → S) (v : S → ℝ)
    (hres : signedResidual (detKernel f) v = 0) :
    ∀ n y, y ∉ Set.range (f^[n]) → v y = 0 := by
  intro n
  induction n with
  | zero =>
      intro y hy
      exfalso
      apply hy
      exact ⟨y, by simp⟩
  | succ n ih =>
      intro y hy
      rw [residual_zero_coord_eq_fiber_sum f v hres y]
      apply Finset.sum_eq_zero
      intro x hx
      have hfx : f x = y := by
        simpa using (Finset.mem_filter.mp hx).2
      apply ih x
      intro hxrange
      rcases hxrange with ⟨z, hz⟩
      apply hy
      refine ⟨z, ?_⟩
      calc
        f^[n + 1] z = f (f^[n] z) := by
          simpa using Function.iterate_succ_apply' f n z
        _ = f x := congrArg f hz
        _ = y := hfx

theorem residual_zero_vanishes_off_periodic
    (f : S → S) (v : S → ℝ)
    (hres : signedResidual (detKernel f) v = 0)
    {y : S} (hy : y ∉ periodicPts f) :
    v y = 0 := by
  apply residual_zero_vanishes_outside_range f v hres (Fintype.card S) y
  rw [range_iterate_card_eq_periodicPts f]
  exact hy

end
end UEOT.V3.Compression.TopologyChangingGoaFunctionalGraphClassification

namespace UEOT.V3.Compression.TopologyChangingGoaFunctionalGraphClassification

open Function
open UEOT.V3
open UEOT.V3.Compression.TopologyChangingGoaSpectralIsolation
open UEOT.V3.Compression.TopologyChangingGoaRestrictedResidualAdapter
open UEOT.V3.Compression.TopologyChangingGoaL1ResidualConorm

universe u
noncomputable section
variable {S : Type u} [Fintype S] [Nonempty S]
noncomputable local instance : DecidableEq S := Classical.decEq S
local instance : MeasurableSpace S := ⊤

private theorem periodic_preimage_unique
    (f : S → S) {y : S} (hy : y ∈ periodicPts f) :
    ∃! x : S, x ∈ periodicPts f ∧ f x = y := by
  let N := Nat.factorial (Fintype.card S)
  have hNpos : 0 < N := Nat.factorial_pos _
  have hyN : y ∈ ptsOfPeriod f N := by
    exact (mem_periodicPts_iff_isPeriodicPt_factorial_card).1 hy
  have hbij := bijOn_ptsOfPeriod f hNpos
  rcases hbij.surjOn hyN with ⟨x, hxN, hxy⟩
  have hxper : x ∈ periodicPts f := by
    exact (mem_periodicPts_iff_isPeriodicPt_factorial_card).2 hxN
  refine ⟨x, ⟨hxper, hxy⟩, ?_⟩
  intro z hz
  have hzN : z ∈ ptsOfPeriod f N := by
    exact (mem_periodicPts_iff_isPeriodicPt_factorial_card).1 hz.1
  apply hbij.injOn hzN hxN
  exact hz.2.trans hxy.symm

private theorem periodic_apply
    (f : S → S) {x : S} (hx : x ∈ periodicPts f) :
    f x ∈ periodicPts f := by
  rw [mem_periodicPts_iff_isPeriodicPt_factorial_card] at hx ⊢
  exact hx.apply

theorem residual_zero_periodic_step
    (f : S → S) (v : S → ℝ)
    (hres : signedResidual (detKernel f) v = 0)
    {x : S} (hx : x ∈ periodicPts f) :
    v (f x) = v x := by
  let fiber := Finset.univ.filter (fun z => f z = f x)
  rw [residual_zero_coord_eq_fiber_sum f v hres (f x)]
  have hxfiber : x ∈ fiber := by simp [fiber]
  rw [show Finset.univ.filter (fun z => f z = f x) = fiber from rfl]
  apply Finset.sum_eq_single x
  · intro z hz hzx
    have hfz : f z = f x := by
      exact (Finset.mem_filter.mp hz).2
    by_cases hzper : z ∈ periodicPts f
    · have huniq := periodic_preimage_unique f (periodic_apply f hx)
      have hzx' : z = x := huniq.unique ⟨hzper, hfz⟩ ⟨hx, rfl⟩
      exact (hzx hzx').elim
    · exact residual_zero_vanishes_off_periodic f v hres hzper
  · intro hxnot
    exact (hxnot hxfiber).elim

theorem residual_zero_periodic_iterate
    (f : S → S) (v : S → ℝ)
    (hres : signedResidual (detKernel f) v = 0)
    {x : S} (hx : x ∈ periodicPts f) :
    ∀ n, v (f^[n] x) = v x := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      have hxn : f^[n] x ∈ periodicPts f := by
        have hxN := (mem_periodicPts_iff_isPeriodicPt_factorial_card).1 hx
        exact (mem_periodicPts_iff_isPeriodicPt_factorial_card).2 (hxN.apply_iterate n)
      rw [residual_zero_periodic_step f v hres hxn]
      exact ih

def HasUniquePeriodicOrbit (f : S → S) : Prop :=
  ∃ x : S, x ∈ periodicPts f ∧
    ∀ y : S, y ∈ periodicPts f → y ∈ periodicOrbit f x

theorem residual_zero_const_on_periodic_of_unique
    (f : S → S) (huniq : HasUniquePeriodicOrbit f)
    (v : S → ℝ) (hres : signedResidual (detKernel f) v = 0) :
    ∃ c : ℝ, ∀ y : S, y ∈ periodicPts f → v y = c := by
  rcases huniq with ⟨x, hx, hall⟩
  refine ⟨v x, ?_⟩
  intro y hy
  have hyorbit := hall y hy
  rw [mem_periodicOrbit_iff hx] at hyorbit
  rcases hyorbit with ⟨n, hn⟩
  rw [← hn]
  exact residual_zero_periodic_iterate f v hres hx n

theorem zero_sum_residual_kernel_trivial_of_unique_periodic_orbit
    (f : S → S) (huniq : HasUniquePeriodicOrbit f)
    (v : S → ℝ) (hv : (∑ s, v s) = 0)
    (hres : signedResidual (detKernel f) v = 0) :
    v = 0 := by
  classical
  rcases huniq with ⟨x0, hx0, hall⟩
  have huniq' : HasUniquePeriodicOrbit f := ⟨x0, hx0, hall⟩
  rcases residual_zero_const_on_periodic_of_unique f huniq' v hres with ⟨c, hc⟩
  let A : Finset S := Finset.univ.filter (fun y => y ∈ periodicPts f)
  have hxA : x0 ∈ A := by simp [A, hx0]
  have hApos : 0 < A.card := Finset.card_pos.mpr ⟨x0, hxA⟩
  have hvpiece : ∀ y : S, v y = if y ∈ periodicPts f then c else 0 := by
    intro y
    by_cases hy : y ∈ periodicPts f
    · simp [hy, hc y hy]
    · simp [hy, residual_zero_vanishes_off_periodic f v hres hy]
  have hsum : (A.card : ℝ) * c = 0 := by
    calc
      (A.card : ℝ) * c = ∑ _y ∈ A, c := by
        simp [nsmul_eq_mul, mul_comm]
      _ = ∑ y ∈ A, v y := by
        apply Finset.sum_congr rfl
        intro y hyA
        have hy : y ∈ periodicPts f := by simpa [A] using hyA
        symm
        exact hc y hy
      _ = ∑ y, v y := by
        have hout : ∀ y ∈ (Finset.univ : Finset S), y ∉ A → v y = 0 := by
          intro y hyu hyA
          have hy : y ∉ periodicPts f := by
            intro hyper
            apply hyA
            simp [A, hyper]
          exact residual_zero_vanishes_off_periodic f v hres hy
        exact Finset.sum_subset (by simp [A]) hout
      _ = 0 := hv
  have hc0 : c = 0 := by
    have hAreal : (0 : ℝ) < A.card := by exact_mod_cast hApos
    exact (mul_eq_zero.mp hsum).resolve_left (ne_of_gt hAreal)
  funext y
  by_cases hy : y ∈ periodicPts f
  · simp [hc y hy, hc0]
  · simpa using residual_zero_vanishes_off_periodic f v hres hy

end
end UEOT.V3.Compression.TopologyChangingGoaFunctionalGraphClassification

namespace UEOT.V3.Compression.TopologyChangingGoaFunctionalGraphClassification

open Function
open UEOT.V3
open UEOT.V3.Compression.TopologyChangingGoaSpectralIsolation
open UEOT.V3.Compression.TopologyChangingGoaRestrictedResidualAdapter
open UEOT.V3.Compression.TopologyChangingGoaL1ResidualConorm

universe u
noncomputable section
variable {S : Type u} [Fintype S] [Nonempty S]
noncomputable local instance : DecidableEq S := Classical.decEq S
local instance : MeasurableSpace S := ⊤

theorem detKernel_restricted_injective_of_unique_periodic_orbit
    (f : S → S) (huniq : HasUniquePeriodicOrbit f) :
    Function.Injective (zeroSumResidualLinear (detKernel f)) := by
  intro x y hxy
  have hmapzero : zeroSumResidualLinear (detKernel f) (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  let v : S → ℝ :=
    ((x - y : zeroSumEuclidean (S := S)) : EuclideanSpace ℝ S).ofLp
  have hvsum : (∑ s, v s) = 0 := by
    exact (zeroSum_mem_iff v).1 (by simpa [v] using (x - y).property)
  have hlinzero :
      residualEuclideanLinear (detKernel f) (WithLp.toLp 2 v) = 0 := by
    simpa [zeroSumResidualLinear, v] using hmapzero
  have hresCoord : signedResidual (detKernel f) v = 0 := by
    rw [← residualEuclideanLinear_ofLp]
    funext s
    have hs := congrArg (fun z : EuclideanSpace ℝ S => z.ofLp s) hlinzero
    simpa using hs
  have hvzero :=
    zero_sum_residual_kernel_trivial_of_unique_periodic_orbit
      f huniq v hvsum hresCoord
  have hsub : x - y = 0 := by
    apply Subtype.ext
    rw [WithLp.ext_iff]
    simpa [v] using hvzero
  exact sub_eq_zero.mp hsub

private theorem periodicOrbit_eq_of_mem
    (f : S → S) {x y : S} (hx : x ∈ periodicPts f)
    (hy : y ∈ periodicOrbit f x) :
    periodicOrbit f y = periodicOrbit f x := by
  rw [mem_periodicOrbit_iff hx] at hy
  rcases hy with ⟨n, rfl⟩
  exact periodicOrbit_apply_iterate_eq hx n

private theorem periodicOrbit_mem_apply_iff
    (f : S → S) {x z : S}
    (hx : x ∈ periodicPts f) (hz : z ∈ periodicPts f) :
    f z ∈ periodicOrbit f x ↔ z ∈ periodicOrbit f x := by
  constructor
  · intro hfz
    have hfxper : f z ∈ periodicPts f := periodic_apply f hz
    have horb_fz : periodicOrbit f (f z) = periodicOrbit f x :=
      periodicOrbit_eq_of_mem f hx hfz
    have horb_step : periodicOrbit f (f z) = periodicOrbit f z :=
      periodicOrbit_apply_eq hz
    have hzself : z ∈ periodicOrbit f z := self_mem_periodicOrbit hz
    rw [← horb_step, horb_fz] at hzself
    exact hzself
  · intro hzorb
    have horb_z : periodicOrbit f z = periodicOrbit f x :=
      periodicOrbit_eq_of_mem f hx hzorb
    have hstep : f z ∈ periodicOrbit f z := by
      exact iterate_mem_periodicOrbit hz 1
    simpa [horb_z] using hstep

theorem signedResidual_detKernel_eq_zero_of_periodic_structure
    (f : S → S) (v : S → ℝ)
    (hoff : ∀ y : S, y ∉ periodicPts f → v y = 0)
    (hstep : ∀ x : S, x ∈ periodicPts f → v (f x) = v x) :
    signedResidual (detKernel f) v = 0 := by
  funext y
  unfold signedResidual
  change Matrix.vecMul v (detKernel f) y - v y = 0
  rw [vecMul_detKernel]
  by_cases hyper : y ∈ periodicPts f
  · obtain ⟨z0, hz0, huniq⟩ := periodic_preimage_unique f hyper
    have hz0mem : z0 ∈ Finset.univ.filter (fun z => f z = y) := by
      simp [hz0.2]
    have hsum :
        (∑ z ∈ Finset.univ.filter (fun z => f z = y), v z) = v z0 := by
      apply Finset.sum_eq_single z0
      · intro z hz hzneq
        have hfz : f z = y := (Finset.mem_filter.mp hz).2
        by_cases hzper : z ∈ periodicPts f
        · have hzeq : z = z0 := huniq z ⟨hzper, hfz⟩
          exact (hzneq hzeq).elim
        · exact hoff z hzper
      · intro hznot
        exact (hznot hz0mem).elim
    rw [hsum]
    have hstep0 := hstep z0 hz0.1
    rw [hz0.2] at hstep0
    linarith
  · have hy0 := hoff y hyper
    have hsum0 :
        (∑ z ∈ Finset.univ.filter (fun z => f z = y), v z) = 0 := by
      apply Finset.sum_eq_zero
      intro z hz
      have hfz : f z = y := (Finset.mem_filter.mp hz).2
      apply hoff z
      intro hzper
      apply hyper
      rw [← hfz]
      exact periodic_apply f hzper
    rw [hsum0, hy0]
    norm_num

private theorem exists_two_periodic_orbits_of_not_unique
    (f : S → S) (hnot : ¬ HasUniquePeriodicOrbit f) :
    ∃ x y : S,
      x ∈ periodicPts f ∧
      y ∈ periodicPts f ∧
      y ∉ periodicOrbit f x := by
  let a0 : S := Classical.choice (inferInstance : Nonempty S)
  let x := f^[Fintype.card S] a0
  have hx : x ∈ periodicPts f := iterate_card_mem_periodicPts f a0
  by_contra h
  apply hnot
  refine ⟨x, hx, ?_⟩
  intro y hy
  by_contra hyorb
  exact h ⟨x, y, hx, hy, hyorb⟩

theorem exists_zero_sum_residual_kernel_of_not_unique_periodic_orbit
    (f : S → S) (hnot : ¬ HasUniquePeriodicOrbit f) :
    ∃ v : S → ℝ,
      v ≠ 0 ∧
      (∑ s, v s) = 0 ∧
      signedResidual (detKernel f) v = 0 := by
  classical
  obtain ⟨x, y, hx, hy, hyNotOrbit⟩ :=
    exists_two_periodic_orbits_of_not_unique f hnot
  let A : Finset S :=
    Finset.univ.filter (fun z => z ∈ periodicOrbit f x)
  let B : Finset S :=
    Finset.univ.filter (fun z => z ∈ periodicPts f ∧ z ∉ periodicOrbit f x)
  have hxA : x ∈ A := by
    simp [A, self_mem_periodicOrbit hx]
  have hyB : y ∈ B := by
    simp [B, hy, hyNotOrbit]
  have hApos : 0 < A.card := Finset.card_pos.mpr ⟨x, hxA⟩
  have hBpos : 0 < B.card := Finset.card_pos.mpr ⟨y, hyB⟩
  let v : S → ℝ := fun z =>
    if hzper : z ∈ periodicPts f then
      if z ∈ periodicOrbit f x then (B.card : ℝ) else -(A.card : ℝ)
    else 0
  have hvsum : (∑ s, v s) = 0 := by
    let P : Finset S :=
      Finset.univ.filter (fun z => z ∈ periodicPts f)
    have hPpart := Finset.sum_filter_add_sum_filter_not
      P (fun z => z ∈ periodicOrbit f x) v
    have hAeq :
        P.filter (fun z => z ∈ periodicOrbit f x) = A := by
      ext z
      constructor
      · intro hz
        have hz' := Finset.mem_filter.mp hz
        have hzorb := hz'.2
        simp [A, hzorb]
      · intro hz
        have hzorb : z ∈ periodicOrbit f x := by simpa [A] using hz
        have hzper : z ∈ periodicPts f := by
          rw [mem_periodicOrbit_iff hx] at hzorb
          rcases hzorb with ⟨n, rfl⟩
          exact (mem_periodicPts_iff_isPeriodicPt_factorial_card).2
            (((mem_periodicPts_iff_isPeriodicPt_factorial_card).1 hx).apply_iterate n)
        simp [P, hzper, hzorb]
    have hBeq :
        P.filter (fun z => z ∉ periodicOrbit f x) = B := by
      ext z
      simp [P, B]
    have hsumA : (∑ z ∈ A, v z) = (A.card : ℝ) * B.card := by
      calc
        (∑ z ∈ A, v z) = ∑ _z ∈ A, (B.card : ℝ) := by
          apply Finset.sum_congr rfl
          intro z hz
          have hzorb : z ∈ periodicOrbit f x := by simpa [A] using hz
          have hzper : z ∈ periodicPts f := by
            rw [mem_periodicOrbit_iff hx] at hzorb
            rcases hzorb with ⟨n, rfl⟩
            exact (mem_periodicPts_iff_isPeriodicPt_factorial_card).2
              (((mem_periodicPts_iff_isPeriodicPt_factorial_card).1 hx).apply_iterate n)
          simp [v, hzper, hzorb]
        _ = (A.card : ℝ) * B.card := by simp [nsmul_eq_mul]
    have hsumB : (∑ z ∈ B, v z) = (B.card : ℝ) * (-(A.card : ℝ)) := by
      calc
        (∑ z ∈ B, v z) = ∑ _z ∈ B, (-(A.card : ℝ)) := by
          apply Finset.sum_congr rfl
          intro z hz
          have hz' : z ∈ periodicPts f ∧ z ∉ periodicOrbit f x := by
            simpa [B] using hz
          simp [v, hz'.1, hz'.2]
        _ = (B.card : ℝ) * (-(A.card : ℝ)) := by simp [nsmul_eq_mul]
    have hsumP : (∑ z ∈ P, v z) = 0 := by
      rw [← hPpart, hAeq, hBeq, hsumA, hsumB]
      ring
    have hoffsum : ∀ z ∈ (Finset.univ : Finset S), z ∉ P → v z = 0 := by
      intro z hzu hzP
      have hznot : z ∉ periodicPts f := by
        intro hzper
        apply hzP
        simp [P, hzper]
      simp [v, hznot]
    calc
      (∑ z, v z) = ∑ z ∈ P, v z := by
        symm
        exact Finset.sum_subset (by simp [P]) hoffsum
      _ = 0 := hsumP
  have hoff : ∀ z : S, z ∉ periodicPts f → v z = 0 := by
    intro z hz
    simp [v, hz]
  have hstep : ∀ z : S, z ∈ periodicPts f → v (f z) = v z := by
    intro z hz
    have hfzper := periodic_apply f hz
    have horb := periodicOrbit_mem_apply_iff f hx hz
    by_cases hzorb : z ∈ periodicOrbit f x
    · have hfzorb : f z ∈ periodicOrbit f x := horb.mpr hzorb
      simp [v, hz, hfzper, hzorb, hfzorb]
    · have hfzorb : f z ∉ periodicOrbit f x := by
        intro h
        exact hzorb (horb.mp h)
      simp [v, hz, hfzper, hzorb, hfzorb]
  have hres := signedResidual_detKernel_eq_zero_of_periodic_structure f v hoff hstep
  have hvne : v ≠ 0 := by
    intro hv0
    have hx0 := congrFun hv0 x
    have hxorb : x ∈ periodicOrbit f x := self_mem_periodicOrbit hx
    simp [v, hx] at hx0
    exact (Finset.ne_empty_of_mem hyB) hx0
  exact ⟨v, hvne, hvsum, hres⟩

end
end UEOT.V3.Compression.TopologyChangingGoaFunctionalGraphClassification

namespace UEOT.V3.Compression.TopologyChangingGoaFunctionalGraphClassification

open Function
open UEOT.V3
open UEOT.V3.Compression.TopologyChangingGoaSpectralIsolation
open UEOT.V3.Compression.TopologyChangingGoaRestrictedResidualAdapter
open UEOT.V3.Compression.TopologyChangingGoaL1ResidualConorm

universe u
noncomputable section
variable {S : Type u} [Fintype S] [Nonempty S]
noncomputable local instance : DecidableEq S := Classical.decEq S
local instance : MeasurableSpace S := ⊤

theorem detKernel_not_restricted_injective_of_not_unique_periodic_orbit
    (f : S → S) (hnot : ¬ HasUniquePeriodicOrbit f) :
    ¬ Function.Injective (zeroSumResidualLinear (detKernel f)) := by
  obtain ⟨v, hvne, hvsum, hres⟩ :=
    exists_zero_sum_residual_kernel_of_not_unique_periodic_orbit f hnot
  let w : zeroSumEuclidean (S := S) :=
    ⟨WithLp.toLp 2 v, (zeroSum_mem_iff v).2 hvsum⟩
  have hwne : w ≠ 0 := by
    intro hw0
    have hval := congrArg (fun z : zeroSumEuclidean (S := S) =>
      (z.1 : EuclideanSpace ℝ S).ofLp) hw0
    apply hvne
    simpa [w] using hval
  have hmapzero : zeroSumResidualLinear (detKernel f) w = 0 := by
    rw [WithLp.ext_iff]
    simpa [zeroSumResidualLinear, w, residualEuclideanLinear_ofLp] using hres
  intro hinj
  apply hwne
  apply hinj
  simpa using hmapzero

theorem detKernel_restricted_injective_iff_unique_periodic_orbit
    (f : S → S) :
    Function.Injective (zeroSumResidualLinear (detKernel f)) ↔
      HasUniquePeriodicOrbit f := by
  constructor
  · intro hinj
    by_contra hnot
    exact (detKernel_not_restricted_injective_of_not_unique_periodic_orbit f hnot) hinj
  · intro huniq
    exact detKernel_restricted_injective_of_unique_periodic_orbit f huniq

theorem detKernel_l1ResidualConorm_pos_iff_unique_periodic_orbit
    (f : S → S) (hcard : 1 < Fintype.card S) :
    0 < l1ResidualConorm (detKernel f) ↔
      HasUniquePeriodicOrbit f := by
  rw [l1ResidualConorm_pos_iff_restricted_injective (detKernel f) hcard]
  exact detKernel_restricted_injective_iff_unique_periodic_orbit f

end
end UEOT.V3.Compression.TopologyChangingGoaFunctionalGraphClassification

namespace UEOT.V3.Compression.TopologyChangingGoaFunctionalGraphClassification

open UEOT.V3
open UEOT.V3.Compression.InvariantSetGaugeInvariance
open UEOT.V3.Compression.TopologyChangingGoaRestrictedResidualAdapter
open UEOT.V3.Compression.TopologyChangingGoaInvariantUniquenessIsolation

universe u
noncomputable section
variable {S : Type u} [Fintype S] [Nonempty S]
noncomputable local instance : DecidableEq S := Classical.decEq S
local instance : MeasurableSpace S := ⊤

/-- For every finite deterministic system, unique invariant probability
semantics is exactly one recurrent periodic orbit of its functional graph. -/
theorem detKernel_unique_invariant_law_iff_unique_periodic_orbit
    (f : S → S) :
    (∃! mu : stdSimplex ℝ S,
      mu ∈ invariantLawSet (detKernel f) (detKernel_stochastic f)) ↔
      HasUniquePeriodicOrbit f := by
  constructor
  · intro huniq
    have hsub :
        (invariantLawSet (detKernel f) (detKernel_stochastic f)).Subsingleton :=
      (invariantLawSet_subsingleton_iff_existsUnique
        (detKernel f) (detKernel_stochastic f)).2 huniq
    have hinj : Function.Injective (zeroSumResidualLinear (detKernel f)) :=
      (restricted_injective_iff_invariantLawSet_subsingleton
        (detKernel f) (detKernel_stochastic f)).2 hsub
    exact (detKernel_restricted_injective_iff_unique_periodic_orbit f).1 hinj
  · intro hperiod
    have hinj : Function.Injective (zeroSumResidualLinear (detKernel f)) :=
      (detKernel_restricted_injective_iff_unique_periodic_orbit f).2 hperiod
    have hsub :
        (invariantLawSet (detKernel f) (detKernel_stochastic f)).Subsingleton :=
      (restricted_injective_iff_invariantLawSet_subsingleton
        (detKernel f) (detKernel_stochastic f)).1 hinj
    exact (invariantLawSet_subsingleton_iff_existsUnique
      (detKernel f) (detKernel_stochastic f)).1 hsub

end
end UEOT.V3.Compression.TopologyChangingGoaFunctionalGraphClassification

namespace UEOT.V3.Compression.TopologyChangingGoaFunctionalGraphClassification

open UEOT.V3
open UEOT.V3.FiniteDobrushin

universe u
noncomputable section
variable {S : Type u} [Fintype S] [Nonempty S]
noncomputable local instance : DecidableEq S := Classical.decEq S
local instance : MeasurableSpace S := ⊤

private theorem detKernel_rowTV_eq_zero_of_eq_image
    (f : S → S) {x y : S} (hxy : f x = f y) :
    rowTV (detKernel f) (detKernel_stochastic f) x y = 0 := by
  unfold rowTV UEOT.V3.FiniteDiscountedControl.FiniteProbabilityRow.tvDist
  rw [UEOT.V3.FiniteRecurrentDecompositionStability.pmf_tv_eq_half_sum_abs]
  simp_rw [rowPMF_toReal]
  simp [detKernel, hxy]

private theorem detKernel_rowTV_eq_one_of_ne_image
    (f : S → S) {x y : S} (hxy : f x ≠ f y) :
    rowTV (detKernel f) (detKernel_stochastic f) x y = 1 := by
  unfold rowTV UEOT.V3.FiniteDiscountedControl.FiniteProbabilityRow.tvDist
  rw [UEOT.V3.FiniteRecurrentDecompositionStability.pmf_tv_eq_half_sum_abs]
  simp_rw [rowPMF_toReal]
  have habs : ∀ z : S,
      |detKernel f x z - detKernel f y z| =
        (if z = f x then 1 else 0) + (if z = f y then 1 else 0) := by
    intro z
    by_cases hxz : z = f x
    · subst z
      simp [detKernel, hxy]
    · by_cases hyz : z = f y
      · subst z
        simp [detKernel, hxz]
      · simp [detKernel, hxz, hyz]
  simp_rw [habs, Finset.sum_add_distrib]
  norm_num

theorem detKernel_dobrushinAlpha_eq_zero_of_constant
    (f : S → S) (a : S) (hconst : ∀ x, f x = a) :
    dobrushinAlpha (detKernel f) (detKernel_stochastic f) = 0 := by
  apply le_antisymm
  · unfold dobrushinAlpha
    apply Finset.sup'_le
    intro z hz
    rw [detKernel_rowTV_eq_zero_of_eq_image f (by rw [hconst z.1, hconst z.2])]
  · let x : S := Classical.choice (inferInstance : Nonempty S)
    have h := rowTV_le_dobrushinAlpha
      (detKernel f) (detKernel_stochastic f) x x
    rw [detKernel_rowTV_eq_zero_of_eq_image f rfl] at h
    exact h

theorem detKernel_dobrushinAlpha_eq_one_of_two_images
    (f : S → S) {x y : S} (hxy : f x ≠ f y) :
    dobrushinAlpha (detKernel f) (detKernel_stochastic f) = 1 := by
  have hle :
      dobrushinAlpha (detKernel f) (detKernel_stochastic f) ≤ 1 := by
    unfold dobrushinAlpha
    apply Finset.sup'_le
    intro z hz
    unfold rowTV UEOT.V3.FiniteDiscountedControl.FiniteProbabilityRow.tvDist
    exact UEOT.V3.TotalVariation.tvDist_le_one _ _
  apply le_antisymm hle
  have h := rowTV_le_dobrushinAlpha
    (detKernel f) (detKernel_stochastic f) x y
  rw [detKernel_rowTV_eq_one_of_ne_image f hxy] at h
  exact h

theorem detKernel_dobrushin_dichotomy (f : S → S) :
    (dobrushinAlpha (detKernel f) (detKernel_stochastic f) = 0 ∧
      ∃ a : S, ∀ x, f x = a) ∨
    (dobrushinAlpha (detKernel f) (detKernel_stochastic f) = 1 ∧
      ∃ x y : S, f x ≠ f y) := by
  classical
  by_cases hconst : ∃ a : S, ∀ x, f x = a
  · rcases hconst with ⟨a, ha⟩
    exact Or.inl ⟨detKernel_dobrushinAlpha_eq_zero_of_constant f a ha, ⟨a, ha⟩⟩
  · right
    have htwo : ∃ x y : S, f x ≠ f y := by
      let x0 : S := Classical.choice (inferInstance : Nonempty S)
      by_contra h
      apply hconst
      refine ⟨f x0, ?_⟩
      intro x
      by_contra hne
      exact h ⟨x, x0, hne⟩
    rcases htwo with ⟨x, y, hxy⟩
    exact ⟨detKernel_dobrushinAlpha_eq_one_of_two_images f hxy, ⟨x, y, hxy⟩⟩

end
end UEOT.V3.Compression.TopologyChangingGoaFunctionalGraphClassification
