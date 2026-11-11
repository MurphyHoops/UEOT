import UEOTQM.Mixture
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionRealizability

/-!
# Actual instrument randomization, with visible labels and observation fibers

This module consumes Core's real-module convex-hull theorem.  Its vectors are
the Choi matrices of actual complex-linear Kraus maps, indexed by VISIBLE
outcomes.  The sampled library action and the Kraus refinement stay hidden.

`input` can be the identity (a specified full-space instrument), conjugation
by a support projector (a universal support task), or another declared linear
input restriction.  Failure for one chosen full-space completion is NOT a
no-go theorem for other completions or for one fixed initial trajectory.
-/

namespace UEOTQM.QuantumActionRealizability

open Matrix
open UEOT.V3.PathError UEOT.V3.TotalVariation
open UEOT.V3.FiniteDiscountedControl UEOT.V3.CoreOperationalAssembly
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open FiniteActionRealizabilityCheck
open scoped BigOperators ComplexOrder

noncomputable section

variable {ι O κ A : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype O] [Fintype κ] [Fintype A]

/-- Matrix units are fixed input coordinates, not additional physical outcomes. -/
def matrixUnit (i j : ι) : Operator ι :=
  fun a b => if i = a ∧ j = b then 1 else 0

theorem matrix_expansion (X : Operator ι) :
    X = ∑ i, ∑ j, (X i j) • matrixUnit i j := by
  classical
  ext a b
  simp [matrixUnit, Matrix.sum_apply, Pi.smul_apply, smul_eq_mul, ite_and]

/-- Complex linearity is proved for the existing Kraus branch. -/
def branchLinear (I : Instrument ι O κ) (o : O) :
    Operator ι →ₗ[ℂ] Operator ι where
  toFun := I.branch o
  map_add' X Y := by
    simp only [Instrument.branch, krausMap, Matrix.mul_add, Matrix.add_mul,
      Finset.sum_add_distrib]
  map_smul' c X := by
    simp only [Instrument.branch, krausMap, Matrix.mul_smul, Matrix.smul_mul,
      Finset.smul_sum, RingHom.id_apply]

@[simp] theorem branchLinear_apply (I : Instrument ι O κ) (o : O) (X : Operator ι) :
    branchLinear I o X = I.branch o X := rfl

/-- Input-first Choi convention: C(F)[(i,a),(j,b)] = F(E_ij)[a,b]. -/
def choi (F : Operator ι →ₗ[ℂ] Operator ι) : Operator (ι × ι) :=
  fun ia jb => F (matrixUnit ia.1 jb.1) ia.2 jb.2

/-- These are actual operator-map coordinates: their equality implies equality
on every complex matrix, not merely equality on a finite sample of states. -/
theorem choi_injective : Function.Injective (choi (ι := ι)) := by
  intro F G h
  apply LinearMap.ext
  intro X
  have expand (L : Operator ι →ₗ[ℂ] Operator ι) :
      L X = ∑ i, ∑ j, (X i j) • L (matrixUnit i j) := by
    conv_lhs => rw [matrix_expansion X]
    simp only [map_sum, map_smul]
  rw [expand F, expand G]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ext a b
  exact congrFun (congrFun h (i, a)) (j, b)

def conjugationLinear (P : Operator ι) : Operator ι →ₗ[ℂ] Operator ι where
  toFun X := P * X * Pᴴ
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

/-- One Choi block per visible outcome.  No Kraus index is promoted to a label. -/
def instrumentChoiAfter (I : Instrument ι O κ)
    (input : Operator ι →ₗ[ℂ] Operator ι) : O → Operator (ι × ι) :=
  fun o => choi ((branchLinear I o).comp input)

def targetChoiAfter (T : O → Operator ι →ₗ[ℂ] Operator ι)
    (input : Operator ι →ₗ[ℂ] Operator ι) : O → Operator (ι × ι) :=
  fun o => choi ((T o).comp input)

theorem instrumentChoiAfter_eq_iff (I : Instrument ι O κ)
    (T : O → Operator ι →ₗ[ℂ] Operator ι)
    (input : Operator ι →ₗ[ℂ] Operator ι) :
    instrumentChoiAfter I input = targetChoiAfter T input ↔
      ∀ o X, I.branch o (input X) = T o (input X) := by
  constructor
  · intro h o X
    have hm := choi_injective (congrFun h o)
    exact LinearMap.congr_fun hm X
  · intro h
    funext o
    apply congrArg choi
    apply LinearMap.ext
    intro X
    exact h o X

/-- Existing square-root-weight Kraus construction, converted to actual Choi
barycenters.  Randomization equality is a conclusion, not a supplied field. -/
theorem mixture_instrumentChoiAfter (p : Mixture.Weights A)
    (I : A → Instrument ι O κ) (input : Operator ι →ₗ[ℂ] Operator ι) :
    instrumentChoiAfter (Mixture.instrument p I) input =
      ∑ a, p.weight a • instrumentChoiAfter (I a) input := by
  funext o ia jb
  change (Mixture.instrument p I).branch o (input (matrixUnit ia.1 jb.1)) ia.2 jb.2 = _
  rw [Mixture.instrument_branch]
  simp only [instrumentChoiAfter, choi, LinearMap.comp_apply, branchLinear_apply,
    Finset.sum_apply, Pi.smul_apply, Matrix.sum_apply, Matrix.smul_apply]

def weightsOfPMF (sigma : PMF A) : Mixture.Weights A where
  weight a := (sigma a).toReal
  nonneg _ := ENNReal.toReal_nonneg
  sum_one := coverage_sum_toReal sigma

/-- Positive certificate: declared nonnegative normalized weights build an
actual complete Kraus instrument with precisely the target restricted maps. -/
theorem realizes_of_weights (p : Mixture.Weights A)
    (I : A → Instrument ι O κ) (T : O → Operator ι →ₗ[ℂ] Operator ι)
    (input : Operator ι →ₗ[ℂ] Operator ι)
    (h : (∑ a, p.weight a • instrumentChoiAfter (I a) input) =
      targetChoiAfter T input) :
    ∀ o X, (Mixture.instrument p I).branch o (input X) = T o (input X) := by
  apply (instrumentChoiAfter_eq_iff _ _ _).mp
  rw [mixture_instrumentChoiAfter, h]

/-- Exact implementation iff: a direct consumer of Core's generic real-module
convex theorem, instantiated with families of genuine complex Choi matrices. -/
theorem realizable_after_iff_mem_convexHull
    (I : A → Instrument ι O κ) (T : O → Operator ι →ₗ[ℂ] Operator ι)
    (input : Operator ι →ₗ[ℂ] Operator ι) :
    (∃ sigma : PMF A, ∀ o X,
      (Mixture.instrument (weightsOfPMF sigma) I).branch o (input X) =
        T o (input X)) ↔
    targetChoiAfter T input ∈ convexHull ℝ
      (Set.range (fun a => instrumentChoiAfter (I a) input)) := by
  rw [← pmf_barycenter_exists_iff_mem_convexHull]
  constructor
  · rintro ⟨sigma, hsigma⟩
    refine ⟨sigma, ?_⟩
    have h := (instrumentChoiAfter_eq_iff _ _ _).mpr hsigma
    rw [mixture_instrumentChoiAfter] at h
    exact h
  · rintro ⟨sigma, hsigma⟩
    exact ⟨sigma, realizes_of_weights (weightsOfPMF sigma) I T input hsigma⟩

/-- Full-space task: the specified target instrument, including its behavior
on inputs outside any reachable support, must be reproduced. -/
theorem full_instrument_realizable_iff {κ' : Type*} [Fintype κ']
    (I : A → Instrument ι O κ) (J : Instrument ι O κ') :
    (∃ sigma : PMF A, ∀ o X,
      (Mixture.instrument (weightsOfPMF sigma) I).branch o X = J.branch o X) ↔
    instrumentChoiAfter J LinearMap.id ∈ convexHull ℝ
      (Set.range (fun a => instrumentChoiAfter (I a) LinearMap.id)) := by
  exact realizable_after_iff_mem_convexHull I (branchLinear J) LinearMap.id

/-- Universal support task.  For an orthogonal projector P, this is agreement
on the whole supported matrix algebra.  The mixture itself supplies a valid
full-space completion; no arbitrary fallback completion is preselected. -/
theorem support_realizable_iff
    (I : A → Instrument ι O κ) (T : O → Operator ι →ₗ[ℂ] Operator ι)
    (P : Operator ι) :
    (∃ sigma : PMF A, ∀ o X,
      (Mixture.instrument (weightsOfPMF sigma) I).branch o (P * X * Pᴴ) =
        T o (P * X * Pᴴ)) ↔
    targetChoiAfter T (conjugationLinear P) ∈ convexHull ℝ
      (Set.range (fun a => instrumentChoiAfter (I a) (conjugationLinear P))) := by
  exact realizable_after_iff_mem_convexHull I T (conjugationLinear P)

/-- Observation fibers enforce ONE common action distribution across all hidden
nodes with that observation.  Individual-node convex feasibility is weaker. -/
theorem observation_realizable_iff_fiber_choi
    {N Y : Type*} (q : N → Y) (I : N → A → Instrument ι O κ)
    (T : N → O → Operator ι →ₗ[ℂ] Operator ι)
    (input : N → Operator ι →ₗ[ℂ] Operator ι) :
    (∃ sigma : Y → PMF A, ∀ n o X,
      (Mixture.instrument (weightsOfPMF (sigma (q n))) (I n)).branch o (input n X) =
        T n o (input n X)) ↔
    ∀ y, (fun n : {n : N // q n = y} => targetChoiAfter (T n.val) (input n.val)) ∈
      convexHull ℝ (Set.range (fun a (n : {n : N // q n = y}) =>
        instrumentChoiAfter (I n.val a) (input n.val))) := by
  constructor
  · rintro ⟨sigma, hsigma⟩ y
    apply (pmf_barycenter_exists_iff_mem_convexHull _ _).mp
    refine ⟨sigma y, ?_⟩
    funext n
    have hn := (instrumentChoiAfter_eq_iff _ _ _).mpr (hsigma n.val)
    rw [n.property, mixture_instrumentChoiAfter] at hn
    simpa only [Finset.sum_apply, Pi.smul_apply, weightsOfPMF] using hn
  · intro h
    have hex (y : Y) := (pmf_barycenter_exists_iff_mem_convexHull
      (fun a (n : {n : N // q n = y}) => instrumentChoiAfter (I n.val a) (input n.val))
      (fun n : {n : N // q n = y} => targetChoiAfter (T n.val) (input n.val))).mpr (h y)
    choose sigma hsigma using hex
    refine ⟨sigma, ?_⟩
    intro n
    apply realizes_of_weights (weightsOfPMF (sigma (q n))) (I n) (T n) (input n)
    have hn := congrFun (hsigma (q n)) ⟨n, rfl⟩
    simpa only [Finset.sum_apply, Pi.smul_apply, weightsOfPMF] using hn

/-- A supplied, checkable real linear separator is a rigorous negative
certificate.  It rules out precisely the target/fiber vector it separates. -/
theorem separator_excludes_convexHull
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (v : A → E) (z : E) (ell : E →ₗ[ℝ] ℝ) (bound : ℝ)
    (ha : ∀ a, ell (v a) ≤ bound) (hz : bound < ell z) :
    z ∉ convexHull ℝ (Set.range v) := by
  intro hmem
  obtain ⟨sigma, hsigma⟩ :=
    (pmf_barycenter_exists_iff_mem_convexHull v z).mpr hmem
  have hle : ell z ≤ bound := by
    rw [← hsigma, map_sum]
    simp only [map_smul, smul_eq_mul]
    calc
      (∑ a, (sigma a).toReal * ell (v a)) ≤ ∑ a, (sigma a).toReal * bound := by
        exact Finset.sum_le_sum (fun a _ =>
          mul_le_mul_of_nonneg_left (ha a) ENNReal.toReal_nonneg)
      _ = bound := by rw [← Finset.sum_mul, coverage_sum_toReal sigma, one_mul]
  exact (not_le_of_gt hz) hle

/-- Universal support agreement specializes to any actual supported input.
The converse is deliberately absent: one initial trajectory tests fewer maps. -/
theorem support_agreement_on_fixed_input
    (I : Instrument ι O κ) (T : O → Operator ι →ₗ[ℂ] Operator ι)
    (P X : Operator ι) (hX : P * X * Pᴴ = X)
    (h : ∀ o Y, I.branch o (P * Y * Pᴴ) = T o (P * Y * Pᴴ)) :
    ∀ o, I.branch o X = T o X := by
  intro o
  simpa only [hX] using h o X

end

end UEOTQM.QuantumActionRealizability
