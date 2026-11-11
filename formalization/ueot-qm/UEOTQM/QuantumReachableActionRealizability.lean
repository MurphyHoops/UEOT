import UEOTQM.QuantumActionRealizability

/-!
# The weaker fixed-input branch task

This is deliberately a different contract from universal support realization.
For each specified actual reachable unnormalized input, all next visible branch
outputs must match.  Used along a tree, this requires the separate induction
that the declared inputs really are the common reachable prefix states.
It is not an iff for agreement only at final leaves after arbitrary erasure.
-/

namespace UEOTQM.QuantumActionRealizability

open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionRealizabilityCheck
open scoped BigOperators

noncomputable section

variable {ι O κ A : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype O] [Fintype κ] [Fintype A]

def branchOutputFamily (I : Instrument ι O κ) (X : Operator ι) : O → Operator ι :=
  fun o => I.branch o X

theorem mixture_branchOutputFamily (p : Mixture.Weights A)
    (I : A → Instrument ι O κ) (X : Operator ι) :
    branchOutputFamily (Mixture.instrument p I) X =
      ∑ a, p.weight a • branchOutputFamily (I a) X := by
  funext o
  simpa only [branchOutputFamily, Finset.sum_apply, Pi.smul_apply] using
    Mixture.instrument_branch p I o X

/-- A fixed declared input tests actual output matrices, not complete maps. -/
theorem fixed_input_branch_realizable_iff
    (I : A → Instrument ι O κ) (X : Operator ι) (R : O → Operator ι) :
    (∃ sigma : PMF A, ∀ o,
      (Mixture.instrument (weightsOfPMF sigma) I).branch o X = R o) ↔
    R ∈ convexHull ℝ (Set.range (fun a => branchOutputFamily (I a) X)) := by
  rw [← pmf_barycenter_exists_iff_mem_convexHull]
  constructor
  · rintro ⟨sigma, hsigma⟩
    refine ⟨sigma, ?_⟩
    change (∑ a, (weightsOfPMF sigma).weight a • branchOutputFamily (I a) X) = R
    rw [← mixture_branchOutputFamily]
    exact funext hsigma
  · rintro ⟨sigma, hsigma⟩
    refine ⟨sigma, ?_⟩
    have hf : branchOutputFamily (Mixture.instrument (weightsOfPMF sigma) I) X = R := by
      rw [mixture_branchOutputFamily]
      exact hsigma
    exact fun o => congrFun hf o

/-- Common observation weights are still essential for fixed reachable inputs.
This iff only governs the named branch-output task; terminal-only feasibility
can be weaker if later processing discards a distinguishing intermediate state. -/
theorem fixed_input_observation_realizable_iff
    {N Y : Type*} (q : N → Y) (I : N → A → Instrument ι O κ)
    (X : N → Operator ι) (R : N → O → Operator ι) :
    (∃ sigma : Y → PMF A, ∀ n o,
      (Mixture.instrument (weightsOfPMF (sigma (q n))) (I n)).branch o (X n) = R n o) ↔
    ∀ y, (fun n : {n : N // q n = y} => R n.val) ∈ convexHull ℝ
      (Set.range (fun a (n : {n : N // q n = y}) => branchOutputFamily (I n.val a) (X n.val))) := by
  constructor
  · rintro ⟨sigma, hsigma⟩ y
    apply (pmf_barycenter_exists_iff_mem_convexHull _ _).mp
    refine ⟨sigma y, ?_⟩
    funext n
    have hn : branchOutputFamily
        (Mixture.instrument (weightsOfPMF (sigma (q n.val))) (I n.val)) (X n.val) = R n.val :=
      funext (hsigma n.val)
    rw [n.property, mixture_branchOutputFamily] at hn
    simpa only [Finset.sum_apply, Pi.smul_apply, weightsOfPMF] using hn
  · intro h
    have hex (y : Y) := (pmf_barycenter_exists_iff_mem_convexHull
      (fun a (n : {n : N // q n = y}) => branchOutputFamily (I n.val a) (X n.val))
      (fun n : {n : N // q n = y} => R n.val)).mpr (h y)
    choose sigma hsigma using hex
    refine ⟨sigma, ?_⟩
    intro n o
    have hn : branchOutputFamily
        (Mixture.instrument (weightsOfPMF (sigma (q n))) (I n)) (X n) = R n := by
      rw [mixture_branchOutputFamily]
      have hx := congrFun (hsigma (q n)) ⟨n, rfl⟩
      simpa only [Finset.sum_apply, Pi.smul_apply, weightsOfPMF] using hx
    exact congrFun hn o

end

end UEOTQM.QuantumActionRealizability
