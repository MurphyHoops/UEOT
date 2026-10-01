import UEOT.V3.Compression.QuotientDescent
import Mathlib.Probability.ProbabilityMassFunction.Constructions

namespace UEOT.V3.Compression.Hierarchy

open Function
open UEOT.V3.Compression.QuotientDescent

noncomputable section

/-- A common witness for a coarse and a richer representation does not by
itself induce a lift from the coarse representation to the richer one. M-QD
already identifies the missing condition as fibre compatibility. -/
theorem commonWitness_not_hierarchyLift :
    ¬ ∃ lift : Bool → Bool × Bool, lift ∘ Prod.fst = id := by
  rintro ⟨lift, hfactor⟩
  have hcompat : FiberCompatible Prod.fst (id : Bool × Bool → Bool × Bool) :=
    fiberCompatible_of_comp_eq Prod.fst id lift hfactor
  have hpairs : (false, false) = (false, true) := by
    exact hcompat (x := (false, false)) (x' := (false, true)) rfl
  have hbool : (false : Bool) = true := congrArg Prod.snd hpairs
  simp at hbool

/-- Child consistency alone does not canonically determine a parent completion:
there exist two distinct parent completions with exactly the same child
projection. -/
theorem childConsistency_does_not_determine_unique_parent :
    ∃ p₀ p₁ : Bool → Bool × Bool,
      Prod.fst ∘ p₀ = id ∧
      Prod.fst ∘ p₁ = id ∧
      p₀ ≠ p₁ := by
  let p₀ : Bool → Bool × Bool := fun b => (b, false)
  let p₁ : Bool → Bool × Bool := fun b => (b, true)
  refine ⟨p₀, p₁, ?_, ?_, ?_⟩
  · funext b
    rfl
  · funext b
    rfl
  · intro h
    have hpairs : (false, false) = (false, true) := congrFun h false
    have hbool : (false : Bool) = true := congrArg Prod.snd hpairs
    simp at hbool

private def fairBool : PMF Bool :=
  PMF.ofFintype (fun _ => (2 : ENNReal)⁻¹) (by
    rw [Fintype.sum_bool]
    exact ENNReal.inv_two_add_inv_two)

private def correlatedJoint : PMF (Bool × Bool) :=
  fairBool.map (fun b => (b, b))

private def anticorrelatedJoint : PMF (Bool × Bool) :=
  fairBool.map (fun b => (b, !b))

private theorem correlated_fst_marginal :
    correlatedJoint.map Prod.fst = fairBool := by
  rw [correlatedJoint, PMF.map_comp]
  have hfun : (Prod.fst ∘ fun b : Bool => (b, b)) = id := by
    funext b
    rfl
  rw [hfun, PMF.map_id]

private theorem anticorrelated_fst_marginal :
    anticorrelatedJoint.map Prod.fst = fairBool := by
  rw [anticorrelatedJoint, PMF.map_comp]
  have hfun : (Prod.fst ∘ fun b : Bool => (b, !b)) = id := by
    funext b
    rfl
  rw [hfun, PMF.map_id]

private theorem fairBool_map_not : fairBool.map (!·) = fairBool := by
  ext b
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_bool]
  cases b <;> simp [fairBool]

private theorem correlated_snd_marginal :
    correlatedJoint.map Prod.snd = fairBool := by
  rw [correlatedJoint, PMF.map_comp]
  have hfun : (Prod.snd ∘ fun b : Bool => (b, b)) = id := by
    funext b
    rfl
  rw [hfun, PMF.map_id]

private theorem anticorrelated_snd_marginal :
    anticorrelatedJoint.map Prod.snd = fairBool := by
  rw [anticorrelatedJoint, PMF.map_comp]
  simpa [Function.comp_def] using fairBool_map_not

/-- Child marginals do not determine the common joint law required by
P-COMP-01: there exist distinct finite joint laws with exactly the same two
child marginals. -/
theorem same_child_marginals_different_joint :
    ∃ p q : PMF (Bool × Bool),
      p.map Prod.fst = q.map Prod.fst ∧
      p.map Prod.snd = q.map Prod.snd ∧
      p ≠ q := by
  refine ⟨correlatedJoint, anticorrelatedJoint, ?_, ?_, ?_⟩
  · rw [correlated_fst_marginal, anticorrelated_fst_marginal]
  · rw [correlated_snd_marginal, anticorrelated_snd_marginal]
  · intro h
    have hpoint := congrArg (fun r : PMF (Bool × Bool) => r (false, false)) h
    simp [correlatedJoint, anticorrelatedJoint, fairBool] at hpoint

end
end UEOT.V3.Compression.Hierarchy
