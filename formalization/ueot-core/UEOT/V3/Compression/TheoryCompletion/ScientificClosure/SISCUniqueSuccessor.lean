import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCIdentityNoGo
import Mathlib.Tactic.Linarith

/-!
# SISC SI-2: a non-circular unique operational successor certificate

The edge is independent causal provenance. Response observations and the
candidate-separation margin are separate supplied measurements. No identity
token, `SameObject`, global chosen selector or target uniqueness is an input.
Only uniqueness **among registered admissible targets** is concluded.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

universe uS uT uR

/-- An eligible successor has an independently registered causal edge and a
response within the predeclared prediction tolerance. -/
def AdmissibleSuccessor
    {Source : Type uS} {Target : Type uT} {Response : Type uR}
    [PseudoMetricSpace Response]
    (edge : Source → Target → Prop)
    (predicted : Source → Response) (observed : Target → Response)
    (eps : ℝ) (s : Source) (t : Target) : Prop :=
  edge s t ∧ dist (observed t) (predicted s) ≤ eps

/-- At one fixed source, all registered admissible candidates must be unique.
This intentionally does not say that the target is the ontically same object. -/
def CertifiedUniqueSuccessor
    {Source : Type uS} {Target : Type uT} {Response : Type uR}
    [PseudoMetricSpace Response]
    (edge : Source → Target → Prop)
    (predicted : Source → Response) (observed : Target → Response)
    (eps : ℝ) (s : Source) : Prop :=
  ∃ t, AdmissibleSuccessor edge predicted observed eps s t ∧
    ∀ u, AdmissibleSuccessor edge predicted observed eps s u → u = t

/-- Separate registered candidate responses by more than twice the total
tolerance. This is an identifiable, independently falsifiable premise. -/
def ResponseSeparated
    {Target : Type uT} {Response : Type uR}
    [PseudoMetricSpace Response]
    (observed : Target → Response) (eps : ℝ) : Prop :=
  ∀ a b, a ≠ b → 2 * eps < dist (observed a) (observed b)

/-- Two admissible successors cannot coexist if their independently measured
responses exceed the registered separation threshold. -/
theorem admissible_successor_unique
    {Source : Type uS} {Target : Type uT} {Response : Type uR}
    [PseudoMetricSpace Response]
    (edge : Source → Target → Prop)
    (predicted : Source → Response) (observed : Target → Response)
    (eps : ℝ) (hsep : ResponseSeparated observed eps)
    (s : Source) {a b : Target}
    (ha : AdmissibleSuccessor edge predicted observed eps s a)
    (hb : AdmissibleSuccessor edge predicted observed eps s b) : a = b := by
  by_contra hne
  have hs := hsep a b hne
  have ht := dist_triangle (observed a) (predicted s) (observed b)
  have hb' : dist (predicted s) (observed b) ≤ eps := by
    simpa only [dist_comm] using hb.2
  dsimp [AdmissibleSuccessor] at ha
  linarith [ha.2]

/-- Existence comes from a causal-and-response witness, *not* from the
uniqueness theorem. This endpoint is the exact SI-2 local certificate. -/
theorem certified_unique_successor_of_witness
    {Source : Type uS} {Target : Type uT} {Response : Type uR}
    [PseudoMetricSpace Response]
    (edge : Source → Target → Prop)
    (predicted : Source → Response) (observed : Target → Response)
    (eps : ℝ) (hsep : ResponseSeparated observed eps)
    (s : Source) (t : Target)
    (ht : AdmissibleSuccessor edge predicted observed eps s t) :
    CertifiedUniqueSuccessor edge predicted observed eps s := by
  refine ⟨t, ht, ?_⟩
  intro u hu
  exact admissible_successor_unique edge predicted observed eps hsep s hu ht

/-- A noisy estimator still identifies at most one successor when true
candidate responses are separated by `2 * (eps + eta)` and each candidate's
estimation error is bounded by `eta`. Thus the uncertainty budget cannot be
silently omitted from the separation premise. -/
theorem noisy_admissible_successor_unique
    {Source : Type uS} {Target : Type uT} {Response : Type uR}
    [PseudoMetricSpace Response]
    (edge : Source → Target → Prop)
    (predicted : Source → Response)
    (trueResponse estimatedResponse : Target → Response)
    (eps eta : ℝ)
    (hnoise : ∀ t, dist (trueResponse t) (estimatedResponse t) ≤ eta)
    (hsep : ResponseSeparated trueResponse (eps + eta))
    (s : Source) {a b : Target}
    (ha : AdmissibleSuccessor edge predicted estimatedResponse eps s a)
    (hb : AdmissibleSuccessor edge predicted estimatedResponse eps s b) :
    a = b := by
  by_contra hne
  have hs := hsep a b hne
  have ht1 := dist_triangle (trueResponse a) (estimatedResponse a) (trueResponse b)
  have ht2 := dist_triangle (estimatedResponse a) (predicted s) (trueResponse b)
  have ht3 := dist_triangle (predicted s) (estimatedResponse b) (trueResponse b)
  have hn2 : dist (estimatedResponse b) (trueResponse b) ≤ eta := by
    simpa only [dist_comm] using hnoise b
  have hb' : dist (predicted s) (estimatedResponse b) ≤ eps := by
    simpa only [dist_comm] using hb.2
  have ht3' : dist (predicted s) (trueResponse b) ≤ eps + eta := by
    linarith
  have ht2' : dist (estimatedResponse a) (trueResponse b) ≤
      eps + (eps + eta) := by
    linarith [ha.2]
  linarith [hnoise a]

/-- Positive finite witness: there is one causally admissible target and a
strictly separated alternative. This contrasts with the SI-1 clone witness. -/
theorem finite_unique_successor_example :
    CertifiedUniqueSuccessor
      (fun (_ : PUnit) (t : Bool) => t = false)
      (fun (_ : PUnit) => (0 : ℝ))
      (fun t : Bool => if t then (1 : ℝ) else 0)
      0 PUnit.unit := by
  have hsep : ResponseSeparated
      (fun t : Bool => if t then (1 : ℝ) else 0) 0 := by
    intro a b hab
    cases a <;> cases b <;> simp_all [Real.dist_eq]
  apply certified_unique_successor_of_witness _ _ _ 0 hsep PUnit.unit false
  exact ⟨rfl, by norm_num [Real.dist_eq]⟩

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
