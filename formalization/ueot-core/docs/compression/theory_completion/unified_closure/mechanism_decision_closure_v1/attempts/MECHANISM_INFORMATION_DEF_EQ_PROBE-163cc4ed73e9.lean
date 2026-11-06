import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionNative
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterDecisionObserverSource

/-!
# Joint mechanism/body information from permitted histories

A visible-history likelihood is computed from the new native-derived primitive.
The posterior carries the mechanism and physical state jointly. The same proof
covers arbitrary real causal action probabilities: their visible-history factor
cancels on every positive-mass conditioning event. Zero-mass histories are not
assigned empirical meaning. The reachable 11/00 history shows precisely why the
old S-only deterministic body observer cannot be used unchanged for G.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismInformationProbe

open scoped BigOperators
open RegisterMechanismDecisionSource
open RegisterJointDecisionSource (Act Obs Noise primitiveWeight packedLookup initialStore initial_aligned)
open RegisterJointDecisionConsumer (Wallet)
open FiniteJointDecisionBelief FiniteJointDecisionSolver FiniteJointDecisionFilteredModel
open FiniteJointDecisionSupportedPolicy (RawCausalPolicy)

abbrev History := List (Act × Obs)

def historyIntegral (goal : Bool) (r : ℚ) (terminal : World → ℚ) : World → History → ℚ
  | w, [] => terminal w
  | w, (a,o) :: h =>
      ∑ z : Noise, primitiveWeight (fun _ => r) w z *
        if observe goal w a z = o then historyIntegral goal r terminal (step goal w a z) h else 0

def jointFilter (P : Parameters) : Belief World → History → Belief World
  | b, [] => b
  | b, (a,o) :: h => jointFilter P (posterior (source P) b a o) h

def evidenceMass (P : Parameters) : Belief World → History → ℚ
  | _, [] => 1
  | b, (a,o) :: h => mass (source P) b a o * evidenceMass P (posterior (source P) b a o) h

theorem historyInfo_joint (P : Parameters) : ∀ (h : History) (i : Info),
    (RegisterMechanismDecisionSource.historyInfo P i h).1 = jointFilter P i.1 h := by
  intro h
  induction h with
  | nil => intro i; rfl
  | cons e h ih =>
      intro i
      exact ih ((model P).next i e.1 e.2)

/-- Full joint disintegration, including impossible histories without division. -/
set_option pp.all true in
theorem history_disintegration (P : Parameters) : ∀ (h : History) (b : Belief World)
    (f : World → ℚ),
    evidenceMass P b h * expect (jointFilter P b h) f =
      expect b (fun w => historyIntegral P.goal P.normal f w h) := by
  intro h
  induction h with
  | nil => intro b f; simp [evidenceMass, jointFilter, historyIntegral]
  | cons e h ih =>
      rcases e with ⟨a,o⟩
      intro b f
      simp only [evidenceMass, jointFilter]
      rw [mul_assoc, ih, posterior_identity]
      simp only [expect, historyIntegral, source, joint, Fintype.sum_prod_type,
        Finset.mul_sum, mul_assoc, mul_ite, ite_mul, mul_zero, zero_mul]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro label hlabel
      trace_state
      by_cases heq : observe P.goal (b.state x) a (z,label) = o
      · simp only [if_pos heq]
        ring
      · simp only [if_neg heq, mul_zero, zero_mul]


end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismInformationProbe
