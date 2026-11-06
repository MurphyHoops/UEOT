import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionConsumer
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismExperimentPaths

/-!
# Short-horizon non-identification can coexist with common optimal control

For any registered parameters and wallet, H≤2 gives the same whole-run value
for every shared table. The same known-S returned table is therefore optimal in
both mechanisms, against the original supported real-randomized comparison
class. The fixed consumer separately supplies a positive value 13/16 example.
No terminal identification result is promoted to a same-H3 learning gain.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionShort

open scoped BigOperators
open RegisterJointDecisionSource (Act Obs Noise)
open RegisterJointDecisionConsumer (Wallet)
open RegisterMechanismDecisionSource
open RegisterMechanismDecisionConsumer (feasible_same_wallet)
open RegisterMechanismExperimentPaths (firstReceipt secondReceipt firstWorld
  first_receipt_eq second_receipt_eq)
open FiniteJointDecisionBelief FiniteJointDecisionSolver
open FiniteJointDecisionFilteredModel FiniteJointDecisionSupportedPolicy

private theorem source_zero (P : Parameters) (table : Table Act Obs 0) (w : World) :
    sourceValue (source P) (gain P) P.discount table w = 0 := by cases table; rfl

 theorem source_one_equal (P : Parameters) (table : Table Act Obs 1) :
    sourceValue (source P) (gain P) P.discount table (initialWorld P.goal .S) =
      sourceValue (source P) (gain P) P.discount table (initialWorld P.goal .G) := by
  cases table with
  | node a children =>
      simp only [sourceValue, source_zero, mul_zero, add_zero]
      apply Finset.sum_congr rfl
      intro z _
      have ho := first_receipt_eq P.goal a z.1
      change observe P.goal (initialWorld P.goal .S) a z =
        observe P.goal (initialWorld P.goal .G) a z at ho
      change (source P).chance (initialWorld P.goal .G) z *
        gain P a (observe P.goal (initialWorld P.goal .S) a z) = _
      rw [ho]
      rfl

private theorem after_first_one_equal (P : Parameters) (a : Act) (z : Noise)
    (table : Table Act Obs 1) :
    sourceValue (source P) (gain P) P.discount table
        (step P.goal (initialWorld P.goal .S) a z) =
      sourceValue (source P) (gain P) P.discount table
        (step P.goal (initialWorld P.goal .G) a z) := by
  cases table with
  | node b children =>
      simp only [sourceValue, source_zero, mul_zero, add_zero]
      apply Finset.sum_congr rfl
      intro y _
      have ho := second_receipt_eq P.goal a b z.1 y.1
      change observe P.goal (step P.goal (initialWorld P.goal .S) a z) b y =
        observe P.goal (step P.goal (initialWorld P.goal .G) a z) b y at ho
      change (source P).chance (step P.goal (initialWorld P.goal .G) a z) y *
        gain P b (observe P.goal (step P.goal (initialWorld P.goal .S) a z) b y) = _
      rw [ho]
      rfl

 theorem source_two_equal (P : Parameters) (table : Table Act Obs 2) :
    sourceValue (source P) (gain P) P.discount table (initialWorld P.goal .S) =
      sourceValue (source P) (gain P) P.discount table (initialWorld P.goal .G) := by
  cases table with
  | node a children =>
      simp only [sourceValue]
      apply Finset.sum_congr rfl
      intro z _
      have ho := first_receipt_eq P.goal a z.1
      change observe P.goal (initialWorld P.goal .S) a z =
        observe P.goal (initialWorld P.goal .G) a z at ho
      change (source P).chance (initialWorld P.goal .G) z *
        (gain P a (observe P.goal (initialWorld P.goal .S) a z) + P.discount *
          sourceValue (source P) (gain P) P.discount
            (children (observe P.goal (initialWorld P.goal .S) a z))
            (step P.goal (initialWorld P.goal .S) a z)) = _
      rw [ho, after_first_one_equal]
      rfl

 theorem short_source_values_equal (P : Parameters) (H : ℕ) (hH : H ≤ 2)
    (table : Table Act Obs H) :
    sourceValue (source P) (gain P) P.discount table (initialWorld P.goal .S) =
      sourceValue (source P) (gain P) P.discount table (initialWorld P.goal .G) := by
  interval_cases H
  · simp only [source_zero]
  · exact source_one_equal P table
  · exact source_two_equal P table

def knownInfo (P : Parameters) (wallet : Wallet) (m : FaultMechanism) : Info :=
  initialInfo P (fun k => if k = m then 1 else 0)
    (by intro k; split <;> norm_num)
    (by simp) wallet

 theorem known_expect (P : Parameters) (wallet : Wallet) (m : FaultMechanism) (f : World → ℚ) :
    expect (knownInfo P wallet m).1 f = f (initialWorld P.goal m) := by
  change (∑ k : FaultMechanism, (if k = m then 1 else 0 : ℚ) * f (initialWorld P.goal k)) = _
  simp

 theorem known_expectReal (P : Parameters) (wallet : Wallet) (m : FaultMechanism) (f : World → ℝ) :
    expectReal (knownInfo P wallet m).1 f = f (initialWorld P.goal m) := by
  change (∑ k : FaultMechanism, ((if k = m then 1 else 0 : ℚ) : ℝ) * f (initialWorld P.goal k)) = _
  simp

 theorem known_value (P : Parameters) (wallet : Wallet) (m : FaultMechanism)
    {H : ℕ} (table : Table Act Obs H) :
    value (model P) (knownInfo P wallet m) table =
      sourceValue (source P) (gain P) P.discount table (initialWorld P.goal m) := by
  rw [RegisterMechanismDecisionSource.value_eq_source, known_expect]

 theorem short_model_values_equal (P : Parameters) (wallet : Wallet) (H : ℕ) (hH : H ≤ 2)
    (table : Table Act Obs H) :
    value (model P) (knownInfo P wallet .S) table = value (model P) (knownInfo P wallet .G) table := by
  rw [known_value, known_value]
  exact short_source_values_equal P H hH table

/-- One actual complete returned table, shared by both mechanism runs. -/
def commonReturned (P : Parameters) (wallet : Wallet) (H : ℕ) : Table Act Obs H :=
  solve (model P) H (knownInfo P wallet .S)

 theorem commonReturned_feasible (P : Parameters) (wallet : Wallet) (H : ℕ)
    (i : Info) (hi : i.2 = wallet) : Feasible (model P) i (commonReturned P wallet H) :=
  feasible_same_wallet P _ (knownInfo P wallet .S) i hi.symm (solve_feasible _ _ _)

 theorem short_optimal_values_equal (P : Parameters) (wallet : Wallet) (H : ℕ) (hH : H ≤ 2) :
    optimalValue (model P) H (knownInfo P wallet .S) =
      optimalValue (model P) H (knownInfo P wallet .G) := by
  apply le_antisymm
  · have hu := value_le_solve (model P) H (knownInfo P wallet .G)
      (solve (model P) H (knownInfo P wallet .S))
      (feasible_same_wallet P _ (knownInfo P wallet .S) (knownInfo P wallet .G)
        rfl (solve_feasible _ _ _))
    rw [← short_model_values_equal P wallet H hH] at hu
    exact hu
  · have hu := value_le_solve (model P) H (knownInfo P wallet .S)
      (solve (model P) H (knownInfo P wallet .G))
      (feasible_same_wallet P _ (knownInfo P wallet .G) (knownInfo P wallet .S)
        rfl (solve_feasible _ _ _))
    rw [short_model_values_equal P wallet H hH] at hu
    exact hu

 theorem short_common_optimal (P : Parameters) (wallet : Wallet) (H : ℕ) (hH : H ≤ 2)
    (m : FaultMechanism) :
    sourceValue (source P) (gain P) P.discount (commonReturned P wallet H)
      (initialWorld P.goal m) = optimalValue (model P) H (knownInfo P wallet m) := by
  rw [← known_value]
  cases m with
  | S => rfl
  | G =>
      rw [← short_model_values_equal P wallet H hH]
      exact short_optimal_values_equal P wallet H hH

/-- Full real-randomized competitors, not only deterministic alternatives.
The shared return achieves the known-m oracle for both S and G when H≤2. -/
 theorem short_common_dominates_raw (P : Parameters) (wallet : Wallet) (H : ℕ) (hH : H ≤ 2)
    (m : FaultMechanism) (pi : RawCausalPolicy (model P)) (h : pi.Memory)
    (hi : pi.info h = knownInfo P wallet m)
    (hl : SupportedAdmissible (model P) pi H h) :
    rawSourceValue (source P) (gain P) P.discount pi H h (initialWorld P.goal m) ≤
      (sourceValue (source P) (gain P) P.discount (commonReturned P wallet H)
        (initialWorld P.goal m) : ℝ) := by
  have he := rawSourceValue_eq_model (source P)
    (fun i => RegisterJointDecisionConsumer.menu P.tariff i.2)
    (fun i => RegisterJointDecisionConsumer.menu_nonempty P.tariff i.2)
    (RegisterJointDecisionConsumer.advance P.tariff) (gain P) P.discount P.discount_bounds.1 pi H h
  change expectReal (pi.info h).1 (rawSourceValue (source P) (gain P) P.discount pi H h) =
    rawValue (model P) pi H h at he
  have hu := rawValue_le_solve (model P) pi H h hl
  rw [← he, hi, known_expectReal] at hu
  rw [short_common_optimal P wallet H hH m]
  exact hu

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionShort
