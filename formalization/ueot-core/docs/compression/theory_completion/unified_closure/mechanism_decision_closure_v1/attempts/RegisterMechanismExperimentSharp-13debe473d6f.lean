import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismExperimentLaw

/-!
# Same-wallet attainment of the sharp H3 experiment bound

The proof separates the universal all-action bound from its legal attaining
experiment. Its one correct write is prepaid before any fault/None outcome.
The following two real dispatch ticks use the same remaining wallet.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismExperimentSharp

open RegisterJointDecisionSource (Act Obs Noise cap effective)
open RegisterJointDecisionExecution (prepend)
open RegisterMechanismDecisionSource
open RegisterMechanismExperimentPaths RegisterMechanismExperimentZero
open RegisterMechanismTableLaw RegisterMechanismExperimentLaw RegisterMechanismExperimentRate
open RegisterJointDecisionConsumer (charge)
open UEOT.V3.TotalVariation
open FiniteJointDecisionSolver (Table)

local instance : MeasurableSpace (List (Act × Obs)) := ⊤
local instance : MeasurableSingletonClass (List (Act × Obs)) := by infer_instance
local instance : MeasurableSpace (Table Act Obs 3) := ⊤
local instance : MeasurableSingletonClass (Table Act Obs 3) := by infer_instance

@[simp] theorem idle_charge_zero (tariff : ℚ) (goal : Bool) (w : World) (j : Bool) (z : Noise) :
    charge tariff (observe goal w (some (j,none)) z) = 0 := by
  have hcap : cap (some (j,none)) = 0 := rfl
  have hf : RegisterJointDecisionSource.feeUnit goal w (some (j,none)) z = 0 := by
    have hn := RegisterJointDecisionSource.feeUnit_nonneg goal w (some (j,none)) z
    have hl := RegisterJointDecisionSource.feeUnit_le_cap goal w (some (j,none)) z
    rw [hcap] at hl
    exact le_antisymm hl hn
  unfold RegisterJointDecisionSource.feeUnit at hf
  change (if (observe goal w (some (j,none)) z).2 then 1 else 0 : ℚ) = 0 at hf
  cases ho : (observe goal w (some (j,none)) z).2 <;> simp_all [charge]

theorem charge_le_tariff (tariff : ℚ) (hc : 0 ≤ tariff) (o : Obs) : charge tariff o ≤ tariff := by
  unfold charge
  split <;> linarith

/-- Same-world prepayment on EVERY full primitive tape, including failed
writes and missing child1. No event is postselected or given a fresh wallet. -/
theorem separation_prepaid (P : PhysicalExperiment) (tariff B : ℚ) (hc : 0 ≤ tariff) (hB : tariff ≤ B)
    (m : FaultMechanism) (z : Fin 3 → Noise) :
    PrepaidHistory tariff B
      (packedExecute P.goal (separationTable P.goal) (initialWorld P.goal m) z).history := by
  have hf := charge_le_tariff tariff hc
    (observe P.goal (initialWorld P.goal m) (some (false,some P.goal)) (z 0))
  have hrem : 0 ≤ B - charge tariff
      (observe P.goal (initialWorld P.goal m) (some (false,some P.goal)) (z 0)) := by linarith
  simp only [separationTable,packedExecute,prepend,zero_history,PrepaidHistory,idle_charge_zero,
    cap,effective,Bool.false_eq_true,if_false,Option.getD_some,Option.isSome_some,
    Option.isSome_none,if_true,mul_one,mul_zero,sub_zero]
  exact ⟨hB,hrem,hrem,trivial⟩

/-- The universal upper bound and one actual legal attaining table together
are the maximum/supremum statement Δ(3,B)=r²(1-r), for B≥c. -/
theorem H3_experiment_sharp (P : PhysicalExperiment) (tariff B : ℚ) (hc : 0 < tariff) (hB : tariff ≤ B) :
    (∀ μ : PMF (Table Act Obs 3),
      tvDist (seededLaw P μ id .S).toMeasure (seededLaw P μ id .G).toMeasure ≤
        (P.normal : ℝ)^2 * (1-P.normal)) ∧
    (∀ m z, PrepaidHistory tariff B
      (packedExecute P.goal (separationTable P.goal) (initialWorld P.goal m) z).history) ∧
    tvDist (separationLaw P .S).toMeasure (separationLaw P .G).toMeasure =
      (P.normal : ℝ)^2 * (1-P.normal) :=
  ⟨fun μ => seeded_H3_TV_upper P μ id, separation_prepaid P tariff B hc.le hB,separation_TV_exact P⟩

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismExperimentSharp
