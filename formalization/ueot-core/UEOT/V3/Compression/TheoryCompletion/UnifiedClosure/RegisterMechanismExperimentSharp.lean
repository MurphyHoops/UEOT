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

local instance : MeasurableSpace Noise := ⊤
local instance : MeasurableSingletonClass Noise := by infer_instance
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

/-- Literal allowed history law (the terminal seed may also be retained in
`seededLaw`, whose uniform upper bound is stronger). -/
noncomputable def allowedHistoryLaw (P : PhysicalExperiment) (μ : PMF (Table Act Obs 3))
    (m : FaultMechanism) : PMF (List (Act × Obs)) :=
  (commonInput μ (tapeLaw (primitiveLaw P) 3)).map (fun x =>
    (packedExecute P.goal x.1 (initialWorld P.goal m) x.2).history)

theorem allowedHistoryLaw_upper (P : PhysicalExperiment) (μ : PMF (Table Act Obs 3)) :
    tvDist (allowedHistoryLaw P μ .S).toMeasure (allowedHistoryLaw P μ .G).toMeasure ≤
      P.normal^2*(1-P.normal) := by
  let ν := tapeLaw (primitiveLaw P) 3
  have h := tv_map_le_event (commonInput μ ν)
    (fun x => (packedExecute P.goal x.1 (initialWorld P.goal .S) x.2).history)
    (fun x => (packedExecute P.goal x.1 (initialWorld P.goal .G) x.2).history)
    {x | x.2 ∈ NFN} (fun x hx => history_three_eq_unless_NFN P.goal x.1 x.2 hx)
  rw [commonInput_event,NFN_mass] at h
  exact h

theorem separation_pure_law (P : PhysicalExperiment) (m : FaultMechanism) :
    allowedHistoryLaw P (PMF.pure (separationTable P.goal)) m = separationLaw P m := by
  simp [allowedHistoryLaw,commonInput,PMF.map_comp,Function.comp_def,
    separationLaw,tableHistoryLaw_eq_tape]

/-- Exactly the H3 experiment comparison: any common real mixed complete
plan, legal before outcomes on all positive actual S/G paths. -/
def AttainableDistance (P : PhysicalExperiment) (tariff B : ℚ) : Set ℝ :=
  {v | ∃ μ : PMF (Table Act Obs 3),
    (∀ m t, t ∈ μ.support → ∀ z, z ∈ (tapeLaw (primitiveLaw P) 3).support →
      PrepaidHistory tariff B (packedExecute P.goal t (initialWorld P.goal m) z).history) ∧
    tvDist (allowedHistoryLaw P μ .S).toMeasure (allowedHistoryLaw P μ .G).toMeasure = v}

/-- The literal registered distance supremum is achieved, not merely bounded
by a coupling and not merely a candidate value from experiment search. -/
theorem H3_distance_greatest (P : PhysicalExperiment) (tariff B : ℚ)
    (hc : 0 < tariff) (hB : tariff ≤ B) :
    IsGreatest (AttainableDistance P tariff B) (P.normal^2*(1-P.normal)) := by
  constructor
  · refine ⟨PMF.pure (separationTable P.goal), ?_, ?_⟩
    · intro m t ht z hz
      have he : t = separationTable P.goal := by simpa using ht
      subst t
      exact separation_prepaid P tariff B hc.le hB m z
    · simp only [separation_pure_law]
      exact separation_TV_exact P
  · rintro v ⟨μ,hpay,he⟩
    rw [← he]
    exact allowedHistoryLaw_upper P μ

theorem H3_distance_supremum (P : PhysicalExperiment) (tariff B : ℚ)
    (hc : 0 < tariff) (hB : tariff ≤ B) :
    sSup (AttainableDistance P tariff B) = P.normal^2*(1-P.normal) := by
  have hg := H3_distance_greatest P tariff B hc hB
  exact le_antisymm (csSup_le ⟨_,hg.1⟩ hg.2) (le_csSup ⟨_,hg.2⟩ hg.1)

/-! Conditioning keeps even a non-atomic private seed, including any fresh
terminal randomizer, independent of the physical tape. Once that seed is fixed
the source only needs its finite action table; the terminal event can still
depend on the entire seed. The expectation below integrates the actual binary
risk over the same seed law for both fixed mechanisms. -/
open MeasureTheory UEOT.V3.BinaryTesting

noncomputable def conditionalTestRisk (P : PhysicalExperiment) {H : ℕ}
    (t : Table Act Obs H) (A : Set (List (Act × Obs))) : ℝ :=
  binaryRisk (seededLaw P (PMF.pure ()) (fun _ => t) .S).toMeasure
    (seededLaw P (PMF.pure ()) (fun _ => t) .G).toMeasure (Prod.snd ⁻¹' A)

/-- The terminal measurement is an arbitrary (seed-dependent) decision event.
Writing nonnegative expectation as a lower integral avoids imposing an
extraneous integrability certificate on every legal measurable procedure. -/
noncomputable def privateTestRisk {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) (P : PhysicalExperiment) {H : ℕ}
    (choose : Seed → Table Act Obs H) (test : Seed → Set (List (Act × Obs))) : ENNReal :=
  ∫⁻ s, ENNReal.ofReal (conditionalTestRisk P (choose s) (test s)) ∂ν

/-- For every probability space of independent private coins, even an
arbitrary seed-aware terminal test faces the full finite all-fault obstruction. -/
theorem arbitrary_private_finite_error {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] (P : PhysicalExperiment) {H : ℕ}
    (choose : Seed → Table Act Obs H) (test : Seed → Set (List (Act × Obs))) :
    ENNReal.ofReal ((1/2:ℝ) * (1-P.normal)^H) ≤ privateTestRisk ν P choose test := by
  have h (s : Seed) := classification_finite_lower P (PMF.pure ()) (fun _ => choose s)
    (Prod.snd ⁻¹' test s) ((Set.to_countable _).measurableSet.preimage measurable_snd)
  calc
    _ = ∫⁻ _s : Seed, ENNReal.ofReal ((1/2:ℝ) * (1-P.normal)^H) ∂ν := by simp
    _ ≤ _ := lintegral_mono (fun s => ENNReal.ofReal_le_ofReal (h s))

/-- At H3 this same unrestricted conditioning gives the sharp error lower
bound, including every terminal private coin and its correlation with the
controller's *own* earlier coins. Physical noise remains independent. -/
theorem arbitrary_private_H3_error {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] (P : PhysicalExperiment)
    (choose : Seed → Table Act Obs 3) (test : Seed → Set (List (Act × Obs))) :
    ENNReal.ofReal ((1/2:ℝ) * (1-P.normal^2*(1-P.normal))) ≤
      privateTestRisk ν P choose test := by
  have h (s : Seed) := H3_classification_lower P (PMF.pure ()) (fun _ => choose s)
    (Prod.snd ⁻¹' test s) ((Set.to_countable _).measurableSet.preimage measurable_snd)
  calc
    _ = ∫⁻ _s : Seed, ENNReal.ofReal ((1/2:ℝ) * (1-P.normal^2*(1-P.normal))) ∂ν := by simp
    _ ≤ _ := lintegral_mono (fun s => ENNReal.ofReal_le_ofReal (h s))

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismExperimentSharp
