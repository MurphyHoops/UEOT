import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscape

/-!
Actual-occupancy path and event-risk bounds for arbitrary measurable observation alphabets with measurable singletons. Finite microscopic and action types provide a finite full observation image. Final reference probabilities and deployment occupancies remain those of the original process and the same policy.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ArbitraryObservationRiskCheck

open MeasureTheory UEOT.V3.TotalVariation UEOT.V3.PathError
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PathObservationEscapeCheck
open scoped BigOperators Classical

noncomputable section

universe u

/-- Each original transition row has exactly the encoded transition TV.
The finite source PMF is constructed as P.map qI inside the proof. -/
theorem escape_transition_row_tv
    {X I Y A : Type u} [Fintype I]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [MeasurableSpace (Option I)] [MeasurableSingletonClass (Option I)]
    (qI : X → I) (i : I → Y) (hi : Function.Injective i)
    (P : ℕ → X → A → PMF X) (Q : ℕ → Y → A → PMF Y)
    (n : ℕ) (x : X) (a : A) :
    tvDist ((P n x a).map (i ∘ qI)).toMeasure
        (Q n (i (qI x)) a).toMeasure =
      tvDist ((P n x a).map (fun x => some (qI x))).toMeasure
        (escapeReferenceKernel i Q n (some (qI x)) a).toMeasure := by
  have h := tvDist_embedded_eq_encoded i hi ((P n x a).map qI)
    (Q n (i (qI x)) a)
  rw [PMF.map_comp, PMF.map_comp] at h
  exact h

/-- Internal factorization adapter: the finite theorem is applied to the
explicit escape model, then path TV and actual deployment weights are restored. -/
theorem factorized_same_policy_path_error
    {X I Y A : Type u} [Fintype X] [Fintype I] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace (Option I)] [MeasurableSingletonClass (Option I)]
    (p₀ : PMF X) (qI : X → I) (i : I → Y) (hi : Function.Injective i)
    (fallback : Y) (P : ℕ → X → A → PMF X) (Q : ℕ → Y → A → PMF Y)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A) (T : ℕ) :
    tvDist ((causalLaw p₀ (riskMicroControlKernel (i ∘ qI) P π) T).map
        (observationHistoryMap (i ∘ qI) T)).toMeasure
      (causalLaw (p₀.map (i ∘ qI)) (riskMacroControlKernel Q π) T).toMeasure ≤
      ∑ n ∈ Finset.range T, ∑ xa,
        (coverageDeploymentRowLaw p₀ (i ∘ qI) P π n xa).toReal *
          tvDist ((P n xa.1 xa.2).map (i ∘ qI)).toMeasure
            (Q n (i (qI xa.1)) xa.2).toMeasure := by
  have hfinite := coverage_same_policy_path_error p₀ (fun x => some (qI x)) P
    (escapeReferenceKernel i Q) (escapePolicy i fallback π) T
  refine (le_of_eq (escape_path_tv p₀ qI i hi fallback P Q π T)).trans
    (hfinite.trans_eq ?_)
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro xa _
  rw [escape_deployment_row_law p₀ qI i fallback P π n,
    ← escape_transition_row_tv qI i hi P Q n xa.1 xa.2]

/-- Actual-occupancy path TV for an arbitrary observation alphabet.
The finite full image range q is constructed from finite X, and a total
decoder fallback is obtained from the existing initial PMF's nonempty support. -/
theorem coverage_arbitrary_observation_path_error
    {X Y A : Type u} [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p₀ : PMF X) (q : X → Y)
    (P : ℕ → X → A → PMF X) (Q : ℕ → Y → A → PMF Y)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A) (T : ℕ) :
    tvDist ((causalLaw p₀ (riskMicroControlKernel q P π) T).map
        (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) T)).toMeasure
      (causalLaw (p₀.map q) (riskMacroControlKernel Q π) T).toMeasure ≤
      ∑ n ∈ Finset.range T, ∑ xa,
        (coverageDeploymentRowLaw p₀ q P π n xa).toReal *
          tvDist ((P n xa.1 xa.2).map q).toMeasure
            (Q n (q xa.1) xa.2).toMeasure := by
  let I : Type u := Set.range q
  letI : Fintype I := (Set.finite_range q).fintype
  letI : MeasurableSpace I := ⊤
  letI : MeasurableSpace (Option I) := ⊤
  let qI : X → I := fun x => ⟨q x, ⟨x, rfl⟩⟩
  let i : I → Y := fun s => s.1
  have hi : Function.Injective i := fun _ _ h => Subtype.ext h
  obtain ⟨x₀, _hx₀⟩ := p₀.support_nonempty
  have h := factorized_same_policy_path_error p₀ qI i hi (q x₀) P Q π T
  simpa only [i, qI, Function.comp_def] using h

/-- Original restricted row certification and original uncovered occupancy
control the path without any global Fintype instance for Y. -/
theorem coverage_arbitrary_observation_certified_path_error
    {X Y A : Type u} [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p₀ : PMF X) (q : X → Y)
    (P : ℕ → X → A → PMF X) (Q : ℕ → Y → A → PMF Y)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (certified : ℕ → X → A → Prop) (ε : ℕ → ℝ) (T : ℕ)
    (hcert : ∀ n, n < T → ∀ x a, certified n x a →
      tvDist ((P n x a).map q).toMeasure (Q n (q x) a).toMeasure ≤ ε n) :
    tvDist ((causalLaw p₀ (riskMicroControlKernel q P π) T).map
        (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) T)).toMeasure
      (causalLaw (p₀.map q) (riskMacroControlKernel Q π) T).toMeasure ≤
      ∑ n ∈ Finset.range T, (ε n + (1 - ε n) *
        (coverageDeploymentRowLaw p₀ q P π n).toMeasure.real
          {xa | ¬ certified n xa.1 xa.2}) := by
  refine (coverage_arbitrary_observation_path_error p₀ q P Q π T).trans ?_
  apply Finset.sum_le_sum
  intro n hn
  exact coverage_expected_error_le (coverageDeploymentRowLaw p₀ q P π n)
    (fun xa => certified n xa.1 xa.2)
    (fun xa => tvDist ((P n xa.1 xa.2).map q).toMeasure
      (Q n (q xa.1) xa.2).toMeasure) (ε n)
    (fun _ => tvDist_le_one _ _)
    (fun xa hx => hcert n (Finset.mem_range.mp hn) xa.1 xa.2 hx)

/-- The microscopic event is transferred against the ORIGINAL Q-reference
event probability. Measurability of F is explicit for the arbitrary alphabet;
the escape construction is only an internal path-TV proof device. -/
theorem coverage_arbitrary_observation_microscopic_failure_risk
    {X Y A : Type u} [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p₀ : PMF X) (q : X → Y)
    (P : ℕ → X → A → PMF X) (Q : ℕ → Y → A → PMF Y)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (certified : ℕ → X → A → Prop) (ε : ℕ → ℝ) (T : ℕ)
    (hcert : ∀ n, n < T → ∀ x a, certified n x a →
      tvDist ((P n x a).map q).toMeasure (Q n (q x) a).toMeasure ≤ ε n)
    (E : Set (CausalHistory X (A × X) T))
    (F : Set (CausalHistory Y (A × Y) T)) (hF : MeasurableSet F)
    (hEF : E ⊆ (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) T) ⁻¹' F) :
    (causalLaw p₀ (riskMicroControlKernel q P π) T).toMeasure.real E ≤
      min 1 ((causalLaw (p₀.map q) (riskMacroControlKernel Q π) T).toMeasure.real F +
        ∑ n ∈ Finset.range T, (ε n + (1 - ε n) *
          (coverageDeploymentRowLaw p₀ q P π n).toMeasure.real
            {xa | ¬ certified n xa.1 xa.2})) := by
  exact (risk_microscopic_event_le_envelope _ _ (measurable_of_countable _)
    E F hF hEF).trans (risk_event_transfer _ _ _
      (coverage_arbitrary_observation_certified_path_error p₀ q P Q π certified ε T hcert)
      F hF)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ArbitraryObservationRiskCheck
