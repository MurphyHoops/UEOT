import UEOT

/-!
Original commitment: funding conditions need an exact quantifier for a shared actual population source.
Existing result: g>=c funds every registered ongoing plan; g<c has a positive-mass failure for fixedPlan j at a real retained parent.
Premise reduced: connect those SAME-source results into the exact ALL-registered-plans guarantee, not an individual-plan necessity claim.
Model: original own-program source/hazard1/4/uniform labels/shared valid-idle port, finite R>=0/g>=0 and at least one actually occupied initial slot.
Consumer: original ResourceViable for every registered plan iff c<=g, with the original three-founder population as actual consumer.

Each plan's AE assertion uses its own actual pushforward of the SAME primitive
infiniteSource. No common measurable event over uncountably many plans is
assumed. This is NOT (for every plan, funding iff c<=g): the reverse direction
uses exactly the existing fixed real-parent counterexample, and says nothing
new about alternatingPlan or other individual policies. No source/action/
observation/right/data changes, no general organizational World are introduced.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterPopulationUniformFunding
open MeasureTheory ProbabilityTheory
open UEOT.V3.Compression.Objecthood.ResourceClosure
open RegisterTimestampedBirthSource (ClockedOrganism ClockedRecord)
open RegisterPopulationHistorySource (Store)
open RegisterPopulationFundedProtocol RegisterPopulationFundedInfinite RegisterPopulationFundingObstruction
noncomputable section

local instance {d : ℕ} : MeasurableSpace (Option (ClockedRecord d)) := ⊤

/-- Definition of the scientific guarantee, not an assumed implementation
certificate. Plan ranges over actual registered compiled/literal work schedules. -/
def AllRegisteredPlansFunded {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n) (g R : ℝ) : Prop :=
  ∀ plan : ℕ → ℕ × Command,
    ∀ᵐ ts ∂ RegisterPopulationFundedInfinite.recordPathLaw i c s plan (PMF.uniformOfFintype Bool)
      (1/4) (by exact_mod_cast (by norm_num : (1/4 : ℝ)≤1)),
      ResourceViable R (fun t => credit g (ts t)) (fun t => fee (ts t))

/-- Exact uniform guarantee on the SAME actual population/primitive source.
Initial occupancy is a literal lookup, not a supplied parent/identity function. -/
theorem all_registered_plans_funded_iff {n : ℕ} (i : Fin n) (c : NNReal) (s : Store n)
    (hoccupied : ∃ j p, RegisterPopulationHistorySource.lookup s j=some p)
    (g R : ℝ) (hg : 0≤g) (hR : 0≤R) :
    AllRegisteredPlansFunded i c s g R ↔ (c : ℝ)≤g := by
  constructor
  · intro hall
    by_contra hn
    obtain ⟨j,p,hp⟩ := hoccupied
    exact subcost_fixed_protocol_not_ae_viable i c s j p hp g R hg (lt_of_not_ge hn) (hall (fixedPlan j))
  · intro hc plan
    exact actual_infinite_law_resource_viable i c s plan (PMF.uniformOfFintype Bool)
      (1/4) (by exact_mod_cast (by norm_num : (1/4 : ℝ)≤1)) g R hc hR

/-- The original actual false,false,true founders discharge the initial
occupancy requirement by their real allocator lookup. No fresh preparation. -/
theorem original_founders_uniform_funding_iff (g R : ℝ) (hg : 0≤g) (hR : 0≤R) :
    AllRegisteredPlansFunded (0 : Fin 1) 1 RegisterOwnProgramPopulation.witnessInitial g R ↔ 1≤g := by
  apply all_registered_plans_funded_iff _ _ _ _ g R hg hR
  exact ⟨0,⟨⟨[],fun _=>false,false⟩,[(0,false)],0⟩,rfl⟩

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterPopulationUniformFunding

namespace UniformFundingActualConsumers
open MeasureTheory ProbabilityTheory
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open RegisterPopulationUniformFunding RegisterActuatorPopulationScale
open RegisterTimestampedBirthSource (ClockedOrganism)
noncomputable section
example : AllRegisteredPlansFunded (0 : Fin 1) 1 RegisterOwnProgramPopulation.witnessInitial 1 0 :=
  (original_founders_uniform_funding_iff 1 0 (by norm_num) (by norm_num)).mpr (by norm_num)
example (R : ℝ) (hR : 0≤R) :
    ¬ AllRegisteredPlansFunded (0 : Fin 1) 1 RegisterOwnProgramPopulation.witnessInitial (1/2) R := by
  intro h
  have hg := (original_founders_uniform_funding_iff (1/2) R (by norm_num) hR).mp h
  norm_num at hg
-- Same registered fine actuator population; occupancy obtained from its ACTUAL initial slot0.
example (hidden : Bool) (g R : ℝ) (hg : 0≤g) (hR : 0≤R) :
    AllRegisteredPlansFunded (1 : Fin 3) 1 (witnessStore hidden) g R ↔ 1≤g := by
  apply all_registered_plans_funded_iff _ _ _ _ g R hg hR
  exact ⟨0,embedClocked hidden ⟨⟨[],fun _=>false,false⟩,[(0,false)],0⟩,rfl⟩
-- Without actual occupancy the premise is NOT silently totalized to a fake object.
example : ¬ ∃ j p, RegisterPopulationHistorySource.lookup ([] : RegisterPopulationHistorySource.Store 1) j=some p := by
  simp [RegisterPopulationHistorySource.lookup]
#print axioms all_registered_plans_funded_iff
#print axioms original_founders_uniform_funding_iff
end
end UniformFundingActualConsumers
