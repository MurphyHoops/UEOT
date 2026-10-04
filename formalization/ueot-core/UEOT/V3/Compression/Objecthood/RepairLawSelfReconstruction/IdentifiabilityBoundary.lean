import UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction.ProgramSemantics

/-!
# RLSR3 — corruption / identifiability boundary

Self-reconstruction needs surviving information.  If the corruption/observation
channel collapses two behaviorally distinct repair programs to one observation,
then no deterministic reconstructor seeing only that observation can be exactly
behavior-correct for both.
-/

namespace UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction

open Set

universe uX uA uP uO

variable {X : Type uX} {A : Type uA} {Program : Type uP} {Obs : Type uO}

/-- Exact carrier-relative behavioral reconstruction from an observation. -/
def ExactBehavioralReconstructor
    (T : TrustedRepairSubstrate Program X A) (K : Set X)
    (observe : Program → Obs) (reconstruct : Obs → Program) : Prop :=
  ∀ r, RepairProgramEquivalentOn T K (reconstruct (observe r)) r

/-- Any exact reconstructor forces the observation channel to separate
behavioral equivalence classes: equal observations imply equivalent behavior. -/
theorem observation_separates_behavior_of_exact_reconstructor
    (T : TrustedRepairSubstrate Program X A) (K : Set X)
    (observe : Program → Obs) (reconstruct : Obs → Program)
    (hexact : ExactBehavioralReconstructor T K observe reconstruct)
    {r₁ r₂ : Program}
    (hobs : observe r₁ = observe r₂) :
    RepairProgramEquivalentOn T K r₁ r₂ := by
  intro x hx
  have h₁ := hexact r₁ x hx
  have h₂ := hexact r₂ x hx
  calc
    T.execute r₁ x = T.execute (reconstruct (observe r₁)) x := h₁.symm
    _ = T.execute (reconstruct (observe r₂)) x := by rw [hobs]
    _ = T.execute r₂ x := h₂

/-- **RLSR identifiability no-go.** Behaviorally distinct repair programs that
collapse to the same corrupted observation cannot both be exactly reconstructed
by any deterministic observation-only decoder. -/
theorem no_exact_behavioral_reconstruction_of_observation_collision
    (T : TrustedRepairSubstrate Program X A) (K : Set X)
    (observe : Program → Obs)
    {r₁ r₂ : Program}
    (hdist : ¬ RepairProgramEquivalentOn T K r₁ r₂)
    (hobs : observe r₁ = observe r₂) :
    ¬ ∃ reconstruct : Obs → Program,
        ExactBehavioralReconstructor T K observe reconstruct := by
  rintro ⟨reconstruct, hexact⟩
  exact hdist
    (observation_separates_behavior_of_exact_reconstructor
      T K observe reconstruct hexact hobs)

/-- Pointwise version: for a fixed reconstructor, a collision of behaviorally
distinct programs prevents simultaneous correctness on those two programs. -/
theorem no_pairwise_behavioral_reconstruction_of_collision
    (T : TrustedRepairSubstrate Program X A) (K : Set X)
    (observe : Program → Obs) (reconstruct : Obs → Program)
    {r₁ r₂ : Program}
    (hdist : ¬ RepairProgramEquivalentOn T K r₁ r₂)
    (hobs : observe r₁ = observe r₂) :
    ¬ (RepairProgramEquivalentOn T K (reconstruct (observe r₁)) r₁ ∧
       RepairProgramEquivalentOn T K (reconstruct (observe r₂)) r₂) := by
  rintro ⟨h₁, h₂⟩
  apply hdist
  intro x hx
  calc
    T.execute r₁ x = T.execute (reconstruct (observe r₁)) x := (h₁ x hx).symm
    _ = T.execute (reconstruct (observe r₂)) x := by rw [hobs]
    _ = T.execute r₂ x := h₂ x hx

end UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
