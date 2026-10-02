import UEOT.V3.Compression.CrossTrack.InteractionBindingIsolation
import UEOT.Core.Finite

/-!
# Minimal separating probe families

Once a finite probe family separates all richer parent candidates, a finite
inclusion-minimal separating subfamily exists.  Together with monotonicity of
the interaction isolation conorm, this is the first exact probe-selection
surface for later active experiment design.
-/

namespace UEOT.V3.Compression.CrossTrack

open UEOT.V3

universe uA uI uY

noncomputable section

variable {A : Type uA} {I : Type uI} {Y : Type uY}
variable [MeasurableSpace Y]

theorem pairwiseInteractionSeparating_nonempty_probes
    [Nontrivial A]
    (F : InteractionResponseFamily A I Y)
    (probes : Finset I)
    (hsep : PairwiseInteractionSeparating F probes) :
    probes.Nonempty := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne A
  rcases hsep hab with ⟨i, hi, _hne⟩
  exact ⟨i, hi⟩

/-- Any finite separating experiment admits an inclusion-minimal separating
subexperiment. -/
theorem exists_minimal_pairwiseSeparating_probeFamily
    (F : InteractionResponseFamily A I Y)
    (probes : Finset I)
    (hsep : PairwiseInteractionSeparating F probes) :
    ∃ minimalProbes,
      minimalProbes ⊆ probes ∧
      UEOT.Finite.Minimal (PairwiseInteractionSeparating F) minimalProbes := by
  exact UEOT.Finite.exists_minimal_subset
    (PairwiseInteractionSeparating F) probes hsep

variable [Fintype A] [Nontrivial A] [MetricSpace A]

/-- Every inclusion-minimal separating probe family still has positive
canonical interaction isolation. -/
theorem minimalSeparatingProbeFamily_positiveIsolation
    (F : InteractionResponseFamily A I Y)
    (probes : Finset I)
    (hmin : UEOT.Finite.Minimal (PairwiseInteractionSeparating F) probes) :
    ∃ hprobes : probes.Nonempty,
      0 < interactionIsolationConorm F probes hprobes := by
  have hnonempty := pairwiseInteractionSeparating_nonempty_probes
    F probes hmin.1
  exact ⟨hnonempty,
    (interactionIsolationConorm_pos_iff_pairwiseSeparating
      F probes hnonempty).2 hmin.1⟩

end

end UEOT.V3.Compression.CrossTrack
