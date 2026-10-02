import UEOT.V3.Compression.CrossTrack.ParentSemanticCore

/-!
# Track X — X2 exact parent-semantic descent

Parent completion may be nonunique while the induced effective dynamics are
exactly child-determined.  The dynamics descent is precisely M-QD quotient
descent, not a new primitive.
-/

namespace UEOT.V3.Compression.CrossTrack

open Function
open UEOT.V3
open UEOT.V3.Compression.QuotientDescent
open UEOT.V3.Compression.InvariantSetGaugeInvariance
open UEOT.V3.Compression.TopologyChangingGoaL1ResidualConorm
open UEOT.V3.Compression.TopologyChangingGoaTrackSClosure

universe uP uC uS

noncomputable section

variable {P : Type uP} {C : Type uC}
variable {S : Type uS}
noncomputable local instance parentSemanticDescentDecidableEq : DecidableEq S :=
  Classical.decEq S

/-- **X2 — exact parent-kernel descent.**

This is exactly M-QD `existsUnique_descend` specialized to a finite Markov
matrix family. -/
theorem x2_exactParentKernelDescent
    (pi : P → C) (K : P → Matrix S S ℝ)
    (hpi : Surjective pi)
    (hcompat : FiberCompatible pi K) :
    ∃! Kbar : C → Matrix S S ℝ, Kbar ∘ pi = K := by
  exact existsUnique_descend pi K hpi hcompat

/-- Row stochasticity transfers to the descended child-level kernel family
because every child value has a parent representative. -/
theorem x2_descendedKernel_rowStochastic
    [Fintype S]
    (pi : P → C) (K : P → Matrix S S ℝ)
    (hpi : Surjective pi)
    (hK : ∀ p, K p ∈ Matrix.rowStochastic ℝ S)
    (Kbar : C → Matrix S S ℝ)
    (hfactor : Kbar ∘ pi = K) :
    ∀ c, Kbar c ∈ Matrix.rowStochastic ℝ S := by
  intro c
  rcases hpi c with ⟨p, rfl⟩
  have heq : Kbar (pi p) = K p := by
    simpa only [Function.comp_apply] using congrFun hfactor p
  simpa only [heq] using hK p

/-- Once exact descent has produced a stochastic child-level kernel, positive
Track-S residual isolation gives unique long-run invariant semantics for that
child evidence.  This does not select a unique parent completion. -/
theorem x2_descendedKernel_uniqueSemantics
    [Fintype S] [Nonempty S]
    (Kbar : C → Matrix S S ℝ)
    (hKbar : ∀ c, Kbar c ∈ Matrix.rowStochastic ℝ S)
    (c : C)
    (hcard : 1 < Fintype.card S)
    (hisolation : 0 < l1ResidualConorm (Kbar c)) :
    ∃! mu : stdSimplex ℝ S,
      mu ∈ invariantLawSet (Kbar c) (hKbar c) := by
  exact
    (finite_markov_isolation_iff_unique_semantics
      (Kbar c) (hKbar c) hcard).1 hisolation

end

end UEOT.V3.Compression.CrossTrack
