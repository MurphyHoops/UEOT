import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCFormationIdentityBridge

/-!
# SISC protocol evidence: formal formation can be vacuous

The SI-3 formation predicate quantifies over registered observations. If the
protocol has no registered coordinates, *every* candidate is formed at *every*
real tolerance, including negative thresholds. This is not object discovery;
it demonstrates why nonempty, separating interventions are scientific gates.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

universe uX uP uO

/-- Empty observation protocol: no response measurements, hence any candidate
passes the formation predicate vacuously. -/
theorem empty_protocol_forms_every_candidate
    {X : Type uX} {P : Type uP}
    (actual : X → Fin 0 → ℝ) (predicted : P → Fin 0 → ℝ)
    (tau : ℝ) (x : X) (p : P) :
    FormedByResponse actual predicted tau x p := by
  intro j
  exact Fin.elim0 j

/-- Under nonempty evidence, any formed witness implies a nonnegative error
budget. This fails without protocol coverage, as the preceding no-go shows. -/
theorem formed_has_nonnegative_budget
    {X : Type uX} {P : Type uP} {Obs : Type uO} [Nonempty Obs]
    (actual : X → Obs → ℝ) (predicted : P → Obs → ℝ)
    (tau : ℝ) (x : X) (p : P)
    (h : FormedByResponse actual predicted tau x p) : 0 ≤ tau := by
  obtain ⟨j⟩ := ‹Nonempty Obs›
  exact (abs_nonneg _).trans (h j)

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
