import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCKernelLineageBridge
import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCRegisteredCandidateExamples
import Mathlib.Tactic

/-! # N5 finite non-vacuity: a verified flip K, no supplied tp

The existing two-state K is normalized, gives a positive false→true
transition and zero mass to false from source false. The experiment
measures the post-action state. N3's C2 candidate risks certify true;
the P8 reproductive interpretation explicitly declares flip transitions
as new offspring, so the bridge concludes OffspringOf false true.

The P8 compatibility is demonstrated *for this toy model only* and
not claimed for any physical implementation.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

open UEOT.V3.Compression.TheoryCompletion
open UEOT.V3.Compression.TheoryCompletion.ScientificClosure

noncomputable def n5ToySearch :
    RegisteredCausalCandidateProtocol Bool Unit Bool PUnit.{1} where
  kernel := n5PhysicalKernel
  source := false
  action := ()
  read := fun y _ => if y then 1 else 0
  prediction := fun c _ => if c then 1 else 0
  registered := Finset.univ
  causal := fun _ => True
  tolerance := 1 / 4
  interval := fun c => exactToyInterval (if c then 0 else 1)
  observed_nonempty := ⟨PUnit.unit⟩

theorem n5_toy_risk_true :
    registeredCandidateRisk n5ToySearch true = 0 := by
  norm_num [registeredCandidateRisk, n5ToySearch,
    n5PhysicalKernel, flipObservationKernel]

theorem n5_toy_risk_false :
    registeredCandidateRisk n5ToySearch false = 1 := by
  norm_num [registeredCandidateRisk, n5ToySearch,
    n5PhysicalKernel, flipObservationKernel]

theorem n5_toy_support_calibrated :
    (supportAdmittedProtocol n5ToySearch).Calibrated := by
  intro c _
  rw [support_admitted_risk_eq_original]
  cases c
  · rw [n5_toy_risk_false]
    norm_num [supportAdmittedProtocol, n5ToySearch, exactToyInterval,
      IntervalCertificate.totalRadius]
  · rw [n5_toy_risk_true]
    norm_num [supportAdmittedProtocol, n5ToySearch, exactToyInterval,
      IntervalCertificate.totalRadius]

theorem n5_toy_supported_unique :
    resolveRegisteredCandidates (supportAdmittedProtocol n5ToySearch) =
      .unique true := by
  apply registered_unique_identified_of_calibrated_margin
    (supportAdmittedProtocol n5ToySearch) true 0
  · simp [supportAdmittedProtocol, n5ToySearch]
  · norm_num [supportAdmittedProtocol, n5ToySearch,
      n5PhysicalKernel, flipObservationKernel]
  · rw [support_admitted_risk_eq_original, n5_toy_risk_true]
    norm_num [supportAdmittedProtocol, n5ToySearch]
  · intro d _ _ hne
    cases d
    · rw [support_admitted_risk_eq_original, n5_toy_risk_false]
      norm_num [supportAdmittedProtocol, n5ToySearch]
    · exact False.elim (hne rfl)
  · intro d _
    simp [supportAdmittedProtocol, n5ToySearch, exactToyInterval,
      IntervalCertificate.totalRadius]
  · exact n5_toy_support_calibrated

theorem n5_toy_reproductive_transmission :
    n5ReproductiveInterpretation.ReproductiveTransmission
      (fun x y => n5ToySearch.kernel.mass x n5ToySearch.action y) := by
  intro x y hpos
  cases x <;> cases y <;>
    simp_all [LineageSemantics.OffspringOf,
      LineageSemantics.SameObject, n5ToySearch,
      n5ReproductiveInterpretation, n5PhysicalKernel,
      flipObservationKernel]

/-- Verified witness that N3+K support+P8 lineage can actually fire on a
registered finite process; it is not an unconditional result in nature. -/
theorem n5_toy_derived_offspring :
    n5ReproductiveInterpretation.OffspringOf false true ∧
    ¬ n5ReproductiveInterpretation.SameObject false true := by
  exact support_admitted_unique_compatible_offspring
    n5ToySearch n5ReproductiveInterpretation
    n5_toy_reproductive_transmission n5_toy_support_calibrated
    true n5_toy_supported_unique

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
