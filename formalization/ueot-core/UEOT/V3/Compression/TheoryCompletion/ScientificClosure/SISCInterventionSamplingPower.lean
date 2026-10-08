import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCInterventionTransferAudit
import UEOT.V3.BoundedLossTwoSided
import Mathlib.Tactic

/-!
# N6-D finite-sample intervention provenance identification power

Reuse the original P-STAT-08 finite two-sided Hoeffding/union-bound theorem,
then compose the N6-B audited parent set with the existing SI-2 response
separation lemma. This gives high-probability unique **source-model**
recovery, not experimental proof of genealogy.

The sampling assumptions are explicit: independent repeated experimental
units (Fin N), each carrying a *joint registered intervention-output
record* Z and measurable [0,1] coordinate maps for every tested probe.
Joint per-unit potential outcome vectors are NOT assumed observable in
ordinary single-treatment observational experiments. If data cannot be
legitimately collected in that format, this theorem does not apply.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

open MeasureTheory ProbabilityTheory Real
open UEOT.V3.BoundedLossSampling
open UEOT.V3.BoundedLossTwoSided

universe uP uC uI uΩ uZ

/-- The operational source enumerator uses an actual empirical mean for
each independently registered intervention coordinate. No parent token
is supplied to this *construction*; source appears only in certification
theorems and the separate model-match hypothesis. -/
noncomputable def sampledInterventionAudit
    {Parent : Type uP} {Child : Type uC} {Probe : Type uI}
    [Fintype Parent]
    {Z : Type uZ} {Ω : Type uΩ} {N : ℕ}
    (audit : FiniteInterventionTransferAudit Parent Child Probe)
    (outcome : Probe → Z → ℝ)
    (sample : Fin N → Ω → Z) (ω : Ω) (u : ℝ) :
    FiniteInterventionTransferAudit Parent Child Probe :=
  { audit with
    observedResponse := fun _ i => empiricalRisk (outcome i) sample ω
    tolerance := u }

/-- On a simultaneous good coordinate event, the externally registered
true source fits every measured probe at tolerance u. A full model-match
assumption, not an inference from intervention names, is mandatory. -/
theorem sampled_true_parent_fits_of_uniform_coordinate_accuracy
    {Parent : Type uP} {Child : Type uC} {Probe : Type uI}
    [Fintype Parent]
    {Z : Type uZ} [MeasurableSpace Z]
    {Ω : Type uΩ} {N : ℕ}
    (audit : FiniteInterventionTransferAudit Parent Child Probe)
    (outcome : Probe → Z → ℝ)
    (sample : Fin N → Ω → Z)
    (ω : Ω) (u : ℝ) (parent : Parent) (child : Child)
    (dataLaw : Measure Z)
    (hModel : ∀ i, trueRisk dataLaw (outcome i) = audit.referenceResponse parent i)
    (hUniform : ∀ i,
      |empiricalRisk (outcome i) sample ω -
       trueRisk dataLaw (outcome i)| ≤ u) :
    FormedByResponse
      (fun c i => (sampledInterventionAudit audit outcome sample ω u).observedResponse c i)
      (sampledInterventionAudit audit outcome sample ω u).referenceResponse
      (sampledInterventionAudit audit outcome sample ω u).tolerance
      child parent := by
  intro i
  change |empiricalRisk (outcome i) sample ω -
    audit.referenceResponse parent i| ≤ u
  rw [← hModel i]
  exact hUniform i

/-- Deterministic scientific power: a real source has an independent
transfer record and registered probes that separate it from all other
candidate models by >2u. On uniformly accurate sample means, it is
the unique member of the new sampled audited source set. -/
theorem sampled_audited_source_unique_on_good_event
    {Parent : Type uP} {Child : Type uC} {Probe : Type uI}
    [Fintype Parent] [DecidableEq Parent]
    {Z : Type uZ} [MeasurableSpace Z]
    {Ω : Type uΩ} {N : ℕ}
    (audit : FiniteInterventionTransferAudit Parent Child Probe)
    (outcome : Probe → Z → ℝ)
    (sample : Fin N → Ω → Z)
    (ω : Ω) (u : ℝ) (parent : Parent) (child : Child)
    (dataLaw : Measure Z)
    (hreg : parent ∈ audit.registered)
    (htransfer : audit.authenticatedTransfer parent child)
    (hModel : ∀ i, trueRisk dataLaw (outcome i) = audit.referenceResponse parent i)
    (hgap : LocalResponseGap audit.referenceResponse u parent)
    (hUniform : ∀ i,
      |empiricalRisk (outcome i) sample ω -
       trueRisk dataLaw (outcome i)| ≤ u) :
    auditedSourceCandidates
      (sampledInterventionAudit audit outcome sample ω u) child = {parent} := by
  apply audited_source_candidates_eq_singleton_of_gap
    (sampledInterventionAudit audit outcome sample ω u) child parent
  · exact hreg
  · exact htransfer
  · exact sampled_true_parent_fits_of_uniform_coordinate_accuracy
      audit outcome sample ω u parent child dataLaw hModel hUniform
  · exact hgap

/-- High-probability identification under noncircular source model-match,
intervention-response gap and authenticated transfer evidence. The
probability penalty counts PROBES, not candidate labels, since the same
simultaneous coordinate-good event controls every registered candidate. -/
theorem measure_failure_to_identify_interventional_parent_le
    {Parent : Type uP} {Child : Type uC} {Probe : Type uI}
    [Fintype Parent] [DecidableEq Parent] [Fintype Probe]
    {Z : Type uZ} [MeasurableSpace Z]
    {Ω : Type uΩ} [MeasurableSpace Ω]
    {N : ℕ} (hN : 0 < N)
    (audit : FiniteInterventionTransferAudit Parent Child Probe)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (dataLaw : Measure Z)
    (outcome : Probe → Z → ℝ)
    (hOutcomeMeas : ∀ i, Measurable (outcome i))
    (hOutcome01 : ∀ i z, outcome i z ∈ Set.Icc (0 : ℝ) 1)
    (sample : Fin N → Ω → Z)
    (hSampleMeas : ∀ n, Measurable (sample n))
    (hIID : iIndepFun sample μ)
    (hSampleLaw : ∀ n, μ.map (sample n) = dataLaw)
    (u : ℝ) (hu : 0 ≤ u)
    (parent : Parent) (child : Child)
    (hreg : parent ∈ audit.registered)
    (htransfer : audit.authenticatedTransfer parent child)
    (hModel : ∀ i, trueRisk dataLaw (outcome i) = audit.referenceResponse parent i)
    (hgap : LocalResponseGap audit.referenceResponse u parent) :
    μ.real {ω |
      auditedSourceCandidates
        (sampledInterventionAudit audit outcome sample ω u) child ≠ {parent}} ≤
      (Fintype.card Probe : ℝ) * (2 * exp (-2 * (N : ℝ) * u ^ 2)) := by
  have hsubset :
      {ω |
        auditedSourceCandidates
          (sampledInterventionAudit audit outcome sample ω u) child ≠ {parent}} ⊆
      {ω | ∃ i : Probe,
        u < |empiricalRisk (outcome i) sample ω - trueRisk dataLaw (outcome i)|} := by
    intro ω hfail
    by_contra hnot
    have hUniform : ∀ i,
        |empiricalRisk (outcome i) sample ω -
          trueRisk dataLaw (outcome i)| ≤ u := by
      intro i
      by_contra hi
      exact hnot ⟨i, lt_of_not_ge hi⟩
    exact hfail (sampled_audited_source_unique_on_good_event
      audit outcome sample ω u parent child dataLaw
      hreg htransfer hModel hgap hUniform)
  exact (measureReal_mono hsubset).trans
    (measure_exists_candidate_bad_le hN μ dataLaw
      outcome hOutcomeMeas hOutcome01 sample hSampleMeas
      hIID hSampleLaw hu)

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
