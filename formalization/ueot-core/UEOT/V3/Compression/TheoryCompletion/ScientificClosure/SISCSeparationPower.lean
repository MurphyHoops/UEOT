import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCMeanResponseCalibration
import Mathlib.Tactic

/-!
# N4-C: C2 operational identification power requires an explicit risk margin

The N4 confidence results bound *false* unique/uncovered decisions but
do not prove a unique decision is even attainable. To recover power,
derive a condition on the true candidate risks relative to the threshold
and the interval radius. This is the exact abstaining analogue of finite
ERM gap recovery, and reuses N3's C2 resolver without replacing P4.1.

Correctness and decision power are separate claims: if true candidate
risk gaps are small relative to the statistical radius, a calibrated
algorithm SHOULD abstain. No generic algorithm can guarantee full
identification without a separating response protocol.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

open UEOT.V3.Compression.TheoryCompletion.ScientificClosure
open MeasureTheory ProbabilityTheory Real

universe uX uA uC uO

/-- A certified C2 interval when a candidate is comfortably inside the
threshold, its estimate is calibrated and its declared radius is ≤ r. -/
theorem candidate_certified_of_two_radius_margin
    {X : Type uX} {A : Type uA} {C : Type uC} {O : Type uO}
    [Fintype X] [Fintype O]
    (P : RegisteredCausalCandidateProtocol X A C O)
    (c : C)
    (r : ℝ)
    (hcal : |(P.interval c).estimate - registeredCandidateRisk P c| ≤
      (P.interval c).totalRadius)
    (hradius : (P.interval c).totalRadius ≤ r)
    (hmargin : registeredCandidateRisk P c + 2 * r ≤ P.tolerance) :
    decideAt (P.interval c) P.tolerance = .certified := by
  have hupper : (P.interval c).upper ≤ P.tolerance := by
    have ht := (abs_le.mp hcal).2
    unfold IntervalCertificate.upper
    linarith
  simp [decideAt, hupper]

/-- If candidate d is more than 2r *outside* the threshold, a calibrated
C2 interval with declared radius ≤ r rejects it. -/
theorem candidate_rejected_of_two_radius_margin
    {X : Type uX} {A : Type uA} {C : Type uC} {O : Type uO}
    [Fintype X] [Fintype O]
    (P : RegisteredCausalCandidateProtocol X A C O)
    (d : C)
    (r : ℝ)
    (hcal : |(P.interval d).estimate - registeredCandidateRisk P d| ≤
      (P.interval d).totalRadius)
    (hradius : (P.interval d).totalRadius ≤ r)
    (hmargin : P.tolerance + 2 * r < registeredCandidateRisk P d) :
    decideAt (P.interval d) P.tolerance = .rejected := by
  have hlower : P.tolerance < (P.interval d).lower := by
    have ht := (abs_le.mp hcal).1
    unfold IntervalCertificate.lower
    linarith
  have hnotupper : ¬ (P.interval d).upper ≤ P.tolerance := by
    have hbelow : (P.interval d).lower ≤ (P.interval d).upper := by
      unfold IntervalCertificate.lower IntervalCertificate.upper
      have hnonneg := (P.interval d).totalRadius_nonneg
      linarith
    linarith
  simp [decideAt, hnotupper, hlower]

/-- Full samplewise power: the registered causal class has one actual
candidate with risk safely inside threshold, all other registered causal
candidates safely outside. Under calibrated intervals of radius at most r,
the unmodified N3 resolver outputs *that* candidate, without assuming a
chosen transporter or an oracle-selected winner. -/
theorem registered_unique_identified_of_calibrated_margin
    {X : Type uX} {A : Type uA} {C : Type uC} {O : Type uO}
    [Fintype X] [Fintype O] [DecidableEq C]
    (P : RegisteredCausalCandidateProtocol X A C O)
    (c : C) (r : ℝ)
    (hregistered : c ∈ P.registered)
    (hcausal : P.causal c)
    (hinside : registeredCandidateRisk P c + 2*r ≤ P.tolerance)
    (houtside : ∀ d ∈ P.registered, P.causal d → d ≠ c →
      P.tolerance + 2*r < registeredCandidateRisk P d)
    (hradius : ∀ d ∈ P.registered,
      (P.interval d).totalRadius ≤ r)
    (hcal : P.Calibrated) :
    resolveRegisteredCandidates P = .unique c := by
  classical
  have hcert := candidate_certified_of_two_radius_margin
    P c r (hcal c hregistered) (hradius c hregistered) hinside
  have hcpossible : c ∈ registeredPossible P := by
    exact Finset.mem_filter.mpr
      ⟨hregistered, hcausal, by simp [hcert]⟩
  have hsingleton : registeredPossible P = {c} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨hcpossible, ?_⟩
    intro d hd
    by_contra hne
    have hdreg := (Finset.mem_filter.mp hd).1
    have hdcausal := (Finset.mem_filter.mp hd).2.1
    have hdnotrejected := (Finset.mem_filter.mp hd).2.2
    have hrejected := candidate_rejected_of_two_radius_margin P d r
      (hcal d hdreg) (hradius d hdreg) (houtside d hdreg hdcausal hne)
    exact hdnotrejected hrejected
  have hexists : ∃ d : C, registeredPossible P = {d} ∧
      decideAt (P.interval d) P.tolerance = .certified :=
    ⟨c, hsingleton, hcert⟩
  unfold resolveRegisteredCandidates
  simp only [dif_pos hexists]
  have hselected : Classical.choose hexists = c := by
    have hc : c ∈ registeredPossible P := hcpossible
    have hselected_set := (Classical.choose_spec hexists).1
    have hsubset : registeredPossible P ⊆
        ({Classical.choose hexists} : Finset C) :=
      Finset.subset_of_eq hselected_set
    exact (Finset.mem_singleton.mp (hsubset hc)).symm
  rw [hselected]

/-- The sampled-coordinate protocol has the same kernel-derived risks,
causal gates and registry as P, with a uniform radius exactly |O|u. -/
theorem coordinate_protocol_unique_of_calibration_and_margin
    {X : Type uX} {A : Type uA} {C : Type uC} {O : Type uO}
    [Fintype X] [Fintype O] [DecidableEq C]
    {Ω : Type*} {N : ℕ}
    (P : RegisteredCausalCandidateProtocol X A C O)
    (sample : Fin N → Ω → X) (ω : Ω)
    (u : ℝ) (hu : 0 ≤ u) (c : C)
    (hregistered : c ∈ P.registered)
    (hcausal : P.causal c)
    (hinside : registeredCandidateRisk P c +
      2 * ((Fintype.card O : ℝ) * u) ≤ P.tolerance)
    (houtside : ∀ d ∈ P.registered, P.causal d → d ≠ c →
      P.tolerance + 2 * ((Fintype.card O : ℝ) * u) <
        registeredCandidateRisk P d)
    (hcal : (empiricalCoordinateProtocol P sample ω u hu).Calibrated) :
    resolveRegisteredCandidates (empiricalCoordinateProtocol P sample ω u hu) =
      .unique c := by
  apply registered_unique_identified_of_calibrated_margin
    (empiricalCoordinateProtocol P sample ω u hu)
    c ((Fintype.card O : ℝ) * u)
  · exact hregistered
  · exact hcausal
  · exact hinside
  · intro d hd hcausalD hne
    exact houtside d hd hcausalD hne
  · intro d hd
    simp [empiricalCoordinateProtocol, IntervalCertificate.totalRadius]
  · exact hcal

/-- Detection *power*, not merely error control: for a preregistered true
candidate separated from every other causally allowed registered candidate
by >2r on the outside and ≥2r on the inside, the probability of FAILING to
return the unique true candidate is at most the frozen finite-coordinate
Hoeffding bound. This says nothing about physical candidates outside the
registered causal family. -/
theorem measure_failure_to_identify_separated_candidate_le
    {X : Type uX} {A : Type uA} {C : Type uC} {O : Type uO}
    [Fintype X] [Fintype O] [MeasurableSpace X]
    {Ω : Type*} [MeasurableSpace Ω] [DecidableEq C]
    {N : ℕ} (hN : 0 < N)
    (P : RegisteredCausalCandidateProtocol X A C O)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (dataLaw : Measure X)
    (sample : Fin N → Ω → X)
    (hmeas : ∀ n, Measurable (sample n))
    (hindep : iIndepFun sample μ)
    (hlaw : ∀ n, μ.map (sample n) = dataLaw)
    (hReadMeas : ∀ j, Measurable (fun y => P.read y j))
    (hRead01 : ∀ j y, P.read y j ∈ Set.Icc (0 : ℝ) 1)
    (hModel : PostActionCoordinateLawMatchesKernel P dataLaw)
    (u : ℝ) (hu : 0 ≤ u) (c : C)
    (hregistered : c ∈ P.registered)
    (hcausal : P.causal c)
    (hinside : registeredCandidateRisk P c +
      2 * ((Fintype.card O : ℝ) * u) ≤ P.tolerance)
    (houtside : ∀ d ∈ P.registered, P.causal d → d ≠ c →
      P.tolerance + 2 * ((Fintype.card O : ℝ) * u) <
        registeredCandidateRisk P d) :
    μ.real {ω | resolveRegisteredCandidates
      (empiricalCoordinateProtocol P sample ω u hu) ≠ .unique c} ≤
        (Fintype.card O : ℝ) * (2 * exp (-2 * (N : ℝ) * u ^ 2)) := by
  have hsubset :
      {ω | resolveRegisteredCandidates
        (empiricalCoordinateProtocol P sample ω u hu) ≠ .unique c} ⊆
      {ω | ¬ (empiricalCoordinateProtocol P sample ω u hu).Calibrated} := by
    intro ω hfail hgood
    exact hfail (coordinate_protocol_unique_of_calibration_and_margin
      P sample ω u hu c hregistered hcausal hinside houtside hgood)
  exact (measureReal_mono hsubset).trans
    (measure_bad_coordinate_calibration_le hN P μ dataLaw sample
      hmeas hindep hlaw hReadMeas hRead01 hModel u hu)

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
