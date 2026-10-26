import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ExecutableSupportController
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.C3ExecutableSearch
import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.C2IntervalDecision
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredSamples
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.TrainingDeploymentJoint
import UEOT.V3.StatisticalDefect

/-!
# Fixed-sample noisy certification for an actual finite controller

The executable layer uses sample counts and rational arithmetic. The source
and empirical PMFs occur only in the semantic proofs. Responses retain the
same microscopic output alphabet while a candidate changes the input fibres.
An ambiguous oracle response stops the existing C3 scan.

The source experiment has a fixed allocation of independent responses from
every registered state-action row. Exact structural support is an independent
input to the R1 controller, not a conclusion inferred from unseen transitions.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.NoisyFiniteRiskOracle

open MeasureTheory ProbabilityTheory
open UEOT.V3.PathError UEOT.V3.TotalVariation
open UEOT.V3.Compression.TheoryCompletion.ScientificClosure
open ExecutableSupportSynthesis
open scoped BigOperators

universe u

abbrev SampleTable (X A : Type u) (N : ℕ) := X → A → Fin N → X

abbrev SampleSpace (X A : Type u) (N : ℕ) :=
  VariableRegisteredSamples.SampleCoordinate (fun _ : X × A => N) → X

def samplesAt {X A : Type u} {N : ℕ} (record : SampleSpace X A N) : SampleTable X A N :=
  fun x a k => record ⟨(x, a), k⟩

/-- Count the observed outcomes; division by N is rational. Semantic and
acceptance endpoints require positive N. -/
def empiricalMass {X : Type u} [DecidableEq X] {N : ℕ}
    (sample : Fin N → X) (z : X) : ℚ :=
  (∑ k : Fin N, if sample k = z then (1 : ℚ) else 0) / N

/-- Finite overlap formula for total variation. -/
def empiricalTV {X : Type u} [Fintype X] [DecidableEq X] {N : ℕ}
    (left right : Fin N → X) : ℚ :=
  1 - ∑ z : X, min (empiricalMass left z) (empiricalMass right z)

/-- The same output alphabet is used for all candidate input fibres. -/
def empiricalDefect {X Y A : Type u} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq Y] {N : ℕ}
    (q : X → Y) (sample : SampleTable X A N) : ℚ :=
  let values := (Finset.univ : Finset (X × X × A)).image fun t =>
    if q t.1 = q t.2.1 then empiricalTV (sample t.1 t.2.2) (sample t.2.1 t.2.2) else 0
  (insert 0 values).max' (Finset.insert_nonempty 0 values)

/-- Computable counterpart of the existing real interval decision. -/
def decideRat (estimate radius threshold : ℚ) : CertificationDecision :=
  if estimate + radius ≤ threshold then .certified
  else if threshold < estimate - radius then .rejected
  else .ambiguous

def noisyDecision {X Y A : Type u} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq Y] {N : ℕ}
    (q : X → Y) (sample : SampleTable X A N) (u tau : ℚ) : CertificationDecision :=
  decideRat (empiricalDefect q sample) (2 * u) tau

/-- Reuse C3's actual scan: only a FAIL permits another query. -/
def scanNoisy (oracle : ℕ → CertificationDecision) (count : ℕ) :
    C3ExecutableSearch.SearchRun :=
  C3ExecutableSearch.scan (fun i => decide (oracle i ≠ .rejected)) 0 count

/-- A returned ambiguous index is retained as ambiguous, not skipped. -/
def scanOutcome (oracle : ℕ → CertificationDecision) (count : ℕ) :
    Option (ℕ × CertificationDecision) :=
  (scanNoisy oracle count).found.map (fun i => (i, oracle i))

def candidateDecision {X Y A : Type u} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq Y] {N count : ℕ}
    (q : Fin count → X → Y) (sample : SampleTable X A N) (u tau : ℚ)
    (i : ℕ) : CertificationDecision :=
  if hi : i < count then noisyDecision (q ⟨i, hi⟩) sample u tau else .rejected

/-- A total optional selector, also for an empty registered family. Only an
actual first PASS is selected; ambiguity and exhaustion produce no deployment. -/
def selectCandidate {X Y A : Type u} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq Y] {N count : ℕ}
    (q : Fin count → X → Y) (sample : SampleTable X A N) (u tau : ℚ) : Option (Fin count) :=
  match scanOutcome (candidateDecision q sample u tau) count with
  | some (i, .certified) => if hi : i < count then some ⟨i, hi⟩ else none
  | _ => none

/-- Select the first element of a nonempty observation fibre by enumeration. -/
def representative {X Y : Type u} [Fintype X] [LinearOrder X] [DecidableEq Y]
    (q : X → Y) (fallback : X) (y : Y) : X :=
  let fibre := (Finset.univ : Finset X).filter (fun x => q x = y)
  if h : fibre.Nonempty then fibre.min' h else fallback

def pushMass {X Y : Type u} [Fintype X] [DecidableEq Y]
    (q : X → Y) (mass : X → ℚ) (y : Y) : ℚ :=
  ∑ x : X, if q x = y then mass x else 0

/-- Reference rows are built from the observed samples at computed representatives. -/
def referenceRowMass {X Y A : Type u} [Fintype X]
    [LinearOrder X] [DecidableEq Y] {N : ℕ}
    (q : X → Y) (fallback : X) (sample : SampleTable X A N)
    (y : Y) (a : A) (z : Y) : ℚ :=
  pushMass q (empiricalMass (sample (representative q fallback y) a)) z

/-- Rational mass of one complete reference history under the actual R1
program. The recorded action is checked against its executable memory. -/
def referenceHistoryMass {X Y A : Type u} [Fintype X]
    [LinearOrder X] [DecidableEq Y] [DecidableEq A] {N : ℕ}
    (program : Program X Y A) (initial : X → ℚ) (q : X → Y)
    (fallback : X) (sample : SampleTable X A N) :
    ∀ n, CausalHistory Y (A × Y) n → ℚ
  | 0, y => pushMass q initial y
  | n + 1, h =>
      referenceHistoryMass program initial q fallback sample n h.1 *
        if h.2.1 = program.action (program.memory n h.1) then
          referenceRowMass q fallback sample (riskLastState n h.1) h.2.1 h.2.2
        else 0

/-- Exact finite rational event sum. ponytail: enumerate histories while the
registered horizon is small; use state-memory dynamic programming if measured
enumeration cost blocks a required input. -/
def referenceRisk {X Y A : Type u} [Fintype X] [Fintype Y] [Fintype A]
    [LinearOrder X] [DecidableEq Y] [DecidableEq A] {N : ℕ}
    (program : Program X Y A) (initial : X → ℚ) (q : X → Y)
    (fallback : X) (sample : SampleTable X A N)
    (T : ℕ) (bad : CausalHistory Y (A × Y) T → Bool) : ℚ :=
  ∑ h : CausalHistory Y (A × Y) T,
    if bad h then referenceHistoryMass program initial q fallback sample T h else 0

def riskBudget {X Y A : Type u} [Fintype X] [Fintype Y] [Fintype A]
    [LinearOrder X] [DecidableEq Y] [DecidableEq A] {N : ℕ}
    (program : Program X Y A) (initial : X → ℚ) (q : X → Y)
    (fallback : X) (sample : SampleTable X A N) (u : ℚ)
    (T : ℕ) (bad : CausalHistory Y (A × Y) T → Bool) : ℚ :=
  min 1 (referenceRisk program initial q fallback sample T bad +
    T * min 1 (u + empiricalDefect q sample))

/-- All scalar validity, noisy PASS, and the computed risk budget are checked.
A failed budget is an absent certificate, not proof of excessive true risk. -/
def accepts {X Y A : Type u} [Fintype X] [Fintype Y] [Fintype A]
    [LinearOrder X] [DecidableEq Y] [DecidableEq A] {N : ℕ}
    (program : Program X Y A) (initial : X → ℚ) (q : X → Y)
    (fallback : X) (sample : SampleTable X A N) (u tau beta : ℚ)
    (T : ℕ) (bad : CausalHistory Y (A × Y) T → Bool) : Bool :=
  decide (0 < N ∧ 0 ≤ u ∧ 0 ≤ tau ∧ 0 ≤ beta ∧ beta ≤ 1) &&
    decide (noisyDecision q sample u tau = .certified) &&
    decide (riskBudget program initial q fallback sample u T bad ≤ beta)

section BasicSemantics

variable {X Y A : Type u} [Fintype X] [Fintype A]
variable [LinearOrder X] [DecidableEq Y]
variable {N : ℕ}

theorem empiricalDefect_nonneg (q : X → Y) (sample : SampleTable X A N) :
    0 ≤ empiricalDefect q sample := by
  unfold empiricalDefect
  exact Finset.le_max' _ 0 (Finset.mem_insert_self _ _)

theorem empiricalTV_le_defect (q : X → Y) (sample : SampleTable X A N)
    (x x' : X) (a : A) (h : q x = q x') :
    empiricalTV (sample x a) (sample x' a) ≤ empiricalDefect q sample := by
  unfold empiricalDefect
  apply Finset.le_max'
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨(x, x', a), Finset.mem_univ _, by simp [h]⟩

theorem representative_fibre (q : X → Y) (fallback x : X) :
    q (representative q fallback (q x)) = q x := by
  have hx : ((Finset.univ : Finset X).filter (fun z => q z = q x)).Nonempty :=
    ⟨x, by simp⟩
  unfold representative
  rw [dif_pos hx]
  exact (Finset.mem_filter.mp (Finset.min'_mem _ hx)).2

variable [MeasurableSpace X] [MeasurableSingletonClass X]

/-- Only this semantic interpretation introduces PMFs. -/
noncomputable def empiricalRow (hN : 0 < N) (sample : Fin N → X) : PMF X :=
  empiricalResponsePMF hN (fun k (_ : Unit) => sample k) ()

theorem empiricalMass_eq (hN : 0 < N) (sample : Fin N → X) (z : X) :
    (empiricalMass sample z : ℝ) = (empiricalRow hN sample z).toReal := by
  have h := empiricalResponsePMF_event_mean hN
    (fun k (_ : Unit) => sample k) () ({z} : Finset X)
  simpa [empiricalRow, empiricalMass, Measure.real,
    UEOT.V3.BoundedLossSampling.empiricalRisk,
    UEOT.V3.FiniteAlphabetSampling.eventIndicator, Pi.single_apply] using h.symm

theorem empiricalTV_eq (hN : 0 < N) (left right : Fin N → X) :
    (empiricalTV left right : ℝ) =
      tvDist (empiricalRow hN left).toMeasure (empiricalRow hN right).toMeasure := by
  rw [tvDist_eq_one_sub_pmfCommonMass]
  simp only [empiricalTV, pmfCommonMass, Rat.cast_sub, Rat.cast_one, Rat.cast_sum,
    Rat.cast_min, empiricalMass_eq hN]

/-- The existing source defect with a fixed microscopic response alphabet. -/
noncomputable def sourceDefect (q : X → Y) (P : X → A → PMF X) : ℝ :=
  UEOT.V3.StatisticalDefect.responseDefect (fun _ : Finset Unit => q)
    (fun x a => (P x a).toMeasure) ∅

omit [Fintype X] [Fintype A] [LinearOrder X] [DecidableEq Y]
  [MeasurableSingletonClass X] in
private theorem sourceDiameter_nonempty [Nonempty X] [Nonempty A]
    (q : X → Y) (P : X → A → PMF X) :
    (UEOT.V3.StatisticalDefect.responseDiameterSet (fun _ : Finset Unit => q)
      (fun x a => (P x a).toMeasure) ∅).Nonempty := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨a⟩ := ‹Nonempty A›
  exact ⟨_, x, x, a, rfl, rfl⟩

omit [Fintype X] [Fintype A] [LinearOrder X] [DecidableEq Y]
  [MeasurableSingletonClass X] in
private theorem sourceDiameter_bdd (q : X → Y) (P : X → A → PMF X) :
    BddAbove (UEOT.V3.StatisticalDefect.responseDiameterSet
      (fun _ : Finset Unit => q) (fun x a => (P x a).toMeasure) ∅) := by
  refine ⟨1, ?_⟩
  rintro d ⟨x, x', a, _, rfl⟩
  exact tvDist_le_one _ _

omit [Fintype X] [Fintype A] [LinearOrder X] [DecidableEq Y]
  [MeasurableSingletonClass X] in
private theorem source_pair_le (q : X → Y) (P : X → A → PMF X)
    (x x' : X) (a : A) (h : q x = q x') :
    tvDist (P x a).toMeasure (P x' a).toMeasure ≤ sourceDefect q P := by
  exact le_csSup (sourceDiameter_bdd q P) ⟨x, x', a, h, rfl⟩

omit [Fintype X] [Fintype A] [LinearOrder X] [DecidableEq Y]
  [MeasurableSingletonClass X] in
private theorem sourceDefect_nonneg [Nonempty X] [Nonempty A]
    (q : X → Y) (P : X → A → PMF X) : 0 ≤ sourceDefect q P := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨a⟩ := ‹Nonempty A›
  exact (tvDist_nonneg (P x a).toMeasure (P x a).toMeasure).trans
    (source_pair_le q P x x a rfl)

omit [Fintype X] [Fintype A] [LinearOrder X] [DecidableEq Y]
  [MeasurableSingletonClass X] in
private theorem sourceDefect_le [Nonempty X] [Nonempty A]
    (q : X → Y) (P : X → A → PMF X) (b : ℝ)
    (h : ∀ x x' a, q x = q x' → tvDist (P x a).toMeasure (P x' a).toMeasure ≤ b) :
    sourceDefect q P ≤ b := by
  apply csSup_le (sourceDiameter_nonempty q P)
  rintro d ⟨x, x', a, hq, rfl⟩
  exact h x x' a hq

omit [MeasurableSpace X] [MeasurableSingletonClass X] in
private theorem empiricalDefect_cast_le (q : X → Y) (sample : SampleTable X A N)
    (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ x x' a, q x = q x' →
      (empiricalTV (sample x a) (sample x' a) : ℝ) ≤ b) :
    (empiricalDefect q sample : ℝ) ≤ b := by
  unfold empiricalDefect
  have hm := Finset.max'_mem
    (insert 0 ((Finset.univ : Finset (X × X × A)).image fun t =>
      if q t.1 = q t.2.1 then empiricalTV (sample t.1 t.2.2) (sample t.2.1 t.2.2) else 0))
    (Finset.insert_nonempty 0 _)
  rcases Finset.mem_insert.mp hm with hz | hm
  · rw [hz]
    simpa using hb
  · obtain ⟨⟨x, x', a⟩, _, heq⟩ := Finset.mem_image.mp hm
    rw [← heq]
    by_cases hq : q x = q x'
    · simpa [hq] using h x x' a hq
    · simpa [hq] using hb

/-- The finite rational max is exactly the established semantic defect. -/
theorem empiricalDefect_eq_sourceDefect [Nonempty X] [Nonempty A]
    (hN : 0 < N) (q : X → Y) (sample : SampleTable X A N) :
    (empiricalDefect q sample : ℝ) =
      sourceDefect q (fun x a => empiricalRow hN (sample x a)) := by
  apply le_antisymm
  · apply empiricalDefect_cast_le q sample
      (sourceDefect q (fun x a => empiricalRow hN (sample x a)))
      (sourceDefect_nonneg q (fun x a => empiricalRow hN (sample x a)))
    intro x x' a hq
    rw [empiricalTV_eq hN]
    exact source_pair_le q (fun x a => empiricalRow hN (sample x a)) x x' a hq
  · apply sourceDefect_le q (fun x a => empiricalRow hN (sample x a))
      (empiricalDefect q sample : ℝ)
    intro x x' a hq
    rw [← empiricalTV_eq hN]
    exact_mod_cast empiricalTV_le_defect q sample x x' a hq

/-- Canonical simultaneous row-TV event for the fixed sample table. -/
def CalibrationGood (P : X → A → PMF X) (hN : 0 < N)
    (sample : SampleTable X A N) (u : ℝ) : Prop :=
  ∀ x a, tvDist (P x a).toMeasure (empiricalRow hN (sample x a)).toMeasure ≤ u

/-- P-STAT-02 supplies the full uniform defect error; no candidate union bound. -/
theorem calibrated_defect_error [Nonempty X] [Nonempty A]
    (hN : 0 < N) (P : X → A → PMF X) (q : X → Y)
    (sample : SampleTable X A N) (u : ℚ)
    (hgood : CalibrationGood P hN sample u) :
    |(empiricalDefect q sample : ℝ) - sourceDefect q P| ≤ 2 * (u : ℝ) := by
  have h := UEOT.V3.StatisticalDefect.responseDefect_error
    (fun _ : Finset Unit => q) (fun x a => (P x a).toMeasure)
    (fun x a => (empiricalRow hN (sample x a)).toMeasure)
    (fun _ _ => inferInstance) (fun _ _ => inferInstance) (u : ℝ) hgood ∅
  change |sourceDefect q (fun x a => empiricalRow hN (sample x a)) - sourceDefect q P|
    ≤ 2 * (u : ℝ) at h
  rwa [← empiricalDefect_eq_sourceDefect hN q sample] at h

end BasicSemantics

private noncomputable def ratInterval (estimate radius : ℚ) (hradius : 0 ≤ radius) :
    IntervalCertificate where
  estimate := estimate
  statisticalRadius := radius
  driftRadius := 0
  statisticalRadius_nonneg := by exact_mod_cast hradius
  driftRadius_nonneg := le_refl 0

private theorem decideRat_eq_decideAt (estimate radius threshold : ℚ)
    (hradius : 0 ≤ radius) :
    decideRat estimate radius threshold =
      decideAt (ratInterval estimate radius hradius) threshold := by
  simp only [decideRat, decideAt, ratInterval, IntervalCertificate.upper,
    IntervalCertificate.lower, IntervalCertificate.totalRadius, add_zero,
    ← Rat.cast_add, ← Rat.cast_sub, Rat.cast_le, Rat.cast_lt]

section NoisySoundness

variable {X Y A : Type u} [Fintype X] [Fintype A] [Nonempty X] [Nonempty A]
variable [LinearOrder X] [DecidableEq Y]
variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable {N : ℕ}

theorem noisyDecision_certified_sound
    (hN : 0 < N) (P : X → A → PMF X) (q : X → Y)
    (sample : SampleTable X A N) (u tau : ℚ) (hu : 0 ≤ u)
    (hgood : CalibrationGood P hN sample u)
    (hdecision : noisyDecision q sample u tau = .certified) :
    sourceDefect q P ≤ (tau : ℝ) := by
  have hrad : 0 ≤ 2 * u := mul_nonneg (by norm_num) hu
  apply decideAt_certified_sound
    (ratInterval (empiricalDefect q sample) (2 * u) hrad) (tau : ℝ) (sourceDefect q P)
  · simpa [ratInterval, IntervalCertificate.totalRadius] using
      calibrated_defect_error hN P q sample u hgood
  · rwa [← decideRat_eq_decideAt]

theorem noisyDecision_rejected_sound
    (hN : 0 < N) (P : X → A → PMF X) (q : X → Y)
    (sample : SampleTable X A N) (u tau : ℚ) (hu : 0 ≤ u)
    (hgood : CalibrationGood P hN sample u)
    (hdecision : noisyDecision q sample u tau = .rejected) :
    (tau : ℝ) < sourceDefect q P := by
  have hrad : 0 ≤ 2 * u := mul_nonneg (by norm_num) hu
  apply decideAt_rejected_sound
    (ratInterval (empiricalDefect q sample) (2 * u) hrad) (tau : ℝ) (sourceDefect q P)
  · simpa [ratInterval, IntervalCertificate.totalRadius] using
      calibrated_defect_error hN P q sample u hgood
  · rwa [← decideRat_eq_decideAt]

end NoisySoundness

theorem scanNoisy_found_iff (oracle : ℕ → CertificationDecision) (count i : ℕ) :
    (scanNoisy oracle count).found = some i ↔
      i < count ∧ oracle i ≠ .rejected ∧ ∀ j, j < i → oracle j = .rejected := by
  simp [scanNoisy, C3ExecutableSearch.scan_found_iff]

theorem scanOutcome_some_iff (oracle : ℕ → CertificationDecision) (count i : ℕ)
    (decision : CertificationDecision) :
    scanOutcome oracle count = some (i, decision) ↔
      i < count ∧ oracle i = decision ∧ decision ≠ .rejected ∧
        ∀ j, j < i → oracle j = .rejected := by
  simp only [scanOutcome, Option.map_eq_some_iff, Prod.mk.injEq, scanNoisy_found_iff]
  aesop

theorem scanOutcome_none_iff (oracle : ℕ → CertificationDecision) (count : ℕ) :
    scanOutcome oracle count = none ↔ ∀ i, i < count → oracle i = .rejected := by
  simp [scanOutcome, scanNoisy, C3ExecutableSearch.scan_none_iff]

theorem selectCandidate_eq_some_iff
    {X Y A : Type u} [Fintype X] [Fintype A] [DecidableEq X] [DecidableEq Y]
    {N count : ℕ} (q : Fin count → X → Y) (sample : SampleTable X A N)
    (u tau : ℚ) (i : Fin count) :
    selectCandidate q sample u tau = some i ↔
      scanOutcome (candidateDecision q sample u tau) count = some (i.val, .certified) := by
  cases hout : scanOutcome (candidateDecision q sample u tau) count with
  | none => simp [selectCandidate, hout]
  | some result =>
      rcases result with ⟨j, decision⟩
      cases decision with
      | certified =>
          by_cases hj : j < count
          · simp [selectCandidate, hout, hj, Fin.ext_iff]
          · have hji : j ≠ i.val := by
              intro h
              exact hj (h ▸ i.isLt)
            simp [selectCandidate, hout, hj, hji]
      | rejected => simp [selectCandidate, hout]
      | ambiguous => simp [selectCandidate, hout]

/-- On the single source calibration event, a returned PASS is the first
true qualifying candidate. An earlier ambiguous result would have stopped it. -/
theorem scan_first_certified_on_good
    {X Y A : Type u} [Fintype X] [Fintype A] [Nonempty X] [Nonempty A]
    [LinearOrder X] [DecidableEq Y]
    [MeasurableSpace X] [MeasurableSingletonClass X] {N : ℕ}
    (hN : 0 < N) (P : X → A → PMF X) (q : ℕ → X → Y)
    (sample : SampleTable X A N) (u tau : ℚ) (hu : 0 ≤ u)
    (hgood : CalibrationGood P hN sample u) (count i : ℕ)
    (hfound : scanOutcome (fun j => noisyDecision (q j) sample u tau) count =
      some (i, .certified)) :
    i < count ∧ sourceDefect (q i) P ≤ (tau : ℝ) ∧
      ∀ j, j < i → (tau : ℝ) < sourceDefect (q j) P := by
  obtain ⟨hi, hpass, _, hbefore⟩ := (scanOutcome_some_iff _ count i .certified).mp hfound
  refine ⟨hi, noisyDecision_certified_sound hN P (q i) sample u tau hu hgood hpass, ?_⟩
  intro j hj
  exact noisyDecision_rejected_sound hN P (q j) sample u tau hu hgood (hbefore j hj)

/-- The concrete optional selector inherits first-true-candidate soundness
for its finite registered family on the same calibration event. -/
theorem selectCandidate_first_on_good
    {X Y A : Type u} [Fintype X] [Fintype A] [Nonempty X] [Nonempty A]
    [LinearOrder X] [DecidableEq Y]
    [MeasurableSpace X] [MeasurableSingletonClass X] {N count : ℕ}
    (hN : 0 < N) (P : X → A → PMF X) (q : Fin count → X → Y)
    (sample : SampleTable X A N) (u tau : ℚ) (hu : 0 ≤ u)
    (hgood : CalibrationGood P hN sample u) (i : Fin count)
    (hselected : selectCandidate q sample u tau = some i) :
    sourceDefect (q i) P ≤ (tau : ℝ) ∧
      ∀ j : Fin count, j < i → (tau : ℝ) < sourceDefect (q j) P := by
  obtain ⟨_, hpass, _, hbefore⟩ :=
    (scanOutcome_some_iff _ count i.val .certified).mp
      ((selectCandidate_eq_some_iff q sample u tau i).mp hselected)
  have hpass' : noisyDecision (q i) sample u tau = .certified := by
    simpa [candidateDecision, i.isLt] using hpass
  refine ⟨noisyDecision_certified_sound hN P (q i) sample u tau hu hgood hpass', ?_⟩
  intro j hj
  apply noisyDecision_rejected_sound hN P (q j) sample u tau hu hgood
  simpa [candidateDecision, j.isLt] using hbefore j.val hj

section ReferenceSemantics

variable {X Y A : Type u} [Fintype X] [Fintype Y] [Fintype A]
variable [LinearOrder X] [DecidableEq Y] [DecidableEq A]
variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace Y] [MeasurableSingletonClass Y]
variable [MeasurableSpace A] [MeasurableSingletonClass A]
variable {N : ℕ}

/-- The PMF interpretation of the very same empirical reference rows. -/
noncomputable def referenceKernel (hN : 0 < N) (q : X → Y) (fallback : X)
    (sample : SampleTable X A N) (y : Y) (a : A) : PMF Y :=
  (empiricalRow hN (sample (representative q fallback y) a)).map q

omit [Fintype Y] [LinearOrder X] [MeasurableSpace X] [MeasurableSingletonClass X]
  [MeasurableSpace Y] [MeasurableSingletonClass Y] in
private theorem pushMass_eq (q : X → Y) (mass : X → ℚ) (p : PMF X)
    (hmass : ∀ x, (mass x : ℝ) = (p x).toReal) (y : Y) :
    (pushMass q mass y : ℝ) = (p.map q y).toReal := by
  rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
  · simp only [pushMass, Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : q x = y
    · simp [h, hmass]
    · simp [h, Ne.symm h]
  · intro x _
    split_ifs
    · exact PMF.apply_ne_top _ _
    · exact ENNReal.zero_ne_top

omit [Fintype Y] [Fintype A] [DecidableEq A]
  [MeasurableSpace Y] [MeasurableSingletonClass Y]
  [MeasurableSpace A] [MeasurableSingletonClass A] in
private theorem referenceRowMass_eq (hN : 0 < N) (q : X → Y) (fallback : X)
    (sample : SampleTable X A N) (y : Y) (a : A) (z : Y) :
    (referenceRowMass q fallback sample y a z : ℝ) =
      (referenceKernel hN q fallback sample y a z).toReal := by
  exact pushMass_eq q _ _ (empiricalMass_eq hN _) z

omit [Fintype Y] [DecidableEq A] [MeasurableSingletonClass Y]
  [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- The finite max bounds every actual empirical representative comparison;
no empirical fit inequality is supplied by the caller. -/
theorem empirical_reference_fit (hN : 0 < N) (q : X → Y) (fallback : X)
    (sample : SampleTable X A N) (x : X) (a : A) :
    tvDist ((empiricalRow hN (sample x a)).map q).toMeasure
      (referenceKernel hN q fallback sample (q x) a).toMeasure ≤
        (empiricalDefect q sample : ℝ) := by
  have hmap := tvDist_map_le (empiricalRow hN (sample x a)).toMeasure
    (empiricalRow hN (sample (representative q fallback (q x)) a)).toMeasure
    q (measurable_of_finite _)
  rw [PMF.toMeasure_map q _ (measurable_of_finite _),
    PMF.toMeasure_map q _ (measurable_of_finite _)] at hmap
  refine hmap.trans ?_
  rw [← empiricalTV_eq hN]
  exact_mod_cast empiricalTV_le_defect q sample x (representative q fallback (q x)) a
    (representative_fibre q fallback x).symm

omit [Fintype Y] [DecidableEq A] [MeasurableSingletonClass Y]
  [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- The calibrated source row and the computed fit give the actual reference
error. Only one sampling radius is charged. -/
theorem calibrated_reference_row (hN : 0 < N) (P : X → A → PMF X)
    (q : X → Y) (fallback : X) (sample : SampleTable X A N) (u : ℚ)
    (hgood : CalibrationGood P hN sample u) (x : X) (a : A) :
    tvDist ((P x a).map q).toMeasure
      (referenceKernel hN q fallback sample (q x) a).toMeasure ≤
        min 1 ((u : ℝ) + (empiricalDefect q sample : ℝ)) := by
  exact empirical_coarse_row_tv (P x a) (empiricalRow hN (sample x a)) q
    (measurable_of_finite _) (referenceKernel hN q fallback sample (q x) a)
    (u : ℝ) (empiricalDefect q sample : ℝ) (hgood x a)
    (empirical_reference_fit hN q fallback sample x a)

omit [MeasurableSpace Y] [MeasurableSingletonClass Y]
  [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- The rational recursion has exactly the mass of the reference causal law
using this program's own policy and recorded-action memory. -/
theorem referenceHistoryMass_eq (hN : 0 < N) (program : Program X Y A)
    (initial : X → ℚ) (p₀ : PMF X)
    (hmass : ∀ x, (initial x : ℝ) = (p₀ x).toReal)
    (q : X → Y) (fallback : X) (sample : SampleTable X A N) :
    ∀ n (h : CausalHistory Y (A × Y) n),
      (referenceHistoryMass program initial q fallback sample n h : ℝ) =
        (causalLaw (p₀.map q)
          (riskMacroControlKernel (fun _ => referenceKernel hN q fallback sample)
            program.toController.policy) n h).toReal := by
  intro n
  induction n with
  | zero =>
      intro h
      exact pushMass_eq q initial p₀ hmass h
  | succ n ih =>
      rintro ⟨h, a, y⟩
      change (↑(referenceHistoryMass program initial q fallback sample n h *
        if a = program.action (program.memory n h) then
          referenceRowMass q fallback sample (riskLastState n h) a y else 0) : ℝ) =
        ((pmfExtend
          (causalLaw (p₀.map q)
            (riskMacroControlKernel (fun _ => referenceKernel hN q fallback sample)
              program.toController.policy) n)
          (riskMacroControlKernel (fun _ => referenceKernel hN q fallback sample)
            program.toController.policy n)) (h, (a, y))).toReal
      rw [Rat.cast_mul, ih, UEOT.V3.PathError.pmfExtend_apply, ENNReal.toReal_mul]
      congr 1
      have haction : program.toController.policy n h =
          PMF.pure (program.action (program.memory n h)) := by
        change PMF.pure (program.action (program.toController.memory n h)) = _
        rw [Program.toController_memory]
      rw [riskMacroControlKernel, haction, UEOT.V3.PathError.pmfExtend_apply,
        ENNReal.toReal_mul]
      by_cases ha : a = program.action (program.memory n h)
      · simp [ha, referenceRowMass_eq hN]
      · simp [ha]

/-- The computed rational event sum is the actual reference probability. -/
theorem referenceRisk_eq (hN : 0 < N) (program : Program X Y A)
    (initial : X → ℚ) (p₀ : PMF X)
    (hmass : ∀ x, (initial x : ℝ) = (p₀ x).toReal)
    (q : X → Y) (fallback : X) (sample : SampleTable X A N)
    (T : ℕ) (bad : CausalHistory Y (A × Y) T → Bool) :
    (referenceRisk program initial q fallback sample T bad : ℝ) =
      (causalLaw (p₀.map q)
        (riskMacroControlKernel (fun _ => referenceKernel hN q fallback sample)
          program.toController.policy) T).toMeasure.real {h | bad h = true} := by
  have hset : {h | bad h = true} =
      (↑((Finset.univ : Finset (CausalHistory Y (A × Y) T)).filter
        (fun h => bad h = true)) : Set (CausalHistory Y (A × Y) T)) := by
    ext h
    simp
  rw [hset, pmfMeasureReal_eq_sum_finset]
  simp only [referenceRisk, Rat.cast_sum, apply_ite, Rat.cast_zero, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro h _
  split_ifs
  · exact referenceHistoryMass_eq hN program initial p₀ hmass q fallback sample T h
  · rfl

end ReferenceSemantics

/-- The total runtime check exposes exactly the conditions it evaluated. -/
theorem accepts_eq_true_iff
    {X Y A : Type u} [Fintype X] [Fintype Y] [Fintype A]
    [LinearOrder X] [DecidableEq Y] [DecidableEq A] {N : ℕ}
    (program : Program X Y A) (initial : X → ℚ) (q : X → Y)
    (fallback : X) (sample : SampleTable X A N) (u tau beta : ℚ)
    (T : ℕ) (bad : CausalHistory Y (A × Y) T → Bool) :
    accepts program initial q fallback sample u tau beta T bad = true ↔
      0 < N ∧ 0 ≤ u ∧ 0 ≤ tau ∧ 0 ≤ beta ∧ beta ≤ 1 ∧
        noisyDecision q sample u tau = .certified ∧
          riskBudget program initial q fallback sample u T bad ≤ beta := by
  simp [accepts, and_assoc]

section ActualRisk

variable {X Y A : Type u} [Fintype X] [Fintype Y] [Fintype A]
variable [LinearOrder X] [DecidableEq Y] [DecidableEq A]
variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace Y] [MeasurableSingletonClass Y]
variable [MeasurableSpace A] [MeasurableSingletonClass A]
variable {N : ℕ}
variable (q : X → Y) (R : X → A → X → Prop) (C : X → A → Prop)
variable [∀ x a z, Decidable (R x a z)] [∀ x a, Decidable (C x a)]
variable (I : Finset X) (ordered : List A) (fallbackA : A)

/-- A synthesized program's own zero uncovered occupancy and the computed
empirical fit give its actual source risk, with no external fit or risk check. -/
theorem synthesized_actual_risk_le_budget_on_good
    (hN : 0 < N) (program : Program X Y A)
    (hsynth : synthesize q R C I ordered fallbackA = some program)
    (initial : X → ℚ) (p₀ : PMF X)
    (hmass : ∀ x, (initial x : ℝ) = (p₀ x).toReal)
    (h0 : ∀ x, x ∈ I ↔ x ∈ p₀.support)
    (P : X → A → PMF X)
    (hR : ∀ x a z, z ∈ (P x a).support ↔ R x a z)
    (fallbackX : X) (sample : SampleTable X A N) (u : ℚ)
    (hgood : CalibrationGood P hN sample u)
    (T : ℕ) (bad : CausalHistory Y (A × Y) T → Bool)
    (E : Set (CausalHistory X (A × X) T))
    (henvelope : E ⊆ (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) T) ⁻¹'
      {h | bad h = true}) :
    (causalLaw p₀ (riskMicroControlKernel q (fun _ => P) program.toController.policy) T).toMeasure.real E
      ≤ (riskBudget program initial q fallbackX sample u T bad : ℝ) := by
  have hzero := ExecutableSupportSynthesis.synthesize_some_zero_uncovered
    q R C I ordered fallbackA p₀ (fun _ => P) (fun _ => C) program hsynth
    h0 (fun _ => hR) (fun _ _ _ => Iff.rfl)
  have hrisk := coverage_same_policy_microscopic_failure_risk p₀ q (fun _ => P)
    (fun _ => referenceKernel hN q fallbackX sample) program.toController.policy
    (fun _ => C) (fun _ => min 1 ((u : ℝ) + (empiricalDefect q sample : ℝ))) T
    (fun _ _ x a _ => calibrated_reference_row hN P q fallbackX sample u hgood x a)
    E {h | bad h = true} henvelope
  simp only [hzero, mul_zero, add_zero, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at hrisk
  have hbudget : (riskBudget program initial q fallbackX sample u T bad : ℝ) =
      min 1 ((causalLaw (p₀.map q)
        (riskMacroControlKernel (fun _ => referenceKernel hN q fallbackX sample)
          program.toController.policy) T).toMeasure.real {h | bad h = true} +
        (T : ℝ) * min 1 ((u : ℝ) + (empiricalDefect q sample : ℝ))) := by
    simp only [riskBudget, Rat.cast_min, Rat.cast_one, Rat.cast_add, Rat.cast_mul,
      Rat.cast_natCast, referenceRisk_eq hN program initial p₀ hmass]
  rwa [hbudget]

/-- Runtime acceptance derives the numerical check required by the existing
source-risk endpoint, rather than assuming that final inequality. -/
theorem accepts_actual_risk_on_good
    (hN : 0 < N) (program : Program X Y A)
    (hsynth : synthesize q R C I ordered fallbackA = some program)
    (initial : X → ℚ) (p₀ : PMF X)
    (hmass : ∀ x, (initial x : ℝ) = (p₀ x).toReal)
    (h0 : ∀ x, x ∈ I ↔ x ∈ p₀.support)
    (P : X → A → PMF X)
    (hR : ∀ x a z, z ∈ (P x a).support ↔ R x a z)
    (fallbackX : X) (sample : SampleTable X A N) (u tau beta : ℚ)
    (hgood : CalibrationGood P hN sample u)
    (T : ℕ) (bad : CausalHistory Y (A × Y) T → Bool)
    (E : Set (CausalHistory X (A × X) T))
    (henvelope : E ⊆ (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) T) ⁻¹'
      {h | bad h = true})
    (haccept : accepts program initial q fallbackX sample u tau beta T bad = true) :
    (causalLaw p₀ (riskMicroControlKernel q (fun _ => P) program.toController.policy) T).toMeasure.real E
      ≤ (beta : ℝ) := by
  obtain ⟨_, _, _, _, _, _, hchecked⟩ :=
    (accepts_eq_true_iff program initial q fallbackX sample u tau beta T bad).mp haccept
  exact (synthesized_actual_risk_le_budget_on_good q R C I ordered fallbackA
    hN program hsynth initial p₀ hmass h0 P hR fallbackX sample u hgood
    T bad E henvelope).trans (by exact_mod_cast hchecked)

variable [MeasurableSpace (Finset X)] [MeasurableSingletonClass (Finset X)]

/-- The numerical certificate concerns this program's finite source risk;
its independent structural contract also retains its actual all-times safety. -/
theorem accepts_actual_risk_and_safety_on_good
    (hN : 0 < N) (program : Program X Y A)
    (hsynth : synthesize q R C I ordered fallbackA = some program)
    (initial : X → ℚ) (p₀ : PMF X)
    (hmass : ∀ x, (initial x : ℝ) = (p₀ x).toReal)
    (h0 : ∀ x, x ∈ I ↔ x ∈ p₀.support)
    (P : X → A → PMF X)
    (hR : ∀ x a z, z ∈ (P x a).support ↔ R x a z)
    (fallbackX : X) (sample : SampleTable X A N) (u tau beta : ℚ)
    (hgood : CalibrationGood P hN sample u)
    (T : ℕ) (bad : CausalHistory Y (A × Y) T → Bool)
    (E : Set (CausalHistory X (A × X) T))
    (henvelope : E ⊆ (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) T) ⁻¹'
      {h | bad h = true})
    (haccept : accepts program initial q fallbackX sample u tau beta T bad = true)
    (K : Set X) (hinit : ∀ x ∈ p₀.support, x ∈ K)
    (hclosed : ∀ x a, x ∈ K → C x a → ∀ z, R x a z → z ∈ K) :
    (causalLaw p₀ (riskMicroControlKernel q (fun _ => P) program.toController.policy) T).toMeasure.real E
      ≤ (beta : ℝ) ∧
    FiniteMemoryPhysicalSafety.stateTrajMeasure program.toController p₀ q (fun _ => P)
      {ω | ∀ n : ℕ, ω n ∈ K} = 1 := by
  refine ⟨accepts_actual_risk_on_good q R C I ordered fallbackA hN program hsynth
    initial p₀ hmass h0 P hR fallbackX sample u tau beta hgood T bad E henvelope haccept, ?_⟩
  exact ExecutableSupportSynthesis.synthesize_some_all_times_physical_safe
    q R C I ordered fallbackA p₀ (fun _ => P) (fun _ => C) program hsynth
    h0 (fun _ => hR) (fun _ _ _ => Iff.rfl) K hinit hclosed

end ActualRisk

section ActualTraining

variable {X A : Type u} [Fintype X] [Fintype A]
variable [MeasurableSpace X] [MeasurableSingletonClass X]

/-- Actual fixed-allocation product training, using the same unknown source
rows later consumed by deployment. No source-matching conclusion is assumed. -/
noncomputable def trainingMeasure (N : ℕ) (P : X → A → PMF X) :
    Measure (SampleSpace X A N) :=
  VariableRegisteredSamples.productRowLaw (fun j : X × A => P j.1 j.2) (fun _ => N)

instance trainingMeasure_isProbability (N : ℕ) (P : X → A → PMF X) :
    IsProbabilityMeasure (trainingMeasure N P) := by
  unfold trainingMeasure
  infer_instance

/-- The failure budget is capped before it is used in a good/bad mixture. -/
noncomputable def confidenceFailureBound (X A : Type u) [Fintype X] [Fintype A]
    (N : ℕ) (u : ℚ) : ℝ :=
  min 1 (VariableRegisteredSamples.confidenceBudget X
    (fun _ : X × A => N) (fun _ => (u : ℝ)))

omit [MeasurableSpace X] [MeasurableSingletonClass X] in
theorem confidenceFailureBound_mem_unit (N : ℕ) (u : ℚ) :
    confidenceFailureBound X A N u ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨le_min zero_le_one ?_, min_le_left _ _⟩
  unfold VariableRegisteredSamples.confidenceBudget
  exact Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _)
    (mul_nonneg (by norm_num) (Real.exp_nonneg _))

variable [LinearOrder X]

/-- The existing product experiment proves the probability of the canonical
simultaneous row-TV event. Sampling cost has no candidate-count factor. -/
theorem training_calibration (N : ℕ) (hN : 0 < N) (P : X → A → PMF X)
    (u : ℚ) (hu : 0 ≤ u) :
    MeasurableSet {record : SampleSpace X A N |
      CalibrationGood P hN (samplesAt record) u} ∧
    (trainingMeasure N P).real {record : SampleSpace X A N |
      ¬ CalibrationGood P hN (samplesAt record) u} ≤ confidenceFailureBound X A N u := by
  obtain ⟨good, _, hbad, hcal⟩ := VariableRegisteredSamples.product_experiment_calibration
    (fun j : X × A => P j.1 j.2) (fun _ => N) (fun _ => hN)
    (fun _ => (u : ℝ)) (fun _ => by exact_mod_cast hu)
  refine ⟨(Set.to_countable _).measurableSet, le_min measureReal_le_one ?_⟩
  have hsub : {record : SampleSpace X A N |
      ¬ CalibrationGood P hN (samplesAt record) u} ⊆ goodᶜ := by
    intro record hnot hg
    apply hnot
    intro x a
    exact hcal record hg (x, a)
  exact (measureReal_mono hsub).trans hbad

end ActualTraining

/-- Run the actual first-PASS selector, then its computed risk check. -/
def selectedAccepts
    {X Y A : Type u} [Fintype X] [Fintype Y] [Fintype A]
    [LinearOrder X] [DecidableEq Y] [DecidableEq A] {N count : ℕ}
    (q : Fin count → X → Y) (program : Fin count → Program X Y A)
    (initial : X → ℚ) (fallbackX : X) (sample : SampleTable X A N)
    (u tau beta : ℚ) (T : ℕ)
    (bad : Fin count → CausalHistory Y (A × Y) T → Bool) : Bool :=
  match selectCandidate q sample u tau with
  | none => false
  | some j => accepts (program j) initial (q j) fallbackX sample u tau beta T (bad j)

/-- The selected controller runs on the same source used for training.
The unselected branch is a total fallback law; its acceptance event is empty. -/
noncomputable def selectedSourceDeployment
    {X Y A : Type u} {count : ℕ}
    (q : Fin count → X → Y) (program : Fin count → Program X Y A)
    (p₀ : PMF X) (P : X → A → PMF X) (fallbackA : A) (T : ℕ) :
    Option (Fin count) → PMF (CausalHistory X (A × X) T)
  | none => causalLaw p₀ (riskMicroControlKernel id (fun _ => P)
      (fun _ _ => PMF.pure fallbackA)) T
  | some j => causalLaw p₀
      (riskMicroControlKernel (q j) (fun _ => P) (program j).toController.policy) T

section ActualJoint

variable {X Y A : Type u} [Fintype X] [Fintype Y] [Fintype A]
variable [LinearOrder X] [DecidableEq Y] [DecidableEq A]
variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace Y] [MeasurableSingletonClass Y]
variable [MeasurableSpace A] [MeasurableSingletonClass A]

/-- Fixed product training, the executed selector, and deployment on the same
source satisfy a joint accepted-and-failure bound. The runtime check discharges
the good-event risk premise. This is not a conditional-on-acceptance bound. -/
theorem selected_accepts_and_failure_joint_le
    {N count : ℕ} (hN : 0 < N)
    (q : Fin count → X → Y) (program : Fin count → Program X Y A)
    (R : X → A → X → Prop) (C : X → A → Prop)
    [∀ x a z, Decidable (R x a z)] [∀ x a, Decidable (C x a)]
    (I : Finset X) (ordered : List A) (fallbackA : A)
    (hsynth : ∀ j, synthesize (q j) R C I ordered fallbackA = some (program j))
    (initial : X → ℚ) (p₀ : PMF X)
    (hmass : ∀ x, (initial x : ℝ) = (p₀ x).toReal)
    (h0 : ∀ x, x ∈ I ↔ x ∈ p₀.support)
    (P : X → A → PMF X)
    (hR : ∀ x a z, z ∈ (P x a).support ↔ R x a z)
    (fallbackX : X) (u tau beta : ℚ) (hu : 0 ≤ u)
    (hbeta : beta ∈ Set.Icc (0 : ℚ) 1) (T : ℕ)
    (bad : Fin count → CausalHistory Y (A × Y) T → Bool)
    (E : Set (CausalHistory X (A × X) T))
    (henvelope : ∀ j, E ⊆
      (riskHistoryMap (q j) (fun ax : A × X => (ax.1, q j ax.2)) T) ⁻¹'
        {h | bad j h = true}) :
    (selectedTrainingDeployment (trainingMeasure N P).toPMF
      (fun record => selectCandidate q (samplesAt record) u tau)
      (selectedSourceDeployment q program p₀ P fallbackA T)).toMeasure.real
        {z | selectedAccepts q program initial fallbackX (samplesAt z.1)
            u tau beta T bad = true ∧ z.2 ∈ E} ≤
      min 1 (confidenceFailureBound X A N u +
        (1 - confidenceFailureBound X A N u) * (beta : ℝ)) := by
  obtain ⟨_, hbad⟩ := training_calibration N hN P u hu
  have hbetaReal : (beta : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact_mod_cast hbeta.1
    · exact_mod_cast hbeta.2
  apply selectedTrainingDeployment_failure_le (trainingMeasure N P).toPMF
    (fun record => selectCandidate q (samplesAt record) u tau)
    (selectedSourceDeployment q program p₀ P fallbackA T)
    {record | CalibrationGood P hN (samplesAt record) u}
    (fun record => {h | selectedAccepts q program initial fallbackX (samplesAt record)
      u tau beta T bad = true ∧ h ∈ E}) _ (beta : ℝ) hbetaReal
  · rw [Measure.toPMF_toMeasure]
    exact hbad
  · intro record hgood
    cases hselect : selectCandidate q (samplesAt record) u tau with
    | none =>
      simpa only [selectedAccepts, hselect, Bool.false_eq_true, false_and,
        Set.ofPred_false, measureReal_empty] using hbetaReal.1
    | some j =>
      by_cases haccept : accepts (program j) initial (q j) fallbackX (samplesAt record)
          u tau beta T (bad j) = true
      · simpa only [hselect, selectedSourceDeployment, selectedAccepts, haccept,
          true_and, Set.ofPred_mem_eq] using
          accepts_actual_risk_on_good (q j) R C I ordered fallbackA hN (program j)
            (hsynth j) initial p₀ hmass h0 P hR fallbackX (samplesAt record)
            u tau beta hgood T (bad j) E (henvelope j) haccept
      · simpa only [selectedAccepts, hselect, haccept, Bool.false_eq_true, false_and,
          Set.ofPred_false, measureReal_empty] using hbetaReal.1

end ActualJoint

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.NoisyFiniteRiskOracle
