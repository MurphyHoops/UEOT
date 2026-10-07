import UEOT.V3.StatisticalDefect
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith

/-!
# Scientific Closure C2 — registered protocol coverage

A discovery protocol set is scientifically useful only if it separates the
registered candidate pairs it claims to distinguish.  The true separation
certificate is explicit and uniform response estimation transfers it to an
empirical lower bound.  No theorem says the protocol set was discovered
optimally or covers candidates outside the registered family.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure

open MeasureTheory
open UEOT.V3.TotalVariation
open UEOT.V3.StatisticalDefect

universe uC uI uY uRun

variable {Candidate : Type uC} {Protocol : Type uI} {Y : Type uY}
variable [MeasurableSpace Y]

/-- One protocol separates one ordered candidate pair by at least `margin`. -/
def ProtocolSeparatesAt
    (response : Candidate → Protocol → Measure Y)
    (margin : ℝ) (i : Protocol) (a b : Candidate) : Prop :=
  margin ≤ tvDist (response a i) (response b i)

/-- Every distinct registered pair has a witness in the selected protocol set. -/
def ProtocolSetSeparates
    [DecidableEq Protocol]
    (response : Candidate → Protocol → Measure Y)
    (selected : Finset Protocol) (margin : ℝ) : Prop :=
  ∀ a b : Candidate, a ≠ b →
    ∃ i ∈ selected, ProtocolSeparatesAt response margin i a b

/-- Uniform response error transfers a true selected-protocol separation into
an empirical separation lower bound. -/
theorem empirical_selectedProtocol_lowerBound
    [DecidableEq Protocol]
    (response responseHat : Candidate → Protocol → Measure Y)
    (hprob : ∀ c i, IsProbabilityMeasure (response c i))
    (hprobHat : ∀ c i, IsProbabilityMeasure (responseHat c i))
    (selected : Finset Protocol) (margin eta : ℝ)
    (hresp : ∀ c i, tvDist (response c i) (responseHat c i) ≤ eta)
    (hsep : ProtocolSetSeparates response selected margin)
    {a b : Candidate} (hne : a ≠ b) :
    ∃ i ∈ selected,
      margin - 2 * eta ≤ tvDist (responseHat a i) (responseHat b i) := by
  rcases hsep a b hne with ⟨i, hi, htrue⟩
  refine ⟨i, hi, ?_⟩
  letI : IsProbabilityMeasure (response a i) := hprob a i
  letI : IsProbabilityMeasure (response b i) := hprob b i
  letI : IsProbabilityMeasure (responseHat a i) := hprobHat a i
  letI : IsProbabilityMeasure (responseHat b i) := hprobHat b i
  have hpair := abs_tvDist_sub_tvDist_le
    (responseHat a i) (responseHat b i) (response a i) (response b i)
  have ha : tvDist (responseHat a i) (response a i) ≤ eta := by
    simpa [tvDist_symm] using hresp a i
  have hb : tvDist (responseHat b i) (response b i) ≤ eta := by
    simpa [tvDist_symm] using hresp b i
  rw [abs_le] at hpair
  unfold ProtocolSeparatesAt at htrue
  linarith

/-- If the empirical tolerance sits strictly below the transferred lower bound,
every distinct registered candidate pair is still separated by a selected
protocol. -/
theorem empirical_selectedProtocol_separates
    [DecidableEq Protocol]
    (response responseHat : Candidate → Protocol → Measure Y)
    (hprob : ∀ c i, IsProbabilityMeasure (response c i))
    (hprobHat : ∀ c i, IsProbabilityMeasure (responseHat c i))
    (selected : Finset Protocol) (margin eta tolerance : ℝ)
    (hresp : ∀ c i, tvDist (response c i) (responseHat c i) ≤ eta)
    (hsep : ProtocolSetSeparates response selected margin)
    (hmargin : tolerance < margin - 2 * eta) :
    ∀ a b : Candidate, a ≠ b →
      ∃ i ∈ selected,
        tolerance < tvDist (responseHat a i) (responseHat b i) := by
  intro a b hne
  rcases empirical_selectedProtocol_lowerBound
    response responseHat hprob hprobHat selected margin eta hresp hsep hne with
    ⟨i, hi, hlow⟩
  exact ⟨i, hi, lt_of_lt_of_le hmargin hlow⟩

/-- Registration-time separation of discovery and certification runs. -/
structure DiscoveryCertificationSplit
    (Run : Type uRun) [DecidableEq Run] where
  discoveryRuns : Finset Run
  certificationRuns : Finset Run
  disjoint : Disjoint discoveryRuns certificationRuns

namespace DiscoveryCertificationSplit

/-- A run cannot be silently reused in both discovery and certification. -/
theorem not_mem_both
    {Run : Type uRun} [DecidableEq Run]
    (S : DiscoveryCertificationSplit Run) (r : Run)
    (hd : r ∈ S.discoveryRuns) :
    r ∉ S.certificationRuns := by
  intro hc
  exact Finset.disjoint_left.1 S.disjoint hd hc

end DiscoveryCertificationSplit

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure
