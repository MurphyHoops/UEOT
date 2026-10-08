import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCFutureResponseCore

/-!
# SISC finite-state finite-protocol compression

Although the canonical process state is defined by every finite intervention
word, in a *finite* source system the observable distinction between ALL
pairs can be witnessed by one finite family of words. This is a theorem of
existence, NOT yet a computable protocol discovery algorithm or a polynomial
bound on action-word length. An infinite/continuous physical state space is
outside the present scope.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

universe uX uA uO

/-- An explicit future experiment that separates two non-equivalent source
states, selected noncomputably when their future response signatures differ. -/
noncomputable def chooseSeparatingWord
    {X : Type uX} {A : Type uA} {O : Type uO}
    (step : X → A → X) (read : X → O) (x y : X) : List A := by
  classical
  by_cases h : futureResponse step read x = futureResponse step read y
  · exact []
  · have he : ∃ as, futureResponse step read x as ≠
        futureResponse step read y as := by
      by_contra hnone
      apply h
      funext as
      by_contra hdifferent
      exact hnone ⟨as, hdifferent⟩
    exact Classical.choose he

theorem chosenWord_separates_different_future
    {X : Type uX} {A : Type uA} {O : Type uO}
    (step : X → A → X) (read : X → O) (x y : X)
    (hne : futureResponse step read x ≠ futureResponse step read y) :
    futureResponse step read x (chooseSeparatingWord step read x y) ≠
      futureResponse step read y (chooseSeparatingWord step read x y) := by
  classical
  unfold chooseSeparatingWord
  simp only [dif_neg hne]
  exact Classical.choose_spec (by
    by_contra hnone
    apply hne
    funext as
    by_contra hdifferent
    exact hnone ⟨as, hdifferent⟩)

/-- Choose at most one witness word per ordered pair of source states.
The returned family is finite, although witness discovery uses choice. -/
noncomputable def finiteCompleteProbeFamily
    {X : Type uX} [Fintype X] {A : Type uA} {O : Type uO}
    (step : X → A → X) (read : X → O) : Finset (List A) := by
  classical
  exact Finset.univ.image (fun p : X × X =>
    chooseSeparatingWord step read p.1 p.2)

/-- The finite protocol is complete for *all* future-response distinctions
among registered finite source states. No pre-supplied separating probes. -/
theorem finite_probes_identify_canonical_future_classes
    {X : Type uX} [Fintype X] {A : Type uA} {O : Type uO}
    (step : X → A → X) (read : X → O) (x y : X) :
    (∀ as ∈ finiteCompleteProbeFamily step read,
      futureResponse step read x as = futureResponse step read y as) ↔
      futureResponse step read x = futureResponse step read y := by
  classical
  constructor
  · intro hprobe
    by_contra hne
    have hmem : chooseSeparatingWord step read x y ∈
        finiteCompleteProbeFamily step read := by
      unfold finiteCompleteProbeFamily
      apply Finset.mem_image.mpr
      exact ⟨(x, y), Finset.mem_univ _, rfl⟩
    exact (chosenWord_separates_different_future step read x y hne)
      (hprobe (chooseSeparatingWord step read x y) hmem)
  · intro hfuture as _
    exact congrFun hfuture as

/-- Number of chosen tests is at most the number of ordered state pairs,
`|X|²`. This is NOT a bound on word *length* or search/runtime complexity. -/
theorem finite_complete_probe_card_le
    {X : Type uX} [Fintype X] {A : Type uA} {O : Type uO}
    (step : X → A → X) (read : X → O) :
    (finiteCompleteProbeFamily step read).card ≤ (Fintype.card X) ^ 2 := by
  classical
  unfold finiteCompleteProbeFamily
  calc
    (Finset.univ.image (fun p : X × X =>
        chooseSeparatingWord step read p.1 p.2)).card ≤
        (Finset.univ : Finset (X × X)).card := Finset.card_image_le
    _ = (Fintype.card X) ^ 2 := by simp [Fintype.card_prod, pow_two]

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
