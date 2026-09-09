import Mathlib

/-!
# P-CAR-04: response-fiber diameter versus optimal decoder radius

The source specification defines a response-fiber defect diameter e(S) and a
worst-case optimal decoder radius r(S).  This file proves the metric core
without assuming that the infimum over decoders is attained.

`FiberDistances` is the set of all within-readout-fiber response distances.
`DecoderBounds` is the set of all uniform error bounds achieved by some
decoder on the realized readout range.  Thus an `IsLUB` witness for the first
set is e(S), and an `IsGLB` witness for the second is r(S).
-/

namespace UEOT.V3.DecoderRadius

universe uH uI uZ uA

variable {H : Type uH} {I : Type uI} {Z : Type uZ} {A : Type uA}
variable [PseudoMetricSpace A]

def ReadoutRange (R : H → Z) := Set.range R

def readoutValue (R : H → Z) (h : H) : ReadoutRange R :=
  ⟨R h, ⟨h, rfl⟩⟩

def FiberDistances (R : H → Z) (p : H → I → A) : Set ℝ :=
  {d | ∃ h h' i, R h = R h' ∧ d = dist (p h i) (p h' i)}

def DecoderBounds (R : H → Z) (p : H → I → A) : Set ℝ :=
  {a | ∃ q : ReadoutRange R → I → A,
      ∀ h i, dist (p h i) (q (readoutValue R h) i) ≤ a}

theorem diameter_le_two_mul_decoder_bound
    (R : H → Z) (p : H → I → A) {e a : ℝ}
    (he : IsLUB (FiberDistances R p) e)
    (ha : a ∈ DecoderBounds R p) :
    e ≤ 2 * a := by
  rcases ha with ⟨q, hq⟩
  apply he.2
  intro d hd
  rcases hd with ⟨h, h', i, hRh', rfl⟩
  have hz : readoutValue R h = readoutValue R h' := by
    apply Subtype.ext
    exact hRh'
  have hleft :
      dist (p h i) (q (readoutValue R h) i) ≤ a :=
    hq h i
  have hright :
      dist (q (readoutValue R h) i) (p h' i) ≤ a := by
    rw [hz, dist_comm]
    exact hq h' i
  calc
    dist (p h i) (p h' i)
        ≤ dist (p h i) (q (readoutValue R h) i) +
          dist (q (readoutValue R h) i) (p h' i) :=
      dist_triangle _ _ _
    _ ≤ a + a := add_le_add hleft hright
    _ = 2 * a := by ring

theorem diameter_half_le_decoder_radius
    (R : H → Z) (p : H → I → A) {e r : ℝ}
    (he : IsLUB (FiberDistances R p) e)
    (hr : IsGLB (DecoderBounds R p) r) :
    e / 2 ≤ r := by
  apply hr.2
  intro a ha
  have htwo : e ≤ 2 * a :=
    diameter_le_two_mul_decoder_bound R p he ha
  linarith

theorem decoder_radius_le_diameter
    (R : H → Z) (p : H → I → A) {e r : ℝ}
    (he : IsLUB (FiberDistances R p) e)
    (hr : IsGLB (DecoderBounds R p) r) :
    r ≤ e := by
  classical
  let rep : ReadoutRange R → H := fun z => Classical.choose z.property
  have hrep : ∀ z : ReadoutRange R, R (rep z) = z.1 := by
    intro z
    exact Classical.choose_spec z.property
  let q : ReadoutRange R → I → A :=
    fun z i => p (rep z) i
  have heDecoder : e ∈ DecoderBounds R p := by
    refine ⟨q, ?_⟩
    intro h i
    have hsame :
        R h = R (rep (readoutValue R h)) := by
      symm
      exact hrep (readoutValue R h)
    have hdist :
        dist (p h i) (p (rep (readoutValue R h)) i) ∈
          FiberDistances R p := by
      exact ⟨h, rep (readoutValue R h), i, hsame, rfl⟩
    exact he.1 hdist
  exact hr.1 heDecoder

theorem decoder_radius_bounds
    (R : H → Z) (p : H → I → A) {e r : ℝ}
    (he : IsLUB (FiberDistances R p) e)
    (hr : IsGLB (DecoderBounds R p) r) :
    e / 2 ≤ r ∧ r ≤ e :=
  ⟨diameter_half_le_decoder_radius R p he hr,
   decoder_radius_le_diameter R p he hr⟩

end UEOT.V3.DecoderRadius
