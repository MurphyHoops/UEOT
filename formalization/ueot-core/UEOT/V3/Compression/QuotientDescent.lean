import UEOT.V3.DynamicsKernel

/-!
# UEOT Core compression — quotient descent

This module begins the post-106/106 compression formalization.  It does not
replace or reopen any frozen Core v3 P-ID.

The point is to isolate one repeated mathematical skeleton: a representation
`q : X → Y` supports descent of a quantity `g : X → Z` exactly when `g`
is constant on the fibres of `q`.  Surjectivity gives uniqueness of the
descended quantity.

This is deliberately a *set-level* theorem.  It does not claim that the
descended map is measurable, continuous, a probability kernel, or otherwise
admissible in a richer category.  Those are additional realization
obligations, which is precisely one of the boundaries the compression audit is
intended to expose.
-/

namespace UEOT.V3.Compression.QuotientDescent

open Function

universe uX uY uZ

variable {X : Type uX} {Y : Type uY} {Z : Type uZ}

/-- A quantity is compatible with a representation when it is constant on
every representation fibre. -/
def FiberCompatible (q : X → Y) (g : X → Z) : Prop :=
  ∀ ⦃x x' : X⦄, q x = q x' → g x = g x'

/-- The set-level descended quantity.  The compatibility proof is kept in the
interface even though the chosen representative is the only computational
input; it is what makes the result independent of that representative. -/
noncomputable def descend
    (q : X → Y) (g : X → Z)
    (hq : Surjective q) (_hcompat : FiberCompatible q g) : Y → Z :=
  fun y => g (Classical.choose (hq y))

/-- Descent really factors the original quantity through the quotient map. -/
theorem descend_comp
    (q : X → Y) (g : X → Z)
    (hq : Surjective q) (hcompat : FiberCompatible q g) :
    descend q g hq hcompat ∘ q = g := by
  funext x
  unfold descend
  exact hcompat (Classical.choose_spec (hq (q x)))

/-- Surjectivity makes a descended factor unique. -/
theorem eq_descend_of_comp_eq
    (q : X → Y) (g : X → Z)
    (hq : Surjective q) (hcompat : FiberCompatible q g)
    (gbar : Y → Z) (hfactor : gbar ∘ q = g) :
    gbar = descend q g hq hcompat := by
  funext y
  rcases hq y with ⟨x, rfl⟩
  calc
    gbar (q x) = g x := by
      simpa only [Function.comp_apply] using congrFun hfactor x
    _ = descend q g hq hcompat (q x) := by
      symm
      simpa only [Function.comp_apply] using congrFun (descend_comp q g hq hcompat) x

/-- Universal property: fibre compatibility plus surjectivity is sufficient for
existence and uniqueness of a factor through the representation. -/
theorem existsUnique_descend
    (q : X → Y) (g : X → Z)
    (hq : Surjective q) (hcompat : FiberCompatible q g) :
    ∃! gbar : Y → Z, gbar ∘ q = g := by
  refine ⟨descend q g hq hcompat, descend_comp q g hq hcompat, ?_⟩
  intro gbar hfactor
  exact eq_descend_of_comp_eq q g hq hcompat gbar hfactor

/-- Conversely, any factorization through `q` forces fibre compatibility.
Unlike the existence direction, this implication does not require
surjectivity. -/
theorem fiberCompatible_of_comp_eq
    (q : X → Y) (g : X → Z) (gbar : Y → Z)
    (hfactor : gbar ∘ q = g) :
    FiberCompatible q g := by
  intro x x' hxx'
  calc
    g x = gbar (q x) := by
      symm
      simpa only [Function.comp_apply] using congrFun hfactor x
    _ = gbar (q x') := by rw [hxx']
    _ = g x' := by
      simpa only [Function.comp_apply] using congrFun hfactor x'

/-- Exact set-level characterization of quotient descent. -/
theorem fiberCompatible_iff_existsUnique_descend
    (q : X → Y) (g : X → Z) (hq : Surjective q) :
    FiberCompatible q g ↔ ∃! gbar : Y → Z, gbar ∘ q = g := by
  constructor
  · intro hcompat
    exact existsUnique_descend q g hq hcompat
  · rintro ⟨gbar, hfactor, _hunique⟩
    exact fiberCompatible_of_comp_eq q g gbar hfactor

open MeasureTheory ProbabilityTheory
open UEOT.V3.DynamicsKernel

universe uDX uDM

/-- Strong lumpability makes the pushed-forward one-step law constant on every
representation fibre.  This is the exact compatibility hypothesis required by
the set-level quotient-descent theorem. -/
theorem strongLumpability_pushforward_fiberCompatible
    {DX : Type uDX} {DM : Type uDM}
    [MeasurableSpace DX] [MeasurableSpace DM]
    (P : Kernel DX DX) (Pbar : Kernel DM DM)
    (q : DX → DM) (hqmeas : Measurable q)
    (hlump : StrongLumpability P Pbar q hqmeas) :
    FiberCompatible q (fun x => (P x).map q) := by
  intro x x' hxx'
  exact strongLumpability_fiber_constant P Pbar q hqmeas hlump hxx'

/-- A source-level strong-lumpability witness therefore determines a unique
*set-level* macro one-step law on a surjective quotient.

The codomain here is `DM → Measure DM`, not `Kernel DM DM`.  Recovering a
measurable Markov kernel still requires the measurable-kernel obligation from
P-DYN-01; the compression theorem intentionally does not erase that boundary. -/
theorem strongLumpability_unique_setLevel_descend
    {DX : Type uDX} {DM : Type uDM}
    [MeasurableSpace DX] [MeasurableSpace DM]
    (P : Kernel DX DX) (Pbar : Kernel DM DM)
    (q : DX → DM) (hqmeas : Measurable q) (hqsurj : Surjective q)
    (hlump : StrongLumpability P Pbar q hqmeas) :
    ∃! macroLaw : DM → Measure DM,
      macroLaw ∘ q = fun x => (P x).map q := by
  exact existsUnique_descend q (fun x => (P x).map q) hqsurj
    (strongLumpability_pushforward_fiberCompatible P Pbar q hqmeas hlump)

end UEOT.V3.Compression.QuotientDescent
