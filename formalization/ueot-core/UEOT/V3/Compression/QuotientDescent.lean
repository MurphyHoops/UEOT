import UEOT.V3.DynamicsKernel
import UEOT.V3.PredictionDependent
import UEOT.V3.StructuredQuotient

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

/-! ## Countable almost-everywhere measurable descent

The set-level universal property above is not enough for source theorems whose
factorization is only protocol-by-protocol almost everywhere.  The reusable
extra ingredient is countability: it turns the separate exceptional sets into
one common null set, while product measurability bundles the coordinate
decoders into one measurable descended state.

This theorem is independent of probability kernels.  P-PRED-01 is obtained by
specializing the coordinate codomains to spaces of measures. -/

universe uH uI uS uF

/-- A countable family of measurable coordinate factorizations, each valid
almost everywhere, descends jointly through one measurable product decoder on
one common full-measure set. -/
theorem countableAEFamily_descend
    {H : Type uH} {I : Type uI} {S : Type uS}
    {F : I → Type uF}
    [Countable I] [MeasurableSpace H] [MeasurableSpace S]
    [∀ i, MeasurableSpace (F i)]
    (μ : MeasureTheory.Measure H)
    (f : (i : I) → H → F i)
    (s : H → S)
    (d : (i : I) → S → F i)
    (hd : ∀ i, Measurable (d i))
    (hfactor : ∀ i, ∀ᵐ h ∂μ, f i h = d i (s h)) :
    ∃ decoder : S → (∀ i, F i), Measurable decoder ∧
      ∀ᵐ h ∂μ, (fun i => f i h) = decoder (s h) := by
  refine ⟨fun z i => d i z, measurable_pi_lambda _ hd, ?_⟩
  have hcommon : ∀ᵐ h ∂μ, ∀ i, f i h = d i (s h) :=
    MeasureTheory.ae_all_iff.mpr hfactor
  exact hcommon.mono (fun h hh => funext hh)

open UEOT.V3.PredictionAE
open UEOT.V3.PredictionDependent

universe uPY

/-- P-PRED-01 reconstructed from countable a.e. quotient descent.

The source-facing conclusions are kept separate inside one wrapper:

* the canonical response state measurably factors through every jointly
  sufficient statistic on one common full-measure set;
* hence its mod-null sigma-factor is minimal;
* the canonical response state is itself protocol-sufficient because every
  response kernel is recovered by measurable coordinate evaluation.

The source assumes standard-Borel future/statistic spaces to obtain the input
regular conditional kernels.  Once those kernels are supplied, the Lean
factorization argument only needs their measurable structures, so this wrapper
uses genuinely weaker assumptions rather than strengthening the frozen claim. -/
theorem p_pred_01_via_countableAE_descent
    {H : Type uH} {I : Type uI} {S : Type uS}
    {Y : I → Type uPY}
    [Countable I] [MeasurableSpace H] [MeasurableSpace S]
    [∀ i, MeasurableSpace (Y i)]
    (μ : MeasureTheory.Measure H)
    (K : (i : I) → ProbabilityTheory.Kernel H (Y i))
    (s : H → S)
    (L : (i : I) → ProbabilityTheory.Kernel S (Y i))
    (hL : ∀ i, ∀ᵐ h ∂μ, K i h = L i (s h)) :
    AEFactors μ (fun h i => K i h) s ∧
      AESigmaLE μ (fun h i => K i h) s ∧
      (∀ i, ∃ Li : ProbabilityTheory.Kernel (∀ j, MeasureTheory.Measure (Y j)) (Y i),
        ∀ h, K i h = Li (fun j => K j h)) := by
  rcases countableAEFamily_descend
      (μ := μ)
      (f := fun i h => K i h)
      (s := s)
      (d := fun i z => L i z)
      (hd := fun i => (L i).measurable)
      hL with ⟨decoder, hdecoder, hEq⟩
  have hmin : AEFactors μ (fun h i => K i h) s :=
    ⟨decoder, hdecoder, hEq⟩
  refine ⟨hmin, aeFactors_sigmaLE μ hmin, ?_⟩
  intro i
  exact ⟨coordinateKernel i, fun _ => rfl⟩

/-! ## Two-sided quotient descent

Some UEOT interfaces factor through *two* independently compressed coordinates
at once.  The reusable core is still quotient descent: a response family that
is constant on every left fibre and every right fibre descends uniquely through
the product representation.  The second theorem below records the converse
minimality fact used throughout structural quotients: any exact separated
factorization can only merge points that are response-equivalent.
-/

universe uQI uQX uQE uQSX uQSE uQR

/-- Fibre compatibility in each argument of a two-sided response family. -/
def TwoSidedCompatible
    {I : Type uQI} {QX : Type uQX} {QE : Type uQE}
    {SX : Type uQSX} {SE : Type uQSE} {R : Type uQR}
    (qX : QX → SX) (qE : QE → SE) (F : I → QX → QE → R) : Prop :=
  (∀ i e, FiberCompatible qX (fun x => F i x e)) ∧
  (∀ i x, FiberCompatible qE (fun e => F i x e))

/-- Chosen-representative realization of the two-sided descended response. -/
noncomputable def twoSidedDescend
    {I : Type uQI} {QX : Type uQX} {QE : Type uQE}
    {SX : Type uQSX} {SE : Type uQSE} {R : Type uQR}
    (qX : QX → SX) (qE : QE → SE) (F : I → QX → QE → R)
    (hX : Surjective qX) (hE : Surjective qE)
    (_hcompat : TwoSidedCompatible qX qE F) :
    I → SX → SE → R :=
  fun i sx se => F i (Classical.choose (hX sx)) (Classical.choose (hE se))

/-- The two-sided descended response reproduces the original response on every
pair of represented source points. -/
theorem twoSidedDescend_apply
    {I : Type uQI} {QX : Type uQX} {QE : Type uQE}
    {SX : Type uQSX} {SE : Type uQSE} {R : Type uQR}
    (qX : QX → SX) (qE : QE → SE) (F : I → QX → QE → R)
    (hX : Surjective qX) (hE : Surjective qE)
    (hcompat : TwoSidedCompatible qX qE F)
    (i : I) (x : QX) (e : QE) :
    twoSidedDescend qX qE F hX hE hcompat i (qX x) (qE e) = F i x e := by
  unfold twoSidedDescend
  have hx :
      qX (Classical.choose (hX (qX x))) = qX x :=
    Classical.choose_spec (hX (qX x))
  have he :
      qE (Classical.choose (hE (qE e))) = qE e :=
    Classical.choose_spec (hE (qE e))
  calc
    F i (Classical.choose (hX (qX x))) (Classical.choose (hE (qE e))) =
        F i x (Classical.choose (hE (qE e))) :=
      hcompat.1 i (Classical.choose (hE (qE e))) hx
    _ = F i x e := hcompat.2 i x he

/-- Universal property for exact two-sided quotient descent. -/
theorem existsUnique_twoSidedDescend
    {I : Type uQI} {QX : Type uQX} {QE : Type uQE}
    {SX : Type uQSX} {SE : Type uQSE} {R : Type uQR}
    (qX : QX → SX) (qE : QE → SE) (F : I → QX → QE → R)
    (hX : Surjective qX) (hE : Surjective qE)
    (hcompat : TwoSidedCompatible qX qE F) :
    ∃! Q : I → SX → SE → R,
      ∀ i x e, Q i (qX x) (qE e) = F i x e := by
  refine ⟨twoSidedDescend qX qE F hX hE hcompat,
    twoSidedDescend_apply qX qE F hX hE hcompat, ?_⟩
  intro Q hQ
  funext i sx se
  rcases hX sx with ⟨x, rfl⟩
  rcases hE se with ⟨e, rfl⟩
  exact (hQ i x e).trans
    (twoSidedDescend_apply qX qE F hX hE hcompat i x e).symm

/-- Canonical left response equivalence induced by a two-sided response family. -/
def LeftResponseEq
    {I : Type uQI} {QX : Type uQX} {QE : Type uQE} {R : Type uQR}
    (F : I → QX → QE → R) (x x' : QX) : Prop :=
  ∀ e i, F i x e = F i x' e

/-- Canonical right response equivalence induced by a two-sided response family. -/
def RightResponseEq
    {I : Type uQI} {QX : Type uQX} {QE : Type uQE} {R : Type uQR}
    (F : I → QX → QE → R) (e e' : QE) : Prop :=
  ∀ x i, F i x e = F i x e'

/-- Any exact separated representation refines both canonical response
equivalences.  This is the abstract minimality half of structured quotient
constructions. -/
theorem exactSeparatedFactorization_refines_responseEq
    {I : Type uQI} {QX : Type uQX} {QE : Type uQE}
    {SX : Type uQSX} {SE : Type uQSE} {R : Type uQR}
    (F : I → QX → QE → R)
    (f : QX → SX) (g : QE → SE) (Q : I → SX → SE → R)
    (hfac : ∀ i x e, F i x e = Q i (f x) (g e)) :
    (∀ {x x'}, f x = f x' → LeftResponseEq F x x') ∧
    (∀ {e e'}, g e = g e' → RightResponseEq F e e') := by
  constructor
  · intro x x' hxx e i
    rw [hfac i x e, hfac i x' e, hxx]
  · intro e e' hee x i
    rw [hfac i x e, hfac i x e', hee]

open UEOT.V3.StructuredQuotient

/-- P-INT-02 reconstructed from generic two-sided quotient descent plus the
canonical response-equivalence adapter.

The generic compression theorems above do the mathematical work.  This wrapper
only instantiates them with the source theorem's canonical quotient maps and
identifies their response equivalences with the source setoids.  No finiteness,
Bellman, statistical, or algorithmic assumption is added beyond the frozen
source surface. -/
theorem p_int_02_via_twoSidedDescent
    {IX : Type uQX} {IE : Type uQE} {II : Type uQI} {RR : Type uQR}
    [Fintype IX] [Fintype IE] [Fintype II]
    (K : II → IX → IE → RR) :
    (∀ i x e,
      K i x e =
        quotientResponse K i (internalClass K x) (environmentClass K e)) ∧
    (∀ {SX : Type uQSX} {SE : Type uQSE}
      (f : IX → SX) (g : IE → SE) (Q : II → SX → SE → RR),
      (∀ i x e, K i x e = Q i (f x) (g e)) →
      (∀ {x x'}, f x = f x' → (internalSetoid K).r x x') ∧
      (∀ {e e'}, g e = g e' → (environmentSetoid K).r e e')) := by
  have hX : Surjective (internalClass K) := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    exact ⟨x, rfl⟩
  have hE : Surjective (environmentClass K) := by
    intro q
    refine Quotient.inductionOn q ?_
    intro e
    exact ⟨e, rfl⟩
  have hcompat :
      TwoSidedCompatible (internalClass K) (environmentClass K) K := by
    constructor
    · intro i e x x' hxx
      exact (Quotient.exact hxx) e i
    · intro i x e e' hee
      exact (Quotient.exact hee) x i
  rcases existsUnique_twoSidedDescend
      (internalClass K) (environmentClass K) K hX hE hcompat with
    ⟨Qbar, hQbar, hunique⟩
  have hsource :
      quotientResponse K = Qbar := by
    apply hunique
    intro i x e
    exact quotientResponse_mk K i x e
  constructor
  · intro i x e
    rw [hsource]
    exact (hQbar i x e).symm
  · intro SX SE f g Q hfac
    rcases exactSeparatedFactorization_refines_responseEq K f g Q hfac with
      ⟨hleft, hright⟩
    refine ⟨?_, ?_⟩
    · intro x x' hxx
      exact hleft hxx
    · intro e e' hee
      exact hright hee

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
