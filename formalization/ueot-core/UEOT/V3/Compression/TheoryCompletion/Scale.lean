import UEOT.V3.FiniteDiscountedExactQuotient
import UEOT.V3.ClosureResolution
import UEOT.V3.DynamicsCrossScale

/-!
# P0.5 scratch — Scale constitution

Quotient, closure resolution, process/dynamics coarse-graining, and object-scale
transport are kept as distinct typed notions. No definition in this module
identifies these notions with Wilsonian renormalization-group flow.
-/

namespace UEOT.V3.Compression.TheoryCompletion

open Set MeasureTheory Function
open UEOT.V3
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.ClosureResolution
open UEOT.V3.DynamicsCrossScale

universe uX uY uA uV uMs uMr uObjFine uObjCoarse

/-- Minimal quotient-map semantics: every macro state has at least one source
representative. This says nothing by itself about dynamic or reward descent. -/
def IsQuotientMap {X : Type uX} {Y : Type uY} (f : X → Y) : Prop :=
  Surjective f

/-- Exact finite control quotients instantiate the quotient-map semantic. -/
theorem exactControlQuotient_isQuotientMap
    {X : Type uX} [Fintype X]
    {Y : Type uY} [Fintype Y]
    {Abar : Y → Type uA}
    [∀ y, Fintype (Abar y)] [∀ y, Nonempty (Abar y)]
    (Q : ExactControlQuotient X Y Abar) :
    IsQuotientMap Q.f := by
  exact Q.surjective

/-- Closure-resolution coarse graining acts on families of subsets. It is not
the same type of object as a state quotient map. -/
def ClosureCoarseGraining
    {V : Type uV} (L : ClosureSystem V) :
    Set (Set V) → Set (Set V) :=
  resolutionMap L

/-- Nested closure resolutions compose exactly on finite families. -/
theorem closureCoarseGraining_comp
    {V : Type uV}
    (Lr Ls : ClosureSystem V)
    (hrs : Lr.carrier ⊆ Ls.carrier)
    {M : Set (Set V)} (hM : M.Finite) :
    ClosureCoarseGraining Lr M =
      ClosureCoarseGraining Lr (ClosureCoarseGraining Ls M) := by
  exact resolutionMap_comp Lr Ls hrs hM

/-- Exact dynamical scale transport on the reachable fine-scale image. This is
an intertwining condition between two macro transition laws and a measurable
scale map. Measurability is part of the semantic contract so `Measure.map`
cannot be satisfied through its totalized nonmeasurable fallback. -/
def ExactDynamicScaleIntertwining
    {Ms : Type uMs} {Mr : Type uMr} {A : Type uA}
    [MeasurableSpace Ms] [MeasurableSpace Mr]
    (reachable : Set Ms)
    (Ps : Ms → A → Measure Ms)
    (Pr : Mr → A → Measure Mr)
    (c : Ms → Mr) : Prop :=
  Measurable c ∧
    ∀ m ∈ reachable, ∀ a,
      (Ps m a).map c = Pr (c m) a

/-- The canonical common-microscopic-process theorem yields exact cross-scale
intertwining. The wrapper deliberately preserves the source theorem's reachable
fine-scale qualification rather than extending it off-image. -/
theorem exactDynamicScaleIntertwining_on_reachable
    {X : Type uX} {Ms : Type uMs} {Mr : Type uMr} {A : Type uA}
    [MeasurableSpace X] [MeasurableSpace Ms] [MeasurableSpace Mr]
    (P : X → A → Measure X)
    (Ps : Ms → A → Measure Ms)
    (Pr : Mr → A → Measure Mr)
    (fs : X → Ms) (fr : X → Mr) (c : Ms → Mr)
    (hfs : Measurable fs) (hc : Measurable c)
    (hcomp : ∀ x, fr x = c (fs x))
    (hs : ∀ x a, (P x a).map fs = Ps (fs x) a)
    (hr : ∀ x a, (P x a).map fr = Pr (fr x) a) :
    ExactDynamicScaleIntertwining (Set.range fs) Ps Pr c := by
  refine ⟨hc, ?_⟩
  exact p_dyn_04_exact_intertwining
    P Ps Pr fs fr c hfs hc hcomp hs hr

/-- A bare object-scale map carries both state and object representations.
It intentionally contains no preservation theorem as a field. -/
structure ObjectScaleMap
    (FineState : Type uX) (CoarseState : Type uY)
    (FineObject : Type uObjFine) (CoarseObject : Type uObjCoarse) where
  stateMap : FineState → CoarseState
  objectMap : FineObject → CoarseObject

/-- Transport of one object along an explicitly supplied object-scale map.
Identity, purpose, GOD, GOA, repairability, and homeostasis preservation are
separate theorem obligations for P9, not assumptions hidden in this interface. -/
def ObjectScaleTransport
    {FineState : Type uX} {CoarseState : Type uY}
    {FineObject : Type uObjFine} {CoarseObject : Type uObjCoarse}
    (M : ObjectScaleMap FineState CoarseState FineObject CoarseObject)
    (fine : FineObject) (coarse : CoarseObject) : Prop :=
  M.objectMap fine = coarse

end UEOT.V3.Compression.TheoryCompletion
