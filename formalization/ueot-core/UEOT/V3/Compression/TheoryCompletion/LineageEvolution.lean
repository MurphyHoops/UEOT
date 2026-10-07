import UEOT.V3.Compression.Objecthood.OntogeneticConstruction
import UEOT.V3.EvolutionPrice
import UEOT.V3.EvolutionPerronGrowth
import UEOT.V3.SelectionBridge

/-!
# Theory Completion P8 — reproduction, lineage and evolutionary object bridge

P8 distinguishes same-object restoration from reproduction.  The new content is
a typed lineage interface and compatibility condition connecting object-level
parent/offspring relations to the already-proved population evolution kernels.
The Price/Perron/selection mathematics is reused, not relabeled as a theorem of
objecthood.
-/

namespace UEOT.V3.Compression.TheoryCompletion

open Filter Topology
open UEOT.V3
open UEOT.V3.EvolutionPrice
open UEOT.V3.EvolutionPerronGrowth
open UEOT.V3.SelectionBridge

universe uO uI uQ uJ

/-- Identity and genealogy are separate pieces of data.  `parentOf` is a
reproductive relation, not object equality. -/
structure LineageSemantics (Object : Type uO) (Identity : Type uI) where
  identity : Object → Identity
  parentOf : Object → Object → Prop

namespace LineageSemantics

variable {Object : Type uO} {Identity : Type uI}

/-- Same-object relation used to classify repair/restoration events. -/
def SameObject (L : LineageSemantics Object Identity) (x y : Object) : Prop :=
  L.identity x = L.identity y

/-- An offspring is genealogically downstream but carries a distinct object
identity.  This rules out counting same-parent repair as reproduction. -/
def OffspringOf (L : LineageSemantics Object Identity) (parent child : Object) : Prop :=
  L.parentOf parent child ∧ ¬ L.SameObject parent child

@[simp] theorem sameObject_refl (L : LineageSemantics Object Identity) (x : Object) :
    L.SameObject x x := rfl

theorem offspring_not_sameObject
    (L : LineageSemantics Object Identity) {parent child : Object}
    (h : L.OffspringOf parent child) :
    ¬ L.SameObject parent child := h.2

/-- A repair event, by definition, cannot simultaneously be a P8 offspring
under the same lineage semantics. -/
theorem sameObjectRepair_not_offspring
    (L : LineageSemantics Object Identity) {before after : Object}
    (hrepair : L.SameObject before after) :
    ¬ L.OffspringOf before after := by
  intro hoff
  exact hoff.2 hrepair

/-- Population transmission is lineage-compatible when every positive
parent→offspring channel is an actual genealogical edge. -/
def CompatibleTransmission
    [Fintype Object]
    (L : LineageSemantics Object Identity)
    (K : Object → Object → ℝ) : Prop :=
  ∀ parent child, 0 < K parent child → L.parentOf parent child

/-- Stronger reproductive compatibility also requires a new object identity on
every positive transmission edge. -/
def ReproductiveTransmission
    [Fintype Object]
    (L : LineageSemantics Object Identity)
    (K : Object → Object → ℝ) : Prop :=
  ∀ parent child, 0 < K parent child → L.OffspringOf parent child

theorem reproductiveTransmission_compatible
    [Fintype Object]
    (L : LineageSemantics Object Identity)
    {K : Object → Object → ℝ}
    (hK : L.ReproductiveTransmission K) :
    L.CompatibleTransmission K := by
  intro parent child hpos
  exact (hK parent child hpos).1

/-- Object-indexed instance of Core P-BRG-02.  Equal declared behavioral
responses imply equal bridge fitness, but this does not identify lineage or
mutation channels. -/
theorem behaviorEquivalent_objects_have_equal_fitness
    {Q : Type uQ}
    (B : ReplicationBridge Object Q) {x y : Object}
    (h : B.BehaviorEquivalent x y) :
    B.fitness x = B.fitness y :=
  B.behavior_equiv_fitness_eq h

/-- P8 Price bridge: if every positive transmission edge is an offspring edge,
then the exact Core P-EVO-01 decomposition applies to the same reproductive
kernel and every realized positive channel is certified genealogically. -/
theorem lineage_price_bridge
    [Fintype Object]
    (L : LineageSemantics Object Identity)
    (p b z : Object → ℝ) (K : Object → Object → ℝ) (z' : Object → ℝ)
    (hlineage : L.ReproductiveTransmission K)
    (hp0 : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1)
    (hb0 : ∀ i, 0 ≤ b i)
    (hK0 : ∀ i j, 0 ≤ K i j)
    (hKsum : ∀ i, ∑ j, K i j = 1)
    (hbar : 0 < weightedMean p b) :
    offspringTraitMean (nextFrequency p b K) z' - weightedMean p z =
        weightedCov p b z / weightedMean p b +
        weightedMean p
          (fun i => b i * (transmittedTrait K z' i - z i)) /
          weightedMean p b
      ∧ (∀ parent child, 0 < K parent child → L.OffspringOf parent child) := by
  exact ⟨p_evo_01 p b z K z' hp0 hpsum hb0 hK0 hKsum hbar, hlineage⟩

/-- P8 Perron bridge: once a same-type mean operator is explicitly certified as
lineage-compatible on every positive parent→child entry and has the exact KPF
certificate and valuation assumptions required by Core P-EVO-03, its growth,
composition and reproductive-value conclusions transfer unchanged.  P8 adds no
claim that objecthood itself supplies primitive positivity. -/
theorem lineage_perron_bridge
    [Fintype Object] [Nonempty Object] [DecidableEq Object]
    (L : LineageSemantics Object Identity)
    (M : Matrix Object Object ℝ) (pf : KPF01Certificate M)
    (hlineage : L.ReproductiveTransmission M)
    (z0 : Object → ℕ) (hz0 : z0 ≠ 0)
    (rho : ℝ) (w : Object → ℝ)
    (hw : ∀ i, 0 < w i)
    (hval : ∀ z : Object → ℝ, (∀ i, 0 ≤ z i) →
      rowDot (rowApply z M) w = rho * rowDot z w) :
    Tendsto
      (fun n : ℕ => fun j : Object =>
        (pf.R ^ n)⁻¹ * rowApply (natRow z0) (M ^ n) j)
      atTop
      (𝓝 (fun j : Object => rowDot (natRow z0) pf.r * pf.l j))
    ∧ Tendsto
      (fun n : ℕ => fun j : Object =>
        rowApply (natRow z0) (M ^ n) j /
          rowMass (rowApply (natRow z0) (M ^ n)))
      atTop (𝓝 pf.l)
    ∧ rho = pf.R
    ∧ (∃ c : ℝ, 0 < c ∧ ∀ i, w i = c * pf.r i)
    ∧ (∀ parent child, 0 < M parent child → L.OffspringOf parent child) := by
  rcases p_evo_03 M pf z0 hz0 rho w hw hval with
    ⟨hgrowth, hcomposition, hrho, hwuniq⟩
  exact ⟨hgrowth, hcomposition, hrho, hwuniq, hlineage⟩

end LineageSemantics

end UEOT.V3.Compression.TheoryCompletion

namespace UEOT.V3.Compression.TheoryCompletion

open UEOT.V3.EvolutionPrice

/-- **P8 terminal theorem.**  A reproductive edge is formally distinct from
same-object repair, and the same lineage-compatible transmission operator obeys
the exact Core Price decomposition. -/
theorem p8_terminal_lineage_evolution
    {Object : Type uO} {Identity : Type uI} [Fintype Object]
    (L : LineageSemantics Object Identity)
    {parent child : Object} (hoff : L.OffspringOf parent child)
    (p b z : Object → ℝ) (K : Object → Object → ℝ) (z' : Object → ℝ)
    (hlineage : L.ReproductiveTransmission K)
    (hp0 : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1)
    (hb0 : ∀ i, 0 ≤ b i)
    (hK0 : ∀ i j, 0 ≤ K i j)
    (hKsum : ∀ i, ∑ j, K i j = 1)
    (hbar : 0 < weightedMean p b) :
    ¬ L.SameObject parent child ∧
      (offspringTraitMean (nextFrequency p b K) z' - weightedMean p z =
        weightedCov p b z / weightedMean p b +
        weightedMean p
          (fun i => b i * (transmittedTrait K z' i - z i)) /
          weightedMean p b) := by
  refine ⟨hoff.2, ?_⟩
  exact (L.lineage_price_bridge p b z K z' hlineage
    hp0 hpsum hb0 hK0 hKsum hbar).1

end UEOT.V3.Compression.TheoryCompletion
