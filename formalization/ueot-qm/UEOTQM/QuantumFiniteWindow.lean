import UEOTQM.QuantumDoob
import UEOTQM.ClassicalQuantumMemory
import UEOTQM.Mixture

/-!
# Same-source finite-window conditioning, including singular supports

Local certificates contain only finite matrix identities: a support projection,
a generalized inverse, the original backward Gram recurrence, and its local
kernel consequence. They never contain the desired record/conditional-state
identity. Completeness, local transport and finite-tree transport are outputs.

The canonical choice is S = sqrt H, T = its support inverse, P = support H.
Constructing these matrices for every PSD H is a separate spectral-adapter
obligation; exact supplied certificates also cover singular and zero supports.
-/

namespace UEOTQM.QuantumFiniteWindow

open Matrix
open scoped BigOperators ComplexOrder

noncomputable section

universe uI uO uK uX

variable {ι : Type uI} {O : Type uO} {κ : Type uK} {ξ : Type uX}
  [Fintype ι] [DecidableEq ι]
  [Fintype O] [Fintype κ] [Fintype ξ]

/-- A finite support factor and generalized inverse. Invertibility is not
assumed, and the zero filter is permitted. -/
structure SupportFilter (ι : Type*) [Fintype ι] [DecidableEq ι] where
  matrix : Operator ι
  inverse : Operator ι
  projection : Operator ι
  inverse_mul : inverse * matrix = projection
  mul_inverse : matrix * inverse = projection
  projection_adjoint : projectionᴴ = projection
  projection_sq : projection * projection = projection
  projection_mul : projection * matrix = matrix

namespace SupportFilter

def identity : SupportFilter ι where
  matrix := 1
  inverse := 1
  projection := 1
  inverse_mul := by simp
  mul_inverse := by simp
  projection_adjoint := by simp
  projection_sq := by simp
  projection_mul := by simp

def zero : SupportFilter ι where
  matrix := 0
  inverse := 0
  projection := 0
  inverse_mul := by simp
  mul_inverse := by simp
  projection_adjoint := by simp
  projection_sq := by simp
  projection_mul := by simp

def apply (F : SupportFilter ι) (X : Operator ι) : Operator ι :=
  F.matrix * X * F.matrixᴴ

def metric (F : SupportFilter ι) : Operator ι := F.matrixᴴ * F.matrix

def complement (F : SupportFilter ι) : Operator ι := 1 - F.projection

theorem apply_posSemidef (F : SupportFilter ι) {X : Operator ι}
    (hX : X.PosSemidef) : (F.apply X).PosSemidef :=
  hX.mul_mul_conjTranspose_same F.matrix

theorem apply_smul (F : SupportFilter ι) (r : ℝ) (X : Operator ι) :
    F.apply (r • X) = r • F.apply X := by
  simp only [apply, Matrix.mul_smul, Matrix.smul_mul]

@[simp] theorem apply_zero (F : SupportFilter ι) : F.apply 0 = 0 := by
  simp [apply]

@[simp] theorem identity_apply (X : Operator ι) : identity.apply X = X := by
  simp [identity, apply]

@[simp] theorem zero_apply (X : Operator ι) : zero.apply X = 0 := by
  simp [zero, apply]

theorem complement_adjoint (F : SupportFilter ι) : F.complementᴴ = F.complement := by
  simp [complement, F.projection_adjoint]

theorem complement_sq (F : SupportFilter ι) :
    F.complement * F.complement = F.complement := by
  simp only [complement, sub_mul, mul_sub, one_mul, mul_one, F.projection_sq]
  abel

theorem complement_matrix (F : SupportFilter ι) : F.complement * F.matrix = 0 := by
  simp [complement, sub_mul, F.projection_mul]

theorem inverse_metric (F : SupportFilter ι) :
    F.inverseᴴ * F.metric * F.inverse = F.projection := by
  calc
    F.inverseᴴ * F.metric * F.inverse =
        (F.matrix * F.inverse)ᴴ * (F.matrix * F.inverse) := by
      simp only [metric, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = F.projection := by
      rw [F.mul_inverse, F.projection_adjoint, F.projection_sq]

end SupportFilter

/-- Local checks on the original labelled instrument. The second check is the
kernel consequence of the PSD backward recurrence; it is independently
checkable on finite matrices, not a global transport or probability premise. -/
structure StepCertificate (F : SupportFilter ι) (G : O → SupportFilter ι)
    (I : Instrument ι O κ) : Prop where
  backward : (∑ o, ∑ k,
    (I.kraus o k)ᴴ * (G o).metric * I.kraus o k) = F.metric
  support : ∀ o k,
    (G o).matrix * I.kraus o k * F.projection = (G o).matrix * I.kraus o k

def tiltedKraus (F : SupportFilter ι) (G : O → SupportFilter ι)
    (I : Instrument ι O κ) (J : Instrument ι O ξ) (o : O) : κ ⊕ ξ → Operator ι :=
  Sum.elim (fun k => (G o).matrix * I.kraus o k * F.inverse)
    (fun k => J.kraus o k * F.complement)

theorem tilted_main_gram (F : SupportFilter ι) (G : O → SupportFilter ι)
    (I : Instrument ι O κ) (h : StepCertificate F G I) :
    (∑ o, ∑ k,
      ((G o).matrix * I.kraus o k * F.inverse)ᴴ *
        ((G o).matrix * I.kraus o k * F.inverse)) = F.projection := by
  calc
    _ = F.inverseᴴ *
        (∑ o, ∑ k, (I.kraus o k)ᴴ * (G o).metric * I.kraus o k) *
        F.inverse := by
      simp only [SupportFilter.metric, Matrix.conjTranspose_mul, Matrix.mul_assoc,
        Matrix.mul_sum, Matrix.sum_mul]
    _ = F.projection := by rw [h.backward, F.inverse_metric]

theorem tilted_fallback_gram (F : SupportFilter ι) (J : Instrument ι O ξ) :
    (∑ o, ∑ k, (J.kraus o k * F.complement)ᴴ *
      (J.kraus o k * F.complement)) = F.complement := by
  calc
    _ = F.complementᴴ * (∑ o, ∑ k, (J.kraus o k)ᴴ * J.kraus o k) *
        F.complement := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc,
        Matrix.mul_sum, Matrix.sum_mul]
    _ = F.complement := by
      rw [J.complete, F.complement_adjoint]
      simpa using F.complement_sq

/-- A complete physical instrument on the whole carrier, with the original
visible labels; fallback acts only on the unreachable support complement. -/
def tiltedInstrument (F : SupportFilter ι) (G : O → SupportFilter ι)
    (I : Instrument ι O κ) (h : StepCertificate F G I)
    (J : Instrument ι O ξ) : Instrument ι O (κ ⊕ ξ) where
  kraus := tiltedKraus F G I J
  complete := by
    simp only [tiltedKraus, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Finset.sum_add_distrib]
    rw [tilted_main_gram F G I h, tilted_fallback_gram F J]
    simp [SupportFilter.complement]

theorem tilted_main_transport (F : SupportFilter ι) (G : O → SupportFilter ι)
    (I : Instrument ι O κ) (h : StepCertificate F G I) (o : O) (k : κ)
    (X : Operator ι) :
    ((G o).matrix * I.kraus o k * F.inverse) * F.apply X *
        ((G o).matrix * I.kraus o k * F.inverse)ᴴ =
      (G o).apply (I.kraus o k * X * (I.kraus o k)ᴴ) := by
  have ht : ((G o).matrix * I.kraus o k * F.inverse) * F.matrix =
      (G o).matrix * I.kraus o k := by
    rw [Matrix.mul_assoc, F.inverse_mul]
    exact h.support o k
  calc
    _ = (((G o).matrix * I.kraus o k * F.inverse) * F.matrix) * X *
        (((G o).matrix * I.kraus o k * F.inverse) * F.matrix)ᴴ := by
      simp only [SupportFilter.apply, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by
      rw [ht]
      simp only [SupportFilter.apply, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem tilted_fallback_zero (F : SupportFilter ι) (J : Instrument ι O ξ)
    (o : O) (k : ξ) (X : Operator ι) :
    (J.kraus o k * F.complement) * F.apply X *
      (J.kraus o k * F.complement)ᴴ = 0 := by
  have ht : (J.kraus o k * F.complement) * F.matrix = 0 := by
    rw [Matrix.mul_assoc, F.complement_matrix, mul_zero]
  calc
    _ = ((J.kraus o k * F.complement) * F.matrix) * X *
        ((J.kraus o k * F.complement) * F.matrix)ᴴ := by
      simp only [SupportFilter.apply, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = 0 := by rw [ht]; simp

/-- Actual matrix branch transport, including every hidden Kraus alternative.
No positivity or normalization is needed for this all-operator identity. -/
theorem tilted_branch_transport (F : SupportFilter ι) (G : O → SupportFilter ι)
    (I : Instrument ι O κ) (h : StepCertificate F G I)
    (J : Instrument ι O ξ) (o : O) (X : Operator ι) :
    (tiltedInstrument F G I h J).branch o (F.apply X) =
      (G o).apply (I.branch o X) := by
  simp only [Instrument.branch, krausMap, tiltedInstrument, tiltedKraus,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  simp_rw [tilted_main_transport F G I h o, tilted_fallback_zero F J o]
  simp only [Finset.sum_const_zero, add_zero]
  simp only [SupportFilter.apply, Matrix.mul_sum, Matrix.sum_mul]

/-- A finite causal tree of original instruments. A stopping leaf carries an
accept/reject flag; hidden Kraus indices are never promoted to visible labels.
Local support factors are certificates, not additional physical outputs. -/
inductive FilterTree (ι : Type uI) (O : Type uO) (κ : Type uK)
    [Fintype ι] [DecidableEq ι]
    [Fintype O] [Fintype κ] where
  | stop (accept : Bool) : FilterTree ι O κ
  | node (source : Instrument ι O κ) (filter : SupportFilter ι)
      (next : O → FilterTree ι O κ) : FilterTree ι O κ

namespace FilterTree

def rootFilter : FilterTree ι O κ → SupportFilter ι
  | .stop b => if b then SupportFilter.identity else SupportFilter.zero
  | .node _ F _ => F

/-- Only child validity and local source-matrix checks are inputs. -/
def Valid : FilterTree ι O κ → Prop
  | .stop _ => True
  | .node I F next => (∀ o, (next o).Valid) ∧
      StepCertificate F (fun o => (next o).rootFilter) I

def Leaf : FilterTree ι O κ → Type uO
  | .stop _ => PUnit.{uO + 1}
  | .node _ _ next => (o : O) × (next o).Leaf

instance leafFintype (P : FilterTree ι O κ) : Fintype P.Leaf := by
  induction P with
  | stop _ => exact inferInstanceAs (Fintype PUnit.{uO + 1})
  | node _ _ next ih =>
    letI : ∀ o, Fintype (next o).Leaf := ih
    exact inferInstanceAs (Fintype ((o : O) × (next o).Leaf))

def accepts : (P : FilterTree ι O κ) → P.Leaf → Bool
  | .stop b, _ => b
  | .node _ _ next, l => (next l.1).accepts l.2

/-- Original chronological visible action/outcome words. -/
def sourceWord : (P : FilterTree ι O κ) → P.Leaf →
    List (Instrument ι O κ × O)
  | .stop _, _ => []
  | .node I _ next, l => (I, l.1) :: (next l.1).sourceWord l.2

theorem sourceWord_injective (P : FilterTree ι O κ) :
    Function.Injective P.sourceWord := by
  induction P with
  | stop b =>
    intro x y _
    cases x
    cases y
    rfl
  | node I F next ih =>
    rintro ⟨o, x⟩ ⟨p, y⟩ heq
    change (I, o) :: (next o).sourceWord x =
      (I, p) :: (next p).sourceWord y at heq
    have hop : o = p := congrArg Prod.snd (List.cons.inj heq).1
    cases hop
    have hxy := ih o (List.cons.inj heq).2
    cases hxy
    rfl

def sourceLeafOperator : (P : FilterTree ι O κ) → Operator ι → P.Leaf → Operator ι
  | .stop _, X, _ => X
  | .node I _ next, X, l => (next l.1).sourceLeafOperator (I.branch l.1 X) l.2

/-- Exact connection to the pre-existing UEOTQM record interpreter. -/
theorem sourceLeafOperator_eq_recordOperator (P : FilterTree ι O κ)
    (X : Operator ι) (l : P.Leaf) :
    P.sourceLeafOperator X l =
      recordOperator (fun I : Instrument ι O κ => I) (P.sourceWord l) X := by
  induction P generalizing X with
  | stop b => rfl
  | node I F next ih =>
    rcases l with ⟨o, l⟩
    exact ih o (I.branch o X) l

def acceptedLeafOperator (P : FilterTree ι O κ) (X : Operator ι) (l : P.Leaf) :
    Operator ι := if P.accepts l then P.sourceLeafOperator X l else 0

/-- The interpreter calls the actual complete transformed instrument at each
node. It never inserts an intermediate conditional normalization. -/
def tiltedLeafOperator (J : Instrument ι O ξ) :
    (P : FilterTree ι O κ) → P.Valid → Operator ι → P.Leaf → Operator ι
  | .stop _, _, X, _ => X
  | .node I F next, h, X, l =>
      tiltedLeafOperator J (next l.1) (h.1 l.1)
        ((tiltedInstrument F (fun o => (next o).rootFilter) I h.2 J).branch l.1 X) l.2

/-- The finite-tree telescoping identity holds on every complex input matrix,
on singular supports, and for any complete fallback instrument. -/
theorem leaf_transport (J : Instrument ι O ξ) (P : FilterTree ι O κ)
    (h : P.Valid) (X : Operator ι) (l : P.Leaf) :
    tiltedLeafOperator J P h (P.rootFilter.apply X) l =
      P.acceptedLeafOperator X l := by
  induction P generalizing X with
  | stop b =>
    cases b <;>
      simp [tiltedLeafOperator, rootFilter, acceptedLeafOperator, accepts,
        sourceLeafOperator]
  | node I F next ih =>
    rcases l with ⟨o, l⟩
    change tiltedLeafOperator J (next o) (h.1 o)
      ((tiltedInstrument F (fun q => (next q).rootFilter) I h.2 J).branch o
        (F.apply X)) l = (next o).acceptedLeafOperator (I.branch o X) l
    rw [tilted_branch_transport F (fun q => (next q).rootFilter) I h.2 J]
    exact ih o (h.1 o) (I.branch o X) l

theorem tiltedLeafOperator_smul (J : Instrument ι O ξ) (P : FilterTree ι O κ)
    (h : P.Valid) (r : ℝ) (X : Operator ι) (l : P.Leaf) :
    tiltedLeafOperator J P h (r • X) l = r • tiltedLeafOperator J P h X l := by
  induction P generalizing X with
  | stop b => rfl
  | node I F next ih =>
    rcases l with ⟨o, l⟩
    change tiltedLeafOperator J (next o) (h.1 o)
      ((tiltedInstrument F (fun q => (next q).rootFilter) I h.2 J).branch o (r • X)) l = _
    rw [Instrument.branch_smul]
    exact ih o (h.1 o) _ l

theorem tiltedLeafOperator_posSemidef (J : Instrument ι O ξ) (P : FilterTree ι O κ)
    (h : P.Valid) {X : Operator ι} (hX : X.PosSemidef) (l : P.Leaf) :
    (tiltedLeafOperator J P h X l).PosSemidef := by
  induction P generalizing X with
  | stop b => exact hX
  | node I F next ih =>
    rcases l with ⟨o, l⟩
    exact ih o (h.1 o)
      ((tiltedInstrument F (fun q => (next q).rootFilter) I h.2 J).branch_posSemidef o hX) l

theorem sum_tiltedLeafOperator_trace (J : Instrument ι O ξ) (P : FilterTree ι O κ)
    (h : P.Valid) (X : Operator ι) :
    (∑ l : P.Leaf, (tiltedLeafOperator J P h X l).trace) = X.trace := by
  induction P generalizing X with
  | stop b =>
    change (∑ _ : PUnit.{uO + 1}, X.trace) = X.trace
    simp
  | node I F next ih =>
    let D := tiltedInstrument F (fun q => (next q).rootFilter) I h.2 J
    change (∑ l : (o : O) × (next o).Leaf,
      (tiltedLeafOperator J (next l.1) (h.1 l.1) (D.branch l.1 X) l.2).trace) = X.trace
    rw [Fintype.sum_sigma]
    calc
      _ = ∑ o, (D.branch o X).trace := by
        apply Finset.sum_congr rfl
        intro o _
        exact ih o (h.1 o) (D.branch o X)
      _ = X.trace := D.sum_trace_branch X

/-- The success mass is computed from the original accepted records, not from
an independently named surrogate scalar. -/
def successMass (P : FilterTree ι O κ) (X : Operator ι) : ℝ :=
  ∑ l : P.Leaf, mass (P.acceptedLeafOperator X l)

theorem successMass_eq_filtered_mass (J : Instrument ι O ξ)
    (P : FilterTree ι O κ) (h : P.Valid) (X : Operator ι) :
    P.successMass X = mass (P.rootFilter.apply X) := by
  unfold successMass mass
  rw [← Complex.re_sum]
  have hs : (∑ l : P.Leaf, (P.acceptedLeafOperator X l).trace) =
      ∑ l : P.Leaf, (tiltedLeafOperator J P h (P.rootFilter.apply X) l).trace := by
    apply Finset.sum_congr rfl
    intro l _
    exact congrArg Matrix.trace (leaf_transport J P h X l).symm
  rw [hs, sum_tiltedLeafOperator_trace]

theorem successMass_nonneg (J : Instrument ι O ξ) (P : FilterTree ι O κ)
    (h : P.Valid) {X : Operator ι} (hX : X.PosSemidef) : 0 ≤ P.successMass X := by
  rw [successMass_eq_filtered_mass J P h]
  exact mass_nonneg (P.rootFilter.apply_posSemidef hX)

/-- A successful conditioned input exists only with a positive original event
probability. No arbitrary density is installed when the event has mass zero. -/
def initialState (J : Instrument ι O ξ) (P : FilterTree ι O κ)
    (h : P.Valid) (ρ : Density ι) (hp : 0 < P.successMass ρ.matrix) : Density ι :=
  normalize (P.rootFilter.apply ρ.matrix) (P.rootFilter.apply_posSemidef ρ.positive)
    ((successMass_eq_filtered_mass J P h ρ.matrix) ▸ hp)

theorem initialState_matrix (J : Instrument ι O ξ) (P : FilterTree ι O κ)
    (h : P.Valid) (ρ : Density ι) (hp : 0 < P.successMass ρ.matrix) :
    (initialState J P h ρ hp).matrix =
      (P.successMass ρ.matrix)⁻¹ • P.rootFilter.apply ρ.matrix := by
  change (mass (P.rootFilter.apply ρ.matrix))⁻¹ • _ = _
  rw [← successMass_eq_filtered_mass J P h ρ.matrix]

/-- Every original accepted leaf keeps its full quantum block; every rejected
leaf has zero block. The only normalization is the original event mass. -/
theorem conditional_leaf (J : Instrument ι O ξ) (P : FilterTree ι O κ)
    (h : P.Valid) (ρ : Density ι) (hp : 0 < P.successMass ρ.matrix) (l : P.Leaf) :
    tiltedLeafOperator J P h (initialState J P h ρ hp).matrix l =
      (P.successMass ρ.matrix)⁻¹ • P.acceptedLeafOperator ρ.matrix l := by
  rw [initialState_matrix, tiltedLeafOperator_smul, leaf_transport]

theorem zero_success_filter (J : Instrument ι O ξ) (P : FilterTree ι O κ)
    (h : P.Valid) (ρ : Density ι) (hz : P.successMass ρ.matrix = 0) :
    P.rootFilter.apply ρ.matrix = 0 := by
  apply (mass_eq_zero_iff (P.rootFilter.apply_posSemidef ρ.positive)).mp
  rw [← successMass_eq_filtered_mass J P h ρ.matrix, hz]

theorem zero_success_no_positive (P : FilterTree ι O κ) (ρ : Density ι)
    (hz : P.successMass ρ.matrix = 0) : ¬ 0 < P.successMass ρ.matrix := by
  simp [hz]

theorem tiltedLeafOperator_zero (J : Instrument ι O ξ) (P : FilterTree ι O κ)
    (h : P.Valid) (l : P.Leaf) : tiltedLeafOperator J P h 0 l = 0 := by
  have heq := tiltedLeafOperator_smul J P h 0 (0 : Operator ι) l
  simpa only [zero_smul] using heq

theorem zero_success_all_accepted_blocks_zero (J : Instrument ι O ξ)
    (P : FilterTree ι O κ) (h : P.Valid) (ρ : Density ι)
    (hz : P.successMass ρ.matrix = 0) (l : P.Leaf) :
    P.acceptedLeafOperator ρ.matrix l = 0 := by
  rw [← leaf_transport J P h, zero_success_filter J P h ρ hz]
  exact tiltedLeafOperator_zero J P h l

theorem sourceLeafOperator_posSemidef (P : FilterTree ι O κ)
    {X : Operator ι} (hX : X.PosSemidef) (l : P.Leaf) :
    (P.sourceLeafOperator X l).PosSemidef := by
  induction P generalizing X with
  | stop b => exact hX
  | node I F next ih =>
    rcases l with ⟨o, l⟩
    exact ih o (I.branch_posSemidef o hX) l

theorem sum_sourceLeafOperator_trace (P : FilterTree ι O κ) (X : Operator ι) :
    (∑ l : P.Leaf, (P.sourceLeafOperator X l).trace) = X.trace := by
  induction P generalizing X with
  | stop b =>
    change (∑ _ : PUnit.{uO + 1}, X.trace) = X.trace
    simp
  | node I F next ih =>
    change (∑ l : (o : O) × (next o).Leaf,
      ((next l.1).sourceLeafOperator (I.branch l.1 X) l.2).trace) = X.trace
    rw [Fintype.sum_sigma]
    calc
      _ = ∑ o, (I.branch o X).trace := by
        apply Finset.sum_congr rfl
        intro o _
        exact ih o (I.branch o X)
      _ = X.trace := I.sum_trace_branch X

/-- The finite source record law is constructed from the actual original
quantum leaf blocks. It is not independent probability data supplied by hand. -/
def sourceWeights (P : FilterTree ι O κ) (ρ : Density ι) : Mixture.Weights P.Leaf where
  weight l := mass (P.sourceLeafOperator ρ.matrix l)
  nonneg l := mass_nonneg (P.sourceLeafOperator_posSemidef ρ.positive l)
  sum_one := by
    simp only [mass]
    rw [← Complex.re_sum, sum_sourceLeafOperator_trace, ρ.trace_one]
    simp

/-- The accepted part of the actual source law is precisely the source event
mass used by the conditional density and every subsequent resource formula. -/
theorem sourceWeights_accepted_sum (P : FilterTree ι O κ) (ρ : Density ι) :
    (∑ l : P.Leaf, if P.accepts l then (P.sourceWeights ρ).weight l else 0) =
      P.successMass ρ.matrix := by
  unfold successMass
  apply Finset.sum_congr rfl
  intro l _
  cases hb : P.accepts l <;>
    simp [sourceWeights, acceptedLeafOperator, hb, mass]

theorem successMass_le_one (P : FilterTree ι O κ) (ρ : Density ι) :
    P.successMass ρ.matrix ≤ 1 := by
  calc
    P.successMass ρ.matrix ≤
        ∑ l : P.Leaf, mass (P.sourceLeafOperator ρ.matrix l) := by
      apply Finset.sum_le_sum
      intro l _
      cases hb : P.accepts l with
      | false =>
        simpa [acceptedLeafOperator, hb, mass] using
          mass_nonneg (P.sourceLeafOperator_posSemidef ρ.positive l)
      | true => simp [acceptedLeafOperator, hb]
    _ = mass ρ.matrix := by
      simp only [mass]
      rw [← Complex.re_sum, sum_sourceLeafOperator_trace]
    _ = 1 := ρ.mass_one

/-- The backward factor is a genuine effect, including singular nodes. This
provides the physical trace-nonincreasing input-filter premise from the source
tree rather than assuming it as an independent implementation condition. -/
theorem metric_complement_posSemidef (P : FilterTree ι O κ) (h : P.Valid) :
    (1 - P.rootFilter.metric).PosSemidef := by
  induction P with
  | stop b =>
    cases b <;>
      simp [rootFilter, SupportFilter.identity, SupportFilter.zero,
        SupportFilter.metric, Matrix.PosSemidef.zero, Matrix.PosSemidef.one]
  | node I F next ih =>
    have hp : (∑ o, ∑ k, (I.kraus o k)ᴴ *
        (1 - (next o).rootFilter.metric) * I.kraus o k).PosSemidef := by
      apply Matrix.posSemidef_sum Finset.univ
      intro o _
      apply Matrix.posSemidef_sum Finset.univ
      intro k _
      simpa only [Matrix.conjTranspose_conjTranspose] using
        (ih o (h.1 o)).mul_mul_conjTranspose_same (I.kraus o k)ᴴ
    have heq : (∑ o, ∑ k, (I.kraus o k)ᴴ *
        (1 - (next o).rootFilter.metric) * I.kraus o k) = 1 - F.metric := by
      simp only [mul_sub, sub_mul, mul_one, Finset.sum_sub_distrib]
      rw [I.complete, h.2.backward]
    change (1 - F.metric).PosSemidef
    exact heq ▸ hp

instance leafDecidableEq (P : FilterTree ι O κ) : DecidableEq P.Leaf := Classical.decEq _

end FilterTree

section JointBlock

variable {L : Type*} [Fintype L] [DecidableEq L]

theorem block_eq_sum_lifts (B : L → Operator ι) :
    ClassicalQuantumMemory.block B =
      ∑ l, ClassicalQuantumMemory.taggedKraus l (1 : Operator ι) * B l *
        (ClassicalQuantumMemory.taggedKraus l (1 : Operator ι))ᴴ := by
  classical
  ext ⟨o, i⟩ ⟨p, j⟩
  simp only [ClassicalQuantumMemory.block, Matrix.sum_apply,
    ClassicalQuantumMemory.taggedKraus_conjugation, one_mul, mul_one]
  by_cases hop : o = p
  · subst p
    simp
  · simp [hop, Ne.symm hop]

theorem block_posSemidef (B : L → Operator ι) (hB : ∀ l, (B l).PosSemidef) :
    (ClassicalQuantumMemory.block B).PosSemidef := by
  rw [block_eq_sum_lifts]
  exact Matrix.posSemidef_sum Finset.univ (fun l _ =>
    (hB l).mul_mul_conjTranspose_same (ClassicalQuantumMemory.taggedKraus l (1 : Operator ι)))

theorem block_smul (B : L → Operator ι) (r : ℝ) :
    ClassicalQuantumMemory.block (fun l => r • B l) =
      r • ClassicalQuantumMemory.block B := by
  classical
  ext p q
  by_cases hpq : p.1 = q.1 <;>
    simp [ClassicalQuantumMemory.block, hpq]

end JointBlock

namespace FilterTree

/-- The actual classical-record/quantum-memory density of the complete
transformed tree. PSD and trace one are derived from actual instruments. -/
def jointState (J : Instrument ι O ξ) (P : FilterTree ι O κ) (h : P.Valid)
    (ρ : Density ι) : Density (P.Leaf × ι) where
  matrix := ClassicalQuantumMemory.block (tiltedLeafOperator J P h ρ.matrix)
  positive := block_posSemidef _ (fun l =>
    tiltedLeafOperator_posSemidef J P h ρ.positive l)
  trace_one := by
    rw [ClassicalQuantumMemory.trace_block, sum_tiltedLeafOperator_trace, ρ.trace_one]

def acceptedJointOperator (P : FilterTree ι O κ) (X : Operator ι) :
    Operator (P.Leaf × ι) := ClassicalQuantumMemory.block (P.acceptedLeafOperator X)

/-- Full same-source CQ identity. Both the visible leaf and the final quantum
memory are retained, including exact zero blocks for rejected original leaves. -/
theorem conditional_joint (J : Instrument ι O ξ) (P : FilterTree ι O κ)
    (h : P.Valid) (ρ : Density ι) (hp : 0 < P.successMass ρ.matrix) :
    (jointState J P h (initialState J P h ρ hp)).matrix =
      (P.successMass ρ.matrix)⁻¹ • P.acceptedJointOperator ρ.matrix := by
  change ClassicalQuantumMemory.block
      (tiltedLeafOperator J P h (initialState J P h ρ hp).matrix) = _
  have hf : tiltedLeafOperator J P h (initialState J P h ρ hp).matrix =
      fun l => (P.successMass ρ.matrix)⁻¹ • P.acceptedLeafOperator ρ.matrix l := by
    funext l
    exact conditional_leaf J P h ρ hp l
  rw [hf, block_smul]
  rfl

theorem conditional_record_probability (J : Instrument ι O ξ)
    (P : FilterTree ι O κ) (h : P.Valid) (ρ : Density ι)
    (hp : 0 < P.successMass ρ.matrix) (l : P.Leaf) :
    mass (tiltedLeafOperator J P h (initialState J P h ρ hp).matrix l) =
      mass (P.acceptedLeafOperator ρ.matrix l) / P.successMass ρ.matrix := by
  rw [conditional_leaf, mass_smul]
  simp only [div_eq_mul_inv]
  ring

/-- The arbitrary completion on a zero-support complement cannot alter any
accepted conditional record or final memory, even with another Kraus carrier. -/
theorem fallback_independent {ζ : Type*} [Fintype ζ]
    (J : Instrument ι O ξ) (J' : Instrument ι O ζ)
    (P : FilterTree ι O κ) (h : P.Valid) (ρ : Density ι)
    (hp : 0 < P.successMass ρ.matrix) :
    jointState J P h (initialState J P h ρ hp) =
      jointState J' P h (initialState J' P h ρ hp) := by
  apply Density.ext
  rw [conditional_joint, conditional_joint]

end FilterTree

end

end UEOTQM.QuantumFiniteWindow
