import UEOTQM.QuantumSeparation
import UEOTQM.RectangularChannels
import UEOTQM.QuantumPurification
import UEOTQM.Cesaro

/-!
# Actual-map operational identity in the selected finite complex sector

This file extends full-effect separation to unnormalized Hermitian outputs,
proves that all normalized-input statistics determine actual complex-linear
positive maps, and extends input-first Choi injectivity to rectangular maps.
It does not reconstruct the complex sector from Core or turn an exact equality
into a finite-precision calibration theorem.
-/

namespace UEOTQM.OperationalEquivalence

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker

noncomputable section

variable {ι ο κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype ο] [DecidableEq ο] [Fintype κ]

/-- The physical adapter excludes empty carriers; the underlying boundary types
and their empty-carrier tests are unchanged. -/
abbrev PhysicalSystem := {d : ℕ // 0 < d}

def physicalState (A : PhysicalSystem) : Density (Fin A.val) := by
  letI : Nonempty (Fin A.val) := ⟨⟨0, A.property⟩⟩
  exact Cesaro.normalizedIdentity

/-- Same fixed matrix-unit convention as QuantumActionRealizability.matrixUnit.
These elementary coordinates are local to avoid importing unrelated Core paths. -/
def matrixUnit (i j : ι) : Operator ι :=
  fun a b => if i = a ∧ j = b then 1 else 0

theorem matrix_expansion (X : Operator ι) :
    X = ∑ i, ∑ j, (X i j) • matrixUnit i j := by
  classical
  ext a b
  simp [matrixUnit, Matrix.sum_apply, Pi.smul_apply, smul_eq_mul, ite_and]

/-- These Hermitian coordinate units use the existing ComplexLocalTomography
convention without importing its abstract-model/Core adapter dependencies. -/
def symmetricUnit (i j : ι) : Operator ι :=
  Matrix.single i j 1 + Matrix.single j i 1

def imaginaryUnit (i j : ι) : Operator ι :=
  Matrix.single i j Complex.I - Matrix.single j i Complex.I

theorem symmetricUnit_hermitian (i j : ι) : (symmetricUnit i j).IsHermitian := by
  simp [symmetricUnit, Matrix.IsHermitian, Matrix.conjTranspose_single, add_comm]

theorem imaginaryUnit_hermitian (i j : ι) : (imaginaryUnit i j).IsHermitian := by
  simp [imaginaryUnit, Matrix.IsHermitian, Matrix.conjTranspose_single,
    ← Matrix.single_neg, sub_eq_add_neg, add_comm]

theorem sub_kronecker {ν : Type*} (H K : Operator ι) (L : Operator ν) :
    (H - K) ⊗ₖ L = H ⊗ₖ L - K ⊗ₖ L := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [Matrix.kronecker_apply, Matrix.sub_apply]
  ring

/-- All effects separate Hermitian outputs even when neither output is normalized
and their traces have not been assumed equal. -/
theorem hermitian_eq_of_all_effect_pairings_eq (X Y : Operator ο)
    (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (h : ∀ E : Effect ο, pairing E.matrix X = pairing E.matrix Y) : X = Y := by
  let D : Operator ο := X - Y
  have hD : D.IsHermitian := hX.sub hY
  have heq : pairing D X = pairing D Y :=
    QuantumSeparation.pairing_eq_of_all_effect_pairings_eq X Y h D hD
  have hz : pairing D D = 0 := by
    change pairing D (X - Y) = 0
    rw [QuantumSeparation.pairing_sub_right, heq, sub_self]
  have ht : (Dᴴ * D).trace = 0 := by
    apply Complex.ext
    · change ((Dᴴ * D).trace).re = 0
      rw [hD.eq]
      exact hz
    · exact trace_im_eq_zero (Matrix.posSemidef_conjTranspose_mul_self D)
  exact sub_eq_zero.mp (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp ht)

/-- Normalized states span the positive cone by a proved normalization identity. -/
theorem real_maps_eq_on_positive_of_eq_on_densities
    (F G : Operator ι →ₗ[ℝ] Operator ο)
    (h : ∀ ρ : Density ι, F ρ.matrix = G ρ.matrix)
    (X : Operator ι) (hX : X.PosSemidef) : F X = G X := by
  by_cases hz : mass X = 0
  · have hzero := (mass_eq_zero_iff hX).mp hz
    simp [hzero]
  · have hp : 0 < mass X := lt_of_le_of_ne (mass_nonneg hX) (Ne.symm hz)
    have hscale : X = mass X • (normalize X hX hp).matrix := by
      rw [normalize_matrix, smul_smul, mul_inv_cancel₀ hz, one_smul]
    rw [hscale, map_smul, map_smul, h]

/-- No spectral data are supplied as an axiom: the existing affine-effect theorem
provides the two positive inputs used to determine any Hermitian input. -/
theorem real_maps_eq_on_hermitian_of_eq_on_densities
    (F G : Operator ι →ₗ[ℝ] Operator ο)
    (h : ∀ ρ : Density ι, F ρ.matrix = G ρ.matrix)
    (H : Operator ι) (hH : H.IsHermitian) : F H = G H := by
  obtain ⟨r, E, _, heq⟩ := QuantumSeparation.exists_effect_affine_of_hermitian H hH
  have hE := real_maps_eq_on_positive_of_eq_on_densities F G h E.matrix E.positive
  have hI := real_maps_eq_on_positive_of_eq_on_densities F G h (1 : Operator ι)
    Matrix.PosSemidef.one
  rw [heq, map_sub, map_sub, map_smul, map_smul, map_smul, map_smul, hE, hI]

/-- The existing real and imaginary Hermitian matrix units determine a complex
matrix unit; complex linearity is used only after Hermitian-input agreement. -/
theorem matrixUnit_hermitian_expansion (i j : ι) :
    matrixUnit i j =
      (1 / 2 : ℂ) • symmetricUnit i j -
      (Complex.I / 2) • imaginaryUnit i j := by
  ext a b
  simp only [matrixUnit,
    symmetricUnit, imaginaryUnit,
    Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.single_apply]
  split_ifs <;> simp_all [eq_comm] <;> ring_nf <;> norm_num [Complex.I_sq]

/-- Equality on every genuine density determines the actual complex-linear map. -/
theorem complex_linear_eq_of_eq_on_densities
    (F G : Operator ι →ₗ[ℂ] Operator ο)
    (h : ∀ ρ : Density ι, F ρ.matrix = G ρ.matrix) : F = G := by
  have hh (H : Operator ι) (hH : H.IsHermitian) : F H = G H :=
    real_maps_eq_on_hermitian_of_eq_on_densities
      (F.restrictScalars ℝ) (G.restrictScalars ℝ) h H hH
  have hu (i j : ι) :
      F (matrixUnit i j) =
        G (matrixUnit i j) := by
    rw [matrixUnit_hermitian_expansion, map_sub, map_sub,
      map_smul, map_smul, map_smul, map_smul,
      hh _ (symmetricUnit_hermitian i j),
      hh _ (imaginaryUnit_hermitian i j)]
  apply LinearMap.ext
  intro X
  have expand (L : Operator ι →ₗ[ℂ] Operator ο) :
      L X = ∑ i, ∑ j, (X i j) • L (matrixUnit i j) := by
    conv_lhs => rw [matrix_expansion X]
    simp only [map_sum, map_smul]
  rw [expand F, expand G]
  simp only [hu]

/-- Statistics include the raw event probability, since Effect.one is allowed. -/
def SingleStatistics (F G : Operator ι →ₗ[ℂ] Operator ο) : Prop :=
  ∀ (ρ : Density ι) (E : Effect ο),
    pairing E.matrix (F ρ.matrix) = pairing E.matrix (G ρ.matrix)

theorem singleStatistics_iff_map_eq
    (F G : Operator ι →ₗ[ℂ] Operator ο)
    (hF : ∀ X : Operator ι, X.PosSemidef → (F X).PosSemidef)
    (hG : ∀ X : Operator ι, X.PosSemidef → (G X).PosSemidef) :
    SingleStatistics F G ↔ F = G := by
  constructor
  · intro h
    apply complex_linear_eq_of_eq_on_densities F G
    intro ρ
    exact hermitian_eq_of_all_effect_pairings_eq _ _
      (hF _ ρ.positive).isHermitian (hG _ ρ.positive).isHermitian (h ρ)
  · rintro rfl ρ E
    rfl

/-- Input-first Choi convention for separately typed input and output systems. -/
def choi (F : Operator ι →ₗ[ℂ] Operator ο) : Operator (ι × ο) :=
  fun ia jb => F (matrixUnit ia.1 jb.1) ia.2 jb.2

theorem choi_injective : Function.Injective (choi (ι := ι) (ο := ο)) := by
  intro F G h
  apply LinearMap.ext
  intro X
  have expand (L : Operator ι →ₗ[ℂ] Operator ο) :
      L X = ∑ i, ∑ j, (X i j) • L (matrixUnit i j) := by
    conv_lhs => rw [matrix_expansion X]
    simp only [map_sum, map_smul]
  rw [expand F, expand G]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ext a b
  exact congrFun (congrFun h (i, a)) (j, b)

theorem map_eq_iff_choi_eq (F G : Operator ι →ₗ[ℂ] Operator ο) :
    F = G ↔ choi F = choi G := ⟨fun h => congrArg choi h, choi_injective⟩

/-- Tensoring an actual linear map with an untouched finite reference, written
in reference blocks so it is manifestly independent of Kraus presentation. -/
def amplify (F : Operator ι →ₗ[ℂ] Operator ο) (ν : Type*) [Fintype ν] :
    Operator (ι × ν) →ₗ[ℂ] Operator (ο × ν) where
  toFun X a b := F (fun i j => X (i, a.2) (j, b.2)) a.1 b.1
  map_add' X Y := by
    ext ⟨a, r⟩ ⟨b, s⟩
    change F ((fun i j => X (i, r) (j, s)) +
      (fun i j => Y (i, r) (j, s))) a b = _
    rw [map_add]
    rfl
  map_smul' c X := by
    ext ⟨a, r⟩ ⟨b, s⟩
    change F (c • (fun i j => X (i, r) (j, s))) a b = _
    rw [map_smul]
    rfl

theorem amplify_congr (F G : Operator ι →ₗ[ℂ] Operator ο) (h : F = G)
    (ν : Type*) [Fintype ν] : amplify F ν = amplify G ν := congrArg (fun L => amplify L ν) h

theorem context_statistics_of_singleStatistics
    (F G : Operator ι →ₗ[ℂ] Operator ο)
    (hF : ∀ X : Operator ι, X.PosSemidef → (F X).PosSemidef)
    (hG : ∀ X : Operator ι, X.PosSemidef → (G X).PosSemidef)
    (h : SingleStatistics F G)
    (ν : Type*) [Fintype ν] [DecidableEq ν]
    (ρ : Density (ι × ν)) (E : Effect (ο × ν)) :
    pairing E.matrix (amplify F ν ρ.matrix) =
      pairing E.matrix (amplify G ν ρ.matrix) := by
  rw [amplify_congr F G ((singleStatistics_iff_map_eq F G hF hG).mp h) ν]

/-- The tensor unit is one dimensional and has a normalized state. -/
def scalarDensity : Density Unit where
  matrix := 1
  positive := Matrix.PosSemidef.one
  trace_one := by simp [Matrix.trace]

def scalarEffect (E : Effect ο) : Effect (ο × Unit) where
  matrix := E.matrix ⊗ₖ (1 : Operator Unit)
  positive := E.positive.kronecker Matrix.PosSemidef.one
  complement_positive := by
    rw [← Matrix.one_kronecker_one, ← sub_kronecker]
    exact E.complement_positive.kronecker Matrix.PosSemidef.one

/-- Every finite positive-dimensional identity reference with all legal joint
states and effects. No restriction to product inputs appears in this predicate. -/
def ContextStatistics (F G : Operator ι →ₗ[ℂ] Operator ο) : Prop :=
  ∀ (ν : Type) [Fintype ν] [DecidableEq ν] [Nonempty ν]
    (ρ : Density (ι × ν)) (E : Effect (ο × ν)),
    pairing E.matrix (amplify F ν ρ.matrix) =
      pairing E.matrix (amplify G ν ρ.matrix)

theorem scalar_context_pairing (F : Operator ι →ₗ[ℂ] Operator ο)
    (ρ : Density ι) (E : Effect ο) :
    pairing (scalarEffect E).matrix
      (amplify F Unit (QuantumPurification.product ρ scalarDensity).matrix) =
        pairing E.matrix (F ρ.matrix) := by
  simp [pairing, mass, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type,
    scalarEffect, QuantumPurification.product, scalarDensity,
    amplify, Matrix.kronecker_apply, Matrix.one_apply]

theorem contextStatistics_iff_singleStatistics
    (F G : Operator ι →ₗ[ℂ] Operator ο)
    (hF : ∀ X : Operator ι, X.PosSemidef → (F X).PosSemidef)
    (hG : ∀ X : Operator ι, X.PosSemidef → (G X).PosSemidef) :
    ContextStatistics F G ↔ SingleStatistics F G := by
  constructor
  · intro h ρ E
    have hu := h Unit (QuantumPurification.product ρ scalarDensity)
      (scalarEffect E)
    simpa only [scalar_context_pairing] using hu
  · intro h ν _ _ _ ρ E
    exact context_statistics_of_singleStatistics F G hF hG h ν ρ E

theorem contextStatistics_iff_map_eq
    (F G : Operator ι →ₗ[ℂ] Operator ο)
    (hF : ∀ X : Operator ι, X.PosSemidef → (F X).PosSemidef)
    (hG : ∀ X : Operator ι, X.PosSemidef → (G X).PosSemidef) :
    ContextStatistics F G ↔ F = G :=
  (contextStatistics_iff_singleStatistics F G hF hG).trans
    (singleStatistics_iff_map_eq F G hF hG)

theorem contextStatistics_iff_choi_eq
    (F G : Operator ι →ₗ[ℂ] Operator ο)
    (hF : ∀ X : Operator ι, X.PosSemidef → (F X).PosSemidef)
    (hG : ∀ X : Operator ι, X.PosSemidef → (G X).PosSemidef) :
    ContextStatistics F G ↔ choi F = choi G :=
  (contextStatistics_iff_map_eq F G hF hG).trans (map_eq_iff_choi_eq F G)

/-- Legal rectangular TNI Kraus event. The only order premise is the Kraus
completeness inequality; neither an observational equivalence nor its conclusion
is accepted as a certificate field. -/
structure Event (ι ο κ : Type*) [Fintype ι] [DecidableEq ι]
    [Fintype ο] [DecidableEq ο] [Fintype κ] where
  kraus : κ → Matrix ο ι ℂ
  defect_positive : (1 - ∑ k, (kraus k)ᴴ * kraus k).PosSemidef

namespace Event

def operatorLinear (C : Event ι ο κ) : Operator ι →ₗ[ℂ] Operator ο where
  toFun X := ∑ k, C.kraus k * X * (C.kraus k)ᴴ
  map_add' X Y := by
    simp only [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' c X := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum, RingHom.id_apply]

theorem operator_posSemidef (C : Event ι ο κ) {X : Operator ι}
    (hX : X.PosSemidef) : (C.operatorLinear X).PosSemidef :=
  Matrix.posSemidef_sum Finset.univ
    (fun k _ => hX.mul_mul_conjTranspose_same (C.kraus k))

theorem trace_operator (C : Event ι ο κ) (X : Operator ι) :
    (C.operatorLinear X).trace = ((∑ k, (C.kraus k)ᴴ * C.kraus k) * X).trace := by
  rw [operatorLinear, LinearMap.coe_mk, AddHom.coe_mk, Matrix.trace_sum,
    Matrix.sum_mul, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact Matrix.trace_mul_cycle (C.kraus k) X (C.kraus k)ᴴ

theorem mass_operator_le (C : Event ι ο κ) {X : Operator ι}
    (hX : X.PosSemidef) : mass (C.operatorLinear X) ≤ mass X := by
  have h := UEOTQM.pairing_nonneg C.defect_positive hX
  rw [pairing_sub_left, pairing_one] at h
  have ht : mass (C.operatorLinear X) =
      pairing (∑ k, (C.kraus k)ᴴ * C.kraus k) X :=
    congrArg Complex.re (C.trace_operator X)
  rw [ht]
  linarith

/-- A genuine identity-ancilla Kraus extension remains trace nonincreasing. -/
def amplify (C : Event ι ο κ) (ν : Type*) [Fintype ν] [DecidableEq ν] :
    Event (ι × ν) (ο × ν) κ where
  kraus k := C.kraus k ⊗ₖ (1 : Operator ν)
  defect_positive := by
    simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul]
    have hs : (∑ k, ((C.kraus k)ᴴ * C.kraus k) ⊗ₖ (1 : Operator ν)) =
        (∑ k, (C.kraus k)ᴴ * C.kraus k) ⊗ₖ (1 : Operator ν) := by
      ext ⟨i, a⟩ ⟨j, b⟩
      simp [Matrix.sum_apply, Matrix.kronecker_apply, Finset.sum_mul]
    rw [hs, ← Matrix.one_kronecker_one,
      ← sub_kronecker]
    exact C.defect_positive.kronecker Matrix.PosSemidef.one

/-- Equality with the actual tensor-id linear extension is derived from Kraus
matrices; it is not a field supplied by the event constructor. -/
theorem amplify_operator_apply (C : Event ι ο κ)
    (ν : Type*) [Fintype ν] [DecidableEq ν]
    (X : Operator (ι × ν)) (i j : ο) (a b : ν) :
    (C.amplify ν).operatorLinear X (i, a) (j, b) =
      C.operatorLinear (fun x y => X (x, a) (y, b)) i j := by
  classical
  simp only [operatorLinear, amplify, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kronecker_apply,
    Fintype.sum_prod_type, Matrix.one_apply, mul_assoc]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single b]
  · simp [Matrix.mul_apply]
    left
    rfl
  · intro y _ hy
    simp [Ne.symm hy]
  · simp

theorem amplify_operator_eq (C : Event ι ο κ)
    (ν : Type*) [Fintype ν] [DecidableEq ν] :
    (C.amplify ν).operatorLinear = OperationalEquivalence.amplify C.operatorLinear ν := by
  apply LinearMap.ext
  intro X
  ext ⟨i, a⟩ ⟨j, b⟩
  exact C.amplify_operator_apply ν X i j a b

/-- Complete positivity on all joint PSD inputs, including entangled inputs. -/
theorem amplify_posSemidef (C : Event ι ο κ)
    (ν : Type*) [Fintype ν] [DecidableEq ν]
    {X : Operator (ι × ν)} (hX : X.PosSemidef) :
    (OperationalEquivalence.amplify C.operatorLinear ν X).PosSemidef := by
  rw [← C.amplify_operator_eq ν]
  exact (C.amplify ν).operator_posSemidef hX

theorem statistics_iff_map_eq {η : Type*} [Fintype η]
    (C : Event ι ο κ) (D : Event ι ο η) :
    SingleStatistics C.operatorLinear D.operatorLinear ↔
      C.operatorLinear = D.operatorLinear :=
  singleStatistics_iff_map_eq _ _
    (fun _ h => C.operator_posSemidef h) (fun _ h => D.operator_posSemidef h)

/-- A complete rectangular channel is a TNI event, without changing its Kraus data. -/
def ofChannel (C : RectangularChannel ι ο κ) : Event ι ο κ where
  kraus := C.kraus
  defect_positive := by
    rw [C.complete, sub_self]
    exact Matrix.PosSemidef.zero

@[simp] theorem ofChannel_operator (C : RectangularChannel ι ο κ) :
    (ofChannel C).operatorLinear = C.operatorLinear := rfl

end Event

/-- Per-visible-label equality is a congruence under actual sequential maps. -/
theorem labelled_comp_congr {O P μ : Type*} [Fintype μ] [DecidableEq μ]
    (F G : O → Operator ι →ₗ[ℂ] Operator ο)
    (H K : O → P → Operator ο →ₗ[ℂ] Operator μ)
    (hFG : ∀ o, F o = G o) (hHK : ∀ o p, H o p = K o p) :
    ∀ o p, (H o p).comp (F o) = (K o p).comp (G o) := by
  intro o p
  rw [hFG o, hHK o p]

/-- A declared coarse graining sums actual events, preserving each visible fiber. -/
theorem labelled_sum_congr {O : Type*} [Fintype O]
    (F G : O → Operator ι →ₗ[ℂ] Operator ο) (h : ∀ o, F o = G o) :
    (∑ o, F o) = ∑ o, G o := by
  apply Finset.sum_congr rfl
  intro o _
  exact h o

end
end UEOTQM.OperationalEquivalence
