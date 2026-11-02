import UEOT.V3.EvolutionPerronGrowth
import UEOT.V3.Compression.TheoryCompletion.LineageEvolution
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PrimitivePerronSimplicity
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PrimitivePerronBiEigen
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PrimitivePerronUniqueness
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PrimitiveMarkovMixing
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PrimitivePerronSpectral

/-! The original K-PF-01 certificate is constructed from primitivity of the
same arbitrary finite matrix. No power limit or spectral conclusion is input.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PrimitivePerronClosure
noncomputable section
open Filter Topology
open scoped BigOperators
open UEOT.V3.Compression.PositiveEigenstructure
  (BiEigenData invariantWeight invariantWeight_sum invariantWeight_stationary hTransform)
open PrimitivePerronDoob PrimitivePerronBiEigen
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] {M : Matrix I I ℝ}

/-- The paired weight is a probability row of the actual Doob chain. -/
def invariantSimplex (B : BiEigenData M) : stdSimplex ℝ I :=
  ⟨invariantWeight B, fun i => mul_nonneg (B.left_nonneg i) (B.right.vector_pos i).le,
    invariantWeight_sum B⟩

/-- The original matrix's full rank-one power limit, transported from the
actual primitive Doob chain and its actual paired invariant row. -/
theorem actual_power_limit (B : BiEigenData M) (hM : Matrix.IsPrimitive M) (i j : I) :
    Tendsto (fun n : ℕ => (B.right.scale ^ n)⁻¹ * (M ^ n) i j) atTop
      (𝓝 (B.right.vector i * B.left j)) := by
  let p := invariantSimplex B
  have hp : Matrix.vecMul p.val (hTransform B.right) = p.val := by
    funext j
    exact invariantWeight_stationary B j
  have hlim := PrimitiveMarkovMixing.primitive_power_tendsto_invariant
    (hTransform B.right) (transform_stochastic B.right hM.nonneg)
    (transform_primitive B.right hM) p hp i j
  have hR := B.right.scale_pos.ne'
  have hv : ∀ k, B.right.vector k ≠ 0 := fun k => (B.right.vector_pos k).ne'
  have heq : ∀ n : ℕ, (B.right.scale^n)⁻¹ * (M^n) i j =
      (hTransform B.right ^ n) i j * (B.right.vector i / B.right.vector j) := by
    intro n
    rw [transform_power]
    field_simp [hR, hv]
  have ht := hlim.mul_const (B.right.vector i / B.right.vector j)
  have hl : p.val j * (B.right.vector i / B.right.vector j) =
      B.right.vector i * B.left j := by
    change (B.left j * B.right.vector j) * (B.right.vector i / B.right.vector j) = _
    field_simp [hv]
  rw [hl] at ht
  exact (tendsto_congr' (Filter.Eventually.of_forall heq)).mpr ht

/-- All original certificate outputs for the same primitive M. -/
def certificate_of_bieigen (B : BiEigenData M) (hM : Matrix.IsPrimitive M)
    (hl : ∀ i, 0 < B.left i) : UEOT.V3.EvolutionPerronGrowth.KPF01Certificate M where
  primitive := hM
  R := B.right.scale
  r := B.right.vector
  l := B.left
  R_pos := B.right.scale_pos
  r_pos := B.right.vector_pos
  l_pos := hl
  right_eigen := B.right.eigen
  left_eigen := B.left_eigen
  l_sum := B.left_sum_one
  lr_norm := B.pairing_sum_one
  power_coord_tendsto := actual_power_limit B hM
  positive_right_eigen_unique := by
    intro a v hv he
    obtain ⟨ha,c,hc,heq⟩ := PrimitivePerronUniqueness.positive_eigenvector_ray M hM B.right a v hv he
    refine ⟨ha,c,hc,?_⟩
    intro i
    exact congrFun heq i
  strict_spectral_dominance := by
    intro a v hv he ha
    exact PrimitivePerronSpectral.strict_of_power_limit M B.right.scale B.right.scale_pos
      (fun i j => B.right.vector i * B.left j) (actual_power_limit B hM) a v hv he ha

/-- No field of the original K-PF-01 result is now supplied by the caller. -/
noncomputable def certificateOfPrimitive (M : Matrix I I ℝ) (hM : Matrix.IsPrimitive M) :
    UEOT.V3.EvolutionPerronGrowth.KPF01Certificate M :=
  certificate_of_bieigen (biEigenDataOfPrimitive M hM) hM (actual_left_pos M hM)

/-- The root in THIS constructed original certificate is algebraically simple,
    rather than merely unique among positive eigenvectors. -/
theorem actual_root_simple (M : Matrix I I ℝ) (hM : Matrix.IsPrimitive M) :
    M.charpoly.rootMultiplicity (certificateOfPrimitive M hM).R = 1 :=
  PrimitivePerronSimplicity.actual_perron_root_algebraically_simple M hM

open UEOT.V3.EvolutionPerronGrowth

/-- The original P-EVO-03 is consumed with the certificate actually computed
    as a mathematical construction from THIS primitive matrix. -/
theorem actual_p_evo_03 (M : Matrix I I ℝ) (hM : Matrix.IsPrimitive M)
    (z0 : I → ℕ) (hz0 : z0 ≠ 0) (rho : ℝ) (w : I → ℝ)
    (hw : ∀ i, 0 < w i)
    (hval : ∀ z : I → ℝ, (∀ i, 0 ≤ z i) →
      rowDot (rowApply z M) w = rho * rowDot z w) :
    let pf := certificateOfPrimitive M hM
    Tendsto (fun n : ℕ => fun j : I =>
      (pf.R ^ n)⁻¹ * rowApply (natRow z0) (M ^ n) j) atTop
        (𝓝 (fun j : I => rowDot (natRow z0) pf.r * pf.l j)) ∧
    Tendsto (fun n : ℕ => fun j : I => rowApply (natRow z0) (M ^ n) j /
      rowMass (rowApply (natRow z0) (M ^ n))) atTop (𝓝 pf.l) ∧
    rho = pf.R ∧ ∃ c : ℝ, 0 < c ∧ ∀ i, w i = c * pf.r i :=
  UEOT.V3.EvolutionPerronGrowth.p_evo_03 M (certificateOfPrimitive M hM)
    z0 hz0 rho w hw hval

/-- The original lineage consumer retains its genuine transmission condition;
    the previously external Perron certificate is supplied by primitivity. -/
theorem actual_lineage_perron {Identity : Type*}
    (L : UEOT.V3.Compression.TheoryCompletion.LineageSemantics I Identity)
    (M : Matrix I I ℝ) (hM : Matrix.IsPrimitive M)
    (hl : L.ReproductiveTransmission M) (z0 : I → ℕ) (hz0 : z0 ≠ 0)
    (rho : ℝ) (w : I → ℝ) (hw : ∀ i, 0 < w i)
    (hval : ∀ z : I → ℝ, (∀ i, 0 ≤ z i) →
      rowDot (rowApply z M) w = rho * rowDot z w) :
    let pf := certificateOfPrimitive M hM
    Tendsto (fun n : ℕ => fun j : I =>
      (pf.R ^ n)⁻¹ * rowApply (natRow z0) (M ^ n) j) atTop
        (𝓝 (fun j : I => rowDot (natRow z0) pf.r * pf.l j)) ∧
    Tendsto (fun n : ℕ => fun j : I => rowApply (natRow z0) (M ^ n) j /
      rowMass (rowApply (natRow z0) (M ^ n))) atTop (𝓝 pf.l) ∧
    rho = pf.R ∧ (∃ c : ℝ, 0 < c ∧ ∀ i, w i = c * pf.r i) ∧
    (∀ parent child, 0 < M parent child → L.OffspringOf parent child) :=
  L.lineage_perron_bridge M (certificateOfPrimitive M hM) hl z0 hz0 rho w hw hval

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PrimitivePerronClosure
