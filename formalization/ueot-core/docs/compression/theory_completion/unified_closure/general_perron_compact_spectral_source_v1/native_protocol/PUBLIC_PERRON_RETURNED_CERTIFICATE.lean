import UEOT
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open PrimitivePerronClosure
open scoped BigOperators Topology
open Filter
noncomputable section
namespace ActualPFConsumer
abbrev A : Matrix (Fin 2) (Fin 2) ℝ := !![2,1;2,3]
theorem primitiveA : Matrix.IsPrimitive A := by
  constructor
  · intro i j; fin_cases i <;> fin_cases j <;> norm_num [A]
  · refine ⟨1,by decide,?_⟩
    intro i j; fin_cases i <;> fin_cases j <;> norm_num [A]
noncomputable def pf := certificateOfPrimitive A primitiveA
noncomputable def referenceRight : UEOT.V3.Compression.PositiveEigenstructure.RightEigenData A where
  scale := 4
  vector := ![1,2]
  scale_pos := by norm_num
  vector_pos := by intro i; fin_cases i <;> norm_num
  eigen := by
    intro i; fin_cases i <;>
      norm_num [UEOT.V3.Compression.PositiveEigenstructure.colApply,A,Fin.sum_univ_two]
theorem returned_root : pf.R = 4 := by
  exact PrimitivePerronUniqueness.positive_eigenvalue_eq A primitiveA.nonneg referenceRight
    pf.R pf.r pf.r_pos pf.right_eigen
theorem returned_left : pf.l = ![1/2,1/2] := by
  have h := pf.left_eigen 0
  have hs := pf.l_sum
  simp only [Fin.sum_univ_two] at h hs
  norm_num [A] at h
  rw [returned_root] at h
  funext i; fin_cases i
  · change pf.l 0 = (1/2 : ℝ); linarith
  · change pf.l 1 = (1/2 : ℝ); linarith
 theorem returned_right : pf.r = ![2/3,4/3] := by
  have he := pf.right_eigen 0
  have hn := pf.lr_norm
  simp only [Fin.sum_univ_two] at he hn
  norm_num [A] at he
  rw [returned_root] at he
  rw [returned_left] at hn
  norm_num at hn
  funext i; fin_cases i
  · change pf.r 0 = (2/3 : ℝ); linarith
  · change pf.r 1 = (4/3 : ℝ); linarith
example : Tendsto (fun n : ℕ => (4^n : ℝ)⁻¹ * (A^n) 1 0) atTop (𝓝 (2/3)) := by
  have h := pf.power_coord_tendsto 1 0
  rw [returned_root,returned_right,returned_left] at h
  norm_num at h
  exact h
example : A.charpoly.rootMultiplicity 4 = 1 := by
  have h := actual_root_simple A primitiveA
  change A.charpoly.rootMultiplicity pf.R = 1 at h
  rwa [returned_root] at h
abbrev counts : Fin 2 → ℕ := ![2,1]
abbrev value : Fin 2 → ℝ := ![1,2]
example : Tendsto
    (fun n : ℕ => fun j : Fin 2 => UEOT.V3.EvolutionPerronGrowth.rowApply
      (UEOT.V3.EvolutionPerronGrowth.natRow counts) (A^n) j /
      UEOT.V3.EvolutionPerronGrowth.rowMass (UEOT.V3.EvolutionPerronGrowth.rowApply
        (UEOT.V3.EvolutionPerronGrowth.natRow counts) (A^n))) atTop (𝓝 ![1/2,1/2]) := by
  have hc : counts ≠ 0 := by intro h; have := congrFun h 0; norm_num [counts] at this
  have hv : ∀ i, 0 < value i := by intro i; fin_cases i <;> norm_num [value]
  have he : ∀ z : Fin 2 → ℝ, (∀ i, 0 ≤ z i) →
      UEOT.V3.EvolutionPerronGrowth.rowDot (UEOT.V3.EvolutionPerronGrowth.rowApply z A) value =
        4 * UEOT.V3.EvolutionPerronGrowth.rowDot z value := by
    intro z hz
    simp [UEOT.V3.EvolutionPerronGrowth.rowDot,UEOT.V3.EvolutionPerronGrowth.rowApply,
      A,value,Fin.sum_univ_two]
    ring
  have h := actual_p_evo_03 A primitiveA counts hc 4 value hv he
  have hlim := h.2.1
  change Tendsto _ _ (𝓝 pf.l) at hlim
  rwa [returned_left] at hlim
#check certificateOfPrimitive
#print axioms certificateOfPrimitive
#check actual_p_evo_03
#print axioms actual_p_evo_03
#check actual_lineage_perron
#print axioms actual_lineage_perron
#check actual_root_simple
#print axioms actual_root_simple
end ActualPFConsumer
end
