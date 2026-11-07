import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PrimitivePerronClosure

/-!
# Finite row-rectangular growth control from actual Perron factories

This is the finite algebraic implication used by the source consumer. The rows
`m i a` and the legal action types must come from that source. The source must
also establish that a selector can really be implemented with its observations
and resource rules, and that every continuing selector is primitive.

The theorem does not ask for a Bellman eigenpair or an optimal selector. It
constructs each Perron certificate with the existing `certificateOfPrimitive`,
takes a maximum over the finite selector set, and proves the row inequalities
by a single-row replacement. Stop/death actions are not silently included in
the primitive hypothesis; the source can extend the inequality to them by an
actual row domination proof.

The selected maximum is mathematical existence, not an executable optimizer.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteSourceGrowthControl

noncomputable section
open scoped BigOperators
open UEOT.V3.EvolutionPerronGrowth (KPF01Certificate)

universe u v
variable {I : Type u} [Fintype I] [DecidableEq I] [Nonempty I]
variable {A : I → Type v} [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]

/-- A legal selector chooses one element of the actual action type in each
    observable row. A dependent type permits different legal menus. -/
abbrev Selector (A : I → Type v) := (i : I) → A i

/-- This construction changes no row and adds no random transition. -/
def selectedMatrix (m : (i : I) → A i → I → ℝ) (π : Selector A) :
    Matrix I I ℝ := fun i j => m i (π i) j

/-- The entire old Perron result is produced from the selected same matrix. -/
def selectedPerron (m : (i : I) → A i → I → ℝ)
    (hp : ∀ π : Selector A, Matrix.IsPrimitive (selectedMatrix m π))
    (π : Selector A) : KPF01Certificate (selectedMatrix m π) :=
  PrimitivePerronClosure.certificateOfPrimitive (selectedMatrix m π) (hp π)

private theorem pairing_left_eigen {M : Matrix I I ℝ}
    (pf : KPF01Certificate M) (r : I → ℝ) :
    (∑ i, pf.l i * (∑ j, M i j * r j)) =
      pf.R * (∑ i, pf.l i * r i) := by
  calc
    _ = ∑ j, (∑ i, pf.l i * M i j) * r j := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ j, (pf.R * pf.l j) * r j := by
      simp_rw [pf.left_eigen]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

private theorem positive_pairing {M : Matrix I I ℝ}
    (pf : KPF01Certificate M) (r : I → ℝ) (hr : ∀ i, 0 < r i) :
    0 < ∑ i, pf.l i * r i := by
  let i : I := Classical.choice (inferInstance : Nonempty I)
  exact Finset.sum_pos'
    (fun j _ => (mul_pos (pf.l_pos j) (hr j)).le)
    ⟨i, Finset.mem_univ i, mul_pos (pf.l_pos i) (hr i)⟩

/-- A positive subeigenvector with a genuine strict coordinate gives a
strict root comparison, using the constructed matrix's positive left vector. -/
theorem root_lt_of_subsolution {M : Matrix I I ℝ}
    (pf : KPF01Certificate M) (r : I → ℝ) (hr : ∀ i, 0 < r i)
    (rho : ℝ) (hle : ∀ i, rho * r i ≤ ∑ j, M i j * r j)
    (hlt : ∃ i, rho * r i < ∑ j, M i j * r j) :
    rho < pf.R := by
  obtain ⟨i, hi⟩ := hlt
  have hsum :
      (∑ k, pf.l k * (rho * r k)) <
        ∑ k, pf.l k * (∑ j, M k j * r j) := by
    apply Finset.sum_lt_sum
    · intro k _
      exact mul_le_mul_of_nonneg_left (hle k) (pf.l_pos k).le
    · exact ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left hi (pf.l_pos i)⟩
  have hleft : (∑ k, pf.l k * (rho * r k)) =
      rho * (∑ k, pf.l k * r k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hleft, pairing_left_eigen pf r] at hsum
  have hpositive := positive_pairing pf r hr
  nlinarith

/-- The corresponding weak comparison is useful for checking an explicitly
computed source program, without claiming the abstract maximum runs. -/
theorem root_le_of_supersolution {M : Matrix I I ℝ}
    (pf : KPF01Certificate M) (r : I → ℝ) (hr : ∀ i, 0 < r i)
    (rho : ℝ) (hle : ∀ i, (∑ j, M i j * r j) ≤ rho * r i) :
    pf.R ≤ rho := by
  have hsum :
      (∑ k, pf.l k * (∑ j, M k j * r j)) ≤
        ∑ k, pf.l k * (rho * r k) := by
    apply Finset.sum_le_sum
    intro k _
    exact mul_le_mul_of_nonneg_left (hle k) (pf.l_pos k).le
  have hright : (∑ k, pf.l k * (rho * r k)) =
      rho * (∑ k, pf.l k * r k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hright, pairing_left_eigen pf r] at hsum
  have hpositive := positive_pairing pf r hr
  nlinarith

/-- Coordinate domination certifies a concretely encoded selector against the
whole legal row product. The positive vector is produced for that same selector
by the old Perron factory; it is not a premise supplied by the consumer. -/
theorem selector_maximal_of_rowwise_domination (m : (i : I) → A i → I → ℝ)
    (hp : ∀ π : Selector A, Matrix.IsPrimitive (selectedMatrix m π))
    (π : Selector A) (hdom : ∀ i (a : A i) j, m i a j ≤ m i (π i) j) :
    ∀ σ : Selector A, (selectedPerron m hp σ).R ≤ (selectedPerron m hp π).R := by
  intro σ
  let pf := selectedPerron m hp π
  apply root_le_of_supersolution (selectedPerron m hp σ) pf.r pf.r_pos pf.R
  intro i
  calc
    (∑ j, selectedMatrix m σ i j * pf.r j) ≤
        ∑ j, selectedMatrix m π i j * pf.r j := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (hdom i (σ i) j) (pf.r_pos j).le
    _ = pf.R * pf.r i := pf.right_eigen i

/-- A maximum-root selector obeys every actual row inequality. The proof's
replacement stays in the dependent product of legal action types. -/
theorem maximal_selector_row_bound (m : (i : I) → A i → I → ℝ)
    (hp : ∀ π : Selector A, Matrix.IsPrimitive (selectedMatrix m π))
    (π : Selector A)
    (hmax : ∀ σ : Selector A, (selectedPerron m hp σ).R ≤
      (selectedPerron m hp π).R) :
    ∀ i (a : A i),
      (∑ j, m i a j * (selectedPerron m hp π).r j) ≤
        (selectedPerron m hp π).R * (selectedPerron m hp π).r i := by
  classical
  intro i a
  by_contra hn
  have hstrict := lt_of_not_ge hn
  let σ : Selector A := Function.update π i a
  let pf := selectedPerron m hp π
  let pf' := selectedPerron m hp σ
  have hle : ∀ k, pf.R * pf.r k ≤ ∑ j, selectedMatrix m σ k j * pf.r j := by
    intro k
    by_cases hki : k = i
    · subst k
      simpa [selectedMatrix, σ, pf] using hstrict.le
    · have hk := pf.right_eigen k
      simpa [selectedMatrix, σ, hki] using hk.ge
  have hi : pf.R * pf.r i < ∑ j, selectedMatrix m σ i j * pf.r j := by
    simpa [selectedMatrix, σ, pf] using hstrict
  have hroot : pf.R < pf'.R :=
    root_lt_of_subsolution pf' pf.r pf.r_pos pf.R hle ⟨i, hi⟩
  exact (not_lt_of_ge (hmax σ)) hroot

/-- Finite maximum-root existence followed by the single-row argument.
No eigenpair, optimality, or successful control certificate is an input. -/
theorem exists_optimal_selector (m : (i : I) → A i → I → ℝ)
    (hp : ∀ π : Selector A, Matrix.IsPrimitive (selectedMatrix m π)) :
    ∃ π : Selector A,
      (∀ σ : Selector A, (selectedPerron m hp σ).R ≤ (selectedPerron m hp π).R) ∧
      ∀ i (a : A i),
        (∑ j, m i a j * (selectedPerron m hp π).r j) ≤
          (selectedPerron m hp π).R * (selectedPerron m hp π).r i := by
  classical
  obtain ⟨π, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun σ : Selector A => (selectedPerron m hp σ).R) Finset.univ_nonempty
  have hmax' : ∀ σ : Selector A, (selectedPerron m hp σ).R ≤
      (selectedPerron m hp π).R := fun σ => hmax σ (Finset.mem_univ σ)
  exact ⟨π, hmax', maximal_selector_row_bound m hp π hmax'⟩

/-- Mathematical choice of the proved selector. Source-specific executable
programs are certified separately; this is not an algorithm declaration. -/
def optimalSelector (m : (i : I) → A i → I → ℝ)
    (hp : ∀ π : Selector A, Matrix.IsPrimitive (selectedMatrix m π)) : Selector A :=
  Classical.choose (exists_optimal_selector m hp)

theorem optimalSelector_maximal (m : (i : I) → A i → I → ℝ)
    (hp : ∀ π : Selector A, Matrix.IsPrimitive (selectedMatrix m π))
    (σ : Selector A) :
    (selectedPerron m hp σ).R ≤
      (selectedPerron m hp (optimalSelector m hp)).R :=
  (Classical.choose_spec (exists_optimal_selector m hp)).1 σ

theorem optimalSelector_row_bound (m : (i : I) → A i → I → ℝ)
    (hp : ∀ π : Selector A, Matrix.IsPrimitive (selectedMatrix m π))
    (i : I) (a : A i) :
    (∑ j, m i a j * (selectedPerron m hp (optimalSelector m hp)).r j) ≤
      (selectedPerron m hp (optimalSelector m hp)).R *
        (selectedPerron m hp (optimalSelector m hp)).r i :=
  (Classical.choose_spec (exists_optimal_selector m hp)).2 i a

/-- The Bellman maximum is attained by the selected legal row itself. -/
theorem optimalSelector_row_isGreatest (m : (i : I) → A i → I → ℝ)
    (hp : ∀ π : Selector A, Matrix.IsPrimitive (selectedMatrix m π)) (i : I) :
    IsGreatest
      (Set.range (fun a : A i => ∑ j, m i a j *
        (selectedPerron m hp (optimalSelector m hp)).r j))
      ((selectedPerron m hp (optimalSelector m hp)).R *
        (selectedPerron m hp (optimalSelector m hp)).r i) := by
  refine ⟨⟨optimalSelector m hp i, ?_⟩, ?_⟩
  · exact (selectedPerron m hp (optimalSelector m hp)).right_eigen i
  · intro x hx
    obtain ⟨a, rfl⟩ := hx
    exact optimalSelector_row_bound m hp i a

/-- Arbitrary real mixed actions inherit the same bound; no rationality or
policy-independent random seed restriction is introduced at this algebraic step. -/
theorem optimalSelector_mixed_row_bound (m : (i : I) → A i → I → ℝ)
    (hp : ∀ π : Selector A, Matrix.IsPrimitive (selectedMatrix m π))
    (i : I) (p : A i → ℝ) (hn : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) :
    (∑ a, p a * (∑ j, m i a j *
      (selectedPerron m hp (optimalSelector m hp)).r j)) ≤
      (selectedPerron m hp (optimalSelector m hp)).R *
        (selectedPerron m hp (optimalSelector m hp)).r i := by
  calc
    _ ≤ ∑ a, p a * ((selectedPerron m hp (optimalSelector m hp)).R *
        (selectedPerron m hp (optimalSelector m hp)).r i) := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left (optimalSelector_row_bound m hp i a) (hn a)
    _ = _ := by rw [← Finset.sum_mul, hs, one_mul]

/-- A source may keep a full menu containing stop or other nonprimitive rows.
Actual coordinate domination by a continuing row extends the bound without
pretending that the extra action was primitive. -/
theorem dominated_extra_row_bound (m : (i : I) → A i → I → ℝ)
    (hp : ∀ π : Selector A, Matrix.IsPrimitive (selectedMatrix m π))
    (i : I) (extra : I → ℝ) (a : A i) (hdom : ∀ j, extra j ≤ m i a j) :
    (∑ j, extra j * (selectedPerron m hp (optimalSelector m hp)).r j) ≤
      (selectedPerron m hp (optimalSelector m hp)).R *
        (selectedPerron m hp (optimalSelector m hp)).r i := by
  apply le_trans _ (optimalSelector_row_bound m hp i a)
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_right (hdom j)
    ((selectedPerron m hp (optimalSelector m hp)).r_pos j).le

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteSourceGrowthControl
