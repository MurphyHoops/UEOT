import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PrimitivePerronClosure
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeSource

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

/-- The weighted value of actual finite offspring records is exactly the row
obtained by summing those records.  No mean is supplied as a separate field. -/
theorem record_value_eq_row_value {O : Type*} [Fintype O]
    (prob : O → ℝ) (count : O → I → ℕ) (r : I → ℝ) :
    (∑ o, prob o * (∑ j, (count o j : ℝ) * r j)) =
      ∑ j, (∑ o, prob o * (count o j : ℝ)) * r j := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro o _
  ring

/-- Summation over an actual finite population does not require independence
between different parents.  The source supplies the joint record weights. -/
theorem population_record_value_bound {P O : Type*} [Fintype P] [Fintype O]
    (prob : O → ℝ) (count : P → O → I → ℕ) (kind : P → I)
    (r : I → ℝ) (rho : ℝ)
    (hlocal : ∀ p, (∑ j, (∑ o, prob o * (count p o j : ℝ)) * r j) ≤
      rho * r (kind p)) :
    (∑ o, prob o * (∑ p, ∑ j, (count p o j : ℝ) * r j)) ≤
      rho * (∑ p, r (kind p)) := by
  calc
    _ = ∑ p, ∑ o, prob o * (∑ j, (count p o j : ℝ) * r j) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ p, ∑ j, (∑ o, prob o * (count p o j : ℝ)) * r j := by
      apply Finset.sum_congr rfl
      intro p _
      exact record_value_eq_row_value prob (count p) r
    _ ≤ ∑ p, rho * r (kind p) := Finset.sum_le_sum (fun p _ => hlocal p)
    _ = _ := (Finset.mul_sum _ _ _).symm

/-! ## Exact finite-history conditional expectations

`H n` is the actual history at census `n`; `O n h` is its finite next-step
raw branch type.  The source supplies `next` and its actual branch probabilities.
This recursion is the finite law itself, rather than an assumed vector mean.
The algebraic implication below is consumed after source records establish its
one-step premise.  It does not add observations, an independent parent-noise
assumption, or another population execution rule.
-/

section FiniteHistory
universe h o
variable {H : ℕ → Type h} {O : (n : ℕ) → H n → Type o}
variable [∀ n (x : H n), Fintype (O n x)]

def historyExpectation (initial : H 0)
    (next : ∀ n x, O n x → H (n + 1))
    (prob : ∀ n x, O n x → ℝ) : (n : ℕ) → (H n → ℝ) → ℝ
  | 0, f => f initial
  | n + 1, f => historyExpectation initial next prob n
      (fun x => ∑ u, prob n x u * f (next n x u))

theorem historyExpectation_mono (initial : H 0)
    (next : ∀ n x, O n x → H (n + 1)) (prob : ∀ n x, O n x → ℝ)
    (hn : ∀ n x u, 0 ≤ prob n x u) (n : ℕ)
    {f g : H n → ℝ} (hfg : ∀ x, f x ≤ g x) :
    historyExpectation initial next prob n f ≤
      historyExpectation initial next prob n g := by
  induction n with
  | zero => exact hfg initial
  | succ n ih =>
    apply ih
    intro x
    apply Finset.sum_le_sum
    intro u _
    exact mul_le_mul_of_nonneg_left (hfg (next n x u)) (hn n x u)

theorem historyExpectation_const_mul (initial : H 0)
    (next : ∀ n x, O n x → H (n + 1)) (prob : ∀ n x, O n x → ℝ)
    (n : ℕ) (c : ℝ) (f : H n → ℝ) :
    historyExpectation initial next prob n (fun x => c * f x) =
      c * historyExpectation initial next prob n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change historyExpectation initial next prob n
      (fun x => ∑ u, prob n x u * (c * f (next n x u))) = _
    have he : (fun x => ∑ u, prob n x u * (c * f (next n x u))) =
        (fun x => c * (∑ u, prob n x u * f (next n x u))) := by
      funext x
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      ring
    rw [he, ih]
    rfl

/-- Normalized actual branch probabilities give a normalized finite path law. -/
theorem historyExpectation_const (initial : H 0)
    (next : ∀ n x, O n x → H (n + 1)) (prob : ∀ n x, O n x → ℝ)
    (hs : ∀ n x, ∑ u, prob n x u = 1) (n : ℕ) (c : ℝ) :
    historyExpectation initial next prob n (fun _ => c) = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change historyExpectation initial next prob n
      (fun x => ∑ u, prob n x u * c) = c
    have he : (fun x => ∑ u, prob n x u * c) = (fun _ => c) := by
      funext x
      rw [← Finset.sum_mul, hs, one_mul]
    rw [he]
    exact ih

def normalizedValue (rho : ℝ) (V : ∀ n, H n → ℝ) (n : ℕ) (x : H n) : ℝ :=
  (rho ^ n)⁻¹ * V n x

/-- This is the full-history one-step supermartingale inequality for the
finite conditional law at the actual node, including zero-probability nodes. -/
theorem historyConditional_normalized_le
    (next : ∀ n x, O n x → H (n + 1)) (prob : ∀ n x, O n x → ℝ)
    (rho : ℝ) (hrho : 0 < rho) (V : ∀ n, H n → ℝ) (n : ℕ) (x : H n)
    (hstep : (∑ u, prob n x u * V (n + 1) (next n x u)) ≤ rho * V n x) :
    (∑ u, prob n x u * normalizedValue rho V (n + 1) (next n x u)) ≤
      normalizedValue rho V n x := by
  have hscale : (rho ^ (n + 1))⁻¹ * rho = (rho ^ n)⁻¹ := by
    rw [pow_succ]
    field_simp [hrho.ne']
  calc
    _ = (rho ^ (n + 1))⁻¹ *
        (∑ u, prob n x u * V (n + 1) (next n x u)) := by
      simp only [normalizedValue, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      ring
    _ ≤ (rho ^ (n + 1))⁻¹ * (rho * V n x) :=
      mul_le_mul_of_nonneg_left hstep (inv_nonneg.mpr (pow_pos hrho _).le)
    _ = _ := by rw [← mul_assoc, hscale]; rfl

/-- The same actual conditional law is a martingale when the source's selected
program attains its local row equality. -/
theorem historyConditional_normalized_eq
    (next : ∀ n x, O n x → H (n + 1)) (prob : ∀ n x, O n x → ℝ)
    (rho : ℝ) (hrho : 0 < rho) (V : ∀ n, H n → ℝ) (n : ℕ) (x : H n)
    (hstep : (∑ u, prob n x u * V (n + 1) (next n x u)) = rho * V n x) :
    (∑ u, prob n x u * normalizedValue rho V (n + 1) (next n x u)) =
      normalizedValue rho V n x := by
  have hscale : (rho ^ (n + 1))⁻¹ * rho = (rho ^ n)⁻¹ := by
    rw [pow_succ]
    field_simp [hrho.ne']
  calc
    _ = (rho ^ (n + 1))⁻¹ *
        (∑ u, prob n x u * V (n + 1) (next n x u)) := by
      simp only [normalizedValue, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      ring
    _ = _ := by rw [hstep, ← mul_assoc, hscale]; rfl

theorem historyExpectation_iterate_le (initial : H 0)
    (next : ∀ n x, O n x → H (n + 1)) (prob : ∀ n x, O n x → ℝ)
    (hn : ∀ n x u, 0 ≤ prob n x u) (rho : ℝ) (hrho : 0 ≤ rho)
    (V : ∀ n, H n → ℝ)
    (hstep : ∀ n x, (∑ u, prob n x u * V (n + 1) (next n x u)) ≤ rho * V n x)
    (n : ℕ) :
    historyExpectation initial next prob n (V n) ≤ rho ^ n * V 0 initial := by
  induction n with
  | zero => simp [historyExpectation]
  | succ n ih =>
    calc
      _ ≤ historyExpectation initial next prob n (fun x => rho * V n x) :=
        historyExpectation_mono initial next prob hn n (hstep n)
      _ = rho * historyExpectation initial next prob n (V n) :=
        historyExpectation_const_mul initial next prob n rho (V n)
      _ ≤ rho * (rho ^ n * V 0 initial) := mul_le_mul_of_nonneg_left ih hrho
      _ = _ := by rw [pow_succ]; ring

theorem historyExpectation_iterate_eq (initial : H 0)
    (next : ∀ n x, O n x → H (n + 1)) (prob : ∀ n x, O n x → ℝ)
    (rho : ℝ) (V : ∀ n, H n → ℝ)
    (hstep : ∀ n x, (∑ u, prob n x u * V (n + 1) (next n x u)) = rho * V n x)
    (n : ℕ) :
    historyExpectation initial next prob n (V n) = rho ^ n * V 0 initial := by
  induction n with
  | zero => simp [historyExpectation]
  | succ n ih =>
    change historyExpectation initial next prob n
      (fun x => ∑ u, prob n x u * V (n + 1) (next n x u)) = _
    have he : (fun x => ∑ u, prob n x u * V (n + 1) (next n x u)) =
        (fun x => rho * V n x) := funext (hstep n)
    rw [he, historyExpectation_const_mul, ih, pow_succ]
    ring

open UEOT.V3.EvolutionPerronGrowth (rowDot rowMass natRow)

/-- The existing count-row and reproductive-value objects bound actual mass. -/
theorem count_value_bounds (z : I → ℕ) (r : I → ℝ) (lo hi : ℝ)
    (hl : ∀ i, lo ≤ r i) (hu : ∀ i, r i ≤ hi) :
    lo * rowMass (natRow z) ≤ rowDot (natRow z) r ∧
      rowDot (natRow z) r ≤ hi * rowMass (natRow z) := by
  constructor
  · simp only [rowMass, rowDot, natRow, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have h := mul_le_mul_of_nonneg_left (hl i) (Nat.cast_nonneg (z i) : (0 : ℝ) ≤ z i)
    simpa [mul_comm] using h
  · simp only [rowMass, rowDot, natRow, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have h := mul_le_mul_of_nonneg_left (hu i) (Nat.cast_nonneg (z i) : (0 : ℝ) ≤ z i)
    simpa [mul_comm] using h

/-- All legal full-history controls obey this population expectation upper
bound once their actual record law establishes the conditional row inequality. -/
theorem history_population_upper (initial : H 0)
    (next : ∀ n x, O n x → H (n + 1)) (prob : ∀ n x, O n x → ℝ)
    (hn : ∀ n x u, 0 ≤ prob n x u) (rho : ℝ) (hrho : 0 ≤ rho)
    (r : I → ℝ) (lo : ℝ) (hlo : 0 < lo) (hl : ∀ i, lo ≤ r i)
    (Z : ∀ n, H n → I → ℕ)
    (hstep : ∀ n x,
      (∑ u, prob n x u * rowDot (natRow (Z (n + 1) (next n x u))) r) ≤
        rho * rowDot (natRow (Z n x)) r) (n : ℕ) :
    historyExpectation initial next prob n (fun x => rowMass (natRow (Z n x))) ≤
      (rho ^ n * rowDot (natRow (Z 0 initial)) r) / lo := by
  have hweighted := historyExpectation_iterate_le initial next prob hn rho hrho
    (fun n x => rowDot (natRow (Z n x)) r) hstep n
  have hbelow : lo * historyExpectation initial next prob n
      (fun x => rowMass (natRow (Z n x))) ≤
        historyExpectation initial next prob n (fun x => rowDot (natRow (Z n x)) r) := by
    rw [← historyExpectation_const_mul]
    apply historyExpectation_mono initial next prob hn n
    intro x
    simp only [rowMass, rowDot, natRow, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have h := mul_le_mul_of_nonneg_left (hl i)
      (Nat.cast_nonneg (Z n x i) : (0 : ℝ) ≤ Z n x i)
    simpa [mul_comm] using h
  apply (le_div_iff₀ hlo).2
  nlinarith [hbelow, hweighted]

/-- For the actual attaining program, the expected population is trapped
between explicit constant multiples of the same spectral exponential.  Positive
constants require a nonzero initial population, separately verified by source. -/
theorem history_population_bounds (initial : H 0)
    (next : ∀ n x, O n x → H (n + 1)) (prob : ∀ n x, O n x → ℝ)
    (hn : ∀ n x u, 0 ≤ prob n x u) (rho : ℝ) (hrho : 0 ≤ rho)
    (r : I → ℝ) (lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 < hi)
    (hl : ∀ i, lo ≤ r i) (hu : ∀ i, r i ≤ hi)
    (Z : ∀ n, H n → I → ℕ)
    (hstep : ∀ n x,
      (∑ u, prob n x u * rowDot (natRow (Z (n + 1) (next n x u))) r) =
        rho * rowDot (natRow (Z n x)) r) (n : ℕ) :
    (rho ^ n * rowDot (natRow (Z 0 initial)) r) / hi ≤
      historyExpectation initial next prob n (fun x => rowMass (natRow (Z n x))) ∧
    historyExpectation initial next prob n (fun x => rowMass (natRow (Z n x))) ≤
      (rho ^ n * rowDot (natRow (Z 0 initial)) r) / lo := by
  constructor
  · have heq := historyExpectation_iterate_eq initial next prob rho
      (fun n x => rowDot (natRow (Z n x)) r) hstep n
    have habove : historyExpectation initial next prob n
        (fun x => rowDot (natRow (Z n x)) r) ≤
          hi * historyExpectation initial next prob n
            (fun x => rowMass (natRow (Z n x))) := by
      rw [← historyExpectation_const_mul]
      apply historyExpectation_mono initial next prob hn n
      intro x
      exact (count_value_bounds (Z n x) r lo hi hl hu).2
    apply (div_le_iff₀ hhi).2
    nlinarith [heq, habove]
  · exact history_population_upper initial next prob hn rho hrho r lo hlo hl Z
      (fun n x => (hstep n x).le) n

end FiniteHistory

/-! ## Consumer of the same paid, damaged, inherited physical source

The continuing row matrix below is defined by the finite sum of actual event
counts.  Its positivity, primitive certificates, optimal program, and the
conditional potential bound are all proved here from `Parameters.Valid`.
The full request menu retains stop and the actual rejected identity transition.
-/

namespace SourceConsumer
open CoreRegenerativeSource

def ContinueAction (i : Kind) :=
  {a : Action // a = .care ∨ (i = false ∧ a = .bloom)}

instance (i : Kind) : Fintype (ContinueAction i) := by
  unfold ContinueAction
  infer_instance

instance (i : Kind) : Nonempty (ContinueAction i) :=
  ⟨⟨.care, Or.inl rfl⟩⟩

def sourceRows (p : Parameters) (i : Kind) (a : ContinueAction i) (j : Kind) : ℝ :=
  eventMean p a.val j

/-- The selector is exactly the H-bloom/D-care code of the actual true program. -/
def bestSelector : Selector ContinueAction
  | false => ⟨.bloom, Or.inr ⟨rfl, rfl⟩⟩
  | true => ⟨.care, Or.inl rfl⟩

@[simp] theorem bestSelector_program (i : Kind) :
    (bestSelector i).val = programAction true i := by cases i <;> rfl

theorem damageWeight_pos (p : Parameters) (hp : Valid p) (j : Kind) :
    0 < damageWeight p j := by
  cases j <;> simp [damageWeight] <;> linarith [hp.damage_pos, hp.damage_lt_one]

theorem careRate_pos (p : Parameters) (hp : Valid p) : 0 < countRate p .care := by
  simp only [countRate, survivalRate, birthRate]
  linarith [hp.supercritical]

theorem careRate_le_bloomRate (p : Parameters) (hp : Valid p) :
    countRate p .care ≤ countRate p .bloom := by
  simp only [countRate, survivalRate, birthRate]
  linarith [hp.advantage]

theorem sourceRows_pos (p : Parameters) (hp : Valid p)
    (i : Kind) (a : ContinueAction i) (j : Kind) : 0 < sourceRows p i a j := by
  simp only [sourceRows, eventMean_eq_row, row]
  apply mul_pos _ (damageWeight_pos p hp j)
  rcases a.property with ha | ⟨_, ha⟩
  · rw [ha]
    exact careRate_pos p hp
  · rw [ha]
    exact lt_of_lt_of_le (careRate_pos p hp) (careRate_le_bloomRate p hp)

/-- Every actual continuing selector has a strictly positive first power. -/
theorem source_primitive (p : Parameters) (hp : Valid p) (π : Selector ContinueAction) :
    Matrix.IsPrimitive (selectedMatrix (sourceRows p) π) := by
  refine ⟨fun i j => (sourceRows_pos p hp i (π i) j).le, 1, by norm_num, ?_⟩
  intro i j
  simpa [selectedMatrix] using sourceRows_pos p hp i (π i) j

theorem bestRow_domination (p : Parameters) (hp : Valid p)
    (i : Kind) (a : ContinueAction i) (j : Kind) :
    sourceRows p i a j ≤ sourceRows p i (bestSelector i) j := by
  rcases a.property with ha | ⟨hi, ha⟩
  · cases i
    · simpa [sourceRows, eventMean_eq_row, bestSelector, ha, row] using
        mul_le_mul_of_nonneg_right (careRate_le_bloomRate p hp)
          (damageWeight_pos p hp j).le
    · simp [sourceRows, bestSelector, ha]
  · cases i
    · simp [sourceRows, bestSelector, ha]
    · cases hi

/-- The existing finite-max theorem is applied to actual event-derived rows. -/
theorem source_finite_optimizer_exists (p : Parameters) (hp : Valid p) :
    ∃ π : Selector ContinueAction,
      (∀ σ : Selector ContinueAction,
        (selectedPerron (sourceRows p) (source_primitive p hp) σ).R ≤
          (selectedPerron (sourceRows p) (source_primitive p hp) π).R) ∧
      ∀ i (a : ContinueAction i),
        (∑ j, sourceRows p i a j *
          (selectedPerron (sourceRows p) (source_primitive p hp) π).r j) ≤
          (selectedPerron (sourceRows p) (source_primitive p hp) π).R *
            (selectedPerron (sourceRows p) (source_primitive p hp) π).r i :=
  exists_optimal_selector (sourceRows p) (source_primitive p hp)

/-- The actual source has an explicitly encoded maximizer, not just a choice. -/
theorem source_best_maximal (p : Parameters) (hp : Valid p) :
    ∀ σ : Selector ContinueAction,
      (selectedPerron (sourceRows p) (source_primitive p hp) σ).R ≤
        (selectedPerron (sourceRows p) (source_primitive p hp) bestSelector).R :=
  selector_maximal_of_rowwise_domination (sourceRows p) (source_primitive p hp)
    bestSelector (bestRow_domination p hp)

/-- This consumer also uses the general single-row replacement conclusion. -/
theorem source_best_bellman (p : Parameters) (hp : Valid p)
    (i : Kind) (a : ContinueAction i) :
    (∑ j, sourceRows p i a j *
      (selectedPerron (sourceRows p) (source_primitive p hp) bestSelector).r j) ≤
      (selectedPerron (sourceRows p) (source_primitive p hp) bestSelector).R *
        (selectedPerron (sourceRows p) (source_primitive p hp) bestSelector).r i :=
  maximal_selector_row_bound (sourceRows p) (source_primitive p hp) bestSelector
    (source_best_maximal p hp) i a

def sourceValue (p : Parameters) (i : Kind) : ℝ :=
  countRate p (programAction true i)

theorem sourceValue_pos (p : Parameters) (hp : Valid p) (i : Kind) :
    0 < sourceValue p i := by
  cases i
  · exact lt_of_lt_of_le (careRate_pos p hp) (careRate_le_bloomRate p hp)
  · exact careRate_pos p hp

theorem sourceValue_bounds (p : Parameters) (hp : Valid p) (i : Kind) :
    countRate p .care ≤ sourceValue p i ∧ sourceValue p i ≤ countRate p .bloom := by
  cases i
  · exact ⟨careRate_le_bloomRate p hp, le_rfl⟩
  · exact ⟨le_rfl, careRate_le_bloomRate p hp⟩

theorem sourceRate_gt_one (p : Parameters) (hp : Valid p) : 1 < growthRate p true := by
  have he : growthRate p true = p.survival + p.commonBirth +
      (1 - p.damage) * (p.bloomOnly - p.careOnly) := by
    simp [growthRate, programAction, countRate, survivalRate, birthRate]
    ring
  rw [he]
  have hprod := mul_pos (sub_pos.mpr hp.damage_lt_one) (sub_pos.mpr hp.advantage)
  linarith [hp.supercritical]

theorem row_sourceValue (p : Parameters) (a : Action) :
    (∑ j, row p a j * sourceValue p j) = countRate p a * growthRate p true := by
  simp [row, sourceValue, programAction, growthRate, damageWeight]
  ring

theorem sourceValue_eigen (p : Parameters) (i : Kind) :
    (∑ j, selectedMatrix (sourceRows p) bestSelector i j * sourceValue p j) =
      growthRate p true * sourceValue p i := by
  simp only [selectedMatrix, sourceRows, eventMean_eq_row, bestSelector_program]
  rw [row_sourceValue]
  exact mul_comm _ _

/-- The directly calculated source value is the positive Perron ray of the
same factory matrix; both root and eigenvector claims are conclusions. -/
theorem sourceValue_actual_perron (p : Parameters) (hp : Valid p) :
    growthRate p true =
      (selectedPerron (sourceRows p) (source_primitive p hp) bestSelector).R ∧
    ∃ c : ℝ, 0 < c ∧ ∀ i, sourceValue p i =
      c * (selectedPerron (sourceRows p) (source_primitive p hp) bestSelector).r i :=
  (selectedPerron (sourceRows p) (source_primitive p hp) bestSelector).positive_right_eigen_unique
      (growthRate p true) (sourceValue p)
      (sourceValue_pos p hp) (sourceValue_eigen p)

/-- Every raw request is included.  D-bloom is the actual rejected identity
transition; supercriticality, rather than removal of this request, bounds it. -/
theorem actual_row_bound (p : Parameters) (hp : Valid p) (i : Kind) (a : Action) :
    (∑ j, realizedRow p i a j * sourceValue p j) ≤
      growthRate p true * sourceValue p i := by
  have hr : 0 < growthRate p true := lt_trans zero_lt_one (sourceRate_gt_one p hp)
  cases i with
  | false =>
    cases a with
    | care =>
      have he : (∑ j, realizedRow p false .care j * sourceValue p j) =
          countRate p .care * growthRate p true := by
        simpa [realizedRow] using row_sourceValue p .care
      rw [he]
      change countRate p .care * growthRate p true ≤
        growthRate p true * countRate p .bloom
      calc
        _ ≤ countRate p .bloom * growthRate p true :=
          mul_le_mul_of_nonneg_right (careRate_le_bloomRate p hp) hr.le
        _ = _ := mul_comm _ _
    | bloom =>
      have he : (∑ j, realizedRow p false .bloom j * sourceValue p j) =
          countRate p .bloom * growthRate p true := by
        simpa [realizedRow] using row_sourceValue p .bloom
      rw [he]
      exact le_of_eq (mul_comm _ _)
    | stop =>
      have he : (∑ j, realizedRow p false .stop j * sourceValue p j) = 0 := by
        simp [realizedRow, row, countRate, survivalRate, birthRate]
      rw [he]
      exact mul_nonneg hr.le (sourceValue_pos p hp false).le
  | true =>
    cases a with
    | care =>
      have he : (∑ j, realizedRow p true .care j * sourceValue p j) =
          countRate p .care * growthRate p true := by
        simpa [realizedRow] using row_sourceValue p .care
      rw [he]
      exact le_of_eq (mul_comm _ _)
    | bloom =>
      have he : (∑ j, realizedRow p true .bloom j * sourceValue p j) =
          sourceValue p true := by simp [realizedRow]
      rw [he]
      have hh := mul_le_mul_of_nonneg_right (sourceRate_gt_one p hp).le
        (sourceValue_pos p hp true).le
      simpa using hh
    | stop =>
      have he : (∑ j, realizedRow p true .stop j * sourceValue p j) = 0 := by
        simp [realizedRow, row, countRate, survivalRate, birthRate]
      rw [he]
      exact mul_nonneg hr.le (sourceValue_pos p hp true).le

/-- This inequality is obtained by summing the actual paid `step` records. -/
theorem actual_one_step_value_le (p : Parameters) (hp : Valid p)
    (theta i tag : Bool) (a : Action) :
    (∑ z : Noise, noiseWeight p z *
      (∑ j, (resultCount (step (programBody theta i tag) a z) j : ℝ) * sourceValue p j)) ≤
        growthRate p true * sourceValue p i := by
  calc
    _ = ∑ j, realizedMean p theta i tag a j * sourceValue p j :=
      record_value_eq_row_value (noiseWeight p)
        (fun z j => resultCount (step (programBody theta i tag) a z) j) (sourceValue p)
    _ = ∑ j, realizedRow p i a j * sourceValue p j := by simp_rw [realizedMean_eq]
    _ ≤ _ := actual_row_bound p hp i a

/-- The same actual raw-executing program attains the conditional equality. -/
theorem actual_program_one_step_value_eq (p : Parameters) (i tag : Bool) :
    (∑ z : Noise, noiseWeight p z *
      (∑ j, (resultCount (programStep (programBody true i tag) z) j : ℝ) * sourceValue p j)) =
        growthRate p true * sourceValue p i := by
  simp only [programStep_eq_step, requestOf_programBody]
  calc
    _ = ∑ j, realizedMean p true i tag (programAction true i) j * sourceValue p j :=
      record_value_eq_row_value (noiseWeight p)
        (fun z j => resultCount (step (programBody true i tag) (programAction true i) z) j)
        (sourceValue p)
    _ = ∑ j, row p (programAction true i) j * sourceValue p j := by
      simp_rw [program_realizedMean, programRow]
    _ = _ := by rw [row_sourceValue]; exact mul_comm _ _

/-- Any real action kernel based on the permitted past is covered.  Its fresh
private action draw and the source's current world atom remain independent. -/
theorem actual_mixed_request_value_le (p : Parameters) (hp : Valid p)
    (theta i tag : Bool) (mix : Action → ℝ)
    (hn : ∀ a, 0 ≤ mix a) (hs : ∑ a, mix a = 1) :
    (∑ a, mix a * (∑ z : Noise, noiseWeight p z *
      (∑ j, (resultCount (step (programBody theta i tag) a z) j : ℝ) * sourceValue p j))) ≤
        growthRate p true * sourceValue p i := by
  calc
    _ ≤ ∑ a, mix a * (growthRate p true * sourceValue p i) := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left (actual_one_step_value_le p hp theta i tag a) (hn a)
    _ = _ := by rw [← Finset.sum_mul, hs, one_mul]

/-- The original rejected transaction is a genuine subcritical obstruction. -/
noncomputable def subcriticalParameters : Parameters := ⟨1/2, 1/8, 1/4, 1/4, 1/3⟩

theorem rejection_subcritical_counterexample :
    growthRate subcriticalParameters true = 5/6 ∧
    ∀ theta tag z,
      (step (programBody theta true tag) .bloom z).retained =
        some (programBody theta true tag) ∧
      (step (programBody theta true tag) .bloom z).newborn = none := by
  constructor
  · norm_num [growthRate, programAction, countRate, survivalRate, birthRate,
      subcriticalParameters]
  · intro theta tag z
    simp [step, damaged_bloom_rejected]

end SourceConsumer

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteSourceGrowthControl
