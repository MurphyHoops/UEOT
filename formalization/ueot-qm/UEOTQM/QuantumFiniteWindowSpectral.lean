import UEOTQM.QuantumFiniteWindow
import UEOTQM.QuantumTraceDistance

/-!
# Canonical singular-support factory for finite-window conditioning

This module constructs support factors from every actual finite PSD matrix and
derives the local kernel relation from the original backward Gram equation.
No strict-positivity or full-rank premise is used.
-/

namespace UEOTQM.QuantumFiniteWindow

open Matrix QuantumTraceDistance
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

variable {ι O κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype O] [Fintype κ]

/-- The actual finite spectral square root, its zero-on-kernel reciprocal,
and its support projection. -/
def spectralFilter (H : Operator ι) (hH : H.PosSemidef) : SupportFilter ι := by
  classical
  let U := hH.isHermitian.eigenvectorUnitary
  let d : ι → ℝ := fun i => Real.sqrt (hH.isHermitian.eigenvalues i)
  let p : ι → ℝ := fun i => if d i = 0 then 0 else 1
  refine {
    matrix := unitaryDiagonal U d
    inverse := unitaryDiagonal U (fun i => (d i)⁻¹)
    projection := unitaryDiagonal U p
    inverse_mul := ?_
    mul_inverse := ?_
    projection_adjoint := ?_
    projection_sq := ?_
    projection_mul := ?_ }
  · rw [unitaryDiagonal_mul]
    congr 1
    funext i
    by_cases hi : d i = 0 <;> simp [p, hi]
  · rw [unitaryDiagonal_mul]
    congr 1
    funext i
    by_cases hi : d i = 0 <;> simp [p, hi]
  · exact (unitaryDiagonal_posSemidef U p (fun i => by
      dsimp [p]
      split_ifs <;> norm_num)).isHermitian.eq
  · rw [unitaryDiagonal_mul]
    congr 1
    funext i
    dsimp [p]
    split_ifs <;> norm_num
  · rw [unitaryDiagonal_mul]
    congr 1
    funext i
    by_cases hi : d i = 0 <;> simp [p, hi]

theorem spectralFilter_matrix_posSemidef (H : Operator ι) (hH : H.PosSemidef) :
    (spectralFilter H hH).matrix.PosSemidef := by
  change (unitaryDiagonal hH.isHermitian.eigenvectorUnitary
    (fun i => Real.sqrt (hH.isHermitian.eigenvalues i))).PosSemidef
  exact unitaryDiagonal_posSemidef _ _ (fun i => Real.sqrt_nonneg _)

/-- The factory factor has exactly the input PSD operator as its Gram matrix. -/
theorem spectralFilter_metric (H : Operator ι) (hH : H.PosSemidef) :
    (spectralFilter H hH).metric = H := by
  unfold SupportFilter.metric
  rw [(spectralFilter_matrix_posSemidef H hH).isHermitian.eq]
  change unitaryDiagonal hH.isHermitian.eigenvectorUnitary
      (fun i => Real.sqrt (hH.isHermitian.eigenvalues i)) *
    unitaryDiagonal hH.isHermitian.eigenvectorUnitary
      (fun i => Real.sqrt (hH.isHermitian.eigenvalues i)) = H
  rw [unitaryDiagonal_mul]
  have hd : (fun i => Real.sqrt (hH.isHermitian.eigenvalues i) *
      Real.sqrt (hH.isHermitian.eigenvalues i)) = hH.isHermitian.eigenvalues := by
    funext i
    rw [← pow_two, Real.sq_sqrt (hH.eigenvalues_nonneg i)]
  rw [hd]
  simpa only [unitaryDiagonal, RCLike.ofReal_eq_complex_ofReal, Function.comp_def]
    using hH.isHermitian.spectral_theorem.symm

namespace SupportFilter

theorem matrix_projection (F : SupportFilter ι) : F.matrix * F.projection = F.matrix := by
  rw [← F.inverse_mul, ← Matrix.mul_assoc, F.mul_inverse, F.projection_mul]

theorem matrix_complement (F : SupportFilter ι) : F.matrix * F.complement = 0 := by
  simp [complement, mul_sub, F.matrix_projection]

end SupportFilter

/-- A finite sum of positive Gram matrices can be zero only if every original
matrix is zero. This is a theorem, not a new certificate premise. -/
theorem gram_sum_zero_component {B : Type*} [Fintype B]
    (A : B → Operator ι) (hs : (∑ b, (A b)ᴴ * A b) = 0) (b : B) : A b = 0 := by
  have hn : ∀ q, 0 ≤ mass ((A q)ᴴ * A q) :=
    fun q => mass_nonneg (Matrix.posSemidef_conjTranspose_mul_self (A q))
  have hsum : (∑ q, mass ((A q)ᴴ * A q)) = 0 := by
    simp only [mass]
    rw [← Complex.re_sum, ← Matrix.trace_sum, hs]
    simp
  have hz : mass ((A b)ᴴ * A b) = 0 := by
    apply le_antisymm _ (hn b)
    calc
      mass ((A b)ᴴ * A b) ≤ ∑ q, mass ((A q)ᴴ * A q) :=
        Finset.single_le_sum (fun q _ => hn q) (Finset.mem_univ b)
      _ = 0 := hsum
  have ht : ((A b)ᴴ * A b).trace = 0 := by
    apply Complex.ext
    · exact hz
    · exact trace_im_eq_zero (Matrix.posSemidef_conjTranspose_mul_self (A b))
  exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp ht

/-- The local support relation follows from the backward Gram identity alone.
In particular singular branches need no unjustified inverse cancellation. -/
theorem support_of_backward (F : SupportFilter ι) (G : O → SupportFilter ι)
    (I : Instrument ι O κ)
    (hb : (∑ o, ∑ k, (I.kraus o k)ᴴ * (G o).metric * I.kraus o k) = F.metric)
    (o : O) (k : κ) :
    (G o).matrix * I.kraus o k * F.projection = (G o).matrix * I.kraus o k := by
  let A : O × κ → Operator ι := fun q =>
    (G q.1).matrix * I.kraus q.1 q.2 * F.complement
  have hs : (∑ q, (A q)ᴴ * A q) = 0 := by
    calc
      _ = F.complementᴴ *
          (∑ o, ∑ k, (I.kraus o k)ᴴ * (G o).metric * I.kraus o k) *
          F.complement := by
        simp only [A, Fintype.sum_prod_type, SupportFilter.metric,
          Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_sum, Matrix.sum_mul]
      _ = (F.matrix * F.complement)ᴴ * (F.matrix * F.complement) := by
        rw [hb]
        simp only [SupportFilter.metric, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 0 := by rw [F.matrix_complement]; simp
  have hz := gram_sum_zero_component A hs (o, k)
  change (G o).matrix * I.kraus o k * (1 - F.projection) = 0 at hz
  rw [mul_sub, mul_one] at hz
  exact (sub_eq_zero.mp hz).symm

def StepCertificate.of_backward (F : SupportFilter ι) (G : O → SupportFilter ι)
    (I : Instrument ι O κ)
    (hb : (∑ o, ∑ k, (I.kraus o k)ᴴ * (G o).metric * I.kraus o k) = F.metric) :
    StepCertificate F G I where
  backward := hb
  support := support_of_backward F G I hb

/-- A raw finite tree, containing only original instruments and the original
accept/reject decisions at stopping leaves. -/
inductive SourceTree (ι O κ : Type*) [Fintype ι] [DecidableEq ι]
    [Fintype O] [Fintype κ] where
  | stop (accept : Bool) : SourceTree ι O κ
  | node (source : Instrument ι O κ) (next : O → SourceTree ι O κ) : SourceTree ι O κ

def backwardGram (I : Instrument ι O κ) (G : O → SupportFilter ι) : Operator ι :=
  ∑ o, ∑ k, (I.kraus o k)ᴴ * (G o).metric * I.kraus o k

theorem backwardGram_posSemidef (I : Instrument ι O κ) (G : O → SupportFilter ι) :
    (backwardGram I G).PosSemidef := by
  apply Matrix.posSemidef_sum Finset.univ
  intro o _
  apply Matrix.posSemidef_sum Finset.univ
  intro k _
  have hg := Matrix.posSemidef_conjTranspose_mul_self ((G o).matrix * I.kraus o k)
  simpa only [SupportFilter.metric, Matrix.conjTranspose_mul, Matrix.mul_assoc] using hg

namespace SourceTree

/-- Construct every internal support factor from the original backward sum.
This noncomputable finite spectral construction includes rank-deficient nodes. -/
def canonical : SourceTree ι O κ → FilterTree ι O κ
  | .stop b => .stop b
  | .node I next =>
      let children := fun o => canonical (next o)
      let G := fun o => (children o).rootFilter
      .node I (spectralFilter (backwardGram I G) (backwardGram_posSemidef I G)) children

theorem canonical_valid (P : SourceTree ι O κ) : P.canonical.Valid := by
  induction P with
  | stop b => trivial
  | node I next ih =>
    change (∀ o, (canonical (next o)).Valid) ∧ _
    refine ⟨ih, ?_⟩
    apply StepCertificate.of_backward
    exact (spectralFilter_metric _ _).symm

end SourceTree

namespace FilterTree

/-- Erase mathematical certificates, retaining every actual source action,
visible branch and accept/reject decision. -/
def erase : FilterTree ι O κ → SourceTree ι O κ
  | .stop b => .stop b
  | .node I _ next => .node I (fun o => erase (next o))

end FilterTree

/-- The spectral factory changes no source instrument, branch or terminal
decision. Its scientific source is the supplied raw finite tree. -/
theorem canonical_erases_to_source (P : SourceTree ι O κ) :
    P.canonical.erase = P := by
  induction P with
  | stop b => rfl
  | node I next ih =>
    change SourceTree.node I (fun o => (next o).canonical.erase) = SourceTree.node I next
    congr 1
    funext o
    exact ih o

/-- A source-only endpoint for a nontrivial tree: the original root instrument
itself supplies the arbitrary support-complement completion. The caller gives
only raw source instruments, acceptance decisions, an input state and a
positive ORIGINAL event mass; no spectral/support certificates or extra
fallback instrument are additional premises. -/
theorem source_node_conditional_joint
    (I : Instrument ι O κ) (next : O → SourceTree ι O κ) (ρ : Density ι)
    (hp : 0 < (SourceTree.node I next).canonical.successMass ρ.matrix) :
    let P := (SourceTree.node I next).canonical
    (FilterTree.jointState I P (SourceTree.canonical_valid (SourceTree.node I next))
      (FilterTree.initialState I P (SourceTree.canonical_valid (SourceTree.node I next))
        ρ hp)).matrix =
      (P.successMass ρ.matrix)⁻¹ • P.acceptedJointOperator ρ.matrix := by
  exact FilterTree.conditional_joint I (SourceTree.node I next).canonical
    (SourceTree.canonical_valid (SourceTree.node I next)) ρ hp

end

end UEOTQM.QuantumFiniteWindow
