import UEOT.V3.Compression.WeightedQuotientGauge

/-!
# Moving encoder gauge closure

For a finite source with one fixed full-support law, occupation-weighted gauge
convergence is discrete: once the gauge mismatch falls below the least positive
source mass, it must already be zero.  Therefore a sequence of surjective
encoders whose weighted gauge mismatch tends to zero eventually has exactly the
same source fibres as the reference encoder.

This is a representation-level exactification theorem.  It does not yet infer
reward/transition/value convergence.
-/

namespace UEOT.V3.Compression.MovingEncoderGaugeClosure

open Filter Topology Function
open UEOT.V3.Compression.WeightedQuotientGauge
open UEOT.V3.Compression.QuotientGauge

universe uX uS

noncomputable section

variable {X : Type uX} {S : Type uS}
variable [Fintype X] [Nonempty X] [Fintype S]

/-- The finite set of source masses. -/
def sourceMasses (mu : stdSimplex ℝ X) : Finset ℝ := by
  classical
  exact Finset.univ.image (fun x => mu x)

theorem sourceMasses_nonempty (mu : stdSimplex ℝ X) :
    (sourceMasses mu).Nonempty := by
  classical
  let x : X := Classical.choice inferInstance
  exact ⟨mu x, by simp [sourceMasses]⟩

/-- Least source mass under one finite occupation law. -/
def minSourceMass (mu : stdSimplex ℝ X) : ℝ :=
  (sourceMasses mu).min' (sourceMasses_nonempty mu)

theorem minSourceMass_mem (mu : stdSimplex ℝ X) :
    minSourceMass mu ∈ sourceMasses mu :=
  Finset.min'_mem _ (sourceMasses_nonempty mu)

theorem minSourceMass_le (mu : stdSimplex ℝ X) (x : X) :
    minSourceMass mu ≤ mu x := by
  classical
  apply Finset.min'_le
  simp [sourceMasses]

theorem minSourceMass_pos
    (mu : stdSimplex ℝ X)
    (hfull : ∀ x, 0 < mu x) :
    0 < minSourceMass mu := by
  classical
  have hmem := minSourceMass_mem mu
  rcases Finset.mem_image.mp hmem with ⟨x, _, hx⟩
  simpa [hx] using hfull x

/-- One explicit mismatched positive-mass source point already costs at least
the minimum source mass. -/
theorem minSourceMass_le_weightedMismatch_of_mismatch
    (mu : stdSimplex ℝ X)
    (q r : X → S) (e : S ≃ S)
    (x : X) (hne : e (q x) ≠ r x) :
    minSourceMass mu ≤ weightedMismatch mu q r e := by
  classical
  have hxmin : minSourceMass mu ≤ mu x := minSourceMass_le mu x
  have hxmem : x ∈ Finset.univ.filter (fun y => e (q y) ≠ r y) := by
    simp [hne]
  have hxsum :
      mu x ≤ ∑ y ∈ Finset.univ.filter (fun y => e (q y) ≠ r y), mu y :=
    Finset.single_le_sum
      (fun y _ => stdSimplex.zero_le mu y) hxmem
  exact hxmin.trans (by simpa [weightedMismatch] using hxsum)

/-- Under full support, any nonzero optimal weighted gauge cost is bounded
below by the least source mass. -/
theorem minSourceMass_le_weightedGaugeMismatch_of_ne_zero
    (mu : stdSimplex ℝ X)
    (q r : X → S)
    (hneq : weightedGaugeMismatch mu q r ≠ 0) :
    minSourceMass mu ≤ weightedGaugeMismatch mu q r := by
  classical
  rcases exists_optimalEquiv_weighted mu q r with ⟨e, he⟩
  have hcostneq : weightedMismatch mu q r e ≠ 0 := by
    intro hzero
    apply hneq
    rw [← he, hzero]
  have hnotalign : ¬ ∀ x, 0 < mu x → e (q x) = r x := by
    intro halign
    exact hcostneq <|
      (weightedMismatch_eq_zero_iff_supportAligned mu q r e).2 halign
  push_neg at hnotalign
  rcases hnotalign with ⟨x, _, hne⟩
  rw [← he]
  exact minSourceMass_le_weightedMismatch_of_mismatch mu q r e x hne

/-- Falling strictly below the smallest positive source mass forces exact zero
weighted gauge mismatch. -/
theorem weightedGaugeMismatch_eq_zero_of_lt_minSourceMass
    (mu : stdSimplex ℝ X)
    (q r : X → S)
    (hlt : weightedGaugeMismatch mu q r < minSourceMass mu) :
    weightedGaugeMismatch mu q r = 0 := by
  by_contra hneq
  have hle := minSourceMass_le_weightedGaugeMismatch_of_ne_zero
    mu q r hneq
  linarith

/-- Main moving-encoder exactification theorem.

For finite full-support source law `mu`, a sequence of surjective encoders with
weighted gauge mismatch converging to zero eventually induces exactly the same
source fibres as the fixed reference encoder. -/
theorem eventually_sameFibers_of_weightedGaugeMismatch_tendsto_zero
    (mu : stdSimplex ℝ X)
    (hfull : ∀ x, 0 < mu x)
    (Cref : X → S) (href : Surjective Cref)
    (Cseq : ℕ → X → S)
    (hseq_surj : ∀ n, Surjective (Cseq n))
    (hconv :
      Tendsto
        (fun n => weightedGaugeMismatch mu (Cseq n) Cref)
        atTop (𝓝 0)) :
    ∀ᶠ n in atTop, SameFibers (Cseq n) Cref := by
  have hminpos : 0 < minSourceMass mu := minSourceMass_pos mu hfull
  have hsmall :
      ∀ᶠ n in atTop,
        weightedGaugeMismatch mu (Cseq n) Cref < minSourceMass mu :=
    (tendsto_order.1 hconv).2 (minSourceMass mu) hminpos
  filter_upwards [hsmall] with n hn
  have hzero := weightedGaugeMismatch_eq_zero_of_lt_minSourceMass
    mu (Cseq n) Cref hn
  exact (weightedGaugeMismatch_eq_zero_iff_sameFibers_of_fullSupport
    mu hfull (Cseq n) Cref (hseq_surj n) href).1 hzero

/-- Concrete eventual-index form of the moving-encoder closure theorem. -/
theorem exists_eventual_exact_gauge_lock
    (mu : stdSimplex ℝ X)
    (hfull : ∀ x, 0 < mu x)
    (Cref : X → S) (href : Surjective Cref)
    (Cseq : ℕ → X → S)
    (hseq_surj : ∀ n, Surjective (Cseq n))
    (hconv :
      Tendsto
        (fun n => weightedGaugeMismatch mu (Cseq n) Cref)
        atTop (𝓝 0)) :
    ∃ N, ∀ n ≥ N, SameFibers (Cseq n) Cref := by
  exact Filter.eventually_atTop.mp
    (eventually_sameFibers_of_weightedGaugeMismatch_tendsto_zero
      mu hfull Cref href Cseq hseq_surj hconv)

end

end UEOT.V3.Compression.MovingEncoderGaugeClosure
