import UEOT.V3.InformationPacking
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic.FieldSimp

/-!
# P-INFO-05 entropy layer — finite Shannon entropy

This module uses the standard Shannon summand `Real.negMulLog p = -p log p`
already provided by Mathlib.  It first proves that a uniform law on a finite
nonempty support has entropy `log N`.  The packing lane then connects its
injectivity theorem to this entropy identity.
-/

namespace UEOT.V3.InformationEntropy

open MeasureTheory
open UEOT.V3.TotalVariation
open scoped ENNReal
open PMF

universe uα

/-- Shannon entropy of real probability weights on a designated finite
support.  The source application supplies an actual finite-support PMF, so no
normalization assumption is baked into the definition. -/
noncomputable def finiteShannonEntropy {α : Type uα}
    (F : Finset α) (p : α → ℝ) : ℝ :=
  ∑ x ∈ F, Real.negMulLog (p x)

/-- PMF form of finite-support Shannon entropy. -/
noncomputable def pmfEntropyOn {α : Type uα}
    (q : PMF α) (F : Finset α) : ℝ :=
  finiteShannonEntropy F (fun x => (q x).toReal)

theorem finiteShannonEntropy_uniformWeights
    {α : Type uα} (F : Finset α) (hF : F.Nonempty) :
    finiteShannonEntropy F (fun _ => (F.card : ℝ)⁻¹) =
      Real.log (F.card : ℝ) := by
  have hn : (F.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hF)
  simp only [finiteShannonEntropy, Finset.sum_const, nsmul_eq_mul]
  simp [Real.negMulLog, Real.log_inv, hn]

/-- Mathlib's `uniformOfFinset` realizes exactly the uniform weights used by
the previous theorem. -/
theorem pmfEntropyOn_uniformOfFinset
    {α : Type uα} (F : Finset α) (hF : F.Nonempty) :
    pmfEntropyOn (PMF.uniformOfFinset F hF) F =
      Real.log (F.card : ℝ) := by
  unfold pmfEntropyOn finiteShannonEntropy
  calc
    (∑ x ∈ F, Real.negMulLog ((PMF.uniformOfFinset F hF x).toReal)) =
        ∑ x ∈ F, Real.negMulLog ((F.card : ℝ)⁻¹) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [PMF.uniformOfFinset_apply_of_mem hF hx]
      simp
    _ = Real.log (F.card : ℝ) := by
      simpa [finiteShannonEntropy] using
        finiteShannonEntropy_uniformWeights F hF


/-- Standard Shannon entropy of a discrete PMF, written as a `tsum`.  For the
finite-support laws used in P-INFO-05 the sum reduces to the support finset. -/
noncomputable def pmfShannonEntropy {α : Type uα} (q : PMF α) : ℝ :=
  ∑' x, Real.negMulLog (q x).toReal

theorem pmfShannonEntropy_uniformOfFinset
    {α : Type uα} (F : Finset α) (hF : F.Nonempty) :
    pmfShannonEntropy (PMF.uniformOfFinset F hF) =
      Real.log (F.card : ℝ) := by
  unfold pmfShannonEntropy
  rw [tsum_eq_sum (s := F)]
  · simpa [pmfEntropyOn, finiteShannonEntropy] using
      pmfEntropyOn_uniformOfFinset F hF
  · intro x hx
    rw [PMF.uniformOfFinset_apply_of_notMem hF hx]
    simp

/-- An injective deterministic readout preserves the uniform law as a uniform
law on its finite image, hence preserves the `log N` entropy exactly. -/
theorem pmfShannonEntropy_map_uniform_injOn
    {α : Type uα} {β : Type*}
    (F : Finset α) (hF : F.Nonempty)
    (R : α → β) (hinj : Set.InjOn R (F : Set α)) :
    pmfShannonEntropy ((PMF.uniformOfFinset F hF).map R) =
      Real.log (F.card : ℝ) := by
  classical
  let G : Finset β := F.image R
  have hG : G.Nonempty := by
    simpa [G] using hF.image R
  have hcard : G.card = F.card := by
    simpa [G] using Finset.card_image_of_injOn hinj
  have hmap :
      (PMF.uniformOfFinset F hF).map R =
        PMF.uniformOfFinset G hG := by
    ext y
    by_cases hy : y ∈ G
    · obtain ⟨x, hxF, hxy⟩ := by
        simpa [G] using (Finset.mem_image.mp hy)
      subst y
      rw [PMF.uniformOfFinset_apply_of_mem hG hy]
      rw [PMF.map_apply]
      rw [tsum_eq_single x]
      · rw [PMF.uniformOfFinset_apply_of_mem hF hxF]
        simp [hcard]
      · intro z hzx
        by_cases hzF : z ∈ F
        · have hne : R x ≠ R z := by
            intro heq
            exact hzx (hinj hxF hzF heq).symm
          simp [hne]
        · simp [PMF.uniformOfFinset_apply_of_notMem hF hzF]
    · rw [PMF.uniformOfFinset_apply_of_notMem hG hy]
      rw [PMF.map_apply]
      rw [ENNReal.tsum_eq_zero]
      intro x
      by_cases hxF : x ∈ F
      · have hne : y ≠ R x := by
          intro heq
          apply hy
          subst y
          exact Finset.mem_image.mpr ⟨x, hxF, rfl⟩
        simp [hne]
      · simp [PMF.uniformOfFinset_apply_of_notMem hF hxF]
  rw [hmap, pmfShannonEntropy_uniformOfFinset G hG, hcard]

/-- The entropy clause of P-INFO-05: the TV packing hypotheses force the
deterministic representation to be injective on the packed histories, and a
uniform input on those histories therefore has representation entropy
`log N` (hence in particular at least `log N`). -/
theorem p_info_05_uniform_entropy
    {H : Type*} {S : Type*} {Y : Type*} [MeasurableSpace Y]
    (K : H → Measure Y) (R : H → S) (decode : S → Measure Y)
    (hK : ∀ h, IsProbabilityMeasure (K h))
    (hdecode : ∀ s, IsProbabilityMeasure (decode s))
    (F : Finset H) (hF : F.Nonempty) (ε : ℝ)
    (hsep : ∀ ⦃h₁⦄, h₁ ∈ F → ∀ ⦃h₂⦄, h₂ ∈ F →
      h₁ ≠ h₂ → 2 * ε < tvDist (K h₁) (K h₂))
    (herr : ∀ h ∈ F, tvDist (K h) (decode (R h)) ≤ ε) :
    pmfShannonEntropy ((PMF.uniformOfFinset F hF).map R) =
      Real.log (F.card : ℝ) := by
  apply pmfShannonEntropy_map_uniform_injOn F hF R
  exact InformationPacking.packing_forces_injective
    K R decode hK hdecode (A := (F : Set H)) ε
    (by simpa using hsep) (by simpa using herr)

end UEOT.V3.InformationEntropy
