import UEOT.V3.InformationCore
import UEOT.V3.InformationEventBernoulli
import UEOT.V3.InformationBernoulliFano
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Omega

/-!
# P-INFO-04 — sharp Fano lower bound via the error indicator

This is the source-facing route.  Let `J : Fin K` be uniform, let `Y` be an
observation, and let `d(Y)` be an arbitrary measurable decoder.  Push both the
true joint law and its independent-marginals reference through the measurable
correctness event `J = d(Y)`.

Under the true law the success probability is `1-e`; under the independent
reference it is exactly `1/K`.  KL data processing and the exact Bernoulli KL
identity then give

`I(J;Y) ≥ log K - h₂(e) - e log(K-1)`.

No MAP decoder, posterior kernel, conditional-entropy finiteness, or monotonicity
substitution is used.
-/

namespace UEOT.V3.InformationPInfo04

open MeasureTheory InformationTheory
open scoped ENNReal
open UEOT.V3.InformationCore
open UEOT.V3.InformationEventBernoulli
open UEOT.V3.InformationBernoulliFano

universe uY

variable {Y : Type uY} [MeasurableSpace Y]

/-- Uniform probability law on `Fin K`. -/
noncomputable def uniformIdentityLaw (K : ℕ) [NeZero K] : Measure (Fin K) :=
  (PMF.uniformOfFintype (Fin K)).toMeasure

instance uniformIdentityLaw_isProbability (K : ℕ) [NeZero K] :
    IsProbabilityMeasure (uniformIdentityLaw K) := by
  unfold uniformIdentityLaw
  infer_instance

/-- Correct-decoding event in the `(J,Y)` joint space. -/
def correctEvent {K : ℕ} (d : Y → Fin K) : Set (Fin K × Y) :=
  {z | z.1 = d z.2}

lemma measurableSet_correctEvent {K : ℕ}
    (d : Y → Fin K) (hd : Measurable d) :
    MeasurableSet (correctEvent d) := by
  unfold correctEvent
  exact measurableSet_eq_fun measurable_fst (hd.comp measurable_snd)

/-- Decoder error probability under the true joint law. -/
noncomputable def decoderError {K : ℕ}
    (ρ : Measure (Fin K × Y)) (d : Y → Fin K) : ℝ :=
  ρ.real (correctEvent d)ᶜ

lemma decoderError_nonneg {K : ℕ}
    (ρ : Measure (Fin K × Y)) (d : Y → Fin K) :
    0 ≤ decoderError ρ d := by
  exact measureReal_nonneg

lemma decoderError_le_one {K : ℕ}
    (ρ : Measure (Fin K × Y)) [IsProbabilityMeasure ρ]
    (d : Y → Fin K) :
    decoderError ρ d ≤ 1 := by
  exact measureReal_le_one

lemma correctProb_eq_one_sub_error {K : ℕ}
    (ρ : Measure (Fin K × Y)) [IsProbabilityMeasure ρ]
    (d : Y → Fin K) (hd : Measurable d) :
    ρ.real (correctEvent d) = 1 - decoderError ρ d := by
  have h := probReal_add_probReal_compl (μ := ρ) (measurableSet_correctEvent d hd)
  unfold decoderError
  linarith

lemma uniformIdentityLaw_singleton
    {K : ℕ} [NeZero K] (j : Fin K) :
    uniformIdentityLaw K {j} = (K : ℝ≥0∞)⁻¹ := by
  unfold uniformIdentityLaw
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton j)]
  simp [PMF.uniformOfFintype_apply, Fintype.card_fin]

/-- Under a product law with a uniform `Fin K` first coordinate, an arbitrary
measurable decoder agrees with the first coordinate with probability `1/K`. -/
theorem uniform_prod_correctProb
    {K : ℕ} [NeZero K]
    (ν : Measure Y) [IsProbabilityMeasure ν]
    (d : Y → Fin K) (hd : Measurable d) :
    ((uniformIdentityLaw K).prod ν).real (correctEvent d) = (K : ℝ)⁻¹ := by
  have hA : MeasurableSet (correctEvent d) := measurableSet_correctEvent d hd
  have hraw :
      ((uniformIdentityLaw K).prod ν) (correctEvent d) = (K : ℝ≥0∞)⁻¹ := by
    rw [Measure.prod_apply_symm hA]
    have hsection : ∀ y : Y,
        ((fun j : Fin K => (j, y)) ⁻¹' correctEvent d) = {d y} := by
      intro y
      ext j
      simp [correctEvent]
    simp_rw [hsection, uniformIdentityLaw_singleton]
    simp
  rw [measureReal_def, hraw]
  simp

/-- **P-INFO-04, sharp Fano bound.**  The identity prior is uniform over
`K ≥ 2` alternatives and `d` is any measurable decoder. -/
theorem p_info_04
    {K : ℕ} (hK : 2 ≤ K)
    (ρ : Measure (Fin K × Y)) [IsProbabilityMeasure ρ]
    (d : Y → Fin K) (hd : Measurable d)
    (hJ : ρ.fst = (uniformIdentityLaw K : Measure (Fin K))) :
    ENNReal.ofReal
        (Real.log (K : ℝ) - Real.binEntropy (decoderError ρ d) -
          decoderError ρ d * Real.log ((K : ℝ) - 1)) ≤
      mutualInfo ρ := by
  letI : NeZero K := ⟨by omega⟩
  let A : Set (Fin K × Y) := correctEvent d
  have hA : MeasurableSet A := by
    simpa [A] using measurableSet_correctEvent d hd
  have htrue : ρ.real A = 1 - decoderError ρ d := by
    simpa [A] using correctProb_eq_one_sub_error ρ d hd
  have href : (ρ.fst.prod ρ.snd).real A = (K : ℝ)⁻¹ := by
    rw [hJ]
    simpa [A] using uniform_prod_correctProb (K := K) ρ.snd d hd
  have he0 : 0 ≤ decoderError ρ d := decoderError_nonneg ρ d
  have he1 : decoderError ρ d ≤ 1 := decoderError_le_one ρ d
  have hdp := bernoulliKL_event_le ρ (ρ.fst.prod ρ.snd) A hA
  rw [htrue, href,
    bernoulli_correct_kl_eq_fano hK he0 he1] at hdp
  simpa [mutualInfo] using hdp

end UEOT.V3.InformationPInfo04
