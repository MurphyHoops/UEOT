import UEOT.V3.Compression.Objecthood.Homeostasis.CertifiedHomeostaticMargin

namespace UEOT.V3.Compression.Objecthood

open Filter MeasureTheory
open UEOT.V3.ViabilityKernel
open scoped BigOperators ENNReal

noncomputable section

def meanDamageAverage (p : ℕ → ℝ) (n : ℕ) : ℝ :=
  (((n + 1 : ℕ) : ℝ)⁻¹) * ∑ t ∈ Finset.range (n + 1), p t

/-- Mean homeostasis is an asymptotic Cesaro occupation certificate only. -/
def MeanHomeostasis (p : ℕ → ℝ) (rho : ℝ) : Prop :=
  ∀ eta > 0, ∀ᶠ n in atTop, meanDamageAverage p n ≤ rho + eta

/-- Almost every path visits the legitimate set arbitrarily late. -/
def PathwiseRecurrentLegitimacy
    {Z : Type*} [MeasurableSpace Z]
    (mu : Measure (ℕ → Z)) (L : Set Z) : Prop :=
  ∀ᵐ omega ∂mu, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ omega n ∈ L

/-- Almost every path is permanently legitimate after a finite random time. -/
def EventuallyAlwaysLegitimate
    {Z : Type*} [MeasurableSpace Z]
    (mu : Measure (ℕ → Z)) (L : Set Z) : Prop :=
  ∀ᵐ omega ∂mu, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → omega n ∈ L

theorem EventuallyAlwaysLegitimate.toPathwiseRecurrentLegitimacy
    {Z : Type*} [MeasurableSpace Z]
    {mu : Measure (ℕ → Z)} {L : Set Z}
    (h : EventuallyAlwaysLegitimate mu L) :
    PathwiseRecurrentLegitimacy mu L := by
  filter_upwards [h] with omega homega
  rcases homega with ⟨N0, hN0⟩
  intro N
  refine ⟨max N N0, le_max_left _ _, ?_⟩
  exact hN0 _ (le_max_right _ _)

noncomputable def damagedProbFromLaw
    {Z : Type*} [MeasurableSpace Z]
    (mu : Measure (ℕ → Z)) (L : Set Z) (n : ℕ) : ℝ :=
  mu.real {omega | omega n ∉ L}

/-- RH3's asymptotic occupation theorem is exactly a MeanHomeostasis
certificate and nothing stronger. -/
theorem RecurrentHomeostasisSystem.meanHomeostasis
    {Z : Type*} [Fintype Z]
    [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (S : RecurrentHomeostasisSystem Z)
    (C : FaultBurdenCertificate S)
    (mu0 : PMF Z) (hmu0 : StaysIn mu0 S.carrier)
    (hQ : ∀ z, z ∈ S.carrier →
      homeostaticENNExpectation (S.repairKernel z) S.potential +
          S.damagePenalty z ≤ S.potential z)
    (hPotentialTop : ∀ z, z ∈ S.carrier → S.potential z ≠ ∞)
    (hhazard : S.faultHazard < 1) :
    let D : ℕ → ENNReal := fun n =>
      (homeostaticMarginal S.mixedKernel mu0 n).toMeasure S.legitimateᶜ
    let kappa : ENNReal :=
      ((1 - S.faultHazard : NNReal) : ENNReal) * S.repairDrift
    let lambda : ENNReal := (S.faultHazard : ENNReal) * C.burden
    MeanHomeostasis (fun n => (D n).toReal)
      (lambda.toReal / kappa.toReal) := by
  dsimp
  intro eta heta
  have h := S.eventually_realDamageAverage_le
    C mu0 hmu0 hQ hPotentialTop hhazard eta heta
  simpa [MeanHomeostasis, meanDamageAverage, realDamageAverage] using h

def badPath : ℕ → Bool := fun _ => false

def goodPath : ℕ → Bool := fun _ => true

/-- Half the probability mass is forever damaged and half forever legitimate. -/
noncomputable def twoClassPathMeasure : Measure (ℕ → Bool) :=
  (((1 / 2 : NNReal) : ENNReal)) • Measure.dirac badPath +
    (((1 / 2 : NNReal) : ENNReal)) • Measure.dirac goodPath

theorem twoClassPathMeasure_univ :
    twoClassPathMeasure Set.univ = 1 := by
  unfold twoClassPathMeasure
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp only [Measure.dirac_apply, Set.mem_univ, Set.indicator_of_mem,
    smul_eq_mul, Pi.one_apply, mul_one]
  change (((1 / 2 : NNReal) : ENNReal) + ((1 / 2 : NNReal) : ENNReal)) = 1
  rw [← ENNReal.coe_add]
  norm_num

instance : IsProbabilityMeasure twoClassPathMeasure :=
  MeasureTheory.IsProbabilityMeasure.mk twoClassPathMeasure_univ

private theorem damagedEvent_measure_half (n : ℕ) :
    twoClassPathMeasure {omega | omega n ∉ ({true} : Set Bool)} =
      (((1 / 2 : NNReal) : ENNReal)) := by
  unfold twoClassPathMeasure
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  rw [Measure.dirac_apply badPath, Measure.dirac_apply goodPath]
  have hbad : badPath ∈ {omega | omega n ∉ ({true} : Set Bool)} := by
    simp [badPath]
  have hgood : goodPath ∉ {omega | omega n ∉ ({true} : Set Bool)} := by
    simp [goodPath]
  rw [Set.indicator_of_mem hbad, Set.indicator_of_notMem hgood]
  simp

private theorem damagedProbFromLaw_twoClass (n : ℕ) :
    damagedProbFromLaw twoClassPathMeasure ({true} : Set Bool) n =
      (1 / 2 : ℝ) := by
  unfold damagedProbFromLaw
  rw [measureReal_def, damagedEvent_measure_half]
  norm_num

private theorem meanDamageAverage_half (n : ℕ) :
    meanDamageAverage (fun _ : ℕ => (1 / 2 : ℝ)) n = 1 / 2 := by
  unfold meanDamageAverage
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

theorem twoClass_meanHomeostasis :
    MeanHomeostasis
      (damagedProbFromLaw twoClassPathMeasure ({true} : Set Bool))
      (1 / 2 : ℝ) := by
  intro eta heta
  filter_upwards [] with n
  have havg :
      meanDamageAverage
        (damagedProbFromLaw twoClassPathMeasure ({true} : Set Bool)) n =
        1 / 2 := by
    unfold meanDamageAverage
    simp_rw [damagedProbFromLaw_twoClass]
    exact meanDamageAverage_half n
  rw [havg]
  linarith

private theorem badPath_not_recurrent :
    ¬ (∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ badPath n ∈ ({true} : Set Bool)) := by
  intro h
  obtain ⟨n, hn, hleg⟩ := h 0
  simp [badPath] at hleg

theorem twoClass_not_pathwiseRecurrent :
    ¬ PathwiseRecurrentLegitimacy twoClassPathMeasure ({true} : Set Bool) := by
  intro hrec
  have hzero :
      twoClassPathMeasure
        {omega | ¬ (∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
          omega n ∈ ({true} : Set Bool))} = 0 :=
    (MeasureTheory.ae_iff).1 hrec
  let badSet : Set (ℕ → Bool) :=
    {omega | ¬ (∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      omega n ∈ ({true} : Set Bool))}
  have hbad : badPath ∈ badSet := by
    simpa [badSet] using badPath_not_recurrent
  have hpos : (((1 / 2 : NNReal) : ENNReal)) ≤ twoClassPathMeasure badSet := by
    unfold twoClassPathMeasure
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
    rw [Measure.dirac_apply_of_mem hbad]
    simp only [smul_eq_mul, mul_one]
    exact le_add_right (le_refl _)
  have hzero' : twoClassPathMeasure badSet = 0 := by
    simpa [badSet] using hzero
  rw [hzero'] at hpos
  norm_num at hpos

/-- RH6 separation theorem: even for a normalized path probability law,
mean occupation control does not imply pathwise recurrent legitimacy. -/
theorem meanHomeostasis_does_not_imply_pathwiseRecurrent :
    MeanHomeostasis
        (damagedProbFromLaw twoClassPathMeasure ({true} : Set Bool))
        (1 / 2 : ℝ) ∧
      ¬ PathwiseRecurrentLegitimacy
        twoClassPathMeasure ({true} : Set Bool) :=
  ⟨twoClass_meanHomeostasis, twoClass_not_pathwiseRecurrent⟩

end
end UEOT.V3.Compression.Objecthood
