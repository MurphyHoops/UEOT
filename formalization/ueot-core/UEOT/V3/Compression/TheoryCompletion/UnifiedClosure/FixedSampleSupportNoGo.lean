import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredSamples
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.AbsorbingLeakage
import Mathlib.Algebra.Order.Ring.Pow

/-!
# Fixed-sample exact-support certification has no nontrivial uniform power
The training experiment is the existing productRowLaw of N actual Bernoulli
responses. A rule is an arbitrary PMF-valued kernel on the whole finite record,
so randomized as well as deterministic certification rules are included.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FixedSampleSupportNoGo

open MeasureTheory ProbabilityTheory
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open VariableRegisteredSamples
open scoped BigOperators Classical

noncomputable section

abbrev Coordinate (N : ℕ) := SampleCoordinate (fun _ : Unit => N)
abbrev Record (N : ℕ) := Coordinate N → Bool

def zeroRecord (N : ℕ) : Record N := fun _ => false

/-- A genuine Bernoulli response; true records the previously unseen edge. -/
def response (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : PMF Bool :=
  AbsorbingLeakage.kernel p hp0 hp1 false

/-- Exactly N independent samples from that same row, via the existing source. -/
def trainingLaw (N : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : PMF (Record N) :=
  (productRowLaw (fun _ : Unit => response p hp0 hp1) (fun _ => N)).toPMF

theorem trainingLaw_apply (N : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : Record N) :
    trainingLaw N p hp0 hp1 w = ∏ k : Coordinate N, response p hp0 hp1 (w k) := by
  simp [trainingLaw, productRowLaw, Measure.toPMF_apply]

/-- The all-zero probability is derived from the actual product measure. -/
theorem trainingLaw_zeroRecord (N : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (trainingLaw N p hp0 hp1 (zeroRecord N)).toReal = (1 - p) ^ N := by
  rw [trainingLaw_apply]
  simp [zeroRecord, Coordinate, SampleCoordinate,
    response, AbsorbingLeakage.kernel_mass, AbsorbingLeakage.transitionMass]

theorem trainingLaw_at_zero (N : ℕ) :
    trainingLaw N 0 (le_refl 0) zero_le_one = PMF.pure (zeroRecord N) := by
  have hmass : trainingLaw N 0 (le_refl 0) zero_le_one (zeroRecord N) = 1 := by
    apply (ENNReal.toReal_eq_toReal_iff'
      (PMF.apply_ne_top _ _) ENNReal.one_ne_top).mp
    simpa using trainingLaw_zeroRecord N 0 (le_refl 0) zero_le_one
  have hsupp := (PMF.apply_eq_one_iff _ _).mp hmass
  apply PMF.ext
  intro w
  by_cases hw : w = zeroRecord N
  · simpa [hw] using hmass
  · rw [(PMF.apply_eq_zero_iff _ _).mpr (by simpa [hsupp] using hw)]
    simp [hw]

/-- true means that the rule certifies the exact claim p=0. The kernel may
randomize separately at every possible record; it is fixed across source p. -/
def certificationProbability {N : ℕ}
    (rule : Record N → PMF Bool) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : ℝ :=
  (((trainingLaw N p hp0 hp1).bind rule) true).toReal

def zeroPower {N : ℕ} (rule : Record N → PMF Bool) : ℝ :=
  (rule (zeroRecord N) true).toReal

theorem certificationProbability_eq_sum {N : ℕ}
    (rule : Record N → PMF Bool) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    certificationProbability rule p hp0 hp1 =
      ∑ w : Record N, (trainingLaw N p hp0 hp1 w).toReal * (rule w true).toReal := by
  unfold certificationProbability
  rw [PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul]
  · intro w _
    exact ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)

/-- Power at the exact-zero source is the rule's acceptance probability on
the all-zero record, including for randomized rules. -/
theorem certificationProbability_at_zero {N : ℕ} (rule : Record N → PMF Bool) :
    certificationProbability rule 0 (le_refl 0) zero_le_one = zeroPower rule := by
  simp [certificationProbability, trainingLaw_at_zero, zeroPower]

/-- Every positive source can produce the identical zero record. Its
contribution alone lower-bounds the rule's false certification probability. -/
theorem certificationProbability_ge_zeroPower {N : ℕ}
    (rule : Record N → PMF Bool) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    zeroPower rule * (1 - p) ^ N ≤ certificationProbability rule p hp0 hp1 := by
  rw [certificationProbability_eq_sum]
  have hsingle := Finset.single_le_sum
    (s := (Finset.univ : Finset (Record N)))
    (f := fun w => (trainingLaw N p hp0 hp1 w).toReal * (rule w true).toReal)
    (fun w _ => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    (Finset.mem_univ (zeroRecord N))
  simpa [trainingLaw_zeroRecord, zeroPower, mul_comm] using hsingle

/-- Any power exceeding alpha at p=0 forces false certification exceeding
alpha at some strictly positive p. N is fixed and the rule is arbitrary. -/
theorem exists_positive_source_false_certification
    (N : ℕ) (hN : 0 < N) (rule : Record N → PMF Bool)
    (α : ℝ) (hα : 0 ≤ α)
    (hpower : α < certificationProbability rule 0 (le_refl 0) zero_le_one) :
    ∃ p : Set.Ioo (0 : ℝ) 1,
      α < certificationProbability rule p p.property.1.le p.property.2.le := by
  rw [certificationProbability_at_zero] at hpower
  let ρ := zeroPower rule
  have hρ : 0 < ρ := lt_of_le_of_lt hα hpower
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  let p := (ρ - α) / (2 * ρ * N)
  have hden : 0 < 2 * ρ * N := by positivity
  have hp0 : 0 < p := div_pos (sub_pos.mpr hpower) hden
  have hp1 : p < 1 := by
    apply (div_lt_one hden).mpr
    nlinarith
  have hpeq : (2 * ρ * N) * p = ρ - α := by
    dsimp [p]
    field_simp
  have hbern : 1 - (N : ℝ) * p ≤ (1 - p) ^ N := by
    simpa only [mul_neg, add_neg_cancel_right, sub_eq_add_neg] using
      (one_add_mul_le_pow (a := -p) (by linarith) N)
  have hlow := mul_le_mul_of_nonneg_left hbern hρ.le
  have hstrict : α < ρ * (1 - p) ^ N := by
    nlinarith [hpeq]
  refine ⟨⟨p, hp0, hp1⟩, ?_⟩
  exact lt_of_lt_of_le hstrict
    (certificationProbability_ge_zeroPower rule p hp0.le hp1.le)

/-- No uniformly alpha-valid exact-zero certificate has power above alpha
at the exact-zero source, even with arbitrary record-dependent randomization. -/
theorem no_uniform_exact_zero_certificate
    (N : ℕ) (hN : 0 < N) (rule : Record N → PMF Bool)
    (α : ℝ) (hα : 0 ≤ α)
    (hvalid : ∀ p : Set.Ioo (0 : ℝ) 1,
      certificationProbability rule p p.property.1.le p.property.2.le ≤ α) :
    certificationProbability rule 0 (le_refl 0) zero_le_one ≤ α := by
  by_contra h
  obtain ⟨p, hp⟩ := exists_positive_source_false_certification
    N hN rule α hα (lt_of_not_ge h)
  exact (not_lt_of_ge (hvalid p)) hp

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FixedSampleSupportNoGo
