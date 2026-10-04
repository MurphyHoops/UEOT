import UEOT.V3.Compression.Objecthood.Homeostasis.HomeostasisSemantics

namespace UEOT.V3.Compression.Objecthood

open Filter Topology
open UEOT.V3.FiniteCesaroInvariant
open UEOT.V3.ViabilityKernel
open scoped BigOperators ENNReal

noncomputable section

universe uZ
variable {Z : Type uZ} [Fintype Z]
variable [MeasurableSpace Z] [MeasurableSingletonClass Z]
local instance : DecidableEq Z := Classical.decEq Z

noncomputable def damageIndicatorReal (L : Set Z) (z : Z) : ℝ := by
  classical
  exact if z ∈ L then 0 else 1

noncomputable def semanticExpectation
    (nu : stdSimplex ℝ Z) (defect : Z → ℝ) : ℝ :=
  ∑ z, nu.1 z * defect z

theorem simplexDamagedMass_eq_indicatorExpectation
    (nu : stdSimplex ℝ Z) (L : Set Z) :
    simplexDamagedMass L nu =
      ∑ z, nu.1 z * damageIndicatorReal L z := by
  classical
  unfold simplexDamagedMass damageIndicatorReal
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hL : z ∈ L <;> simp [hL]

/-- Explicit semantic coupling: a baseline defect on legitimate states plus an
extra defect budget on damaged states converts damaged occupation into an
average semantic-defect bound. -/
theorem semanticExpectation_le_of_damagedMass
    (nu : stdSimplex ℝ Z) (L : Set Z)
    (defect : Z → ℝ) (good extra rho : ℝ)
    (hextra : 0 ≤ extra)
    (hpoint : ∀ z, defect z ≤ good + extra * damageIndicatorReal L z)
    (hmass : simplexDamagedMass L nu ≤ rho) :
    semanticExpectation nu defect ≤ good + extra * rho := by
  classical
  unfold semanticExpectation
  calc
    (∑ z, nu.1 z * defect z) ≤
        ∑ z, nu.1 z * (good + extra * damageIndicatorReal L z) := by
      apply Finset.sum_le_sum
      intro z hz
      exact mul_le_mul_of_nonneg_left (hpoint z) (stdSimplex.zero_le nu z)
    _ = good + extra * simplexDamagedMass L nu := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      have hsum : (∑ z, nu.1 z) = 1 := stdSimplex.sum_eq_one nu
      have hdamage := simplexDamagedMass_eq_indicatorExpectation nu L
      calc
        (∑ z, nu.1 z * good) +
            ∑ z, nu.1 z * (extra * damageIndicatorReal L z) =
          good * (∑ z, nu.1 z) +
            extra * (∑ z, nu.1 z * damageIndicatorReal L z) := by
              congr 1
              · rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro z hz
                ring
              · rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro z hz
                ring
        _ = good + extra * simplexDamagedMass L nu := by
          rw [hsum, mul_one, ← hdamage]
    _ ≤ good + extra * rho := by
      simpa [add_comm] using
        add_le_add_left (mul_le_mul_of_nonneg_left hmass hextra) good

/-- **RH7 semantic homeostasis.**  Under an explicit statewise semantic-coupling
assumption, RH4 supplies an invariant Cesaro cluster law whose average semantic
defect is bounded by the baseline legitimate defect plus the certified
recurrent-fault damaged-mass ratio. -/
theorem RecurrentHomeostasisSystem.exists_invariant_semanticHomeostasis
    (S : RecurrentHomeostasisSystem Z)
    (C : FaultBurdenCertificate S)
    (mu0 : PMF Z) (hmu0 : StaysIn mu0 S.carrier)
    (hQ : ∀ z, z ∈ S.carrier →
      homeostaticENNExpectation (S.repairKernel z) S.potential +
          S.damagePenalty z ≤ S.potential z)
    (hPotentialTop : ∀ z, z ∈ S.carrier → S.potential z ≠ ∞)
    (hhazard : S.faultHazard < 1)
    (defect : Z → ℝ) (good extra : ℝ)
    (hextra : 0 ≤ extra)
    (hpoint : ∀ z,
      defect z ≤ good + extra * damageIndicatorReal S.legitimate z) :
    let rho :=
      ((S.faultHazard : ENNReal) * C.burden).toReal /
        (((1 - S.faultHazard : NNReal) : ENNReal) * S.repairDrift).toReal
    ∃ nu : stdSimplex ℝ Z, ∃ phi : ℕ → ℕ,
      StrictMono phi ∧
      Tendsto
        (cesaroRow (pmfKernelMatrix S.mixedKernel)
          (pmfKernelMatrix_rowStochastic S.mixedKernel)
          (pmfSimplex mu0) ∘ phi)
        atTop (𝓝 nu) ∧
      Matrix.vecMul nu.1 (pmfKernelMatrix S.mixedKernel) = nu.1 ∧
      semanticExpectation nu defect ≤ good + extra * rho := by
  dsimp
  obtain ⟨nu, phi, hphi, hlim, hinv, hdamage, hlegit⟩ :=
    S.exists_invariant_cesaro_limit_with_damage_bound
      C mu0 hmu0 hQ hPotentialTop hhazard
  refine ⟨nu, phi, hphi, hlim, hinv, ?_⟩
  exact semanticExpectation_le_of_damagedMass
    nu S.legitimate defect good extra
    (((S.faultHazard : ENNReal) * C.burden).toReal /
      (((1 - S.faultHazard : NNReal) : ENNReal) * S.repairDrift).toReal)
    hextra hpoint hdamage

end
end UEOT.V3.Compression.Objecthood
