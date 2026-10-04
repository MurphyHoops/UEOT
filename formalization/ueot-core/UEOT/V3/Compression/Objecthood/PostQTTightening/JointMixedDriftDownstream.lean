import UEOT.V3.Compression.Objecthood.PostQTTightening.CanonicalJointMixedDrift
import UEOT.V3.Compression.Objecthood.Homeostasis.CesaroHomeostasis

/-!
# Post-QT tightening — downstream joint mixed-drift homeostasis

The canonical joint mixed-drift residual is plugged directly into the generic
RH3/RH4 telescope and Cesaro machinery.  No repair/fault factorization is used
at this layer: the actual mixed kernel is the certified transition.
-/

namespace UEOT.V3.Compression.Objecthood

open Set MeasureTheory ProbabilityTheory Filter Topology
open UEOT.V3.FiniteCesaroInvariant
open UEOT.V3.ViabilityKernel
open UEOT.V3.Compression.OccupationLimitInvariance
open scoped ENNReal BigOperators ProbabilityTheory

universe uZ

noncomputable section

variable {Z : Type uZ} [Fintype Z]
variable [MeasurableSpace Z] [MeasurableSingletonClass Z]
local instance jointDownstreamDecidableEq : DecidableEq Z := Classical.decEq Z

/-- Finite-horizon damaged occupation with the least fixed-`kappa` mixed-drift
residual. -/
theorem RecurrentHomeostasisSystem.finiteHorizonDamagedOccupation_canonicalJoint
    (S : RecurrentHomeostasisSystem Z)
    (kappa : ENNReal)
    (mu0 : PMF Z) (hmu0 : StaysIn mu0 S.carrier)
    (N : ℕ) :
    kappa * (∑ n ∈ Finset.range N,
        (homeostaticMarginal S.mixedKernel mu0 n).toMeasure S.legitimateᶜ) ≤
      homeostaticENNExpectation mu0 S.potential +
        (N : ENNReal) * canonicalJointMixedDriftResidual S kappa := by
  apply finiteHorizonDamagedOccupation_on_carrier
    S.mixedKernel mu0 S.carrier S.legitimate S.potential
    kappa (canonicalJointMixedDriftResidual S kappa)
    hmu0 (fun z hz => S.mixed_stays_carrier hz)
    (fun z hz => mixedDrift_le_potential_add_canonicalJointResidual S kappa hz)
    N

/-- The canonical joint residual gives the asymptotic mean damaged-occupation
bound for any positive finite coefficient `kappa`. -/
theorem RecurrentHomeostasisSystem.eventually_realDamageAverage_le_canonicalJoint
    (S : RecurrentHomeostasisSystem Z)
    (kappa : ENNReal)
    (mu0 : PMF Z) (hmu0 : StaysIn mu0 S.carrier)
    (hPotentialTop : ∀ z, z ∈ S.carrier → S.potential z ≠ ∞)
    (hk0 : kappa ≠ 0) (hktop : kappa ≠ ∞) :
    let D : ℕ → ENNReal := fun n =>
      (homeostaticMarginal S.mixedKernel mu0 n).toMeasure S.legitimateᶜ
    let lambda := canonicalJointMixedDriftResidual S kappa
    ∀ eta > 0, ∀ᶠ n in atTop,
      realDamageAverage D n ≤ lambda.toReal / kappa.toReal + eta := by
  dsimp
  let D : ℕ → ENNReal := fun n =>
    (homeostaticMarginal S.mixedKernel mu0 n).toMeasure S.legitimateᶜ
  let lambda := canonicalJointMixedDriftResidual S kappa
  let V0 : ENNReal := homeostaticENNExpectation mu0 S.potential
  have hlamtop : lambda ≠ ∞ :=
    canonicalJointMixedDriftResidual_ne_top S kappa hPotentialTop hktop
  have hVtop : V0 ≠ ∞ :=
    homeostaticENNExpectation_ne_top_of_staysIn
      mu0 S.carrier S.potential hmu0 hPotentialTop
  have hDtop : ∀ n, D n ≠ ∞ := by
    intro n
    exact MeasureTheory.measure_ne_top _ _
  apply mean_homeostasis_of_ennreal_budget
    D kappa lambda V0 hDtop hk0 hktop hlamtop hVtop
  intro N
  simpa [D, lambda, V0] using
    S.finiteHorizonDamagedOccupation_canonicalJoint kappa mu0 hmu0 N

/-- Universal RH4-style subsequential Cesaro theorem for the canonical joint
mixed-drift residual. -/
theorem RecurrentHomeostasisSystem.invariant_cesaro_limit_damage_bound_canonicalJoint
    (S : RecurrentHomeostasisSystem Z)
    (kappa : ENNReal)
    (mu0 : PMF Z) (hmu0 : StaysIn mu0 S.carrier)
    (hPotentialTop : ∀ z, z ∈ S.carrier → S.potential z ≠ ∞)
    (hk0 : kappa ≠ 0) (hktop : kappa ≠ ∞)
    (nu : stdSimplex ℝ Z) (phi : ℕ → ℕ)
    (hphi : StrictMono phi)
    (hlim : Tendsto
      (cesaroRow (pmfKernelMatrix S.mixedKernel)
        (pmfKernelMatrix_rowStochastic S.mixedKernel)
        (pmfSimplex mu0) ∘ phi)
      atTop (𝓝 nu)) :
    Matrix.vecMul nu.1 (pmfKernelMatrix S.mixedKernel) = nu.1 ∧
      simplexDamagedMass S.legitimate nu ≤
        (canonicalJointMixedDriftResidual S kappa).toReal / kappa.toReal ∧
      1 - (canonicalJointMixedDriftResidual S kappa).toReal / kappa.toReal ≤
        simplexLegitimateMass S.legitimate nu := by
  let M := pmfKernelMatrix S.mixedKernel
  let lambda := canonicalJointMixedDriftResidual S kappa
  let V0 : ENNReal := homeostaticENNExpectation mu0 S.potential
  let D : ℕ → ENNReal := fun n =>
    (homeostaticMarginal S.mixedKernel mu0 n).toMeasure S.legitimateᶜ
  have hlamtop : lambda ≠ ∞ :=
    canonicalJointMixedDriftResidual_ne_top S kappa hPotentialTop hktop
  have hVtop : V0 ≠ ∞ :=
    homeostaticENNExpectation_ne_top_of_staysIn
      mu0 S.carrier S.potential hmu0 hPotentialTop
  have hDtop : ∀ n, D n ≠ ∞ := by
    intro n
    exact MeasureTheory.measure_ne_top _ _
  have hfinite : ∀ N,
      kappa * (∑ n ∈ Finset.range N, D n) ≤
        V0 + (N : ENNReal) * lambda := by
    intro N
    simpa [D, lambda, V0] using
      S.finiteHorizonDamagedOccupation_canonicalJoint kappa mu0 hmu0 N
  have hinvariant : Matrix.vecMul nu.1 M = nu.1 := by
    exact finite_invariant_of_cesaro_tendsto
      M (pmfKernelMatrix_rowStochastic S.mixedKernel)
        (pmfSimplex mu0) nu phi hphi (by
          simpa [M] using hlim)
  let tau : ℕ → ℝ := fun n =>
    V0.toReal / ((((phi n) + 1 : ℕ) : ℝ) * kappa.toReal)
  have hkpos : 0 < kappa.toReal := ENNReal.toReal_pos hk0 hktop
  have hbaseStartup : Tendsto
      (fun n : ℕ => V0.toReal / (((n + 1 : ℕ) : ℝ) * kappa.toReal))
      atTop (𝓝 0) := by
    have hn : Tendsto
        (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * kappa.toReal)
        atTop atTop := by
      have hnat : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ))
          atTop atTop := by
        exact (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
      exact hnat.atTop_mul_const hkpos
    exact Filter.Tendsto.const_div_atTop hn V0.toReal
  have htau : Tendsto tau atTop (𝓝 0) :=
    hbaseStartup.comp hphi.tendsto_atTop
  have hbound : ∀ n,
      simplexDamagedMass S.legitimate
          (cesaroRow M (pmfKernelMatrix_rowStochastic S.mixedKernel)
            (pmfSimplex mu0) (phi n)) ≤
        lambda.toReal / kappa.toReal + tau n := by
    intro n
    rw [simplexDamagedMass_cesaroRow_eq_realDamageAverage]
    have havg := real_average_bound_of_ennreal_homeostatic_budget
      D kappa lambda V0 hDtop hk0 hktop hlamtop hVtop
      (phi n + 1) (Nat.succ_pos (phi n)) (hfinite (phi n + 1))
    simpa [D, tau, realDamageAverage, add_comm] using havg
  have hdamage := simplexDamagedMass_limit_le
    S.legitimate
    (fun n => cesaroRow M
      (pmfKernelMatrix_rowStochastic S.mixedKernel)
      (pmfSimplex mu0) (phi n))
    nu tau (lambda.toReal / kappa.toReal)
    (by simpa [M, Function.comp_def] using hlim) htau hbound
  refine ⟨?_, ?_, ?_⟩
  · simpa [M] using hinvariant
  · simpa [lambda] using hdamage
  · exact legitimateMass_ge_one_sub_of_damagedMass_le
      S.legitimate nu
      ((canonicalJointMixedDriftResidual S kappa).toReal / kappa.toReal)
      (by simpa [lambda] using hdamage)

/-- Existence form of the canonical-joint RH4 bound. -/
theorem RecurrentHomeostasisSystem.exists_invariant_cesaro_limit_with_damage_bound_canonicalJoint
    (S : RecurrentHomeostasisSystem Z)
    (kappa : ENNReal)
    (mu0 : PMF Z) (hmu0 : StaysIn mu0 S.carrier)
    (hPotentialTop : ∀ z, z ∈ S.carrier → S.potential z ≠ ∞)
    (hk0 : kappa ≠ 0) (hktop : kappa ≠ ∞) :
    ∃ nu : stdSimplex ℝ Z, ∃ phi : ℕ → ℕ,
      StrictMono phi ∧
      Tendsto
        (cesaroRow (pmfKernelMatrix S.mixedKernel)
          (pmfKernelMatrix_rowStochastic S.mixedKernel)
          (pmfSimplex mu0) ∘ phi)
        atTop (𝓝 nu) ∧
      Matrix.vecMul nu.1 (pmfKernelMatrix S.mixedKernel) = nu.1 ∧
      simplexDamagedMass S.legitimate nu ≤
        (canonicalJointMixedDriftResidual S kappa).toReal / kappa.toReal ∧
      1 - (canonicalJointMixedDriftResidual S kappa).toReal / kappa.toReal ≤
        simplexLegitimateMass S.legitimate nu := by
  obtain ⟨hextract, _⟩ :=
    p_goa_01_via_occupationLimit
      (pmfKernelMatrix S.mixedKernel)
      (pmfKernelMatrix_rowStochastic S.mixedKernel)
      (pmfSimplex mu0)
  rcases hextract with ⟨nu, phi, hphi, hlim⟩
  rcases S.invariant_cesaro_limit_damage_bound_canonicalJoint
    kappa mu0 hmu0 hPotentialTop hk0 hktop nu phi hphi hlim with
      ⟨hinv, hdamage, hlegit⟩
  exact ⟨nu, phi, hphi, hlim, hinv, hdamage, hlegit⟩

/-- At the standard RH coefficient, the final real damaged-occupation ratio from
the joint residual is no larger than the QT canonical fault-burden ratio. -/
theorem canonicalJointMixedDriftRatio_le_canonicalFaultRatio
    (S : RecurrentHomeostasisSystem Z)
    (hPotentialTop : ∀ z, z ∈ S.carrier → S.potential z ≠ ∞)
    (hQ : ∀ z, z ∈ S.carrier →
      homeostaticENNExpectation (S.repairKernel z) S.potential +
          S.damagePenalty z ≤ S.potential z) :
    let kappa : ENNReal :=
      ((1 - S.faultHazard : NNReal) : ENNReal) * S.repairDrift
    (canonicalJointMixedDriftResidual S kappa).toReal / kappa.toReal ≤
      ((S.faultHazard : ENNReal) * canonicalFaultBurden S).toReal /
        kappa.toReal := by
  dsimp
  have hle := canonicalJointMixedDriftResidual_le_canonicalFaultEnvelope
    S hPotentialTop hQ
  have hright :
      (S.faultHazard : ENNReal) * canonicalFaultBurden S ≠ ∞ :=
    ENNReal.mul_ne_top (by simp)
      (canonicalFaultBurden_ne_top_of_carrierPotentialFinite S hPotentialTop)
  have hreal :
      (canonicalJointMixedDriftResidual S
        (((1 - S.faultHazard : NNReal) : ENNReal) * S.repairDrift)).toReal ≤
      ((S.faultHazard : ENNReal) * canonicalFaultBurden S).toReal :=
    ENNReal.toReal_mono hright hle
  exact div_le_div_of_nonneg_right hreal ENNReal.toReal_nonneg

/-- Objecthood specialization of the canonical-joint asymptotic mean bound. -/
theorem objecthood_eventually_realDamageAverage_le_canonicalJoint
    {X : Type*} {A : Type*}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace (UEOT.V3.Compression.CrossTrack.ConstitutiveState X A)]
    [MeasurableSingletonClass (UEOT.V3.Compression.CrossTrack.ConstitutiveState X A)]
    (P : X → A → PMF X) (K : Set X)
    (hfix : UEOT.V3.ViabilityKernel.viabilityStep P K = K)
    (F : UEOT.V3.Compression.CrossTrack.ConstitutiveState X A →
      PMF (UEOT.V3.Compression.CrossTrack.ConstitutiveState X A))
    (epsilon : NNReal) (hepsilon : epsilon ≤ 1) (hepsilon_lt : epsilon < 1)
    (hF : ∀ ⦃z : UEOT.V3.Compression.CrossTrack.ConstitutiveState X A⦄,
      z ∈ gcrHomeostaticCarrier P K →
        StaysIn (F z) (gcrHomeostaticCarrier P K))
    (mu0 : PMF (UEOT.V3.Compression.CrossTrack.ConstitutiveState X A))
    (hmu0 : StaysIn mu0 (gcrHomeostaticCarrier P K)) :
    let S := objecthoodRecurrentHomeostasisSystem
      P K hfix F epsilon hepsilon hF
    let kappa : ENNReal :=
      ((1 - epsilon : NNReal) : ENNReal) * S.repairDrift
    let lambda := canonicalJointMixedDriftResidual S kappa
    let D : ℕ → ENNReal := fun n =>
      (homeostaticMarginal S.mixedKernel mu0 n).toMeasure S.legitimateᶜ
    ∀ eta > 0, ∀ᶠ n in atTop,
      realDamageAverage D n ≤ lambda.toReal / kappa.toReal + eta := by
  dsimp
  let S := objecthoodRecurrentHomeostasisSystem
    P K hfix F epsilon hepsilon hF
  let kappa : ENNReal :=
    ((1 - epsilon : NNReal) : ENNReal) * S.repairDrift
  have hPot : ∀ z, z ∈ S.carrier → S.potential z ≠ ∞ := by
    intro z hz
    exact autonomousRepairPotential_ne_top_on_gcrHomeostaticCarrier
      P K hfix (by
        simpa [S, objecthoodRecurrentHomeostasisSystem] using hz)
  have hsubpos : 0 < (1 - epsilon : NNReal) :=
    tsub_pos_iff_lt.mpr hepsilon_lt
  have hsub0 : ((1 - epsilon : NNReal) : ENNReal) ≠ 0 := by
    exact_mod_cast (ne_of_gt hsubpos)
  have hk0 : kappa ≠ 0 := by
    exact mul_ne_zero hsub0 S.repairDrift_ne_zero
  have hktop : kappa ≠ ∞ := by
    exact ENNReal.mul_ne_top (by simp) S.repairDrift_ne_top
  simpa [S, kappa] using
    S.eventually_realDamageAverage_le_canonicalJoint
      kappa mu0 (by
        simpa [S, objecthoodRecurrentHomeostasisSystem] using hmu0)
      hPot hk0 hktop


end
end UEOT.V3.Compression.Objecthood
