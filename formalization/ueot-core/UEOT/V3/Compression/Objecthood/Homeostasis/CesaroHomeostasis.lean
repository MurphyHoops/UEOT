import UEOT.V3.Compression.Objecthood.Homeostasis.FiniteHorizonHomeostasis
import UEOT.V3.Compression.OccupationLimitInvariance

/-!
# Track O / RH4 — Cesaro/invariant occupation bridge

This module adapts the exact finite PMF homeostatic dynamics to the frozen
row-stochastic/Cesaro machinery and consumes the existing M-OI bridge. It adds
no irreducibility, mixing, invariant-law uniqueness, or source Track-S theorem.
-/

namespace UEOT.V3.Compression.Objecthood

open Set MeasureTheory Filter Topology
open UEOT.V3.FiniteCesaroInvariant
open UEOT.V3.ViabilityKernel
open UEOT.V3.Compression.OccupationLimitInvariance
open scoped BigOperators ENNReal

universe uZ
noncomputable section

variable {Z : Type uZ} [Fintype Z]
variable [MeasurableSpace Z] [MeasurableSingletonClass Z]
local instance : DecidableEq Z := Classical.decEq Z

def pmfKernelMatrix (H : Z → PMF Z) : Matrix Z Z ℝ :=
  fun x y => (H x y).toReal

theorem pmfKernelMatrix_rowStochastic (H : Z → PMF Z) :
    pmfKernelMatrix H ∈ Matrix.rowStochastic ℝ Z := by
  rw [Matrix.mem_rowStochastic_iff_sum]
  constructor
  · intro i j
    exact ENNReal.toReal_nonneg
  · intro i
    have h := congrArg ENNReal.toReal (PMF.tsum_coe (H i))
    rw [tsum_fintype,
      ENNReal.toReal_sum (fun x _ => PMF.apply_ne_top (H i) x)] at h
    simpa [pmfKernelMatrix] using h

def pmfSimplex (mu : PMF Z) : stdSimplex ℝ Z := by
  refine ⟨fun z => (mu z).toReal, ?_, ?_⟩
  · intro z
    exact ENNReal.toReal_nonneg
  · have h := congrArg ENNReal.toReal (PMF.tsum_coe mu)
    rw [tsum_fintype,
      ENNReal.toReal_sum (fun x _ => PMF.apply_ne_top mu x)] at h
    simpa using h

@[simp] theorem pmfSimplex_apply (mu : PMF Z) (z : Z) :
    (pmfSimplex mu : Z → ℝ) z = (mu z).toReal := rfl

theorem pmfSimplex_bind_vecMul
    (H : Z → PMF Z) (mu : PMF Z) :
    (pmfSimplex (mu.bind H) : Z → ℝ) =
      Matrix.vecMul (pmfSimplex mu : Z → ℝ) (pmfKernelMatrix H) := by
  funext y
  change ((mu.bind H) y).toReal =
    Matrix.vecMul (pmfSimplex mu : Z → ℝ) (pmfKernelMatrix H) y
  rw [PMF.bind_apply, tsum_fintype]
  rw [ENNReal.toReal_sum (by
    intro x hx
    exact ENNReal.mul_ne_top
      (PMF.apply_ne_top mu x) (PMF.apply_ne_top (H x) y))]
  simp_rw [ENNReal.toReal_mul]
  rfl

theorem pmfSimplex_homeostaticMarginal_eq_orbit
    (H : Z → PMF Z) (mu : PMF Z) :
    ∀ n,
      pmfSimplex (homeostaticMarginal H mu n) =
        orbit (pmfKernelMatrix H) (pmfKernelMatrix_rowStochastic H)
          (pmfSimplex mu) n := by
  intro n
  induction n with
  | zero =>
      apply Subtype.ext
      change (pmfSimplex mu : Z → ℝ) =
        (orbit (pmfKernelMatrix H) (pmfKernelMatrix_rowStochastic H)
          (pmfSimplex mu) 0 : Z → ℝ)
      rw [orbit_zero]
      rfl
  | succ n ih =>
      apply Subtype.ext
      rw [homeostaticMarginal_succ]
      change
        (pmfSimplex ((homeostaticMarginal H mu n).bind H) : Z → ℝ) =
          (orbit (pmfKernelMatrix H) (pmfKernelMatrix_rowStochastic H)
            (pmfSimplex mu) (n + 1) : Z → ℝ)
      rw [pmfSimplex_bind_vecMul, orbit_succ, ih]

theorem cesaroRow_eq_average_homeostaticMarginal
    (H : Z → PMF Z) (mu : PMF Z) (n : ℕ) :
    (cesaroRow (pmfKernelMatrix H) (pmfKernelMatrix_rowStochastic H)
      (pmfSimplex mu) n : Z → ℝ) =
      ((n + 1 : ℕ) : ℝ)⁻¹ •
        ∑ t ∈ Finset.range (n + 1),
          (pmfSimplex (homeostaticMarginal H mu t) : Z → ℝ) := by
  rw [cesaroRow_coe]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  exact congrArg Subtype.val
    (pmfSimplex_homeostaticMarginal_eq_orbit H mu t).symm

noncomputable def simplexDamagedMass
    (L : Set Z) (nu : stdSimplex ℝ Z) : ℝ := by
  classical
  exact ∑ z, if z ∈ L then 0 else nu.1 z

noncomputable def simplexLegitimateMass
    (L : Set Z) (nu : stdSimplex ℝ Z) : ℝ := by
  classical
  exact ∑ z, if z ∈ L then nu.1 z else 0

theorem simplexLegitimateMass_add_damagedMass
    (L : Set Z) (nu : stdSimplex ℝ Z) :
    simplexLegitimateMass L nu + simplexDamagedMass L nu = 1 := by
  classical
  unfold simplexLegitimateMass simplexDamagedMass
  rw [← Finset.sum_add_distrib]
  calc
    (∑ z, ((if z ∈ L then nu.1 z else 0) +
      (if z ∈ L then 0 else nu.1 z))) =
      ∑ z, nu.1 z := by
        apply Finset.sum_congr rfl
        intro z hz
        by_cases hL : z ∈ L <;> simp [hL]
    _ = 1 := stdSimplex.sum_eq_one nu

theorem legitimateMass_ge_one_sub_of_damagedMass_le
    (L : Set Z) (nu : stdSimplex ℝ Z) (rho : ℝ)
    (h : simplexDamagedMass L nu ≤ rho) :
    1 - rho ≤ simplexLegitimateMass L nu := by
  have hsum := simplexLegitimateMass_add_damagedMass L nu
  linarith

theorem continuous_simplexDamagedMass (L : Set Z) :
    Continuous (simplexDamagedMass (Z := Z) L) := by
  classical
  unfold simplexDamagedMass
  apply continuous_finsetSum
  intro z hz
  by_cases hL : z ∈ L
  · simpa [hL] using
      (continuous_const :
        Continuous (fun _ : stdSimplex ℝ Z => (0 : ℝ)))
  · simp only [hL, if_false]
    exact (continuous_apply z).comp continuous_subtype_val

theorem simplexDamagedMass_limit_le
    (L : Set Z) (seq : ℕ → stdSimplex ℝ Z) (nu : stdSimplex ℝ Z)
    (tau : ℕ → ℝ) (rho : ℝ)
    (hseq : Tendsto seq atTop (𝓝 nu))
    (htau : Tendsto tau atTop (𝓝 0))
    (hbound : ∀ n, simplexDamagedMass L (seq n) ≤ rho + tau n) :
    simplexDamagedMass L nu ≤ rho := by
  have hleft :
      Tendsto (fun n => simplexDamagedMass L (seq n)) atTop
        (𝓝 (simplexDamagedMass L nu)) :=
    (continuous_simplexDamagedMass L).tendsto nu |>.comp hseq
  have hright : Tendsto (fun n => rho + tau n) atTop (𝓝 rho) := by
    simpa using tendsto_const_nhds.add htau
  exact le_of_tendsto_of_tendsto' hleft hright hbound

theorem simplexDamagedMass_pmfSimplex
    (mu : PMF Z) (L : Set Z) :
    simplexDamagedMass L (pmfSimplex mu) = mu.toMeasure.real Lᶜ := by
  classical
  unfold simplexDamagedMass
  rw [MeasureTheory.measureReal_def]
  rw [PMF.toMeasure_apply_fintype]
  rw [ENNReal.toReal_sum (fun z _ => by
    by_cases hz : z ∈ L <;>
      simp [Set.indicator, hz, PMF.apply_ne_top])]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hL : z ∈ L <;>
    simp [pmfSimplex, Set.indicator, hL]

theorem simplexDamagedMass_cesaroRow_eq_realDamageAverage
    (H : Z → PMF Z) (mu : PMF Z) (L : Set Z) (n : ℕ) :
    simplexDamagedMass L
      (cesaroRow (pmfKernelMatrix H) (pmfKernelMatrix_rowStochastic H)
        (pmfSimplex mu) n) =
      realDamageAverage
        (fun t => (homeostaticMarginal H mu t).toMeasure Lᶜ) n := by
  classical
  unfold realDamageAverage
  have hces := cesaroRow_eq_average_homeostaticMarginal H mu n
  have hcoord : ∀ z : Z,
      (cesaroRow (pmfKernelMatrix H) (pmfKernelMatrix_rowStochastic H)
        (pmfSimplex mu) n : Z → ℝ) z =
      ((((n + 1 : ℕ) : ℝ)⁻¹) •
        ∑ t ∈ Finset.range (n + 1),
          (pmfSimplex (homeostaticMarginal H mu t) : Z → ℝ)) z := by
    intro z
    exact congrArg (fun f : Z → ℝ => f z) hces
  unfold simplexDamagedMass
  change
    (∑ z, if z ∈ L then 0 else
      (cesaroRow (pmfKernelMatrix H) (pmfKernelMatrix_rowStochastic H)
        (pmfSimplex mu) n : Z → ℝ) z) = _
  have hsum :
      (∑ z, if z ∈ L then 0 else
        (cesaroRow (pmfKernelMatrix H) (pmfKernelMatrix_rowStochastic H)
          (pmfSimplex mu) n : Z → ℝ) z) =
      ∑ z, if z ∈ L then 0 else
        (((((n + 1 : ℕ) : ℝ)⁻¹) •
          ∑ t ∈ Finset.range (n + 1),
            (pmfSimplex (homeostaticMarginal H mu t) : Z → ℝ)) z) := by
    apply Finset.sum_congr rfl
    intro z hz
    by_cases hL : z ∈ L
    · simp [hL]
    · simp only [hL, if_false]
      exact hcoord z
  rw [hsum]
  simp_rw [Pi.smul_apply, Finset.sum_apply]
  simp only [smul_eq_mul]
  have hfactor :
      (∑ x, if x ∈ L then 0 else
        (((n + 1 : ℕ) : ℝ)⁻¹) *
          ∑ c ∈ Finset.range (n + 1),
            (pmfSimplex (homeostaticMarginal H mu c)) x) =
      (((n + 1 : ℕ) : ℝ)⁻¹) *
        ∑ x, if x ∈ L then 0 else
          ∑ c ∈ Finset.range (n + 1),
            (pmfSimplex (homeostaticMarginal H mu c)) x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hL : x ∈ L <;> simp [hL]
  rw [hfactor]
  congr 1
  have hexpand :
      (∑ x, if x ∈ L then 0 else
        ∑ c ∈ Finset.range (n + 1),
          (pmfSimplex (homeostaticMarginal H mu c)) x) =
      ∑ x, ∑ c ∈ Finset.range (n + 1),
        if x ∈ L then 0 else
          (pmfSimplex (homeostaticMarginal H mu c)) x := by
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hL : x ∈ L <;> simp [hL]
  rw [hexpand, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  change
    simplexDamagedMass L (pmfSimplex (homeostaticMarginal H mu t)) =
      ((homeostaticMarginal H mu t).toMeasure Lᶜ).toReal
  simpa [MeasureTheory.measureReal_def] using
    (simplexDamagedMass_pmfSimplex (homeostaticMarginal H mu t) L)

/-- RH4 universal subsequential-limit theorem. Any convergent Cesaro
subsequence is invariant by the existing M-OI/P-GOA bridge and inherits the RH3
certified damaged-mass bound. -/
theorem RecurrentHomeostasisSystem.invariant_cesaro_limit_damage_bound
    (S : RecurrentHomeostasisSystem Z)
    (C : FaultBurdenCertificate S)
    (mu0 : PMF Z) (hmu0 : StaysIn mu0 S.carrier)
    (hQ : ∀ z, z ∈ S.carrier →
      homeostaticENNExpectation (S.repairKernel z) S.potential +
          S.damagePenalty z ≤ S.potential z)
    (hPotentialTop : ∀ z, z ∈ S.carrier → S.potential z ≠ ∞)
    (hhazard : S.faultHazard < 1)
    (nu : stdSimplex ℝ Z) (phi : ℕ → ℕ)
    (hphi : StrictMono phi)
    (hlim : Tendsto
      (cesaroRow (pmfKernelMatrix S.mixedKernel)
        (pmfKernelMatrix_rowStochastic S.mixedKernel)
        (pmfSimplex mu0) ∘ phi)
      atTop (𝓝 nu)) :
    Matrix.vecMul nu.1 (pmfKernelMatrix S.mixedKernel) = nu.1 ∧
      simplexDamagedMass S.legitimate nu ≤
        ((S.faultHazard : ENNReal) * C.burden).toReal /
          (((1 - S.faultHazard : NNReal) : ENNReal) * S.repairDrift).toReal ∧
      1 - ((S.faultHazard : ENNReal) * C.burden).toReal /
          (((1 - S.faultHazard : NNReal) : ENNReal) * S.repairDrift).toReal ≤
        simplexLegitimateMass S.legitimate nu := by
  let M := pmfKernelMatrix S.mixedKernel
  let kappa : ENNReal :=
    ((1 - S.faultHazard : NNReal) : ENNReal) * S.repairDrift
  let lambda : ENNReal := (S.faultHazard : ENNReal) * C.burden
  let V0 : ENNReal := homeostaticENNExpectation mu0 S.potential
  let D : ℕ → ENNReal := fun n =>
    (homeostaticMarginal S.mixedKernel mu0 n).toMeasure S.legitimateᶜ
  have hsubpos : 0 < (1 - S.faultHazard : NNReal) :=
    tsub_pos_iff_lt.mpr hhazard
  have hsub0 : ((1 - S.faultHazard : NNReal) : ENNReal) ≠ 0 := by
    exact_mod_cast (ne_of_gt hsubpos)
  have hk0 : kappa ≠ 0 := mul_ne_zero hsub0 S.repairDrift_ne_zero
  have hktop : kappa ≠ ∞ := by
    exact ENNReal.mul_ne_top (by simp) S.repairDrift_ne_top
  have hlamtop : lambda ≠ ∞ := by
    exact ENNReal.mul_ne_top (by simp) C.burden_ne_top
  have hVtop : V0 ≠ ∞ := by
    exact homeostaticENNExpectation_ne_top_of_staysIn
      mu0 S.carrier S.potential hmu0 hPotentialTop
  have hDtop : ∀ n, D n ≠ ∞ := by
    intro n
    exact MeasureTheory.measure_ne_top _ _
  have hfinite : ∀ N,
      kappa * (∑ n ∈ Finset.range N, D n) ≤
        V0 + (N : ENNReal) * lambda := by
    intro N
    simpa [D, kappa, lambda, V0] using
      S.finiteHorizonDamagedOccupation C mu0 hmu0 hQ N
  have hinvariant :
      Matrix.vecMul nu.1 M = nu.1 := by
    exact finite_invariant_of_cesaro_tendsto
      M (pmfKernelMatrix_rowStochastic S.mixedKernel)
        (pmfSimplex mu0) nu phi hphi (by
          simpa [M] using hlim)
  let tau : ℕ → ℝ := fun n =>
    V0.toReal / ((((phi n) + 1 : ℕ) : ℝ) * kappa.toReal)
  have hkpos : 0 < kappa.toReal := ENNReal.toReal_pos hk0 hktop
  have hbaseStartup : Tendsto
      (fun n : ℕ =>
        V0.toReal / (((n + 1 : ℕ) : ℝ) * kappa.toReal))
      atTop (𝓝 0) := by
    have hn : Tendsto
        (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * kappa.toReal)
        atTop atTop := by
      have hnat : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ))
          atTop atTop := by
        exact (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
      exact hnat.atTop_mul_const hkpos
    exact Filter.Tendsto.const_div_atTop hn V0.toReal
  have htau : Tendsto tau atTop (𝓝 0) := by
    exact hbaseStartup.comp hphi.tendsto_atTop
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
  · simpa [kappa, lambda] using hdamage
  · exact legitimateMass_ge_one_sub_of_damagedMass_le
      S.legitimate nu
      (((S.faultHazard : ENNReal) * C.burden).toReal /
        (((1 - S.faultHazard : NNReal) : ENNReal) * S.repairDrift).toReal)
      (by simpa [kappa, lambda] using hdamage)

/-- RH4 existence form, obtained from the existing finite Cesaro compactness
adapter and the universal subsequential-limit theorem above. -/
theorem RecurrentHomeostasisSystem.exists_invariant_cesaro_limit_with_damage_bound
    (S : RecurrentHomeostasisSystem Z)
    (C : FaultBurdenCertificate S)
    (mu0 : PMF Z) (hmu0 : StaysIn mu0 S.carrier)
    (hQ : ∀ z, z ∈ S.carrier →
      homeostaticENNExpectation (S.repairKernel z) S.potential +
          S.damagePenalty z ≤ S.potential z)
    (hPotentialTop : ∀ z, z ∈ S.carrier → S.potential z ≠ ∞)
    (hhazard : S.faultHazard < 1) :
    ∃ nu : stdSimplex ℝ Z, ∃ phi : ℕ → ℕ,
      StrictMono phi ∧
      Tendsto
        (cesaroRow (pmfKernelMatrix S.mixedKernel)
          (pmfKernelMatrix_rowStochastic S.mixedKernel)
          (pmfSimplex mu0) ∘ phi)
        atTop (𝓝 nu) ∧
      Matrix.vecMul nu.1 (pmfKernelMatrix S.mixedKernel) = nu.1 ∧
      simplexDamagedMass S.legitimate nu ≤
        ((S.faultHazard : ENNReal) * C.burden).toReal /
          (((1 - S.faultHazard : NNReal) : ENNReal) * S.repairDrift).toReal ∧
      1 - ((S.faultHazard : ENNReal) * C.burden).toReal /
          (((1 - S.faultHazard : NNReal) : ENNReal) * S.repairDrift).toReal ≤
        simplexLegitimateMass S.legitimate nu := by
  obtain ⟨hextract, _⟩ :=
    p_goa_01_via_occupationLimit
      (pmfKernelMatrix S.mixedKernel)
      (pmfKernelMatrix_rowStochastic S.mixedKernel)
      (pmfSimplex mu0)
  rcases hextract with ⟨nu, phi, hphi, hlim⟩
  rcases S.invariant_cesaro_limit_damage_bound
    C mu0 hmu0 hQ hPotentialTop hhazard nu phi hphi hlim with
      ⟨hinv, hdamage, hlegit⟩
  exact ⟨nu, phi, hphi, hlim, hinv, hdamage, hlegit⟩

end
end UEOT.V3.Compression.Objecthood
