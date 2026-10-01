import UEOT.V3.Compression.TopologyChangingGoaL1ResidualConorm
import UEOT.V3.Compression.InvariantSetGaugeInvariance
import UEOT.V3.Compression.TopologyChangingGoaDobrushinL1Bridge
/-!
# Finite-Markov invariant uniqueness as canonical residual isolation

This Track-S module identifies the qualitative meaning of the canonical
direct-L1 residual conorm for an arbitrary finite stochastic kernel.  On the
zero-total-mass signed-law space, injectivity of the fixed-point residual is
equivalent to uniqueness of the invariant probability law.  Since frozen
P-GOA-01 supplies invariant-law existence for every finite stochastic kernel,
positivity of the canonical L1 residual conorm is therefore equivalent (on a
nontrivial carrier) to existence of a unique invariant law.

The reverse implication is not assumed from recurrent-class folklore.  A
nonzero zero-mass residual-null vector is split into normalized positive and
negative probability laws.  Its invariance keeps their difference fixed under
all iterates and Cesaro averages.  Compactness plus P-GOA-01 then yields two
distinct invariant-law limits, contradicting uniqueness.

This is post-FINAL, uncounted Track-S research and does not change the frozen
four-generator core.
-/


namespace UEOT.V3.Compression.TopologyChangingGoaInvariantUniquenessIsolation

open UEOT.V3
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.InvariantSetGaugeInvariance
open UEOT.V3.Compression.TopologyChangingGoaSpectralIsolation
open UEOT.V3.Compression.TopologyChangingGoaRestrictedResidualAdapter
open UEOT.V3.Compression.TopologyChangingGoaL1ResidualConorm

universe u
noncomputable section
variable {S : Type u} [Fintype S] [Nonempty S]
noncomputable local instance : DecidableEq S := Classical.decEq S

private theorem law_difference_sum_zero (mu nu : stdSimplex ℝ S) :
    (∑ s, (nu s - mu s)) = 0 := by
  calc
    (∑ s, (nu s - mu s)) = (∑ s, nu s) - (∑ s, mu s) := by
      rw [Finset.sum_sub_distrib]
    _ = 1 - 1 := by rw [stdSimplex.sum_eq_one nu, stdSimplex.sum_eq_one mu]
    _ = 0 := by norm_num

private theorem law_difference_residual_zero
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (mu nu : stdSimplex ℝ S)
    (hmu : step P hP mu = mu)
    (hnu : step P hP nu = nu) :
    signedResidual P (fun s => nu s - mu s) = 0 := by
  unfold signedResidual
  change Matrix.vecMul (nu.1 - mu.1) P - (nu.1 - mu.1) = 0
  rw [Matrix.sub_vecMul]
  have hmu' := congrArg Subtype.val hmu
  have hnu' := congrArg Subtype.val hnu
  change Matrix.vecMul mu.1 P = mu.1 at hmu'
  change Matrix.vecMul nu.1 P = nu.1 at hnu'
  rw [hmu', hnu']
  simp

theorem invariantLaw_unique_of_restricted_injective
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hinj : Function.Injective (zeroSumResidualLinear P))
    (mu nu : stdSimplex ℝ S)
    (hmu : mu ∈ invariantLawSet P hP)
    (hnu : nu ∈ invariantLawSet P hP) :
    mu = nu := by
  rw [mem_invariantLawSet] at hmu hnu
  let v : S → ℝ := fun s => nu s - mu s
  have hvsum : (∑ s, v s) = 0 := law_difference_sum_zero mu nu
  have hres : signedResidual P v = 0 :=
    law_difference_residual_zero P hP mu nu hmu hnu
  let w : zeroSumEuclidean (S := S) :=
    ⟨WithLp.toLp 2 v, (zeroSum_mem_iff v).2 hvsum⟩
  have hmapzero : zeroSumResidualLinear P w = 0 := by
    rw [WithLp.ext_iff]
    simpa [zeroSumResidualLinear, w, residualEuclideanLinear_ofLp] using hres
  have hwzero : w = 0 := by
    apply hinj
    simpa using hmapzero
  have hvzero : v = 0 := by
    have hval := congrArg (fun z : zeroSumEuclidean (S := S) =>
      (z.1 : EuclideanSpace ℝ S).ofLp) hwzero
    simpa [w] using hval
  apply Subtype.ext
  funext s
  have hs := congrFun hvzero s
  change nu s - mu s = 0 at hs
  exact (sub_eq_zero.mp hs).symm

theorem invariantLawSet_subsingleton_of_restricted_injective
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hinj : Function.Injective (zeroSumResidualLinear P)) :
    (invariantLawSet P hP).Subsingleton := by
  intro mu hmu nu hnu
  exact invariantLaw_unique_of_restricted_injective P hP hinj mu nu hmu hnu

end
end UEOT.V3.Compression.TopologyChangingGoaInvariantUniquenessIsolation

namespace UEOT.V3.Compression.TopologyChangingGoaInvariantUniquenessIsolation

open UEOT.V3
open UEOT.V3.FiniteDobrushin
open UEOT.V3.FiniteCesaroInvariant
open UEOT.V3.Compression.InvariantSetGaugeInvariance
open UEOT.V3.Compression.TopologyChangingGoaSpectralIsolation
open UEOT.V3.Compression.TopologyChangingGoaRestrictedResidualAdapter
open UEOT.V3.Compression.TopologyChangingGoaL1ResidualConorm
open UEOT.V3.Compression.TopologyChangingGoaDobrushinL1Bridge
open Filter Topology

universe u
noncomputable section
variable {S : Type u} [Fintype S] [Nonempty S]
noncomputable local instance : DecidableEq S := Classical.decEq S

private theorem vecMul_fixed_of_residual_zero
    (P : Matrix S S ℝ) (v : S → ℝ)
    (hres : signedResidual P v = 0) :
    Matrix.vecMul v P = v := by
  unfold signedResidual at hres
  exact sub_eq_zero.mp hres

private theorem vecMul_pow_fixed_of_residual_zero
    (P : Matrix S S ℝ) (v : S → ℝ)
    (hres : signedResidual P v = 0) :
    ∀ n, Matrix.vecMul v (P ^ n) = v := by
  intro n
  induction n with
  | zero =>
      simpa using Matrix.vecMul_one v
  | succ n ih =>
      rw [pow_succ, ← Matrix.vecMul_vecMul, ih]
      exact vecMul_fixed_of_residual_zero P v hres

private theorem scaled_orbit_difference_of_residual_zero
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (v : S → ℝ) (hres : signedResidual P v = 0)
    (c : ℝ) (nu mu : stdSimplex ℝ S)
    (hvrep : v = fun s => c * (nu s - mu s)) :
    ∀ n, v = fun s =>
      c * ((orbit P hP nu n : S → ℝ) s - (orbit P hP mu n : S → ℝ) s) := by
  intro n
  have hfixed := vecMul_pow_fixed_of_residual_zero P v hres n
  funext y
  have hfixedy := congrFun hfixed y
  rw [← hfixedy]
  change Matrix.vecMul v (P ^ n) y =
    c * (Matrix.vecMul nu.1 (P ^ n) y - Matrix.vecMul mu.1 (P ^ n) y)
  rw [hvrep, Matrix.vecMul_apply_eq_sum]
  calc
    (∑ x, (c * (nu x - mu x)) * (P ^ n) x y)
        = ∑ x, c * ((nu x - mu x) * (P ^ n) x y) := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
    _ = c * ∑ x, ((nu x - mu x) * (P ^ n) x y) := by
          rw [Finset.mul_sum]
    _ = c * ((∑ x, nu x * (P ^ n) x y) -
        ∑ x, mu x * (P ^ n) x y) := by
          congr 1
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro x hx
          ring

private theorem scaled_cesaro_difference_of_residual_zero
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (v : S → ℝ) (hres : signedResidual P v = 0)
    (c : ℝ) (nu mu : stdSimplex ℝ S)
    (hvrep : v = fun s => c * (nu s - mu s)) :
    ∀ n, v = fun s =>
      c * ((cesaroRow P hP nu n : S → ℝ) s -
        (cesaroRow P hP mu n : S → ℝ) s) := by
  intro n
  have horbit := scaled_orbit_difference_of_residual_zero
    P hP v hres c nu mu hvrep
  funext y
  rw [cesaroRow_coe, cesaroRow_coe]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  let N : ℕ := n + 1
  have hN : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero n)
  have hsum :
      (N : ℝ) * v y =
        c * ((∑ t ∈ Finset.range N, (orbit P hP nu t : S → ℝ) y) -
          ∑ t ∈ Finset.range N, (orbit P hP mu t : S → ℝ) y) := by
    calc
      (N : ℝ) * v y = ∑ _t ∈ Finset.range N, v y := by
        rw [Finset.sum_const, Finset.card_range]
        simp [nsmul_eq_mul]
      _ = ∑ t ∈ Finset.range N,
          c * ((orbit P hP nu t : S → ℝ) y -
            (orbit P hP mu t : S → ℝ) y) := by
            apply Finset.sum_congr rfl
            intro t ht
            exact congrFun (horbit t) y
      _ = c * ((∑ t ∈ Finset.range N, (orbit P hP nu t : S → ℝ) y) -
          ∑ t ∈ Finset.range N, (orbit P hP mu t : S → ℝ) y) := by
            rw [← Finset.mul_sum, ← Finset.sum_sub_distrib]
  change v y =
    c * (((N : ℝ)⁻¹ *
      ∑ t ∈ Finset.range N, (orbit P hP nu t : S → ℝ) y) -
      ((N : ℝ)⁻¹ *
      ∑ t ∈ Finset.range N, (orbit P hP mu t : S → ℝ) y))
  field_simp [hN]
  simpa [N, mul_comm] using hsum

private theorem exists_distinct_invariant_laws_of_nonzero_fixed_zero_sum
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (v : S → ℝ)
    (hvsum : (∑ s, v s) = 0)
    (hvne : v ≠ 0)
    (hres : signedResidual P v = 0) :
    ∃ mu nu : stdSimplex ℝ S,
      mu ∈ invariantLawSet P hP ∧
      nu ∈ invariantLawSet P hP ∧
      mu ≠ nu := by
  let c : ℝ := ∑ s, (v s)⁺
  have hl1 : signedL1 v = 2 * c := by
    simpa [c] using signedL1_eq_two_pos_mass v hvsum
  have hl1pos : 0 < signedL1 v := signedL1_pos_of_ne_zero v hvne
  have hc : 0 < c := by nlinarith
  have hmass : (∑ s, (v s)⁻) = c := by
    simpa [c] using (zeroSum_pos_neg_mass_eq v hvsum).symm
  let nu0 : stdSimplex ℝ S := by
    refine ⟨fun s => (v s)⁺ / c, ?_, ?_⟩
    · intro s
      exact div_nonneg (posPart_nonneg _) hc.le
    · change (∑ s, (v s)⁺ / c) = 1
      rw [← Finset.sum_div]
      simp [c, hc.ne']
  let mu0 : stdSimplex ℝ S := by
    refine ⟨fun s => (v s)⁻ / c, ?_, ?_⟩
    · intro s
      exact div_nonneg (negPart_nonneg _) hc.le
    · change (∑ s, (v s)⁻ / c) = 1
      rw [← Finset.sum_div, hmass]
      exact div_self hc.ne'
  have hvrep : v = fun s => c * (nu0 s - mu0 s) := by
    funext s
    change v s = c * ((v s)⁺ / c - (v s)⁻ / c)
    field_simp [hc.ne']
    exact (posPart_sub_negPart (v s)).symm
  have hcesaro := scaled_cesaro_difference_of_residual_zero
    P hP v hres c nu0 mu0 hvrep
  rcases (UEOT.V3.FiniteCesaroInvariant.p_goa_01 P hP nu0).1 with
    ⟨nuStar, phi, hphi, hnuLim⟩
  rcases CompactSpace.tendsto_subseq
      (fun n => cesaroRow P hP mu0 (phi n)) with
    ⟨muStar, psi, hpsi, hmuLim⟩
  let theta : ℕ → ℕ := phi ∘ psi
  have htheta : StrictMono theta := hphi.comp hpsi
  have hnuTheta :
      Tendsto (cesaroRow P hP nu0 ∘ theta) atTop (𝓝 nuStar) := by
    exact hnuLim.comp hpsi.tendsto_atTop
  have hmuTheta :
      Tendsto (cesaroRow P hP mu0 ∘ theta) atTop (𝓝 muStar) := by
    simpa [theta, Function.comp_def] using hmuLim
  have hnuInvVec :=
    (UEOT.V3.FiniteCesaroInvariant.p_goa_01 P hP nu0).2
      nuStar theta htheta hnuTheta
  have hmuInvVec :=
    (UEOT.V3.FiniteCesaroInvariant.p_goa_01 P hP mu0).2
      muStar theta htheta hmuTheta
  have hnuInv : nuStar ∈ invariantLawSet P hP := by
    rw [mem_invariantLawSet]
    apply Subtype.ext
    exact hnuInvVec
  have hmuInv : muStar ∈ invariantLawSet P hP := by
    rw [mem_invariantLawSet]
    apply Subtype.ext
    exact hmuInvVec
  have hlimitRelation : v = fun s => c * (nuStar s - muStar s) := by
    funext s
    have hnuCoord :
        Tendsto (fun n => (cesaroRow P hP nu0 (theta n) : S → ℝ) s)
          atTop (𝓝 (nuStar s)) := by
      exact (tendsto_pi_nhds.mp
        (show Tendsto
          (fun n => (cesaroRow P hP nu0 (theta n) : S → ℝ))
          atTop (𝓝 (nuStar : S → ℝ)) from
            (continuous_subtype_val.tendsto nuStar).comp hnuTheta)) s
    have hmuCoord :
        Tendsto (fun n => (cesaroRow P hP mu0 (theta n) : S → ℝ) s)
          atTop (𝓝 (muStar s)) := by
      exact (tendsto_pi_nhds.mp
        (show Tendsto
          (fun n => (cesaroRow P hP mu0 (theta n) : S → ℝ))
          atTop (𝓝 (muStar : S → ℝ)) from
            (continuous_subtype_val.tendsto muStar).comp hmuTheta)) s
    have hscaled :
        Tendsto
          (fun n => c * ((cesaroRow P hP nu0 (theta n) : S → ℝ) s -
            (cesaroRow P hP mu0 (theta n) : S → ℝ) s))
          atTop (𝓝 (c * (nuStar s - muStar s))) := by
      exact (hnuCoord.sub hmuCoord).const_mul c
    have hconst :
        Tendsto
          (fun _n : ℕ => v s)
          atTop (𝓝 (v s)) := tendsto_const_nhds
    have heqseq :
        (fun n => c * ((cesaroRow P hP nu0 (theta n) : S → ℝ) s -
          (cesaroRow P hP mu0 (theta n) : S → ℝ) s)) =
          (fun _n : ℕ => v s) := by
      funext n
      symm
      exact congrFun (hcesaro (theta n)) s
    rw [heqseq] at hscaled
    exact tendsto_nhds_unique hconst hscaled
  have hne : muStar ≠ nuStar := by
    intro heq
    apply hvne
    rw [hlimitRelation]
    funext s
    rw [heq]
    simp
  exact ⟨muStar, nuStar, hmuInv, hnuInv, hne⟩

theorem restricted_injective_of_invariantLawSet_subsingleton
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hsub : (invariantLawSet P hP).Subsingleton) :
    Function.Injective (zeroSumResidualLinear P) := by
  by_contra hnot
  rw [Function.not_injective_iff] at hnot
  rcases hnot with ⟨x, y, hmap, hxy⟩
  let z := x - y
  have hz_ne : z ≠ 0 := sub_ne_zero.mpr hxy
  have hzmap : zeroSumResidualLinear P z = 0 := by
    rw [show z = x - y from rfl, map_sub, hmap, sub_self]
  let v : S → ℝ := ((z : zeroSumEuclidean (S := S)) : EuclideanSpace ℝ S).ofLp
  have hvsum : (∑ s, v s) = 0 := by
    exact (zeroSum_mem_iff v).1 (by simpa [v] using z.property)
  have hvne : v ≠ 0 := by
    intro hv0
    apply hz_ne
    apply Subtype.ext
    rw [WithLp.ext_iff]
    simpa [v] using hv0
  have hlinzero :
      residualEuclideanLinear P (WithLp.toLp 2 v) = 0 := by
    simpa [zeroSumResidualLinear, z, v] using hzmap
  have hres : signedResidual P v = 0 := by
    rw [← residualEuclideanLinear_ofLp]
    funext s
    have hs := congrArg (fun q : EuclideanSpace ℝ S => q.ofLp s) hlinzero
    simpa using hs
  rcases exists_distinct_invariant_laws_of_nonzero_fixed_zero_sum
      P hP v hvsum hvne hres with ⟨mu, nu, hmu, hnu, hmune⟩
  exact hmune (hsub hmu hnu)

theorem restricted_injective_iff_invariantLawSet_subsingleton
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S) :
    Function.Injective (zeroSumResidualLinear P) ↔
      (invariantLawSet P hP).Subsingleton := by
  constructor
  · exact invariantLawSet_subsingleton_of_restricted_injective P hP
  · exact restricted_injective_of_invariantLawSet_subsingleton P hP

end
end UEOT.V3.Compression.TopologyChangingGoaInvariantUniquenessIsolation

namespace UEOT.V3.Compression.TopologyChangingGoaInvariantUniquenessIsolation

open UEOT.V3
open UEOT.V3.FiniteDobrushin
open UEOT.V3.FiniteCesaroInvariant
open UEOT.V3.Compression.InvariantSetGaugeInvariance
open UEOT.V3.Compression.TopologyChangingGoaRestrictedResidualAdapter
open UEOT.V3.Compression.TopologyChangingGoaL1ResidualConorm

universe u
noncomputable section
variable {S : Type u} [Fintype S] [Nonempty S]
noncomputable local instance : DecidableEq S := Classical.decEq S

theorem l1ResidualConorm_pos_iff_invariantLawSet_subsingleton
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hcard : 1 < Fintype.card S) :
    0 < l1ResidualConorm P ↔
      (invariantLawSet P hP).Subsingleton := by
  rw [l1ResidualConorm_pos_iff_restricted_injective P hcard]
  exact restricted_injective_iff_invariantLawSet_subsingleton P hP

theorem invariantLawSet_nonempty
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S) :
    (invariantLawSet P hP).Nonempty := by
  let x0 : S := Classical.choice (inferInstance : Nonempty S)
  let mu0 : stdSimplex ℝ S := pureSimplex x0
  rcases (UEOT.V3.FiniteCesaroInvariant.p_goa_01 P hP mu0).1 with
    ⟨nu, phi, hphi, hlim⟩
  refine ⟨nu, ?_⟩
  rw [mem_invariantLawSet]
  apply Subtype.ext
  exact (UEOT.V3.FiniteCesaroInvariant.p_goa_01 P hP mu0).2
    nu phi hphi hlim

theorem invariantLawSet_subsingleton_iff_existsUnique
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S) :
    (invariantLawSet P hP).Subsingleton ↔
      ∃! mu : stdSimplex ℝ S, mu ∈ invariantLawSet P hP := by
  constructor
  · intro hsub
    rcases invariantLawSet_nonempty P hP with ⟨mu, hmu⟩
    refine ⟨mu, hmu, ?_⟩
    intro nu hnu
    exact hsub hnu hmu
  · rintro ⟨mu, hmu, huniq⟩
    intro a ha b hb
    exact (huniq a ha).trans (huniq b hb).symm

theorem l1ResidualConorm_pos_iff_unique_invariant_law
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hcard : 1 < Fintype.card S) :
    0 < l1ResidualConorm P ↔
      ∃! mu : stdSimplex ℝ S, mu ∈ invariantLawSet P hP := by
  rw [l1ResidualConorm_pos_iff_restricted_injective P hcard]
  rw [restricted_injective_iff_invariantLawSet_subsingleton P hP]
  exact invariantLawSet_subsingleton_iff_existsUnique P hP

end
end UEOT.V3.Compression.TopologyChangingGoaInvariantUniquenessIsolation
