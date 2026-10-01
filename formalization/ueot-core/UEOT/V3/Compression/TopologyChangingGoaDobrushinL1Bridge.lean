import UEOT.V3.Compression.TopologyChangingGoaL1ResidualConorm
import UEOT.V3.FiniteRecurrentDecompositionStability

/-!
# Dobrushin contraction as a canonical direct-L1 residual certificate

This module bridges the finite Dobrushin contraction geometry used by M-CF to
the canonical direct-L1 residual conorm developed in Track S.

The key theorem extends the usual simplex-TV contraction to the entire
zero-total-mass signed space with the exact same Dobrushin coefficient.  The
triangle inequality then gives a residual lower gain `1 - alpha(P)`.  Under a
strict Dobrushin margin this is a `ZeroSumL1Isolation` certificate, hence the
canonical direct-L1 conorm dominates the Dobrushin margin and its stationary
tracking radius is never worse than `epsilon / (1 - alpha(P))`.
-/

namespace UEOT.V3.Compression.TopologyChangingGoaDobrushinL1Bridge

open UEOT.V3
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.TopologyChangingGoaSpectralIsolation
open UEOT.V3.Compression.TopologyChangingGoaL1ResidualConorm
open UEOT.V3.Compression.TopologyChangingGoaL1ResidualAdapter
open UEOT.V3.Compression.TopologyChangingGoaRestrictedResidualAdapter
open UEOT.V3.Compression.InvariantSetGaugeInvariance

universe uS
noncomputable section
variable {S : Type uS} [Fintype S] [Nonempty S]
noncomputable local instance : DecidableEq S := Classical.decEq S

lemma signedL1_difference_eq_two_lawTV
    (mu nu : stdSimplex ℝ S) :
    signedL1 (fun s => nu s - mu s) = 2 * lawTV mu nu := by
  rw [UEOT.V3.FiniteRecurrentDecompositionStability.lawTV_eq_half_sum_abs]
  unfold signedL1
  have habs :
      (∑ s, |nu s - mu s|) = ∑ s, |mu.1 s - nu.1 s| := by
    apply Finset.sum_congr rfl
    intro s hs
    exact abs_sub_comm _ _
  rw [habs]
  ring

lemma signedL1_smul_of_nonneg
    (c : ℝ) (hc : 0 ≤ c) (v : S → ℝ) :
    signedL1 (fun s => c * v s) = c * signedL1 v := by
  unfold signedL1
  calc
    (∑ s, |c * v s|) = ∑ s, c * |v s| := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [abs_mul, abs_of_nonneg hc]
    _ = c * ∑ s, |v s| := by rw [Finset.mul_sum]

lemma signedL1_pos_of_ne_zero
    (v : S → ℝ) (hv0 : v ≠ 0) :
    0 < signedL1 v := by
  unfold signedL1
  apply Finset.sum_pos' (fun s hs => abs_nonneg _)
  have hex : ∃ s, v s ≠ 0 := by
    by_contra h
    push Not at h
    apply hv0
    funext s
    exact h s
  rcases hex with ⟨s, hs⟩
  exact ⟨s, Finset.mem_univ s, abs_pos.mpr hs⟩

lemma zeroSum_pos_neg_mass_eq
    (v : S → ℝ) (hv : (∑ s, v s) = 0) :
    (∑ s, (v s)⁺) = ∑ s, (v s)⁻ := by
  apply sub_eq_zero.mp
  rw [← Finset.sum_sub_distrib]
  simpa only [posPart_sub_negPart] using hv

lemma signedL1_eq_two_pos_mass
    (v : S → ℝ) (hv : (∑ s, v s) = 0) :
    signedL1 v = 2 * ∑ s, (v s)⁺ := by
  have heq := zeroSum_pos_neg_mass_eq v hv
  unfold signedL1
  calc
    (∑ s, |v s|) = ∑ s, ((v s)⁺ + (v s)⁻) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [posPart_add_negPart]
    _ = (∑ s, (v s)⁺) + ∑ s, (v s)⁻ := Finset.sum_add_distrib
    _ = 2 * ∑ s, (v s)⁺ := by rw [← heq]; ring

/-- Sharp Dobrushin contraction on the whole zero-mass signed L1 space. -/
theorem signedL1_vecMul_le_dobrushin
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (v : S → ℝ) (hv : (∑ s, v s) = 0) :
    signedL1 (Matrix.vecMul v P) ≤ dobrushinAlpha P hP * signedL1 v := by
  by_cases hv0 : v = 0
  · subst v
    simp [signedL1]
  · let c : ℝ := ∑ s, (v s)⁺
    have hl1 : signedL1 v = 2 * c := by
      simpa [c] using signedL1_eq_two_pos_mass v hv
    have hl1pos : 0 < signedL1 v := signedL1_pos_of_ne_zero v hv0
    have hc : 0 < c := by nlinarith
    have hmass : (∑ s, (v s)⁻) = c := by
      simpa [c] using (zeroSum_pos_neg_mass_eq v hv).symm
    let nu : stdSimplex ℝ S := by
      refine ⟨fun s => (v s)⁺ / c, ?_, ?_⟩
      · intro s
        exact div_nonneg (posPart_nonneg _) hc.le
      · change (∑ s, (v s)⁺ / c) = 1
        rw [← Finset.sum_div]
        simp [c, hc.ne']
    let mu : stdSimplex ℝ S := by
      refine ⟨fun s => (v s)⁻ / c, ?_, ?_⟩
      · intro s
        exact div_nonneg (negPart_nonneg _) hc.le
      · change (∑ s, (v s)⁻ / c) = 1
        rw [← Finset.sum_div, hmass]
        exact div_self hc.ne'
    have hvrep : v = fun s => c * (nu s - mu s) := by
      funext s
      change v s = c * ((v s)⁺ / c - (v s)⁻ / c)
      field_simp [hc.ne']
      exact (posPart_sub_negPart (v s)).symm
    have hinput : lawTV mu nu = 1 := by
      have hd := signedL1_difference_eq_two_lawTV mu nu
      have hscaled :
          signedL1 v = c * signedL1 (fun s => nu s - mu s) := by
        rw [hvrep]
        exact signedL1_smul_of_nonneg c hc.le _
      rw [hd, hl1] at hscaled
      nlinarith
    have hvec :
        Matrix.vecMul v P =
          fun s => c * ((step P hP nu) s - (step P hP mu) s) := by
      funext y
      rw [hvrep, Matrix.vecMul_apply_eq_sum]
      change (∑ x, (c * (nu x - mu x)) * P x y) =
        c * ((∑ x, nu x * P x y) - ∑ x, mu x * P x y)
      calc
        (∑ x, (c * (nu x - mu x)) * P x y)
            = ∑ x, c * ((nu x - mu x) * P x y) := by
                apply Finset.sum_congr rfl
                intro x hx
                ring
        _ = c * ∑ x, ((nu x - mu x) * P x y) := by
                rw [Finset.mul_sum]
        _ = c * ((∑ x, nu x * P x y) - ∑ x, mu x * P x y) := by
                congr 1
                rw [← Finset.sum_sub_distrib]
                apply Finset.sum_congr rfl
                intro x hx
                ring
    have hout :
        signedL1 (Matrix.vecMul v P) =
          c * (2 * lawTV (step P hP mu) (step P hP nu)) := by
      rw [hvec, signedL1_smul_of_nonneg c hc.le]
      rw [signedL1_difference_eq_two_lawTV]
    have htv := tv_step_le_dobrushin P hP mu nu
    rw [hout, hl1, hinput] at *
    nlinarith [hc]


lemma signedL1_sub_le_add (a b : S → ℝ) :
    signedL1 (fun s => a s - b s) ≤ signedL1 a + signedL1 b := by
  unfold signedL1
  calc
    (∑ s, |a s - b s|) ≤ ∑ s, (|a s| + |b s|) := by
      apply Finset.sum_le_sum
      intro s hs
      exact abs_sub _ _
    _ = (∑ s, |a s|) + ∑ s, |b s| := Finset.sum_add_distrib

/-- Dobrushin contraction directly lower-bounds the zero-mass residual gain. -/
theorem one_sub_dobrushin_signedL1_le_residual
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (v : S → ℝ) (hv : (∑ s, v s) = 0) :
    (1 - dobrushinAlpha P hP) * signedL1 v ≤
      signedL1 (signedResidual P v) := by
  have hcontract := signedL1_vecMul_le_dobrushin P hP v hv
  have htri := signedL1_sub_le_add
    (Matrix.vecMul v P) (signedResidual P v)
  have hid :
      (fun s => Matrix.vecMul v P s - signedResidual P v s) = v := by
    funext s
    unfold signedResidual
    change Matrix.vecMul v P s - (Matrix.vecMul v P s - v s) = v s
    ring
  rw [hid] at htri
  linarith

/-- Strict Dobrushin contraction is a direct-L1 residual-isolation certificate. -/
theorem dobrushin_l1Isolation
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (halpha : dobrushinAlpha P hP < 1) :
    ZeroSumL1Isolation P (1 - dobrushinAlpha P hP) := by
  refine ⟨sub_pos.mpr halpha, ?_⟩
  intro v hv
  exact one_sub_dobrushin_signedL1_le_residual P hP v hv

/-- On a nontrivial finite state space, the canonical direct-L1 conorm dominates
Dobrushin's contraction margin. -/
theorem one_sub_dobrushin_le_l1ResidualConorm
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hcard : 1 < Fintype.card S)
    (halpha : dobrushinAlpha P hP < 1) :
    1 - dobrushinAlpha P hP ≤ l1ResidualConorm P := by
  exact l1Isolation_le_l1ResidualConorm P hcard _
    (dobrushin_l1Isolation P hP halpha)

/-- Consequently the canonical direct-L1 stationary radius is never worse than
Dobrushin's standard `epsilon/(1-alpha)` radius. -/
theorem canonical_l1_radius_le_dobrushin_radius
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hcard : 1 < Fintype.card S)
    (halpha : dobrushinAlpha P hP < 1)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    epsilon / l1ResidualConorm P ≤
      epsilon / (1 - dobrushinAlpha P hP) := by
  exact canonical_l1_radius_le_of_isolation P hcard epsilon _ hepsilon
    (dobrushin_l1Isolation P hP halpha)


/-- Under the same strict source Dobrushin margin used by the M-CF lane, the
canonical direct-L1 residual theorem supplies stationary tracking at the finer
kernel-specific radius `epsilon / kappa1*(P)`. -/
theorem canonical_l1_stationary_tracking_of_dobrushin
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (Q : Matrix S S ℝ) (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (muStar : stdSimplex ℝ S)
    (hmuStar : step P hP muStar = muStar)
    (epsilon : ℝ)
    (hcard : 1 < Fintype.card S)
    (halpha : dobrushinAlpha P hP < 1)
    (hrow : ∀ x, crossRowTV P hP Q hQ x ≤ epsilon) :
    ∃ muhat : stdSimplex ℝ S,
      muhat ∈ invariantLawSet Q hQ ∧
      lawTV muStar muhat ≤ epsilon / l1ResidualConorm P := by
  have hiso := dobrushin_l1Isolation P hP halpha
  have hinj1 : Function.Injective (zeroSumResidualL1Linear P) :=
    l1_restricted_injective_of_l1Isolation P _ hiso
  have hinj : Function.Injective (zeroSumResidualLinear P) :=
    l2_restricted_injective_of_l1_restricted_injective P hinj1
  exact canonical_l1_stationary_tracking
    P hP Q hQ muStar hmuStar epsilon hcard hinj hrow

end
end UEOT.V3.Compression.TopologyChangingGoaDobrushinL1Bridge
