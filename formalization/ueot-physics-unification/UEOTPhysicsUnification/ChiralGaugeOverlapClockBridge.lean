import UEOT.V3.Compression.QuotientDescent
import UEOTPhysicsUnification.GaugeFlavorSelection
import UEOTPhysicsUnification.TopologicalCarrierAndIndex
import UEOTPhysicsUnification.LocalizedClockAndDiracAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Non-Perturbative Chiral Gauge-Fermion Neuberger Overlap, `(3,3,1)` Gravitational-Gauge Anomaly Cancellation & Autonomous Clock Coupling (`P-CHIRAL-CLOCK-02`)

Formalizes `NEXT_GATE` Frontier 2 in pure-kernel Lean 4 (`0 sorryAx`, `0 native_decide`, `0` custom axioms):

1. **Exact Lüscher / Ginsparg-Wilson Chiral Gauge Projector Algebra & Neuberger Overlap Realization**:
   - `modifiedChirality_sq_eq_one` & `luscher_projectors_idempotent_orthogonal_complete`:
     In any associative `ℝ`-algebra `R`, if `γ5^2 = 1` and `D * γ5 + γ5 * D = a • (D * γ5 * D)`,
     then Lüscher's lattice-modified chirality `γ̂5 := γ5 * (1 - a • D)` is an exact `(1 - a D)`-deformed
     involution (`γ̂5^2 = 1`), and `P̂_± := (1/2)(1 ± γ̂5)` satisfy `P̂_+^2 = P̂_+`, `P̂_-^2 = P̂_-`,
     `P̂_+ * P̂_- = 0`, `P̂_- * P̂_+ = 0`, and `P̂_+ + P̂_- = 1`.
   - `ginsparg_wilson_chirality_intertwining` & `luscher_chiral_gauge_factorization`:
     Proves `γ5 * D = -(D * γ̂5)`, `P_+ * D = D * P̂_-`, `P_- * D = D * P̂_+`, the exact asymmetric
     chiral gauge factorizations `P_+ * D * P̂_- = D * P̂_-` and `P_- * D * P̂_+ = D * P̂_+`, cross-sector
     decoupling `P_- * D * P̂_- = 0` and `P_+ * D * P̂_+ = 0`, and `P_+ * D * P̂_- + P_- * D * P̂_+ = D`.
   - `neubergerOverlap_gw_hermitian_and_luscher_index`:
     For finite complex matrices `γ5, V : Matrix n n ℂ` with `γ5ᴴ = γ5`, `γ5^2 = 1`, `Vᴴ = V`, `V^2 = 1`
     (`V = H_W (H_W^2)^{-1/2}`, `γ5 V = X (Xᴴ X)^{-1/2}`) and `a ≠ 0`, `D_ov := a⁻¹ • (1 + γ5 * V)`
     satisfies the exact Ginsparg-Wilson relation, `γ5`-Hermiticity `γ5 * D_ov * γ5 = D_ovᴴ`,
     normal Ginsparg-Wilson circle `D_ovᴴ * D_ov = D_ov * D_ovᴴ = a⁻¹ • (D_ov + D_ovᴴ)`, self-adjoint
     projectors `P̂_±ᴴ = P̂_±` (`γ̂5 = -V`), and exact Lüscher chiral index trace identity
     `Tr(P̂_+ - P_+) = -(a/2) Tr(γ5 * D_ov) = -Tr(P̂_- - P_-)`.
   - `luscher_weyl_bilinear_existsUnique_twoSidedDescend` & `luscher_index_gauge_orbit_existsUnique_descend`:
     Applies `UEOT.V3.Compression.QuotientDescent` (`existsUnique_twoSidedDescend` and `existsUnique_descend`)
     to prove unique descent of the Weyl fermion action to `(ran P_+) × (ran P̂_-)` and unique descent of
     the Lüscher chiral index onto gauge-equivalence classes.

2. **15-Weyl-Fermion `(3,3,1)` Gauge + Mixed Gravitational Anomaly Cancellation & Hypercharge Quantization**:
   - `sm_15weyl_complete_anomaly_cancellation`: One `(3,3,1)` Standard Model chiral generation
     `Q_L(3,2,1/6) ⊕ u_R^c(3̄,1,-2/3) ⊕ d_R^c(3̄,1,1/3) ⊕ L_L(1,2,-1/2) ⊕ e_R^c(1,1,1)` (`15` left-handed
     Weyl states, zero sterile right-handed neutrino required) simultaneously cancels all five gauge and
     gravitational anomalies (`[SU(3)_c]^2 U(1)_Y = 0`, `[SU(2)_L]^2 U(1)_Y = 0`, `[U(1)_Y]^3 = 0`,
     mixed gravitational-hypercharge `Tr(Y) = 0`, and Witten `SU(2)_L` doublet parity `3 + 1 = 4` even).
   - `sm_15weyl_gravitational_gauge_hypercharge_quantization`: Proves over `ℝ` that for `Y_Q ≠ 0`,
     requiring `Tr(Y) = 0` alongside the three gauge anomalies uniquely locks `(Y_L, Y_e, {Y_u, Y_d})`
     to `(-3 Y_Q, 6 Y_Q, {-4 Y_Q, 2 Y_Q})`, whereas omitting gravitational anomaly cancellation admits
     an unquantized vectorlike branch `(0, Y_u, -Y_u, 0, 0)`.

3. **Autonomous Positive Clock Lapse (`N(x) > 0`), Spectral Gap Symmetry & Normal-Ordered Particle-Hole Energy**:
   - `clockDressedDirac_hermitian_and_spectral_pairing` & `clockDressedDirac_strict_spectral_gap`:
     Coupling a gapped Dirac Hamiltonian `H_0` (`Δ_0 > 0`, `{Γ, H_0} = 0`) to any spatially inhomogeneous
     positive clock lapse `N_i ≥ N_min > 0` via symmetric half-density dressing `H_N = √N H_0 √N`
     preserves Hermiticity, exact `±E` particle-hole symmetry `{Γ, H_N} = 0`, and a strict spectral gap
     `‖H_N v‖_2^2 ≥ (N_min Δ_0)^2 ‖v‖_2^2` (`|E| ≥ N_min Δ_0 > 0` for all eigenmodes).
   - `normal_ordered_clock_dirac_positive_excitation_and_shift`: Slice `c`-number Dirac-sea subtraction
     preserves zero central commutator anomaly (`LocalizedClockAndDiracAlgebra.cnumber_normal_ordering_preserves_commutator`)
     while guaranteeing strictly positive particle-hole excitation energies and strictly positive
     clock-coupled excitation energy shifts under localized lapse swelling `N(x) = 1 + α(x) > 1`.
-/

namespace UEOTPhysicsUnification.ChiralGaugeOverlapClockBridge

open Matrix Function
open scoped BigOperators
open UEOT.V3.Compression.QuotientDescent

/-! ## 1. Exact Lüscher / Ginsparg-Wilson Chiral Gauge Projector Algebra -/

section AlgebraProjectors

variable {R : Type*} [Ring R] [Algebra ℝ R]

/-- Continuum/unmodified positive-chirality projector `P_+ = (1/2)(1 + γ5)`. -/
noncomputable def stdProjPlus (γ5 : R) : R :=
  algebraMap ℝ R (1 / 2) * (1 + γ5)

/-- Continuum/unmodified negative-chirality projector `P_- = (1/2)(1 - γ5)`. -/
noncomputable def stdProjMinus (γ5 : R) : R :=
  algebraMap ℝ R (1 / 2) * (1 - γ5)

/-- Lüscher's lattice-modified chirality operator `γ̂5 = γ5 (1 - a D)`. -/
noncomputable def modifiedChirality (a : ℝ) (γ5 D : R) : R :=
  γ5 * (1 - algebraMap ℝ R a * D)

/-- Asymmetric Lüscher positive-chirality projector `P̂_+ = (1/2)(1 + γ̂5)`. -/
noncomputable def luscherProjPlus (a : ℝ) (γ5 D : R) : R :=
  algebraMap ℝ R (1 / 2) * (1 + modifiedChirality a γ5 D)

/-- Asymmetric Lüscher negative-chirality projector `P̂_- = (1/2)(1 - γ̂5)`. -/
noncomputable def luscherProjMinus (a : ℝ) (γ5 D : R) : R :=
  algebraMap ℝ R (1 / 2) * (1 - modifiedChirality a γ5 D)

/-- Universal projector algebra generated by any involution `J^2 = 1` in an associative `ℝ`-algebra. -/
theorem involution_projectors_idempotent_orthogonal
    {J : R} (hJ : J * J = 1) :
    let Qp := algebraMap ℝ R (1 / 2) * (1 + J)
    let Qm := algebraMap ℝ R (1 / 2) * (1 - J)
    Qp * Qp = Qp ∧
      Qm * Qm = Qm ∧
      Qp * Qm = 0 ∧
      Qm * Qp = 0 ∧
      Qp + Qm = 1 := by
  intro Qp Qm
  have hcJ : (1 + J) * algebraMap ℝ R (1 / 2) = algebraMap ℝ R (1 / 2) * (1 + J) :=
    (Algebra.commutes (1 / 2 : ℝ) (1 + J)).symm
  have hcJm : (1 - J) * algebraMap ℝ R (1 / 2) = algebraMap ℝ R (1 / 2) * (1 - J) :=
    (Algebra.commutes (1 / 2 : ℝ) (1 - J)).symm
  have hhalf_sq : algebraMap ℝ R (1 / 2) * algebraMap ℝ R (1 / 2) = algebraMap ℝ R (1 / 4) := by
    rw [← map_mul]
    norm_num
  have hhalf_two : algebraMap ℝ R (1 / 4) * (2 : R) = algebraMap ℝ R (1 / 2) := by
    have h2 : (2 : R) = algebraMap ℝ R 2 := (map_ofNat (algebraMap ℝ R) 2).symm
    rw [h2, ← map_mul]
    norm_num
  have hhalf_sum : algebraMap ℝ R (1 / 2) + algebraMap ℝ R (1 / 2) = 1 := by
    rw [← map_add]
    norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp [Qp]
    calc
      algebraMap ℝ R (1 / 2) * (1 + J) * (algebraMap ℝ R (1 / 2) * (1 + J))
          = (algebraMap ℝ R (1 / 2) * ((1 + J) * algebraMap ℝ R (1 / 2))) * (1 + J) := by
            noncomm_ring
      _ = (algebraMap ℝ R (1 / 2) * algebraMap ℝ R (1 / 2)) * ((1 + J) * (1 + J)) := by
            rw [hcJ]
            noncomm_ring
      _ = algebraMap ℝ R (1 / 4) * ((2 : R) * (1 + J)) := by
            rw [hhalf_sq]
            have hexp : (1 + J) * (1 + J) = (2 : R) * (1 + J) := by
              calc
                (1 + J) * (1 + J) = 1 + J * J + (2 : R) * J := by noncomm_ring
                _ = 1 + 1 + (2 : R) * J := by rw [hJ]
                _ = (2 : R) * (1 + J) := by noncomm_ring
            rw [hexp]
      _ = (algebraMap ℝ R (1 / 4) * (2 : R)) * (1 + J) := by noncomm_ring
      _ = algebraMap ℝ R (1 / 2) * (1 + J) := by rw [hhalf_two]
  · dsimp [Qm]
    calc
      algebraMap ℝ R (1 / 2) * (1 - J) * (algebraMap ℝ R (1 / 2) * (1 - J))
          = (algebraMap ℝ R (1 / 2) * ((1 - J) * algebraMap ℝ R (1 / 2))) * (1 - J) := by
            noncomm_ring
      _ = (algebraMap ℝ R (1 / 2) * algebraMap ℝ R (1 / 2)) * ((1 - J) * (1 - J)) := by
            rw [hcJm]
            noncomm_ring
      _ = algebraMap ℝ R (1 / 4) * ((2 : R) * (1 - J)) := by
            rw [hhalf_sq]
            have hexp : (1 - J) * (1 - J) = (2 : R) * (1 - J) := by
              calc
                (1 - J) * (1 - J) = 1 + J * J - (2 : R) * J := by noncomm_ring
                _ = 1 + 1 - (2 : R) * J := by rw [hJ]
                _ = (2 : R) * (1 - J) := by noncomm_ring
            rw [hexp]
      _ = (algebraMap ℝ R (1 / 4) * (2 : R)) * (1 - J) := by noncomm_ring
      _ = algebraMap ℝ R (1 / 2) * (1 - J) := by rw [hhalf_two]
  · dsimp [Qp, Qm]
    calc
      algebraMap ℝ R (1 / 2) * (1 + J) * (algebraMap ℝ R (1 / 2) * (1 - J))
          = (algebraMap ℝ R (1 / 2) * ((1 + J) * algebraMap ℝ R (1 / 2))) * (1 - J) := by
            noncomm_ring
      _ = (algebraMap ℝ R (1 / 2) * algebraMap ℝ R (1 / 2)) * (1 - J * J) := by
            rw [hcJ]
            noncomm_ring
      _ = 0 := by rw [hJ]; noncomm_ring
  · dsimp [Qp, Qm]
    calc
      algebraMap ℝ R (1 / 2) * (1 - J) * (algebraMap ℝ R (1 / 2) * (1 + J))
          = (algebraMap ℝ R (1 / 2) * ((1 - J) * algebraMap ℝ R (1 / 2))) * (1 + J) := by
            noncomm_ring
      _ = (algebraMap ℝ R (1 / 2) * algebraMap ℝ R (1 / 2)) * (1 - J * J) := by
            rw [hcJm]
            noncomm_ring
      _ = 0 := by rw [hJ]; noncomm_ring
  · dsimp [Qp, Qm]
    calc
      algebraMap ℝ R (1 / 2) * (1 + J) + algebraMap ℝ R (1 / 2) * (1 - J)
          = algebraMap ℝ R (1 / 2) + algebraMap ℝ R (1 / 2) := by noncomm_ring
      _ = 1 := hhalf_sum

/-- **Exact `(1 - a D)`-Deformed Chirality Involution (`γ̂5^2 = 1`)**:
Whenever `γ5^2 = 1` and `D` obeys the Ginsparg-Wilson relation `D γ5 + γ5 D = a D γ5 D`,
the modified chirality `γ̂5 = γ5 (1 - a D)` satisfies `γ̂5 * γ̂5 = 1` identically. -/
theorem modifiedChirality_sq_eq_one
    (a : ℝ) {γ5 D : R}
    (hγ5 : γ5 * γ5 = 1)
    (hGW : D * γ5 + γ5 * D = algebraMap ℝ R a * (D * γ5 * D)) :
    modifiedChirality a γ5 D * modifiedChirality a γ5 D = 1 := by
  unfold modifiedChirality
  let aR := algebraMap ℝ R a
  have hca_γ5 : γ5 * aR = aR * γ5 := (Algebra.commutes a γ5).symm
  have hca_Dγ5 : (D * γ5) * aR = aR * (D * γ5) := (Algebra.commutes a (D * γ5)).symm
  have hGW' : aR * (D * γ5 * D) = D * γ5 + γ5 * D := hGW.symm
  calc
    γ5 * (1 - aR * D) * (γ5 * (1 - aR * D))
        = (γ5 * γ5) * (1 - aR * D) - aR * (γ5 * D * γ5) + aR * γ5 * (aR * (D * γ5 * D)) := by
          have hc1 : γ5 * (aR * D) * γ5 = aR * (γ5 * D * γ5) := by
            calc
              γ5 * (aR * D) * γ5 = (γ5 * aR) * D * γ5 := by noncomm_ring
              _ = aR * (γ5 * D * γ5) := by rw [hca_γ5]; noncomm_ring
          have hc2 : γ5 * (aR * D) * (γ5 * (aR * D)) = aR * γ5 * (aR * (D * γ5 * D)) := by
            calc
              γ5 * (aR * D) * (γ5 * (aR * D))
                  = (γ5 * aR) * ((D * γ5) * aR) * D := by noncomm_ring
              _ = aR * γ5 * (aR * (D * γ5 * D)) := by rw [hca_γ5, hca_Dγ5]; noncomm_ring
          calc
            γ5 * (1 - aR * D) * (γ5 * (1 - aR * D))
                = (γ5 * γ5) * (1 - aR * D) - γ5 * (aR * D) * γ5 +
                    γ5 * (aR * D) * (γ5 * (aR * D)) := by noncomm_ring
            _ = (γ5 * γ5) * (1 - aR * D) - aR * (γ5 * D * γ5) +
                  aR * γ5 * (aR * (D * γ5 * D)) := by rw [hc1, hc2]
    _ = 1 - aR * D - aR * (γ5 * D * γ5) + aR * γ5 * (D * γ5 + γ5 * D) := by
          rw [hγ5, hGW', one_mul]
    _ = 1 - aR * D - aR * (γ5 * D * γ5) + aR * (γ5 * D * γ5) + aR * ((γ5 * γ5) * D) := by
          noncomm_ring
    _ = 1 := by rw [hγ5]; noncomm_ring

/-- **Complete Lüscher & Continuum Chiral Projector Algebra**:
Under `γ5^2 = 1` and the Ginsparg-Wilson relation, both `(P_+, P_-)` and `(P̂_+, P̂_-)` form exact
complete pairs of mutually orthogonal idempotents. -/
theorem luscher_projectors_idempotent_orthogonal_complete
    (a : ℝ) {γ5 D : R}
    (hγ5 : γ5 * γ5 = 1)
    (hGW : D * γ5 + γ5 * D = algebraMap ℝ R a * (D * γ5 * D)) :
    (stdProjPlus γ5 * stdProjPlus γ5 = stdProjPlus γ5 ∧
      stdProjMinus γ5 * stdProjMinus γ5 = stdProjMinus γ5 ∧
      stdProjPlus γ5 * stdProjMinus γ5 = 0 ∧
      stdProjMinus γ5 * stdProjPlus γ5 = 0 ∧
      stdProjPlus γ5 + stdProjMinus γ5 = 1) ∧
    (luscherProjPlus a γ5 D * luscherProjPlus a γ5 D = luscherProjPlus a γ5 D ∧
      luscherProjMinus a γ5 D * luscherProjMinus a γ5 D = luscherProjMinus a γ5 D ∧
      luscherProjPlus a γ5 D * luscherProjMinus a γ5 D = 0 ∧
      luscherProjMinus a γ5 D * luscherProjPlus a γ5 D = 0 ∧
      luscherProjPlus a γ5 D + luscherProjMinus a γ5 D = 1) := by
  refine ⟨?_, ?_⟩
  · simpa [stdProjPlus, stdProjMinus] using involution_projectors_idempotent_orthogonal hγ5
  · simpa [luscherProjPlus, luscherProjMinus] using
      involution_projectors_idempotent_orthogonal (modifiedChirality_sq_eq_one a hγ5 hGW)

/-- **Ginsparg-Wilson Chirality Intertwining Identity (`γ5 D = - D γ̂5`)**:
The Ginsparg-Wilson relation implies exact intertwining `γ5 * D = -(D * γ̂5)` and
`P_+ * D = D * P̂_-`, `P_- * D = D * P̂_+`. -/
theorem ginsparg_wilson_chirality_intertwining
    (a : ℝ) {γ5 D : R}
    (hGW : D * γ5 + γ5 * D = algebraMap ℝ R a * (D * γ5 * D)) :
    γ5 * D = -(D * modifiedChirality a γ5 D) ∧
      stdProjPlus γ5 * D = D * luscherProjMinus a γ5 D ∧
      stdProjMinus γ5 * D = D * luscherProjPlus a γ5 D := by
  let aR := algebraMap ℝ R a
  have hca_Dγ5 : (D * γ5) * aR = aR * (D * γ5) := (Algebra.commutes a (D * γ5)).symm
  have hc_half : D * algebraMap ℝ R (1 / 2) = algebraMap ℝ R (1 / 2) * D :=
    (Algebra.commutes (1 / 2 : ℝ) D).symm
  have hinter : γ5 * D = -(D * modifiedChirality a γ5 D) := by
    unfold modifiedChirality
    have hmul : D * (γ5 * (aR * D)) = aR * (D * γ5 * D) := by
      calc
        D * (γ5 * (aR * D)) = ((D * γ5) * aR) * D := by noncomm_ring
        _ = aR * (D * γ5 * D) := by rw [hca_Dγ5]; noncomm_ring
    calc
      γ5 * D = - (D * γ5) + (D * γ5 + γ5 * D) := by abel
      _ = - (D * γ5) + aR * (D * γ5 * D) := by rw [hGW]
      _ = - (D * γ5) + D * (γ5 * (aR * D)) := by rw [← hmul]
      _ = -(D * (γ5 * (1 - aR * D))) := by noncomm_ring
  refine ⟨hinter, ?_, ?_⟩
  · unfold stdProjPlus luscherProjMinus
    calc
      algebraMap ℝ R (1 / 2) * (1 + γ5) * D
          = algebraMap ℝ R (1 / 2) * (D + γ5 * D) := by noncomm_ring
      _ = (algebraMap ℝ R (1 / 2) * D) * (1 - modifiedChirality a γ5 D) := by
            rw [hinter]
            noncomm_ring
      _ = D * (algebraMap ℝ R (1 / 2) * (1 - modifiedChirality a γ5 D)) := by
            rw [← hc_half]
            noncomm_ring
  · unfold stdProjMinus luscherProjPlus
    calc
      algebraMap ℝ R (1 / 2) * (1 - γ5) * D
          = algebraMap ℝ R (1 / 2) * (D - γ5 * D) := by noncomm_ring
      _ = (algebraMap ℝ R (1 / 2) * D) * (1 + modifiedChirality a γ5 D) := by
            rw [hinter]
            noncomm_ring
      _ = D * (algebraMap ℝ R (1 / 2) * (1 + modifiedChirality a γ5 D)) := by
            rw [← hc_half]
            noncomm_ring

/-- **Lüscher's Chiral Gauge Factorization Theorem**:
Under `γ5^2 = 1` and `D γ5 + γ5 D = a D γ5 D`, the Dirac operator splits cleanly into decoupled
left- and right-handed Weyl blocks without Nielsen-Ninomiya doubler mixing:
`P_+ D P̂_- = D P̂_-`, `P_- D P̂_+ = D P̂_+`, `P_- D P̂_- = 0`, `P_+ D P̂_+ = 0`, and
`P_+ D P̂_- + P_- D P̂_+ = D`. -/
theorem luscher_chiral_gauge_factorization
    (a : ℝ) {γ5 D : R}
    (hγ5 : γ5 * γ5 = 1)
    (hGW : D * γ5 + γ5 * D = algebraMap ℝ R a * (D * γ5 * D)) :
    stdProjPlus γ5 * D * luscherProjMinus a γ5 D = D * luscherProjMinus a γ5 D ∧
      stdProjMinus γ5 * D * luscherProjPlus a γ5 D = D * luscherProjPlus a γ5 D ∧
      stdProjMinus γ5 * D * luscherProjMinus a γ5 D = 0 ∧
      stdProjPlus γ5 * D * luscherProjPlus a γ5 D = 0 ∧
      stdProjPlus γ5 * D * luscherProjMinus a γ5 D +
        stdProjMinus γ5 * D * luscherProjPlus a γ5 D = D := by
  obtain ⟨_, hp_sq, hm_sq, hpm_zero, hmp_zero, hsum_one⟩ :=
    luscher_projectors_idempotent_orthogonal_complete a hγ5 hGW
  obtain ⟨_, hPD_minus, hMD_plus⟩ := ginsparg_wilson_chirality_intertwining a hGW
  have h1 : stdProjPlus γ5 * D * luscherProjMinus a γ5 D = D * luscherProjMinus a γ5 D := by
    rw [hPD_minus, mul_assoc, hm_sq]
  have h2 : stdProjMinus γ5 * D * luscherProjPlus a γ5 D = D * luscherProjPlus a γ5 D := by
    rw [hMD_plus, mul_assoc, hp_sq]
  have h3 : stdProjMinus γ5 * D * luscherProjMinus a γ5 D = 0 := by
    rw [hMD_plus, mul_assoc, hpm_zero, mul_zero]
  have h4 : stdProjPlus γ5 * D * luscherProjPlus a γ5 D = 0 := by
    rw [hPD_minus, mul_assoc, hmp_zero, mul_zero]
  refine ⟨h1, h2, h3, h4, ?_⟩
  rw [h1, h2, ← mul_add, add_comm (luscherProjMinus a γ5 D) (luscherProjPlus a γ5 D),
    hsum_one, mul_one]

end AlgebraProjectors

/-! ### Finite-Lattice Neuberger Overlap Matrix Realization & Quotient Descent -/

section NeubergerOverlapMatrices

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Finite-lattice Neuberger Overlap Dirac matrix `D_ov = a⁻¹ • (1 + γ5 * V)`, where `V` is the
Hermitian sign operator `V = H_W (H_W^2)^{-1/2}` (`H_W = γ5 X`, so `γ5 * V = X (Xᴴ X)^{-1/2}`). -/
noncomputable def neubergerOverlap (a : ℝ) (γ5 V : Matrix n n ℂ) : Matrix n n ℂ :=
  algebraMap ℝ (Matrix n n ℂ) (1 / a) * (1 + γ5 * V)

/-- **Neuberger Overlap Realization & Lüscher Index Theorem on `Matrix n n ℂ`**:
For `a ≠ 0`, `γ5ᴴ = γ5`, `γ5^2 = 1`, `Vᴴ = V`, and `V^2 = 1`, `D_ov = a⁻¹ (1 + γ5 V)` satisfies:
1. Exact Ginsparg-Wilson relation `D_ov * γ5 + γ5 * D_ov = a • (D_ov * γ5 * D_ov)`,
2. `γ5`-Hermiticity `γ5 * D_ov * γ5 = D_ovᴴ`,
3. Normal Ginsparg-Wilson circle `D_ovᴴ * D_ov = D_ov * D_ovᴴ = a⁻¹ • (D_ov + D_ovᴴ)`,
4. Exact Hermitian chirality `γ̂5 = -V`, `P̂_+ᴴ = P̂_+`, `P̂_-ᴴ = P̂_-`,
5. Exact Lüscher chiral index trace identity:
   `Tr(P̂_+ - P_+) = -((a / 2 : ℝ) : ℂ) * Tr(γ5 * D_ov)` and
   `Tr(P̂_- - P_-) = ((a / 2 : ℝ) : ℂ) * Tr(γ5 * D_ov)`. -/
theorem neubergerOverlap_gw_hermitian_and_luscher_index
    {a : ℝ} (ha : a ≠ 0) {γ5 V : Matrix n n ℂ}
    (hγ5_herm : γ5ᴴ = γ5) (hγ5_sq : γ5 * γ5 = 1)
    (hV_herm : Vᴴ = V) (hV_sq : V * V = 1) :
    let D_ov := neubergerOverlap a γ5 V
    (D_ov * γ5 + γ5 * D_ov = algebraMap ℝ (Matrix n n ℂ) a * (D_ov * γ5 * D_ov)) ∧
      (γ5 * D_ov * γ5 = D_ovᴴ) ∧
      (D_ovᴴ * D_ov = algebraMap ℝ (Matrix n n ℂ) (1 / a) * (D_ov + D_ovᴴ) ∧
        D_ov * D_ovᴴ = D_ovᴴ * D_ov) ∧
      (modifiedChirality a γ5 D_ov = -V ∧
        (luscherProjPlus a γ5 D_ov)ᴴ = luscherProjPlus a γ5 D_ov ∧
        (luscherProjMinus a γ5 D_ov)ᴴ = luscherProjMinus a γ5 D_ov) ∧
      ((luscherProjPlus a γ5 D_ov - stdProjPlus γ5).trace =
          -(((a / 2 : ℝ)) : ℂ) * (γ5 * D_ov).trace ∧
        (luscherProjMinus a γ5 D_ov - stdProjMinus γ5).trace =
          (((a / 2 : ℝ)) : ℂ) * (γ5 * D_ov).trace) := by
  intro D_ov
  let invA : Matrix n n ℂ := algebraMap ℝ (Matrix n n ℂ) (1 / a)
  let aM : Matrix n n ℂ := algebraMap ℝ (Matrix n n ℂ) a
  have ha_inv : aM * invA = 1 := by
    dsimp [aM, invA]
    rw [← map_mul, mul_one_div_cancel ha, map_one]
  have hinv_a : invA * aM = 1 := by
    dsimp [aM, invA]
    rw [← map_mul, one_div_mul_cancel ha, map_one]
  have hinvA_herm : invAᴴ = invA := by
    dsimp [invA]
    rw [Algebra.algebraMap_eq_smul_one, conjTranspose_smul, conjTranspose_one]
    rfl
  have hD_herm : D_ovᴴ = invA * (1 + V * γ5) := by
    dsimp [D_ov, neubergerOverlap]
    rw [conjTranspose_mul, conjTranspose_add, conjTranspose_one, conjTranspose_mul,
      hV_herm, hγ5_herm, hinvA_herm]
    exact (Algebra.commutes (1 / a) (1 + V * γ5)).symm
  have hGW : D_ov * γ5 + γ5 * D_ov = aM * (D_ov * γ5 * D_ov) := by
    dsimp [D_ov, neubergerOverlap]
    have hc_γ5 : γ5 * invA = invA * γ5 := (Algebra.commutes (1 / a) γ5).symm
    have hc_mid : ((1 + γ5 * V) * γ5) * invA = invA * ((1 + γ5 * V) * γ5) :=
      (Algebra.commutes (1 / a) ((1 + γ5 * V) * γ5)).symm
    have hcore : (1 + γ5 * V) * γ5 * (1 + γ5 * V) = (1 + γ5 * V) * γ5 + γ5 * (1 + γ5 * V) := by
      calc
        (1 + γ5 * V) * γ5 * (1 + γ5 * V)
            = γ5 + γ5 * V * γ5 + (γ5 * γ5) * V + γ5 * (V * (γ5 * γ5) * V) := by noncomm_ring
        _ = γ5 + γ5 * V * γ5 + 1 * V + γ5 * (V * 1 * V) := by rw [hγ5_sq]
        _ = γ5 + γ5 * V * γ5 + V + γ5 * (V * V) := by noncomm_ring
        _ = γ5 + γ5 * V * γ5 + (γ5 * γ5) * V + γ5 * 1 := by rw [hV_sq, hγ5_sq, one_mul]
        _ = (1 + γ5 * V) * γ5 + γ5 * (1 + γ5 * V) := by noncomm_ring
    calc
      invA * (1 + γ5 * V) * γ5 + γ5 * (invA * (1 + γ5 * V))
          = invA * ((1 + γ5 * V) * γ5) + (γ5 * invA) * (1 + γ5 * V) := by noncomm_ring
      _ = invA * ((1 + γ5 * V) * γ5 + γ5 * (1 + γ5 * V)) := by
            rw [hc_γ5]
            noncomm_ring
      _ = (aM * invA) * invA * ((1 + γ5 * V) * γ5 * (1 + γ5 * V)) := by
            rw [ha_inv, ← hcore]
            noncomm_ring
      _ = aM * (invA * (((1 + γ5 * V) * γ5) * invA) * (1 + γ5 * V)) := by
            rw [hc_mid]
            noncomm_ring
      _ = aM * (invA * (1 + γ5 * V) * γ5 * (invA * (1 + γ5 * V))) := by noncomm_ring
  have hγ5_herm_D : γ5 * D_ov * γ5 = D_ovᴴ := by
    rw [hD_herm]
    dsimp [D_ov, neubergerOverlap]
    have hc_γ5 : γ5 * invA = invA * γ5 := (Algebra.commutes (1 / a) γ5).symm
    calc
      γ5 * (invA * (1 + γ5 * V)) * γ5
          = (γ5 * invA) * (γ5 + γ5 * V * γ5) := by noncomm_ring
      _ = invA * (γ5 * γ5 + (γ5 * γ5) * V * γ5) := by rw [hc_γ5]; noncomm_ring
      _ = invA * (1 + V * γ5) := by rw [hγ5_sq]; noncomm_ring
  have hcircle1 : D_ovᴴ * D_ov = invA * (D_ov + D_ovᴴ) := by
    rw [hD_herm]
    dsimp [D_ov, neubergerOverlap]
    have hc : (1 + V * γ5) * invA = invA * (1 + V * γ5) :=
      (Algebra.commutes (1 / a) (1 + V * γ5)).symm
    have hprod : (1 + V * γ5) * (1 + γ5 * V) = (1 + γ5 * V) + (1 + V * γ5) := by
      calc
        (1 + V * γ5) * (1 + γ5 * V) = 1 + γ5 * V + V * γ5 + V * (γ5 * γ5) * V := by noncomm_ring
        _ = 1 + γ5 * V + V * γ5 + V * V := by rw [hγ5_sq]; noncomm_ring
        _ = (1 + γ5 * V) + (1 + V * γ5) := by rw [hV_sq]; abel
    calc
      invA * (1 + V * γ5) * (invA * (1 + γ5 * V))
          = invA * (((1 + V * γ5) * invA) * (1 + γ5 * V)) := by noncomm_ring
      _ = invA * (invA * ((1 + V * γ5) * (1 + γ5 * V))) := by rw [hc]; noncomm_ring
      _ = invA * (invA * (1 + γ5 * V) + invA * (1 + V * γ5)) := by rw [hprod]; noncomm_ring
  have hcircle2 : D_ov * D_ovᴴ = D_ovᴴ * D_ov := by
    rw [hcircle1, hD_herm]
    dsimp [D_ov, neubergerOverlap]
    have hc : (1 + γ5 * V) * invA = invA * (1 + γ5 * V) :=
      (Algebra.commutes (1 / a) (1 + γ5 * V)).symm
    have hprod : (1 + γ5 * V) * (1 + V * γ5) = (1 + γ5 * V) + (1 + V * γ5) := by
      calc
        (1 + γ5 * V) * (1 + V * γ5) = 1 + γ5 * V + V * γ5 + γ5 * (V * V) * γ5 := by noncomm_ring
        _ = 1 + γ5 * V + V * γ5 + γ5 * γ5 := by rw [hV_sq]; noncomm_ring
        _ = (1 + γ5 * V) + (1 + V * γ5) := by rw [hγ5_sq]; abel
    calc
      invA * (1 + γ5 * V) * (invA * (1 + V * γ5))
          = invA * (((1 + γ5 * V) * invA) * (1 + V * γ5)) := by noncomm_ring
      _ = invA * (invA * ((1 + γ5 * V) * (1 + V * γ5))) := by rw [hc]; noncomm_ring
      _ = invA * (invA * (1 + γ5 * V) + invA * (1 + V * γ5)) := by rw [hprod]; noncomm_ring
  have hmod_negV : modifiedChirality a γ5 D_ov = -V := by
    unfold modifiedChirality
    dsimp [D_ov, neubergerOverlap]
    calc
      γ5 * (1 - aM * (invA * (1 + γ5 * V)))
          = γ5 * (1 - (aM * invA) * (1 + γ5 * V)) := by noncomm_ring
      _ = γ5 * (1 - (1 + γ5 * V)) := by rw [ha_inv]; noncomm_ring
      _ = -((γ5 * γ5) * V) := by noncomm_ring
      _ = -V := by rw [hγ5_sq]; noncomm_ring
  have hhalf_herm : (algebraMap ℝ (Matrix n n ℂ) (1 / 2))ᴴ =
      algebraMap ℝ (Matrix n n ℂ) (1 / 2) := by
    rw [Algebra.algebraMap_eq_smul_one, conjTranspose_smul, conjTranspose_one]
    rfl
  have hPplus_herm : (luscherProjPlus a γ5 D_ov)ᴴ = luscherProjPlus a γ5 D_ov := by
    unfold luscherProjPlus
    rw [hmod_negV, conjTranspose_mul, conjTranspose_add, conjTranspose_one, conjTranspose_neg,
      hV_herm, hhalf_herm]
    exact (Algebra.commutes (1 / 2 : ℝ) (1 + -V)).symm
  have hPminus_herm : (luscherProjMinus a γ5 D_ov)ᴴ = luscherProjMinus a γ5 D_ov := by
    unfold luscherProjMinus
    rw [hmod_negV, conjTranspose_mul, conjTranspose_sub, conjTranspose_one, conjTranspose_neg,
      hV_herm, hhalf_herm]
    exact (Algebra.commutes (1 / 2 : ℝ) (1 - -V)).symm
  have hdiff_plus :
      luscherProjPlus a γ5 D_ov - stdProjPlus γ5 =
        -(a / 2 : ℝ) • (γ5 * D_ov) := by
    unfold luscherProjPlus stdProjPlus modifiedChirality
    have hca : γ5 * (aM * D_ov) = aM * (γ5 * D_ov) := by
      have hc : γ5 * aM = aM * γ5 := (Algebra.commutes a γ5).symm
      calc
        γ5 * (aM * D_ov) = (γ5 * aM) * D_ov := by noncomm_ring
        _ = aM * (γ5 * D_ov) := by rw [hc]; noncomm_ring
    have h1 :
        algebraMap ℝ (Matrix n n ℂ) (1 / 2) * (1 + γ5 * (1 - aM * D_ov)) -
            algebraMap ℝ (Matrix n n ℂ) (1 / 2) * (1 + γ5) =
          -(algebraMap ℝ (Matrix n n ℂ) (1 / 2) * aM) * (γ5 * D_ov) := by
      calc
        algebraMap ℝ (Matrix n n ℂ) (1 / 2) * (1 + γ5 * (1 - aM * D_ov)) -
            algebraMap ℝ (Matrix n n ℂ) (1 / 2) * (1 + γ5)
            = -(algebraMap ℝ (Matrix n n ℂ) (1 / 2) * (γ5 * (aM * D_ov))) := by noncomm_ring
        _ = -(algebraMap ℝ (Matrix n n ℂ) (1 / 2) * aM) * (γ5 * D_ov) := by
              rw [hca]
              noncomm_ring
    rw [h1]
    have hmul_map : algebraMap ℝ (Matrix n n ℂ) (1 / 2) * aM =
        algebraMap ℝ (Matrix n n ℂ) (a / 2) := by
      dsimp [aM]
      rw [← map_mul]
      ring_nf
    rw [hmul_map, Algebra.algebraMap_eq_smul_one, neg_mul, smul_mul_assoc, one_mul, ← neg_smul]
  have hdiff_minus :
      luscherProjMinus a γ5 D_ov - stdProjMinus γ5 =
        (a / 2 : ℝ) • (γ5 * D_ov) := by
    unfold luscherProjMinus stdProjMinus modifiedChirality
    have hca : γ5 * (aM * D_ov) = aM * (γ5 * D_ov) := by
      have hc : γ5 * aM = aM * γ5 := (Algebra.commutes a γ5).symm
      calc
        γ5 * (aM * D_ov) = (γ5 * aM) * D_ov := by noncomm_ring
        _ = aM * (γ5 * D_ov) := by rw [hc]; noncomm_ring
    have h1 :
        algebraMap ℝ (Matrix n n ℂ) (1 / 2) * (1 - γ5 * (1 - aM * D_ov)) -
            algebraMap ℝ (Matrix n n ℂ) (1 / 2) * (1 - γ5) =
          (algebraMap ℝ (Matrix n n ℂ) (1 / 2) * aM) * (γ5 * D_ov) := by
      calc
        algebraMap ℝ (Matrix n n ℂ) (1 / 2) * (1 - γ5 * (1 - aM * D_ov)) -
            algebraMap ℝ (Matrix n n ℂ) (1 / 2) * (1 - γ5)
            = algebraMap ℝ (Matrix n n ℂ) (1 / 2) * (γ5 * (aM * D_ov)) := by noncomm_ring
        _ = (algebraMap ℝ (Matrix n n ℂ) (1 / 2) * aM) * (γ5 * D_ov) := by
              rw [hca]
              noncomm_ring
    rw [h1]
    have hmul_map : algebraMap ℝ (Matrix n n ℂ) (1 / 2) * aM =
        algebraMap ℝ (Matrix n n ℂ) (a / 2) := by
      dsimp [aM]
      rw [← map_mul]
      ring_nf
    rw [hmul_map, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  refine ⟨hGW, hγ5_herm_D, ⟨hcircle1, hcircle2⟩, ⟨hmod_negV, hPplus_herm, hPminus_herm⟩, ?_, ?_⟩
  · rw [hdiff_plus, trace_smul, neg_smul, Complex.real_smul, neg_mul]
  · rw [hdiff_minus, trace_smul, Complex.real_smul]

omit [DecidableEq n] in
/-- Surjective projection from full lattice spinors `n → ℂ` onto the `P`-invariant chiral subspace
`{ψ : n → ℂ // P.mulVec ψ = ψ}` whenever `P * P = P`. -/
noncomputable def chiralSubspaceProj
    {P : Matrix n n ℂ} (hP : P * P = P) (ψ : n → ℂ) :
    {φ : n → ℂ // P.mulVec φ = φ} :=
  ⟨P.mulVec ψ, by rw [mulVec_mulVec, hP]⟩

omit [DecidableEq n] in
theorem chiralSubspaceProj_surjective
    {P : Matrix n n ℂ} (hP : P * P = P) :
    Surjective (chiralSubspaceProj hP) := by
  rintro ⟨φ, hφ⟩
  exact ⟨φ, Subtype.ext hφ⟩

/-- **Two-Sided Quotient Descent of Lüscher's Chiral Weyl Fermion Action**
(`UEOT.V3.Compression.QuotientDescent.existsUnique_twoSidedDescend`):
Because `P_+ D P̂_- = D P̂_-` with `P_+ᴴ = P_+` (`γ5ᴴ = γ5`), the lattice Weyl fermion bilinear
`(ψ_bar, ψ) ↦ dotProduct ψ_bar ((P_+ * D * P̂_-).mulVec ψ)` is fiber-compatible with the
surjective left/right chiral subspace projections `(P_+, P̂_-)` and descends **uniquely** to a
reduced Weyl bilinear on `{ψ_bar // P_+ ψ_bar = ψ_bar} × {ψ // P̂_- ψ = ψ}` with zero doubler modes. -/
theorem luscher_weyl_bilinear_existsUnique_twoSidedDescend
    (a : ℝ) {γ5 D : Matrix n n ℂ}
    (hγ5_transpose : γ5ᵀ = γ5)
    (hγ5 : γ5 * γ5 = 1)
    (hGW : D * γ5 + γ5 * D = algebraMap ℝ (Matrix n n ℂ) a * (D * γ5 * D)) :
    let hPp := (luscher_projectors_idempotent_orthogonal_complete a hγ5 hGW).1.1
    let hPm_hat := (luscher_projectors_idempotent_orthogonal_complete a hγ5 hGW).2.2.1
    let qLeft := chiralSubspaceProj hPp
    let qRight := chiralSubspaceProj hPm_hat
    let weylAction : Unit → (n → ℂ) → (n → ℂ) → ℂ := fun _ ψBar ψ =>
      dotProduct ψBar ((stdProjPlus γ5 * D * luscherProjMinus a γ5 D).mulVec ψ)
    ∃! Q : Unit → {φ : n → ℂ // (stdProjPlus γ5).mulVec φ = φ} →
        {φ : n → ℂ // (luscherProjMinus a γ5 D).mulVec φ = φ} → ℂ,
      ∀ u ψBar ψ, Q u (qLeft ψBar) (qRight ψ) = weylAction u ψBar ψ := by
  intro hPp hPm_hat qLeft qRight weylAction
  have hPp_trans : (stdProjPlus γ5)ᵀ = stdProjPlus γ5 := by
    unfold stdProjPlus
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, transpose_smul, transpose_add,
      transpose_one, hγ5_transpose]
  have hcompat : TwoSidedCompatible qLeft qRight weylAction := by
    constructor
    · intro _ ψ x x' hxx'
      have hx_eq : (stdProjPlus γ5).mulVec x = (stdProjPlus γ5).mulVec x' :=
        congrArg Subtype.val hxx'
      dsimp [weylAction]
      have hleft_idem : ∀ y : n → ℂ,
          dotProduct y ((stdProjPlus γ5 * D * luscherProjMinus a γ5 D).mulVec ψ) =
            dotProduct ((stdProjPlus γ5).mulVec y)
              ((D * luscherProjMinus a γ5 D).mulVec ψ) := by
        intro y
        rw [Matrix.mul_assoc (stdProjPlus γ5) D (luscherProjMinus a γ5 D),
          ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hPp_trans]
      rw [hleft_idem x, hleft_idem x', hx_eq]
    · intro _ ψBar y y' hyy'
      have hy_eq : (luscherProjMinus a γ5 D).mulVec y = (luscherProjMinus a γ5 D).mulVec y' :=
        congrArg Subtype.val hyy'
      dsimp [weylAction]
      rw [← Matrix.mulVec_mulVec y (stdProjPlus γ5 * D) (luscherProjMinus a γ5 D),
        ← Matrix.mulVec_mulVec y' (stdProjPlus γ5 * D) (luscherProjMinus a γ5 D), hy_eq]
  exact existsUnique_twoSidedDescend qLeft qRight weylAction
    (chiralSubspaceProj_surjective hPp) (chiralSubspaceProj_surjective hPm_hat) hcompat

/-- **Gauge-Orbit Quotient Descent of the Lüscher Chiral Index**
(`UEOT.V3.Compression.QuotientDescent.existsUnique_descend`):
Under any equivalence relation `~` on Dirac operators generated by site-local gauge conjugations
`D' = g * D * g_inv` (`g_inv * g = 1`, `g * γ5 = γ5 * g`), the Lüscher chiral index
`Ind(D) = -((a / 2 : ℝ) : ℂ) * Tr(γ5 * D)` is strictly constant on gauge fibres and descends
uniquely to the quotient space of gauge orbits. -/
theorem luscher_index_gauge_orbit_existsUnique_descend
    (a : ℝ) (γ5 : Matrix n n ℂ) (s : Setoid (Matrix n n ℂ))
    (hgauge : ∀ {D D' : Matrix n n ℂ}, s.r D D' →
      ∃ g g_inv : Matrix n n ℂ, g_inv * g = 1 ∧ g * γ5 = γ5 * g ∧ D' = g * D * g_inv) :
    let luscherIdx : Matrix n n ℂ → ℂ := fun D => -(((a / 2 : ℝ)) : ℂ) * (γ5 * D).trace
    ∃! idxBar : Quotient s → ℂ, idxBar ∘ Quotient.mk s = luscherIdx := by
  intro luscherIdx
  have hsurj : Surjective (Quotient.mk s) := Quotient.mk_surjective
  have hcompat : FiberCompatible (Quotient.mk s) luscherIdx := by
    intro D D' hq
    obtain ⟨g, g_inv, hginv_g, hgγ, rfl⟩ := hgauge (Quotient.exact hq)
    dsimp [luscherIdx]
    congr 1
    have hrew : γ5 * (g * D * g_inv) = (g * (γ5 * D)) * g_inv := by
      calc
        γ5 * (g * D * g_inv) = (γ5 * g) * D * g_inv := by noncomm_ring
        _ = (g * (γ5 * D)) * g_inv := by rw [← hgγ]; noncomm_ring
    symm
    calc
      (γ5 * (g * D * g_inv)).trace
          = ((g * (γ5 * D)) * g_inv).trace := by rw [hrew]
      _ = (g_inv * (g * (γ5 * D))).trace := Matrix.trace_mul_comm (g * (γ5 * D)) g_inv
      _ = ((g_inv * g) * (γ5 * D)).trace := by rw [← Matrix.mul_assoc]
      _ = (γ5 * D).trace := by rw [hginv_g, one_mul]
  exact existsUnique_descend (Quotient.mk s) luscherIdx hsurj hcompat

end NeubergerOverlapMatrices

/-! ## 2. 15-Weyl-Fermion `(3,3,1)` Mixed Gravitational & Gauge Anomaly Cancellation -/

/-- Left-handed 4D Weyl fermion multiplet under `SU(3)_c × SU(2)_L × U(1)_Y`. -/
structure ChiralWeylMultiplet where
  /-- Color representation dimension (`1` for singlet, `3` for `3` or `3̄`). -/
  dimSU3 : ℕ
  /-- Twice the `SU(3)_c` Dynkin index `2 T(R_3)` (`0` for singlet, `1` for `3` or `3̄`). -/
  twoDynkinSU3 : ℕ
  /-- Weak `SU(2)_L` representation dimension (`1` for singlet, `2` for doublet). -/
  dimSU2 : ℕ
  /-- Twice the `SU(2)_L` Dynkin index `2 T(R_2)` (`0` for singlet, `1` for doublet). -/
  twoDynkinSU2 : ℕ
  /-- Weak hypercharge `Y` in the left-handed Weyl basis (`Q_em = T_3 + Y`). -/
  hypercharge : ℚ

/-- Total number of two-component left-handed Weyl states `∑ d(R_3) d(R_2)`. -/
def totalWeylDimension (spec : List ChiralWeylMultiplet) : ℕ :=
  (spec.map (fun m => m.dimSU3 * m.dimSU2)).sum

/-- Total number of fundamental `SU(2)_L` Weyl doublets `∑ d(R_3) (2 T(R_2))` governing Witten's
`π_4(SU(2)) = ℤ_2` global gauge anomaly. -/
def su2DoubletCount (spec : List ChiralWeylMultiplet) : ℕ :=
  (spec.map (fun m => m.dimSU3 * m.twoDynkinSU2)).sum

/-- Mixed QCD-hypercharge chiral anomaly coefficient `𝒜([SU(3)_c]^2 U(1)_Y) = ∑ T(R_3) d(R_2) Y`. -/
def anomalySU3SqU1Y (spec : List ChiralWeylMultiplet) : ℚ :=
  (spec.map (fun m => ((m.twoDynkinSU3 : ℚ) / 2) * (m.dimSU2 : ℚ) * m.hypercharge)).sum

/-- Mixed weak-hypercharge chiral anomaly coefficient `𝒜([SU(2)_L]^2 U(1)_Y) = ∑ d(R_3) T(R_2) Y`. -/
def anomalySU2SqU1Y (spec : List ChiralWeylMultiplet) : ℚ :=
  (spec.map (fun m => (m.dimSU3 : ℚ) * ((m.twoDynkinSU2 : ℚ) / 2) * m.hypercharge)).sum

/-- Cubic abelian hypercharge anomaly coefficient `𝒜([U(1)_Y]^3) = Tr(Y^3)`. -/
def anomalyU1YCubed (spec : List ChiralWeylMultiplet) : ℚ :=
  (spec.map (fun m => (m.dimSU3 : ℚ) * (m.dimSU2 : ℚ) * m.hypercharge ^ 3)).sum

/-- Mixed gravitational-hypercharge diffeomorphism/Lorentz anomaly coefficient
`𝒜([Grav]^2 U(1)_Y) = Tr(Y)`. -/
def anomalyGravSqU1Y (spec : List ChiralWeylMultiplet) : ℚ :=
  (spec.map (fun m => (m.dimSU3 : ℚ) * (m.dimSU2 : ℚ) * m.hypercharge)).sum

/-- One complete minimal `(3,3,1)` Standard Model chiral generation in the left-handed Weyl basis:
`Q_L(3, 2, 1/6)`, `u_R^c(3̄, 1, -2/3)`, `d_R^c(3̄, 1, 1/3)`, `L_L(1, 2, -1/2)`, `e_R^c(1, 1, 1)`
(15 Weyl states, zero sterile right-handed neutrino required). -/
def smChiralGeneration15 : List ChiralWeylMultiplet :=
  [ { dimSU3 := 3, twoDynkinSU3 := 1, dimSU2 := 2, twoDynkinSU2 := 1, hypercharge := 1 / 6 }
  , { dimSU3 := 3, twoDynkinSU3 := 1, dimSU2 := 1, twoDynkinSU2 := 0, hypercharge := -2 / 3 }
  , { dimSU3 := 3, twoDynkinSU3 := 1, dimSU2 := 1, twoDynkinSU2 := 0, hypercharge := 1 / 3 }
  , { dimSU3 := 1, twoDynkinSU3 := 0, dimSU2 := 2, twoDynkinSU2 := 1, hypercharge := -1 / 2 }
  , { dimSU3 := 1, twoDynkinSU3 := 0, dimSU2 := 1, twoDynkinSU2 := 0, hypercharge := 1 }
  ]

/-- **Simultaneous 5-Anomaly Cancellation Theorem for One 15-Weyl `(3,3,1)` Generation**:
With zero sterile right-handed neutrinos (`dim_Weyl = 15`) and `(nc, nf, k) = (3, 3, 1)` uniquely
selected by `GaugeFlavorSelection.multiscale_su3L_to_su2L_uniquely_selects_331`, all four
perturbative gauge and mixed gravitational-chiral anomalies vanish identically while Witten's
`SU(2)_L` doublet count `3 + 1 = 4` is even. -/
theorem sm_15weyl_complete_anomaly_cancellation :
    totalWeylDimension smChiralGeneration15 = 15 ∧
      anomalySU3SqU1Y smChiralGeneration15 = 0 ∧
      anomalySU2SqU1Y smChiralGeneration15 = 0 ∧
      anomalyU1YCubed smChiralGeneration15 = 0 ∧
      anomalyGravSqU1Y smChiralGeneration15 = 0 ∧
      su2DoubletCount smChiralGeneration15 = 4 ∧
      Even (su2DoubletCount smChiralGeneration15) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · norm_num [smChiralGeneration15, anomalySU3SqU1Y]
  · norm_num [smChiralGeneration15, anomalySU2SqU1Y]
  · norm_num [smChiralGeneration15, anomalyU1YCubed]
  · norm_num [smChiralGeneration15, anomalyGravSqU1Y]
  · decide
  · exact ⟨2, by decide⟩

/-- **Mixed Gravitational-Chiral Hypercharge Quantization Theorem (`Tr(Y) = 0` Locks Charge Ratios)**:
Over `ℝ`, for arbitrary hypercharges `(YQ, Yu, Yd, YL, Ye)` on the 15-Weyl `(3,3,1)` representation
`(3,2) ⊕ (3̄,1) ⊕ (3̄,1) ⊕ (1,2) ⊕ (1,1)` with `YQ ≠ 0`, simultaneous cancellation of
`[SU(3)_c]^2 U(1)_Y`, `[SU(2)_L]^2 U(1)_Y`, `[U(1)_Y]^3`, and `[Grav]^2 U(1)_Y` (`Tr(Y) = 0`)
holds **if and only if** `YL = -3 YQ`, `Ye = 6 YQ`, and `{Yu, Yd} = {-4 YQ, 2 YQ}` (exact Standard
Model hypercharge quantization up to `(u_R^c, d_R^c)` relabeling). In contrast, dropping `Tr(Y) = 0`
admits the unquantized vectorlike branch `(YQ, Yu, Yd, YL, Ye) = (0, Yu, -Yu, 0, 0)` for all `Yu ∈ ℝ`. -/
theorem sm_15weyl_gravitational_gauge_hypercharge_quantization
    {YQ Yu Yd YL Ye : ℝ} (hYQ : YQ ≠ 0) :
    ((2 * YQ + Yu + Yd = 0 ∧
      3 * YQ + YL = 0 ∧
      6 * YQ ^ 3 + 3 * Yu ^ 3 + 3 * Yd ^ 3 + 2 * YL ^ 3 + Ye ^ 3 = 0 ∧
      6 * YQ + 3 * Yu + 3 * Yd + 2 * YL + Ye = 0) ↔
      (YL = -3 * YQ ∧ Ye = 6 * YQ ∧
        ((Yu = -4 * YQ ∧ Yd = 2 * YQ) ∨ (Yu = 2 * YQ ∧ Yd = -4 * YQ)))) ∧
    (∀ u : ℝ,
      2 * (0 : ℝ) + u + (-u) = 0 ∧
      3 * (0 : ℝ) + (0 : ℝ) = 0 ∧
      6 * (0 : ℝ) ^ 3 + 3 * u ^ 3 + 3 * (-u) ^ 3 + 2 * (0 : ℝ) ^ 3 + (0 : ℝ) ^ 3 = 0) := by
  refine ⟨?_, fun u => ⟨by ring, by ring, by ring⟩⟩
  constructor
  · rintro ⟨hsu3, hsu2, hu1_3, hgrav⟩
    have hYL : YL = -3 * YQ := by linarith
    have hYd : Yd = -2 * YQ - Yu := by linarith
    have hYe : Ye = 6 * YQ := by linarith
    have hquad : 18 * YQ * (Yu + 4 * YQ) * (2 * YQ - Yu) = 0 := by
      calc
        18 * YQ * (Yu + 4 * YQ) * (2 * YQ - Yu)
            = 6 * YQ ^ 3 + 3 * Yu ^ 3 + 3 * (-2 * YQ - Yu) ^ 3 +
                2 * (-3 * YQ) ^ 3 + (6 * YQ) ^ 3 := by ring
        _ = 6 * YQ ^ 3 + 3 * Yu ^ 3 + 3 * Yd ^ 3 + 2 * YL ^ 3 + Ye ^ 3 := by
              rw [← hYd, ← hYL, ← hYe]
        _ = 0 := hu1_3
    have h18YQ_ne : 18 * YQ ≠ 0 := mul_ne_zero (by norm_num) hYQ
    rcases mul_eq_zero.mp hquad with hleft | hright
    · rcases mul_eq_zero.mp hleft with hbad | hu_m4
      · exact absurd hbad h18YQ_ne
      · have hYu : Yu = -4 * YQ := by linarith
        exact ⟨hYL, hYe, Or.inl ⟨hYu, by linarith⟩⟩
    · have hYu : Yu = 2 * YQ := by linarith
      exact ⟨hYL, hYe, Or.inr ⟨hYu, by linarith⟩⟩
  · rintro ⟨rfl, rfl, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · refine ⟨by ring, by ring, by ring, by ring⟩
    · refine ⟨by ring, by ring, by ring, by ring⟩

/-! ## 3. Autonomous Positive Clock Lapse Coupling, Spectral Symmetry & Particle-Hole Energy -/

/-- Diagonal square-root lapse operator `S = diag(√(N_i))` on an `n`-component lattice spinor space. -/
noncomputable def sqrtLapseMatrix {m : ℕ} (N : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.diagonal (fun i => ((Real.sqrt (N i)) : ℂ))

/-- Symmetric half-density clock-lapse dressed Dirac Hamiltonian `H_N = √N H_0 √N`. -/
noncomputable def clockDressedDirac {m : ℕ} (N : Fin m → ℝ)
    (H0 : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  sqrtLapseMatrix N * H0 * sqrtLapseMatrix N

/-- Euclidean `ℓ^2` norm squared `∑_i ‖v_i‖^2` on `Fin m → ℂ`. -/
noncomputable def l2NormSq {m : ℕ} (v : Fin m → ℂ) : ℝ :=
  ∑ i : Fin m, ‖v i‖ ^ 2

/-- **Clock-Dressed Dirac Hermiticity & Exact `±E` Particle-Hole Spectral Pairing**:
Whenever `H_0ᴴ = H_0`, `{Γ, H_0} = 0`, and the site-local chirality/charge-conjugation grading `Γ`
commutes with the spatial lapse profile `√N`, the clock-coupled Hamiltonian `H_N = √N H_0 √N` is
Hermitian, satisfies `{Γ, H_N} = 0`, and maps every eigenmode `H_N ψ = E ψ` to a partner mode
`Γ ψ` with exact opposite energy `-E`. -/
theorem clockDressedDirac_hermitian_and_spectral_pairing
    {m : ℕ} (N : Fin m → ℝ) {H0 Γ : Matrix (Fin m) (Fin m) ℂ}
    (hH0_herm : H0ᴴ = H0)
    (hanticomm : H0 * Γ + Γ * H0 = 0)
    (hcommS : sqrtLapseMatrix N * Γ = Γ * sqrtLapseMatrix N) :
    let HN := clockDressedDirac N H0
    HNᴴ = HN ∧
      HN * Γ + Γ * HN = 0 ∧
      (∀ (E : ℂ) (ψ : Fin m → ℂ),
        HN.mulVec ψ = E • ψ → HN.mulVec (Γ.mulVec ψ) = (-E) • (Γ.mulVec ψ)) := by
  intro HN
  let S := sqrtLapseMatrix N
  have hS_herm : Sᴴ = S := by
    dsimp [S, sqrtLapseMatrix]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.diagonal_apply_ne' _ hij, Matrix.diagonal_apply_ne _ hij]
  have hHN_herm : HNᴴ = HN := by
    dsimp [HN, clockDressedDirac]
    rw [conjTranspose_mul, conjTranspose_mul, hS_herm, hH0_herm, Matrix.mul_assoc]
  have hHN_anti : HN * Γ + Γ * HN = 0 := by
    dsimp [HN, clockDressedDirac]
    have h1 : S * H0 * S * Γ = S * (H0 * Γ) * S := by
      calc
        S * H0 * S * Γ = S * H0 * (S * Γ) := by noncomm_ring
        _ = S * (H0 * Γ) * S := by rw [hcommS]; noncomm_ring
    have h2 : Γ * (S * H0 * S) = S * (Γ * H0) * S := by
      calc
        Γ * (S * H0 * S) = (Γ * S) * H0 * S := by noncomm_ring
        _ = S * (Γ * H0) * S := by rw [← hcommS]; noncomm_ring
    calc
      S * H0 * S * Γ + Γ * (S * H0 * S)
          = S * (H0 * Γ + Γ * H0) * S := by rw [h1, h2]; noncomm_ring
      _ = 0 := by rw [hanticomm]; noncomm_ring
  refine ⟨hHN_herm, hHN_anti, ?_⟩
  intro E ψ heig
  have hneg : HN * Γ = -(Γ * HN) := eq_neg_of_add_eq_zero_left hHN_anti
  calc
    HN.mulVec (Γ.mulVec ψ)
        = (HN * Γ).mulVec ψ := Matrix.mulVec_mulVec ψ HN Γ
    _ = (-(Γ * HN)).mulVec ψ := by rw [hneg]
    _ = -((Γ * HN).mulVec ψ) := Matrix.neg_mulVec ψ (Γ * HN)
    _ = -(Γ.mulVec (HN.mulVec ψ)) := by rw [← Matrix.mulVec_mulVec ψ Γ HN]
    _ = -(Γ.mulVec (E • ψ)) := by rw [heig]
    _ = -(E • (Γ.mulVec ψ)) := by rw [Matrix.mulVec_smul]
    _ = (-E) • (Γ.mulVec ψ) := (neg_smul E (Γ.mulVec ψ)).symm

/-- Pointwise lower bound on `‖(√N u)_i‖^2` for any positive spatial lapse `0 < N_min ≤ N_i`. -/
lemma l2NormSq_sqrtLapse_ge
    {m : ℕ} {N : Fin m → ℝ} {Nmin : ℝ}
    (hNmin_pos : 0 < Nmin) (hN_ge : ∀ i, Nmin ≤ N i) (u : Fin m → ℂ) :
    Nmin * l2NormSq u ≤ l2NormSq ((sqrtLapseMatrix N).mulVec u) := by
  unfold l2NormSq sqrtLapseMatrix
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro i _
  rw [Matrix.mulVec_diagonal]
  have hNi_nn : 0 ≤ N i := le_trans (le_of_lt hNmin_pos) (hN_ge i)
  have hsqrt_nn : 0 ≤ Real.sqrt (N i) := Real.sqrt_nonneg (N i)
  rw [norm_mul, Complex.norm_of_nonneg hsqrt_nn, mul_pow, Real.sq_sqrt hNi_nn]
  exact mul_le_mul_of_nonneg_right (hN_ge i) (sq_nonneg ‖u i‖)

/-- **Strict Spectral Gap Preservation Under Inhomogeneous Positive Clock Lapse `N(x) ≥ N_min > 0`**:
If the flat-slice Dirac Hamiltonian `H_0` has spectral gap `Δ_0 > 0` (`Δ_0^2 ‖u‖^2 ≤ ‖H_0 u‖^2`
for all `u`), then for EVERY spatially inhomogeneous clock lapse profile satisfying `0 < N_min ≤ N_i`,
the dressed Dirac Hamiltonian `H_N = √N H_0 √N` satisfies `(N_min Δ_0)^2 ‖v‖^2 ≤ ‖H_N v‖^2`
everywhere, preventing any zero-mode crossing (`|E| ≥ N_min Δ_0 > 0` on every nonzero eigenstate). -/
theorem clockDressedDirac_strict_spectral_gap
    {m : ℕ} {N : Fin m → ℝ} {Nmin Δ0 : ℝ} {H0 : Matrix (Fin m) (Fin m) ℂ}
    (hNmin_pos : 0 < Nmin) (hΔ0_pos : 0 < Δ0)
    (hN_ge : ∀ i, Nmin ≤ N i)
    (hgap0 : ∀ u : Fin m → ℂ, Δ0 ^ 2 * l2NormSq u ≤ l2NormSq (H0.mulVec u)) :
    (∀ v : Fin m → ℂ,
      (Nmin * Δ0) ^ 2 * l2NormSq v ≤ l2NormSq ((clockDressedDirac N H0).mulVec v)) ∧
    (∀ (E : ℝ) (v : Fin m → ℂ),
      (∃ i, v i ≠ 0) →
      (clockDressedDirac N H0).mulVec v = ((E : ℂ)) • v →
      Nmin * Δ0 ≤ |E|) := by
  have hbound : ∀ v : Fin m → ℂ,
      (Nmin * Δ0) ^ 2 * l2NormSq v ≤ l2NormSq ((clockDressedDirac N H0).mulVec v) := by
    intro v
    unfold clockDressedDirac
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec v (sqrtLapseMatrix N) (H0 * sqrtLapseMatrix N),
      ← Matrix.mulVec_mulVec v H0 (sqrtLapseMatrix N)]
    have hstep1 : Nmin * l2NormSq v ≤ l2NormSq ((sqrtLapseMatrix N).mulVec v) :=
      l2NormSq_sqrtLapse_ge hNmin_pos hN_ge v
    have hstep2 : Δ0 ^ 2 * l2NormSq ((sqrtLapseMatrix N).mulVec v) ≤
        l2NormSq (H0.mulVec ((sqrtLapseMatrix N).mulVec v)) :=
      hgap0 ((sqrtLapseMatrix N).mulVec v)
    have hstep3 : Nmin * l2NormSq (H0.mulVec ((sqrtLapseMatrix N).mulVec v)) ≤
        l2NormSq ((sqrtLapseMatrix N).mulVec (H0.mulVec ((sqrtLapseMatrix N).mulVec v))) :=
      l2NormSq_sqrtLapse_ge hNmin_pos hN_ge (H0.mulVec ((sqrtLapseMatrix N).mulVec v))
    have h12 : Δ0 ^ 2 * (Nmin * l2NormSq v) ≤
        l2NormSq (H0.mulVec ((sqrtLapseMatrix N).mulVec v)) :=
      le_trans (mul_le_mul_of_nonneg_left hstep1 (sq_nonneg Δ0)) hstep2
    have h123 : Nmin * (Δ0 ^ 2 * (Nmin * l2NormSq v)) ≤
        l2NormSq ((sqrtLapseMatrix N).mulVec (H0.mulVec ((sqrtLapseMatrix N).mulVec v))) :=
      le_trans (mul_le_mul_of_nonneg_left h12 (le_of_lt hNmin_pos)) hstep3
    calc
      (Nmin * Δ0) ^ 2 * l2NormSq v = Nmin * (Δ0 ^ 2 * (Nmin * l2NormSq v)) := by ring
      _ ≤ l2NormSq ((sqrtLapseMatrix N).mulVec (H0.mulVec ((sqrtLapseMatrix N).mulVec v))) := h123
  refine ⟨hbound, ?_⟩
  intro E v ⟨i0, hi0⟩ heig
  have hv_pos : 0 < l2NormSq v := by
    unfold l2NormSq
    have hi_pos : 0 < ‖v i0‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hi0)
    have hle_sum : ‖v i0‖ ^ 2 ≤ ∑ i : Fin m, ‖v i‖ ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg ‖v j‖) (Finset.mem_univ i0)
    linarith
  have heig_norm : l2NormSq ((clockDressedDirac N H0).mulVec v) = E ^ 2 * l2NormSq v := by
    rw [heig]
    unfold l2NormSq
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    simp [Pi.smul_apply, Complex.norm_real, mul_pow, sq_abs]
  have hineq := hbound v
  rw [heig_norm] at hineq
  have hsq_le : (Nmin * Δ0) ^ 2 ≤ E ^ 2 := le_of_mul_le_mul_right hineq hv_pos
  have hprod_nn : 0 ≤ Nmin * Δ0 := mul_nonneg (le_of_lt hNmin_pos) (le_of_lt hΔ0_pos)
  have habs_prod : |Nmin * Δ0| ≤ |E| := sq_le_sq.mp hsq_le
  rwa [abs_of_nonneg hprod_nn] at habs_prod

/-- Normal-ordered second-quantized Dirac particle-hole excitation energy
`E_{:H_N:}(n^+, n^-) = ∑_k ω_k(N) (n_k^+ + n_k^-)` obtained after subtracting the slice Dirac-sea
vacuum expectation `E_sea(N) = -∑_k ω_k(N)`. -/
def normalOrderedDiracExcitationEnergy {p : ℕ}
    (ω : Fin p → ℝ) (nParticle nHole : Fin p → ℕ) : ℝ :=
  ∑ k : Fin p, ω k * ((nParticle k : ℝ) + (nHole k : ℝ))

/-- **Positive Normal-Ordered Fermionic Clock Energy & Anomaly-Free Slice Subtraction**:
1. Subtracting any `c`-number slice Dirac-sea energy `E_sea(N) • 1` preserves exact operator
   commutators with zero central Schwinger anomaly (`cnumber_normal_ordering_preserves_commutator`).
2. Under `ω_k(N) ≥ N_min Δ_0 > 0`:
   - Vacuum energy vanishes (`E_{:H_N:}(0, 0) = 0`),
   - Every Fock occupation `(n^+, n^-)` satisfies `0 ≤ E_{:H_N:}(n^+, n^-)`,
   - Every charge-neutral particle-hole pair state (`n^+_{k1} ≥ 1`, `n^-_{k2} ≥ 1`) satisfies
     `2 N_min Δ_0 ≤ E_{:H_N:}(n^+, n^-)`,
   - Under localized positive clock-lapse swelling (`ω_k(1) ≤ ω_k(N)` everywhere and strict increase
     `ω_{k*}(1) < ω_{k*}(N)` on an occupied mode `1 ≤ n^+_{k*} + n^-_{k*}`), the renormalized
     clock-coupled excitation energy shift `E_{:H_N:} - E_{:H_1:}` is **strictly positive**. -/
theorem normal_ordered_clock_dirac_positive_excitation_and_shift
    {p : ℕ} {ω1 ωN : Fin p → ℝ} {Nmin Δ0 : ℝ}
    (hNmin_pos : 0 < Nmin) (hΔ0_pos : 0 < Δ0)
    (hgapN : ∀ k, Nmin * Δ0 ≤ ωN k)
    (hmono : ∀ k, ω1 k ≤ ωN k) :
    (∀ {R : Type*} [Ring R] [Algebra ℝ R] (HN HM : R) (eSeaN eSeaM : ℝ),
      (HN - algebraMap ℝ R eSeaN) * (HM - algebraMap ℝ R eSeaM) -
        (HM - algebraMap ℝ R eSeaM) * (HN - algebraMap ℝ R eSeaN) =
      HN * HM - HM * HN) ∧
    normalOrderedDiracExcitationEnergy ωN (fun _ => 0) (fun _ => 0) = 0 ∧
    (∀ nP nH : Fin p → ℕ, 0 ≤ normalOrderedDiracExcitationEnergy ωN nP nH) ∧
    (∀ (nP nH : Fin p → ℕ) (k1 k2 : Fin p),
      1 ≤ nP k1 → 1 ≤ nH k2 →
      2 * (Nmin * Δ0) ≤ normalOrderedDiracExcitationEnergy ωN nP nH) ∧
    (∀ (nP nH : Fin p → ℕ) (kStar : Fin p),
      ω1 kStar < ωN kStar →
      1 ≤ nP kStar + nH kStar →
      0 < normalOrderedDiracExcitationEnergy ωN nP nH -
            normalOrderedDiracExcitationEnergy ω1 nP nH) := by
  have hprod_pos : 0 < Nmin * Δ0 := mul_pos hNmin_pos hΔ0_pos
  have hωN_nn : ∀ k, 0 ≤ ωN k := fun k => le_trans (le_of_lt hprod_pos) (hgapN k)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro R _ _ HN HM eSeaN eSeaM
    exact UEOTPhysicsUnification.LocalizedClockAndDiracAlgebra.cnumber_normal_ordering_preserves_commutator
      HN HM eSeaN eSeaM
  · unfold normalOrderedDiracExcitationEnergy
    simp
  · intro nP nH
    unfold normalOrderedDiracExcitationEnergy
    refine Finset.sum_nonneg ?_
    intro k _
    exact mul_nonneg (hωN_nn k) (by positivity)
  · intro nP nH k1 k2 hk1 hk2
    unfold normalOrderedDiracExcitationEnergy
    have hsplit :
        (∑ k : Fin p, ωN k * ((nP k : ℝ) + (nH k : ℝ))) =
          (∑ k : Fin p, ωN k * (nP k : ℝ)) + ∑ k : Fin p, ωN k * (nH k : ℝ) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro k _
      ring
    rw [hsplit]
    have hk1R : (1 : ℝ) ≤ (nP k1 : ℝ) := by exact_mod_cast hk1
    have hk2R : (1 : ℝ) ≤ (nH k2 : ℝ) := by exact_mod_cast hk2
    have hsumP : Nmin * Δ0 ≤ ∑ k : Fin p, ωN k * (nP k : ℝ) := by
      have hterm : Nmin * Δ0 ≤ ωN k1 * (nP k1 : ℝ) := by
        calc
          Nmin * Δ0 = (Nmin * Δ0) * 1 := (mul_one _).symm
          _ ≤ ωN k1 * (nP k1 : ℝ) := mul_le_mul (hgapN k1) hk1R zero_le_one (hωN_nn k1)
      exact le_trans hterm
        (Finset.single_le_sum (fun j _ => mul_nonneg (hωN_nn j) (Nat.cast_nonneg _))
          (Finset.mem_univ k1))
    have hsumH : Nmin * Δ0 ≤ ∑ k : Fin p, ωN k * (nH k : ℝ) := by
      have hterm : Nmin * Δ0 ≤ ωN k2 * (nH k2 : ℝ) := by
        calc
          Nmin * Δ0 = (Nmin * Δ0) * 1 := (mul_one _).symm
          _ ≤ ωN k2 * (nH k2 : ℝ) := mul_le_mul (hgapN k2) hk2R zero_le_one (hωN_nn k2)
      exact le_trans hterm
        (Finset.single_le_sum (fun j _ => mul_nonneg (hωN_nn j) (Nat.cast_nonneg _))
          (Finset.mem_univ k2))
    linarith
  · intro nP nH kStar hstrict hocc
    unfold normalOrderedDiracExcitationEnergy
    rw [← Finset.sum_sub_distrib]
    have hoccR : (1 : ℝ) ≤ (nP kStar : ℝ) + (nH kStar : ℝ) := by exact_mod_cast hocc
    have hterm_pos : 0 < ωN kStar * ((nP kStar : ℝ) + (nH kStar : ℝ)) -
        ω1 kStar * ((nP kStar : ℝ) + (nH kStar : ℝ)) := by
      have hrew : ωN kStar * ((nP kStar : ℝ) + (nH kStar : ℝ)) -
          ω1 kStar * ((nP kStar : ℝ) + (nH kStar : ℝ)) =
        (ωN kStar - ω1 kStar) * ((nP kStar : ℝ) + (nH kStar : ℝ)) := by ring
      rw [hrew]
      exact mul_pos (by linarith) (by linarith)
    have hsingle_le :
        ωN kStar * ((nP kStar : ℝ) + (nH kStar : ℝ)) -
            ω1 kStar * ((nP kStar : ℝ) + (nH kStar : ℝ)) ≤
          ∑ x : Fin p, (ωN x * ((nP x : ℝ) + (nH x : ℝ)) -
            ω1 x * ((nP x : ℝ) + (nH x : ℝ))) := by
      refine Finset.single_le_sum
        (f := fun x : Fin p =>
          ωN x * ((nP x : ℝ) + (nH x : ℝ)) - ω1 x * ((nP x : ℝ) + (nH x : ℝ)))
        ?_ (Finset.mem_univ kStar)
      intro j _
      have hj_rew : ωN j * ((nP j : ℝ) + (nH j : ℝ)) - ω1 j * ((nP j : ℝ) + (nH j : ℝ)) =
          (ωN j - ω1 j) * ((nP j : ℝ) + (nH j : ℝ)) := by ring
      rw [hj_rew]
      exact mul_nonneg (sub_nonneg.mpr (hmono j)) (by positivity)
    linarith

end UEOTPhysicsUnification.ChiralGaugeOverlapClockBridge
