# `chiral_gauge_overlap_clock` — 4D Neuberger Overlap Chiral Gauge Factorization, `(3,3,1)` Gravitational-Gauge Anomaly Cancellation & Autonomous Clock Coupling (`P-CHIRAL-CLOCK-02`)

Companion 40-digit outward-interval verification suite (`mpmath.iv`, `iv.dps = 40`) for
[`ChiralGaugeOverlapClockBridge.lean`](../../../formalization/ueot-physics-unification/UEOTPhysicsUnification/ChiralGaugeOverlapClockBridge.lean).

## Scope & Certified Claims

1. **Exact Lüscher / Ginsparg-Wilson Chiral Gauge Projector Algebra & 4D Overlap Realization**:
   - Lean 4 theorems `modifiedChirality_sq_eq_one`, `luscher_projectors_idempotent_orthogonal_complete`,
     `ginsparg_wilson_chirality_intertwining`, `luscher_chiral_gauge_factorization`,
     `neubergerOverlap_gw_hermitian_and_luscher_index`, `luscher_weyl_bilinear_existsUnique_twoSidedDescend`,
     and `luscher_index_gauge_orbit_existsUnique_descend` (`0 sorryAx`, `0 native_decide`, `0` custom axioms).
   - Python `verify_chiral_clock.py` constructs the explicit $2^4$ 4D Euclidean torus Neuberger Overlap
     operator $D_{\mathrm{ov}} = \frac{1}{a}\bigl(I + X(X^\dagger X)^{-1/2}\bigr)$ ($64 \times 64$ complex
     interval matrices, $a = 1/2$, $m_0 = 3/2$) coupled simultaneously to an orthogonal $U(1)$ instanton/flux-toron
     background $(m_{12}, m_{34}) = (+1, -1)$ and a spatially localized autonomous clock lapse
     $N(\mathbf{x}) = 1 + \alpha(\mathbf{x}) \in [1, 6/5] \subset [1, 5/4]$. Using a rigorous Sylvester/Riccati
     outward-interval enclosure of $(X^\dagger X)^{-1/2}$, it certifies $\|\hat\gamma_5^2 - I\|_F < 10^{-29}$,
     $\|P_+ D_{\mathrm{ov}} \hat P_- - D_{\mathrm{ov}} \hat P_-\|_F < 10^{-29}$,
     $\|P_- D_{\mathrm{ov}} \hat P_+ - D_{\mathrm{ov}} \hat P_+\|_F < 10^{-29}$, and the exact integer Lüscher
     chiral index $\mathrm{Ind}(D_{\mathrm{ov}}) = +1 \in \mathbb{Z}$.

2. **15-Weyl-Fermion `(3,3,1)` Gauge + Mixed Gravitational Anomaly Cancellation & Hypercharge Quantization**:
   - Lean 4 theorems `sm_15weyl_complete_anomaly_cancellation` and
     `sm_15weyl_gravitational_gauge_hypercharge_quantization` prove simultaneous vanishing of
     $[SU(3)_c]^2 U(1)_Y$, $[SU(2)_L]^2 U(1)_Y$, $[U(1)_Y]^3$, mixed gravitational-hypercharge $\mathrm{Tr}(Y)$,
     and even Witten $SU(2)_L$ doublet parity ($3 + 1 = 4$) for one 15-Weyl `(3,3,1)` generation with zero
     sterile right-handed neutrinos, and prove that $\mathrm{Tr}(Y) = 0$ uniquely locks the Standard Model
     hypercharge ratios $(-3 Y_Q, 6 Y_Q, \{-4 Y_Q, 2 Y_Q\})$.

3. **Autonomous Positive Clock Lapse Coupling & Positive Renormalized Particle-Hole Energy**:
   - Lean 4 theorems `clockDressedDirac_hermitian_and_spectral_pairing`,
     `clockDressedDirac_strict_spectral_gap`, and `normal_ordered_clock_dirac_positive_excitation_and_shift`
     prove exact $\pm E$ particle-hole spectral symmetry, strict gap preservation $|E| \ge N_{\min}\Delta_0 > 0$,
     anomaly-free slice Dirac-sea normal ordering, and strictly positive clock-coupled excitation energy shifts.
   - Python certifies all 32 eigenvalues of the $2^3$ spatial clock-dressed Dirac Hamiltonian
     $H_N = \sqrt{N(\mathbf{x})} H_0 \sqrt{N(\mathbf{x})}$ via Weyl + polar-unitary interval bounds, verifying
     $\Delta E_{\mathrm{pair}}^{\mathrm{clock}} > 0$ and $\Delta E_{\mathrm{shell}}^{\mathrm{clock}} > 0$ while
     maintaining `"device_certified": false` and `"physical_unification": "OPEN"`.

## Commands

```bash
/private/tmp/ueot-lapse-boundary-20261121-venv/bin/python -B physics/unification/chiral_gauge_overlap_clock/verify_chiral_clock.py --write
/private/tmp/ueot-lapse-boundary-20261121-venv/bin/python -B physics/unification/chiral_gauge_overlap_clock/verify_chiral_clock.py --check
```
