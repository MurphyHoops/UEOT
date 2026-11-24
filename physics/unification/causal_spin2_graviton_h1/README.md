# `causal_spin2_graviton_h1` — 3+1D Spin-2 Graviton Continuum, Regge–Schläfli, $O(a^2)$ Dirac Algebra & Sharp `H1` Decomposition

Companion 40-digit outward-interval (`mpmath.iv`) and exact symbolic (`sympy`) verification suite for `UEOTPhysicsUnification.CausalSpin2GravitonContinuumH1` (Wave 8 `H1`):

1. **`P-H1-SPIN2-01` (Linearized 3+1D Spin-2 York/DeWitt & Causal Lattice Propagator)**:
   - Symbolic 6-mode symmetric $3\times 3$ reconstruction diagonalizes the DeWitt supermetric to `[-6, 2, 2, 2, 2, 6]` with exact signature `(-, +, +, +, +, +)` and transverse-traceless sector $M_{\mathrm{TT}} \mathbf{e}_3 = 0$, paired with `QuotientDescent` gauge descent.
   - Verifies unconditional $O(a^2)$ 3D spin-2 lattice dispersion and Euclidean propagator convergence ($4\times$ error drop per halving across $a \in \{1/10, 1/20, 1/40\}$), strictly positive 2-polarization reflection transfer matrix, and Stelle fourth-derivative ghost separation (residue `-1` vs `+1`).

2. **`P-H1-REGGE-02` (Regge–Schläfli Stationarity, Curved Deficit & Smeared Dirac $O(a^2)$)**:
   - Verifies exact 4D Cayley–Menger Schläfli identity $\sum_h A_h \delta\theta_h = 0$ on $\sigma^{(4,1)}$ at $\tilde{\alpha} = 2/3 > 7/12$, curved $S^3$ Regge curvature convergence to $R^{(3)} = 6/R^2 = 2/3$ at $O(a^2)$, and smeared central-difference Dirac hypersurface Wronskian restoration at $O(a^2)$.

3. **`P-H1-BIANCHI-03` (Bianchi IX Planck Floor, Isaacson Stress & Projective Refinement)**:
   - Contrasts unbounded classical BKL anisotropic shear against uniform regularization below the `AH01` Planck minimal volume floor $V_{\min} = L_{\min}^3$, verifies trace-free Isaacson null stress ($w_{\mathrm{GW}} = 1/3$, $a^{-4}$ scaling), and verifies multi-mode projective cylindrical `TransportCertificate` refinement.

4. **`C-H1-FRONTIER-04` (Sharp `H1` Decomposition)**:
   - Closes `H1a`, `H1b`, and `H1c` in pure-kernel Lean 4 + 40-digit intervals while proving logical independence of the full nonperturbative 4D fixed-point measure core `H1d`, honestly preserving `"device_certified": false` and `"physical_unification": "OPEN"`.
