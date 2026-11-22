# RC11 — Coupled Two-Branch Schwinger–Keldysh (CTP) Tensor, Vector, and Lapse Kernel on the Continuum Bounce State

## Scope and Results

In `joint_constraints`, the scalar source-CTP phase (`SOURCE_CTP`) and the restricted homogeneous/lapse-CTP phase (`LAPSE_PHASE`) were constructed separately without unifying them into a joint metric perturbation kernel across scalar lapse $\delta N_\pm$, shift $\delta N^i_\pm$, and spatial metric $\delta h_{ij,\pm}$ (including transverse-traceless graviton polarizations $\delta h_{ij}^{\mathrm{TT}}$).

Here we establish the **connected quadratic two-branch CTP influence functional** $\Gamma_{\mathrm{CTP}}^{(2)}[\bar g_{\mu\nu} + \delta g_{\mu\nu}^+,\, \bar g_{\mu\nu} + \delta g_{\mu\nu}^-]$ around the dynamical closed-FRW bounce $\bar g_{\mu\nu} = a(\tau)^2(-d\tau^2 + \gamma_{ij} dx^i dx^j)$ and the common prepared continuum state $|\Psi_\infty\rangle$ (`RC06`–`RC10`) for smooth compactly supported metric perturbations $\delta g_{\mu\nu}^\pm \in C_c^\infty\big((1/2, 5/2) \times S^3\big)$:

1. **Covariant Local Counterterm Splitting ($R^2 + C_{\mu\nu\rho\sigma}C^{\mu\nu\rho\sigma}$) and Retarded Causality**:
   Passing to Keldysh sum/difference variables $\Sigma g^{\mu\nu} := \frac{1}{2}(\delta g_+^{\mu\nu} + \delta g_-^{\mu\nu})$ and $\Delta g^{\mu\nu} := \delta g_+^{\mu\nu} - \delta g_-^{\mu\nu}$, the quadratic CTP influence action takes the universal Schwinger–Keldysh form
   \[
    \Gamma_{\mathrm{CTP}}^{(2)}[\Sigma g, \Delta g] = -\frac{1}{2}\iint \Delta g^{\mu\nu}(x)\,G_{\mathrm{ret},\mathrm{ren}}^{\mu\nu,\rho\sigma}(x, y)\,\Sigma g^{\rho\sigma}(y)\,d\mu_{\bar g}(x)\,d\mu_{\bar g}(y) + \frac{i}{8}\iint \Delta g^{\mu\nu}(x)\,N_{\mathrm{Kel}}^{\mu\nu,\rho\sigma}(x, y)\,\Delta g^{\rho\sigma}(y)\,d\mu_{\bar g}(x)\,d\mu_{\bar g}(y). \tag{1}
   \]
   On four-dimensional curved spacetime, the UV divergence of the retarded two-point stress commutator/contact distribution resides purely in the **real local geometric fourth-derivative counterterms** $\alpha_R \int \sqrt{-g}\,R^2\,d^4x + \alpha_W \int \sqrt{-g}\,C_{\mu\nu\rho\sigma}C^{\mu\nu\rho\sigma}\,d^4x$ (matching `OVERLAP_RESPONSE` / `CONFORMAL_ACTION`), with $\Gamma_{\mathrm{CTP}}^{(2)}[\Sigma g, 0] \equiv 0$ (unitarity normalization) and $G_{\mathrm{ret},\mathrm{ren}}^{\mu\nu,\rho\sigma}(\tau, \mathbf x; \tau', \mathbf y) = 0$ for $\tau < \tau'$.

2. **Strict Positivity and UV Finiteness of the Joint Tensor–Vector–Scalar Noise Kernel**:
   Because $\Delta g^{\mu\nu}$ carries no coincident-point counterterm imaginary part, the imaginary part of $\Gamma_{\mathrm{CTP}}^{(2)}$ is **UV-finite without subtraction** at $K = \infty$ (`RC10`) and equals half the spacetime-smeared symmetrized stress covariance:
   \[
    \operatorname{Im}\Gamma_{\mathrm{CTP}}^{(2)}[\Sigma g, \Delta g] = \frac{1}{8}\operatorname{Var}_{\Psi_\infty}\!\left(\int d^4x\sqrt{-\bar g}\,\Delta g^{\mu\nu}(x)\,\hat T_{\mu\nu}^{\mathrm{tot}}(x)\right) \ge 0. \tag{2}
   \]
   Using the $SO(4)$ York–licit decomposition on $S^3$ into scalar ($\delta N, \delta h_{\mathrm{tr}}, \nabla_i\nabla_j\sigma$), transverse vector ($\delta N_i^{\mathrm{T}}, k \ge 2$), and transverse-traceless tensor ($\delta h_{ij}^{\mathrm{TT}}, k \ge 3$, eigenvalue $-\Delta_{S^3} h_{ij}^{\mathrm{TT}} = (k^2 - 3) h_{ij}^{\mathrm{TT}}$ on unit $S^3$), we prove **strict positivity** $\operatorname{Im}\Gamma_{\mathrm{CTP}}^{(2)} > 0$ on nonzero smooth test functions in **all three irreducible sectors** (scalar lapse, vector shift, and $k = 3$ quadrupole TT tensor!).

3. **Vanishing Cutoff Bianchi / Diffeomorphism Residual as $K \to \infty$**:
   For pure gauge difference perturbations $\Delta g_{\mu\nu} = \nabla_\mu\xi_\nu + \nabla_\nu\xi_\mu$ ($\xi^\mu \in C_c^\infty((1/2, 5/2) \times S^3)$), exact continuum covariant conservation $\nabla^\mu\hat T_{\mu\nu}^{\mathrm{free + frame}} = 0$ holds on the free propagation window $(1/2, 5/2)$ (where $F_j(g X_{\rho_0}) = 0 = F_{\mathrm{read}}(g X_{\rho_0})$ up to the super-Gaussian clock tail), while at finite spectral cutoff $K$ the sharp-projection diffeomorphism defect decays as $O(K^{-10}) \to 0$ (`RC02`).

Note: this establishes the **quadratic perturbative CTP kernel** around the bounce background, NOT a non-perturbative path-integral quantization of arbitrary Lorentzian geometries.
