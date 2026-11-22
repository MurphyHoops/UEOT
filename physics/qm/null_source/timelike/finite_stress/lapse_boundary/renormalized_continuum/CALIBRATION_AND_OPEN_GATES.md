# RC12 — SI / Planck Physical Calibration Dictionary, Sub-Planckian Repeatability Floor, and Remaining Unification Gates

## Scope and Results

Across `RC01`–`RC11`, dimensionless model units set $R_{S^3} = 1, \hbar = 1, c = 1$. Here we establish the exact physical SI / Planck calibration dictionary for the sub-critical closed-FRW bounce (`RC05`–`RC06`), evaluate the physical energy density and minimum trial count for the autonomous continuum pointer (`RC09`), and record the exact remaining open gates separating `renormalized_continuum` from complete physical unification.

## 1. Physical Interpretation of the Sub-Critical Compactness Window $\frac{4\pi G_{\mathrm{model}}}{g^2} < 1$

Restoring CODATA-2022 constants $c = 299792458\text{ m s}^{-1}$, $\hbar = 1.054571817 \times 10^{-34}\text{ J s}$, and $G_{\mathrm{SI}} = 6.67430 \times 10^{-11}\text{ m}^3\text{kg}^{-1}\text{s}^{-2}$ gives Planck length $\ell_{\mathrm{Pl}} = \sqrt{\hbar G_{\mathrm{SI}}/c^3} \approx 1.616255 \times 10^{-35}\text{ m}$. On a three-sphere of physical turnaround radius $R_{S^3}$, dimensionless Newton's constant is
\[
 G_{\mathrm{model}} = \frac{G_{\mathrm{SI}}\hbar}{c^3 R_{S^3}^2} = \left(\frac{\ell_{\mathrm{Pl}}}{R_{S^3}}\right)^2. \tag{1}
\]
Consequently:
1. Setting $G_{\mathrm{model}} \sim O(1)$ (`BACKREACTION_GATE`) implicitly fixed $R_{S^3} \sim \ell_{\mathrm{Pl}}$, cramming $g^{-2} \sim 10^{80}$ quanta into a Planck-sized universe and triggering the $\Delta\tau < \pi$ Big Crunch (`RC05`).
2. At our sub-critical bounce point $\frac{4\pi G_{\mathrm{model}}}{g^2} = \frac{3}{10} < 1$ (`\alpha_G = 1/10`) and benchmark coupling $g = 10^{-40}$, equation (1) uniquely determines the physical turnaround radius and geodesic-cap sensor radius ($\rho_0 = 1/20\text{ rad}$):
\[
 R_{S^3} = \sqrt{\frac{40\pi}{3}}\,\frac{\ell_{\mathrm{Pl}}}{g} \approx 1.0462 \times 10^6\text{ m} \approx 1046.2\text{ km}, \qquad L_{\mathrm{sensor}} = \rho_0 R_{S^3} \approx 52.31\text{ km}. \tag{2}
\]
3. The physical turnaround clock enthalpy density is
\[
 \rho_{X,\mathrm{SI}} = \frac{\hbar c}{2 g^2 R_{S^3}^4} = \frac{3 c^4}{80\pi G_{\mathrm{SI}} R_{S^3}^2} \approx 1.321 \times 10^{30}\text{ J m}^{-3} \quad (\text{mass density } \approx 1.47 \times 10^{13}\text{ kg m}^{-3}), \tag{3}
\]
which is an astrophysical/cosmological spatial-closure density (comparable to sub-nuclear compact-star matter), **not** a tabletop laboratory apparatus in flat space!

## 2. Statistical Sample-Complexity Floor and Open Unification Gates

Even for the stronger linear-in-$\eta$ autonomous pointer gap $\Delta P_{\mathrm{ptr},\infty} \in (9 \times 10^{-23}, 10^{-20})$ at $\eta = 10^{-13}$ (`RC09`), distinguishing the two binary coin laws with error probability $\le 5\%$ requires by Pinsker / Le Cam's inequality at least
\[
 N_{\mathrm{trials}} \ge \frac{\ln 10}{2\,(\Delta P_{\mathrm{ptr},\infty})^2} > 10^{40}\text{ independent universe/apparatus runs}, \tag{4}
\]
confirming that the positive probability gap proves **mathematical distinguishability inside the model**, not an experimentally accessible gravitational measurement.

### Remaining Open Gates (`"physical_unification": "OPEN"`)
1. **Pointlike $\rho_0 \to 0$ continuum apparatus limit**: Removing the finite geodesic-cap sensor scale $\rho_0 = 1/20 \to 0$ at fixed $g > 0$ re-encounters `CLOCK_UV` ($\sigma_{X,\rho_0,\infty}^2 \sim \rho_0^{-2} \to \infty$).
2. **All-harmonic matter constraints and operator quantum Einstein equations**: While the 6-channel Parseval frame eliminates all $\ell \ge 1$ background controller rows and `RC08` matches all 8 $\ell = 1$ total-source dipole means on $\tau = \pi$, higher spatial harmonics ($\ell \ge 2$) of the quadratic code/body perturbation $\frac{1}{2}\eta^2 f^2$ and full operator-valued Einstein equations $\hat G_{\mu\nu} = 8\pi G \hat T_{\mu\nu}$ remain open.
3. **First-principles derivation from `Core v3` and laboratory calibration**: Field content, couplings $(G, \Lambda, g, \rho_0)$, and realistic tabletop gravimetry remain open.
