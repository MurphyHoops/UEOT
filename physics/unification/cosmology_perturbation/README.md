# Breaking Background Expansion Degeneracy via Perturbation Growth & Lensing-Velocity Ratio (`P-COSMO-02`)

```text
Result ID: P-COSMO-02
Core dependencies: Observationally indistinguishable background quotient vs perturbation refinement
Bridge dependencies: Sub-horizon relativistic fluid/scalar linear perturbation equations on shared FLRW metric
Sector inputs: General Relativity linear scalar perturbations, canonical scalar sound speed c_s^2 = 1 vs cold dust c_s^2 = 0
Standard physical inputs: Flat background Omega_m0,eff = 0.30, Planck primordial normalization sigma_8,0 = 0.811
Effective assumptions: Sub-Hubble k >> aH Jeans suppression of canonical scalar perturbations
Formal status: High-precision DOP853 ODE benchmark (rtol = 1e-12) + exact background identity check
Observable/benchmark: Max H(z) diff 4.44e-16; z = 1.48 primordial-matched f*sigma_8 separation 44.06%; galaxy-bias-cancelling E_G(z) separation 5.50%
Falsification condition: Joint multi-redshift RSD + weak-lensing E_G(z) measurements across z in [0.38, 1.48]
```

## Summary of Established Results

1. **Ghost-Free Exact Background Degeneracy**: Splitting $\Omega_{m0}^{\mathrm{LCDM}} = 0.30$ into clustering matter $\Omega_{m0}^{\mathrm{alt}} = 0.26$ plus a canonical relativistic scalar field with $\rho_\phi(a)/\rho_{\mathrm{crit},0} = 0.04\,a^{-3} + 0.70$ preserves $\rho_\phi + p_\phi = 0.04\,a^{-3}\rho_{\mathrm{crit},0} > 0$ ($-0.945946 \le w_\phi(a) < 0$, **zero phantom ghost**) and reproduces the exact $\Lambda\mathrm{CDM}$ Hubble curve $H(z)$, $D_M(z)/r_d$, and $D_H(z)/r_d$ across all redshifts (maximum numerical difference $4.44\times 10^{-16}$).
2. **Sub-Horizon Growth & Multi-Redshift Velocity-Bias Breaking**: Because a canonical scalar ($c_s^2 = 1$) does not cluster on sub-Hubble scales ($k \gg aH$), the early matter-era growing-mode exponent shifts from $p_+ = 1$ to $p_+ = \frac{-1 + \sqrt{1 + 24\times(0.26/0.30)}}{4} \approx 0.917261753$. At the eBOSS quasar redshift $z = 1.48$:
   - Primordial-CMB-matched $f\sigma_8(1.48)$ separates by **$44.06\%$** ($0.37829$ vs $0.21163$);
   - Even if an arbitrary constant tracer velocity bias $b_v$ absorbs normalization at one redshift, the multi-redshift growth slope ratio $f\sigma_8(1.48)/f\sigma_8(0.38)$ still differs by **$4.22\%$**;
   - Combining weak lensing with redshift-space distortions via $E_G(z) = \Omega_{m,\mathrm{clust},0}/f(z)$ cancels linear galaxy bias and $\sigma_8$ normalization while maintaining a **$5.50\%$** separation across $z \in [0.38, 1.48]$.

Evidence: [verify_perturbation_holdout.py](verify_perturbation_holdout.py) · [result.json](result.json)
