# Multiscale `(3,3,1)` Selection, Efficiency-Free `R_τ` Exclusion & Rank-One Flavor Closure (`HG-5`)

```text
Result ID: P-MATTER-02, P-FLAVOR-03
Core dependencies: Complete-record probability conservation (B_e + B_mu + B_had = 1)
Bridge dependencies: Chiral anomaly & 1-loop RG beta-function integer constraints; rank-one Wilson matching
Sector inputs: SU(n_c)_C x SU(3)_L x U(1)_X -> SU(n_c)_C x SU(2)_L x U(1)_Y breaking chain; single VLL operator
Standard physical inputs: PDG/HFLAV tau leptonic branching ratios, nuclear/kaon |V_ud|, |V_us|, FLAG lattice B_hat_K
Effective assumptions: Short-distance Braaten-Narison-Pich OPE at s_0 = m_tau^2; 2-loop QCD Delta S = 2 RG factors
Formal status: Diophantine classification, ABJ invariance, R_tau rational bound & Wilson closure proved in Lean 4 (GaugeFlavorSelection.lean, 0 sorryAx) + outward-interval certificate
Observable/benchmark: IR b_2(SU(2)_L) = +19/6 vs -17/6; R_tau(N=5) >= 4.9710 vs exp <= 3.6754 (>130 sigma); held-out |epsilon_K| in [1.668e-3, 2.551e-3]
Falsification condition: Observing |epsilon_K| outside the top-aligned positive-shift interval or discovering exotic light color states below m_Z/2
```

## Summary of Established Results

1. **Complete $\mathbb{N}^3$ Classification & Multiscale Uniqueness (`uv_331_complete_classification`, `multiscale_su3L_to_su2L_uniquely_selects_331`)**:
   Over all natural numbers $(n_c, n_f, k)$ with $n_c \ge 3, n_f \ge 1, k \le n_f$, cubic $SU(3)_L^3$ anomaly cancellation $2n_c k + n_f = n_c n_f$ together with UV $SU(n_c)_C$ and $SU(3)_L$ asymptotic freedom admits **exclusively** $(3,3,1)$ and $(5,5,2)$. Every solution has even doublet count $n_f(n_c+1)$, explaining why Witten's global $SU(2)$ anomaly cannot separate them. Requiring infrared chiral $SU(2)_L$ asymptotic freedom below the $3\text{-}3\text{-}1$ breaking scale ($b_2^{\mathrm{IR}} = \frac{22}{3} - \frac{n_f(n_c+1)}{3} - \frac{1}{6} > 0$) yields $+\frac{19}{6} > 0$ for $(3,3,1)$ versus $-\frac{17}{6} < 0$ for $(5,5,2)$, **uniquely selecting $(3,3,1)$**.
2. **ABJ Anomaly Degeneracy vs Efficiency-Free $R_\tau$ Unitarity Exclusion**:
   Under $Q_u = \frac{N+1}{2N}, Q_d = -\frac{N-1}{2N}$, the $\pi^0 \to \gamma\gamma$ anomaly factor $N(Q_u^2 - Q_d^2) = 1$ is $N$-independent. By contrast, semileptonic $\tau$ decay unitarity $R_\tau = \frac{1 - B_e - B_\mu}{B_e}$ uses only clean $e, \mu$ identification (**zero dependence on hadronic detector efficiency $E_5$**), bounding $R_\tau^{\mathrm{exp}} \le 3.67543$ ($3\sigma$) while forcing $R_\tau^{\mathrm{th}}(N=5) \ge 4.97103$ ($>130\sigma$ exclusion of unbroken 5-color light $(u,d,s)$ confinement).
3. **Rank-One $\Delta F = 2$ Complex Phase Lock & Kaon Holdout (`rank_one_wilson_closure`)**:
   For $C_{ij}^{\mathrm{NP}} = \eta_{\mathrm{NP}}(u_i u_j^*)^2$ ($\eta_{\mathrm{NP}} > 0, \sum |u_i|^2 = 1$), exact elimination yields:
   $$C_{ds}^{\mathrm{NP}} = \left(\frac{1}{|u_b|^2} - 1\right)\frac{(C_{bd}^{\mathrm{NP}})^*\, C_{bs}^{\mathrm{NP}}}{|C_{bd}^{\mathrm{NP}}| + |C_{bs}^{\mathrm{NP}}|}, \qquad \arg(C_{ds}^{\mathrm{NP}}) \equiv \arg(C_{bs}^{\mathrm{NP}}) - \arg(C_{bd}^{\mathrm{NP}}) \pmod{2\pi}.$$
   In top-aligned $(3,3,1)$, an allowed $0\text{--}8\%$ $B_s$ mixing shift predicts held-out $|\epsilon_K| \in [1.668\times 10^{-3}, 2.551\times 10^{-3}]$ (overlapping PDG $3\sigma$ $[2.195\times 10^{-3}, 2.261\times 10^{-3}]$ with strictly positive new-physics sign $\delta|\epsilon_K| > 0$), whereas a $+60\%$ shift is strictly falsified ($|\epsilon_K| \ge 2.434\times 10^{-3} > 2.285\times 10^{-3}$).

Evidence: [verify_matter_flavor.py](verify_matter_flavor.py) · [result.json](result.json)
