# Complex Quantum Selection Trichotomy & Quotient Descent Bridge (`C-QSEL-05`)

```text
Result ID: C-QSEL-05
Core dependencies: UEOT.V3.Compression.QuotientDescent (FiberCompatible, existsUnique_descend)
Bridge dependencies: Canonical real-to-complex tensor quotient q_{R->C} : U ox_R V -> U ox_C V
Sector inputs: Universal purification, single-system continuous reversible transitivity, two-shot local storage/measurement access
Standard physical inputs: Finite-dimensional operational state/effect duality
Effective assumptions: Finite-shot Hoeffding concentration under i.i.d. or martingale-bounded noise
Formal status: Machine-checked in Lean 4 (RealQuotientSelection.lean, 0 sorryAx) + 288-cell numerical certificate
Observable/benchmark: <O_A^(2) ox O_B^(2)> = +1 on tau^(ox 2) vs 0 on all real separable histories; 288 Renou cells matched to 8.33e-17
Falsification condition: Observing <O_A^(2) ox O_B^(2)> > 2*eps_TV falsifies shot-correlated real separable sources; observing non-zero [E, J_tot] breaks complex quotient equivalence
```

## Summary of Established Results

1. **Holonomic Dimension Gap (`real_holonomic_gap_pos`)**: Standard real symmetric tensor products carry an excess of $\frac{d_A(d_A-1)}{2}\frac{d_B(d_B-1)}{2} > 0$ holonomic parameters ($d_A, d_B \ge 2$), violating Local Tomography, whereas complex Hermitian composites satisfy $(d_A d_B)^2 = d_A^2 d_B^2$.
2. **Two-Copy Real-Symmetric Witness Excluding Fresh Hoffreumon–Woods Sources**: Although $\tau_{AB} = \frac{1}{4}(I_4 - J_A\otimes J_B)$ is indistinguishable from $\frac{1}{4}I_4$ under all single-copy real symmetric product measurements, $O^{(2)} = J\otimes J$ is **real symmetric** ($(O^{(2)})^T = O^{(2)}$) with spectrum $\{\pm 1\}$. Because $\mathrm{Tr}(J\rho) = 0$ for every real symmetric single-rebit state $\rho$, every classically correlated two-shot real product mixture gives $\langle O_A^{(2)}\otimes O_B^{(2)}\rangle = 0$, whereas $\tau^{\otimes 2}$ yields $+1$ (`4239` shots at $\alpha = 0.01$, half-width $0.05$, excluding total-variation radius $0.45$).
3. **Barrios Hita Phase-Relocation Quotient Isomorphism**: Quotienting $U \otimes_{\mathbb{R}} V$ by $S_{UV} = \mathrm{span}_{\mathbb{R}}\{(iu)\otimes_{\mathbb{R}} v - u\otimes_{\mathbb{R}}(iv)\}$ yields a canonical $\mathbb{R}$-linear equivalence $(U\otimes_{\mathbb{R}} V)/S_{UV} \simeq_{\mathbb{R}} U\otimes_{\mathbb{C}} V$. By `UEOT.V3.Compression.QuotientDescent.existsUnique_descend`, any observable invariant under phase relocation descends uniquely to standard complex quantum mechanics.
4. **Zero-Energy Degenerate Reference Reset**: Applying a local improper $O(2)$ reflection twirl $\frac{1}{2}(\mathcal{I} + Z\cdot Z^T)$ on one laboratory alone flips $Z J Z^T = -J$ and collapses $\tau_{AB} \mapsto \frac{1}{4}I_4$ with zero energy-gap requirement.

Evidence: [verify_selection.py](verify_selection.py) · [result.json](result.json)
