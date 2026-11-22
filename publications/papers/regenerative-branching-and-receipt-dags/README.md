# Prepayment Thresholds, Informative Zero Receipts, and Certified Polynomial Decision Diagrams in Partially Observed Regenerative Maintenance

**Degui Qian · Version 1.2 (Standalone Master Edition & INFORMS *Mathematics of Operations Research* Submission Package) · November 2026**

A self-contained stochastic operations research, Bayesian dynamic programming, and formal-verification article establishing arbitrary-price single-repair ($c \le B_0 < 2c$) monotone retry stopping rules, four-step standby-window threshold flips, post-fault posterior threshold contraction, native-to-compressed genealogical commutation, informative zero-receipt counting posteriors, five-coordinate joint sufficiency, and certifying $O(1 + (\min(M,H)+1)H^3)$ reachable / $24(H+1)^4$ `accept`-bounded policy decision diagrams under sample-path prepayment.

## Deliverables

- **Master Complete Edition (v1.2):**
  - [Typeset master manuscript (PDF, with vector Figures 1–3)](manuscript.pdf)
  - [Markdown source](manuscript.md) · [Generated LaTeX source](manuscript.tex) · [Verified external bibliography (99 entries)](references.bib)
  - [Programmatic vector figure generator](generate_figures.py) & [Vector/300-DPI Figures 1–3](figures/)
  - [Chinese abstract and structural synopsis](ABSTRACT_ZH.md) · [Claim, proof, and Lean 4 correspondence matrix](CLAIM_MATRIX.md)
  - [Archived pure-kernel Lean 4 formalization (Apache-2.0, Zenodo DOI: 10.5281/zenodo.24433585)](https://doi.org/10.5281/zenodo.24433585)
  - [Build receipt](BUILD_RECEIPT.json) · [Editorial & live rational solver validation](VALIDATION.json) · [Checksums](SHA256SUMS)
- **Portal-Ready Double-Anonymous Journal Package (`submissions/mor/`):**
  - [*Mathematics of Operations Research* (INFORMS) submission guide & manifest](submissions/mor/SUBMISSION_GUIDE_AND_MANIFEST.md)
  - [Double-anonymous manuscript PDF (`mor_blinded_manuscript.pdf`)](submissions/mor/mor_blinded_manuscript.pdf) · [Separate Title Page PDF (`mor_title_page.pdf`)](submissions/mor/mor_title_page.pdf) · [Tailored Cover Letter](submissions/mor/cover_letter.md) · [MOR compliance receipt (`VALIDATION_MOR.json`)](submissions/mor/VALIDATION_MOR.json)

## Core mathematical and computational results

1. **Native genealogical commutation & real-randomized Bayes optimality (Theorem 1).** Proves exact step-by-step commutation between an unbounded native genealogical population store $\mathcal{S}_t$ (with initialization-epoch standby provisioning at `child1`) and a compressed slot-bit dynamic program, certifying literal sample-path prepayment $B_t = B_0 - \sum_{s<t} C_s \ge 0$ and optimality over all supported-admissible real-randomized history strategies.
2. **Arbitrary-price single-repair ($c \le B_0 < 2c$) optimal retry stopping & value-of-information asymmetries (Theorems 2–3).** Establishes single-crossing marginal retry payoffs $\Delta_t$ and $V_{H+1}^* = \sum_{t=0}^H d^t \max\{0, \Delta_t\}$ across $c \le B_0 < 2c$ and *all* prices $p \ge 0$ (with universal positivity criterion $p < p_0^*(H)$, nested retry-depth thresholds $p_0^* \ge \dots \ge p_H^*$, four-step standby-window threshold flip $53/32 \to 97/64$ at $p = 8/5$, and high-price specialization $p \ge S_H(d)$); isolates the persistence variance premium $d\,\mathrm{Var}(r_\theta)$, strict post-fault threshold drop ($21/16 \to 5/4$, prior-freeze loss $3/640$), four-step device-state receipt-feedback gain $d^3\mathbb{E}[r_\theta^3(1-r_\theta)]$ ($20925/524288$), and exact zero post-repair value of $\theta$-revelation ($\mathrm{EVPI}_{\mathrm{post}} = 0$).
3. **Informative zero-receipt filtering, five-coordinate sufficiency, & certifying polynomial DAGs (Theorems 4–6).** Proves universal counting-posterior factorization $\pi_0(\theta) r_\theta^s (1-r_\theta)^f / Z(s,f)$, joint all-action sufficiency of $\sigma = (t, q, s, f, k)$ (collapsing to $\delta = s - f$ under complementary two-point priors), two-layer `accept` (`certify` + `boundCheck`) soundness with $N_H \le 24(H+1)^4$, and canonical generator completeness with $N_{\mathrm{reach}}(H,M) = O(1 + (\min(M,H)+1)H^3)$ nodes and polynomial-in-$H$ rational synthesis/checking (compressing $23,841,395$ legal positive-probability eight-step histories at $B_0 = 2$ into $1,661$ general certified nodes, $1,020$ log-odds nodes, and $151$ execution nodes in $0.18\text{ s}$ with exact value $884450457 / 1342177280$).

## Reproducible build and live exact-rational verification

```bash
python3 build.py
python3 validate.py
python3 validate.py --benchmark-timings
shasum -a 256 -c SHA256SUMS
```
