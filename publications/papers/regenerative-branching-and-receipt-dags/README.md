# Prepayment Thresholds, Informative Zero Receipts, and Certified Polynomial Decision Diagrams in Partially Observed Regenerative Maintenance

**Degui Qian · Version 1.0 (Standalone Master Edition & INFORMS *Mathematics of Operations Research* Submission Package) · November 2026**

A self-contained stochastic operations research, Bayesian dynamic programming, and formal-verification article establishing native-to-compressed genealogical commutation, exact high-price continuation formulas, post-fault posterior threshold contraction, informative zero-receipt counting posteriors, five-coordinate joint sufficiency, and certified $O(H^4)$ policy decision diagrams under sample-path prepayment.

## Deliverables

- **Master Complete Edition (v1.0):**
  - [Typeset master manuscript (PDF, with vector Figures 1–3)](manuscript.pdf)
  - [Markdown source](manuscript.md) · [Generated LaTeX source](manuscript.tex) · [Verified external bibliography (96 entries)](references.bib)
  - [Programmatic vector figure generator](generate_figures.py) & [Vector/300-DPI Figures 1–3](figures/)
  - [Chinese abstract and structural synopsis](ABSTRACT_ZH.md) · [Claim, proof, and Lean 4 correspondence matrix](CLAIM_MATRIX.md)
  - [Archived pure-kernel Lean 4 formalization (Apache-2.0, Zenodo DOI: 10.5281/zenodo.24433585)](https://doi.org/10.5281/zenodo.24433585)
  - [Build receipt](BUILD_RECEIPT.json) · [Editorial & live rational solver validation](VALIDATION.json) · [Checksums](SHA256SUMS)
- **Portal-Ready Double-Anonymous Journal Package (`submissions/mor/`):**
  - [*Mathematics of Operations Research* (INFORMS) submission guide & manifest](submissions/mor/SUBMISSION_GUIDE_AND_MANIFEST.md)
  - [Double-anonymous manuscript PDF (`mor_blinded_manuscript.pdf`)](submissions/mor/mor_blinded_manuscript.pdf) · [Separate Title Page PDF (`mor_title_page.pdf`)](submissions/mor/mor_title_page.pdf) · [Tailored Cover Letter](submissions/mor/cover_letter.md) · [MOR compliance receipt (`VALIDATION_MOR.json`)](submissions/mor/VALIDATION_MOR.json)

## Core mathematical and computational results

1. **Native genealogical commutation & real-randomized Bayes optimality (Theorem 1).** Proves exact step-by-step commutation between an unbounded native genealogical population store $\mathcal{S}_t$ and a compressed slot-bit dynamic program, certifying literal sample-path prepayment $B_t = B_0 - \sum_{s<t} C_s \ge 0$ and optimality over all supported-admissible real-randomized history strategies.
2. **Closed-form high-price continuation & value-of-information asymmetries (Theorems 2–3).** Establishes $V_{H+1}^* = \max\{0, \mathbb{E}[r_\theta(1 - p + d U_2(r_\theta, d, H))]\}$ for $B_0 = c, p \ge S_H(d)$ with iff threshold $p < 1 + d M_H / \mu_1$; isolates the persistence variance premium $d\,\mathrm{Var}(r_\theta)$ ($+1/160$ vs. $-1/40$), strict post-fault threshold drop ($21/16 \to 5/4$, prior-freeze loss $3/640$), four-step receipt-feedback gain $d^3\mathbb{E}[r_\theta^3(1-r_\theta)]$ ($20925/524288$), and exact zero post-repair value of $\theta$-revelation ($\mathrm{EVPI}_{\mathrm{post}} = 0$).
3. **Informative zero-receipt filtering, five-coordinate sufficiency, & $24(H+1)^4$ certified DAGs (Theorems 4–6).** Proves universal counting-posterior factorization $\pi_0(\theta) r_\theta^s (1-r_\theta)^f / Z(s,f)$ across all randomized policies, joint all-action sufficiency and sharpness separations for $\sigma = (t, q, s, f, k)$, and soundness of the all-action rational certificate checker `certify : Option Certified` enforcing $N_H \le 24(H+1)^4$ (compressing $28^8 \approx 3.78 \times 10^{11}$ raw branches at $H=8, B_0=2$ into $1,661$ certified nodes and $151$ execution nodes with exact value $884450457 / 1342177280$).

## Reproducible build and live exact-rational verification

```bash
python3 build.py
python3 validate.py
shasum -a 256 -c SHA256SUMS
```
