# What Prediction Leaves Out: Relational Objecthood and the Grounds of Purpose

**Degui Qian · Version 2.2 (Standalone Master Edition & Three Journal Submission Packages) · November 2026**

A self-contained philosophical and mathematical research article examining when successful predictive representations justify ontological claims about what persists as an individual and teleological claims about what its activity is for.

## Master deliverables and journal submission folders

- **Master Complete Edition (v2.2):**
  - [Typeset master manuscript (PDF, with Figures 1–3)](manuscript.pdf)
  - [Markdown source](manuscript.md) · [LaTeX source](manuscript.tex) · [Verified bibliography (96 entries)](references.bib)
  - [Programmatic vector figure generator](generate_figures.py) & [Vector/300-DPI Figures 1–3](figures/)
  - [Chinese abstract and structural synopsis](ABSTRACT_ZH.md) · [Claim and proof matrix](CLAIM_MATRIX.md)
  - [Companion pure-kernel Lean 4 formalization archive (Apache-2.0, Zenodo DOI: 10.5281/zenodo.24433585)](https://doi.org/10.5281/zenodo.24433585)
  - [Build receipt](BUILD_RECEIPT.json) · [Editorial/arithmetic validation](VALIDATION.json) · [Checksums](SHA256SUMS)
- **Three Uncompressed, Portal-Ready Journal Submission Packages (`submissions/`):**
  1. [**`submissions/bjps/`**](submissions/bjps/SUBMISSION_GUIDE_AND_MANIFEST.md) — *The British Journal for the Philosophy of Science* (Triple-anonymous, UK English `en-GB`, **12pt Times New Roman, 1.5x spacing, 1-in margins**, post-abstract AI Statement + Appendix B prompt log, strictly $\le 24$ pages excl. Title/Abstract/References and $\le 10,000$ words)
  2. [**`submissions/philosophy-of-science/`**](submissions/philosophy-of-science/SUBMISSION_GUIDE_AND_MANIFEST.md) — *Philosophy of Science* (Double-anonymous, US English `en-US`, Page 1 Title $\to$ 96-word Abstract ($\le 100$ words) $\to$ Section 1, total manuscript incl. abstract & 96 references strictly $\le 9,500$ words)
  3. [**`submissions/synthese/`**](submissions/synthese/SUBMISSION_GUIDE_AND_MANIFEST.md) — *Synthese* (Double-anonymous Springer two-file split: separate `synthese_title_page.pdf` + blinded `synthese_blinded_manuscript.pdf` with 194-word abstract, 6 keywords, integrated proofs, and mandatory `Declarations` before `References`)

## Core contributions of Version 2.2

1. **Incomparable Predictive Refinements & Forward-Marginalization Asymmetry.** Proves across the full strict parameter domain of $\mathcal{M}$ that undamaged and self-repairing conservative individuals share the exact infinite-horizon birth law while paying $0$ versus $3$ repair units, and that extending birth censuses versus adjoining first-step repair calorimetry produces *mutually incomparable three-class refinements* (Proposition 3, Figure 1b)—showing that which type of evidence is added dictates which explanatory question becomes identifiable.
2. **Typed Explanatory Preservation & Calibrated Relational Objecthood.** Establishes countable-protocol predictive minimality (Proposition 1) and closed-test Bayes–Bellman belief-quotient descent (Proposition 2), calibrating three exclusionary criteria for relational objecthood—tested explicitly against symmetrical fission and distinguishing fast-timescale paid endogenous repair from full slow-timescale reciprocal constraint closure (Figure 3).
3. **Syntactic–Constructor Separation, Viability Memory, & Empirical Predictions.** Formalizes $\tau$-blind Markov lumpability versus von Neumann's gap between decoded symbolic instructions and physical gate actuation (Proposition 4), finite-memory versus memoryless viability separation (Proposition 6a, Figure 2a), fixed-sample zero-risk impossibility (Proposition 6b), and smooth bottleneck rank obstructions (Proposition 7), separating established *E. coli* `MutS–MutL–MutH` biochemistry from testable calorimetry predictions.
4. **Full-Policy Ceiling vs. Autonomous Hereditary Attainment & Four-Rung Purpose.** Benchmarks autonomous multi-generational execution of fixed hereditary programs $\theta_i$ against the full public-history growth ceiling $\rho_* = \max\{1, \lambda_0, \lambda_1\}$ (Theorem 1, Figure 2b)—contrasting active hereditary persistence with subcritical dormancy switching $(1/2, 1/4, 1/4, 1/8, 1/3)$—and stratifies four bearer-indexed grounds of purpose separating conditional Rung 2 regulatory standards (answering Corti 2023), prospective growth, and retrospective Rung 3 selection across **96 verified external scholarly works**.

## Reproducible build and verification

```bash
python3 build.py
python3 validate.py
shasum -a 256 -c SHA256SUMS
```
