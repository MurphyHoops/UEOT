# What Prediction Leaves Out: Relational Objecthood and the Grounds of Purpose

**Degui Qian · Version 2.4 (Standalone Master Edition & Three Journal Submission Packages) · November 2026**

A self-contained philosophical and mathematical research article examining when successful predictive representations justify ontological claims about what persists as an individual and teleological claims about what its activity is for.

## Master deliverables and journal submission folders

- **Master Complete Edition (v2.4):**
  - [Typeset master manuscript (PDF, with Figures 1–3)](manuscript.pdf)
  - [Markdown source](manuscript.md) · [LaTeX source](manuscript.tex) · [Verified bibliography (98 entries)](references.bib)
  - [Zero-dependency exact rational referee verifier](verify_standalone.py) · [Programmatic vector figure generator](generate_figures.py) & [Vector/300-DPI Figures 1–3](figures/)
  - [Chinese abstract and structural synopsis](ABSTRACT_ZH.md) · [Claim and proof matrix](CLAIM_MATRIX.md)
  - [Companion pure-kernel Lean 4 formalization archive (Apache-2.0, Zenodo DOI: 10.5281/zenodo.24433585)](https://doi.org/10.5281/zenodo.24433585)
  - [Build receipt](BUILD_RECEIPT.json) · [Editorial/arithmetic validation](VALIDATION.json) · [Checksums](SHA256SUMS)
- **Three Uncompressed, Portal-Ready Journal Submission Packages (`submissions/`):**
  1. [**`submissions/bjps/`**](submissions/bjps/SUBMISSION_GUIDE_AND_MANIFEST.md) — *The British Journal for the Philosophy of Science* (Triple-anonymous, UK English `en-GB`, **12pt Times New Roman, 1.5x spacing, 1-in margins**, unbroken single-page tables, bundled anonymous `verify_standalone.py`, post-abstract AI Statement + complete 5-stage Appendix B prompt/workflow log, strictly $\le 24$ pages excl. Title/Abstract/References and $\le 10,000$ words)
  2. [**`submissions/philosophy-of-science/`**](submissions/philosophy-of-science/SUBMISSION_GUIDE_AND_MANIFEST.md) — *Philosophy of Science* (Double-anonymous, US English `en-US`, bundled anonymous `verify_standalone.py`, Page 1 Title $\to$ $\le 100$-word Abstract $\to$ Section 1, total manuscript incl. abstract & 98 references strictly $\le 9,500$ words)
  3. [**`submissions/synthese/`**](submissions/synthese/SUBMISSION_GUIDE_AND_MANIFEST.md) — *Synthese* (Double-anonymous Springer two-file split: separate `synthese_title_page.pdf` + blinded `synthese_blinded_manuscript.pdf` with 6 keywords, integrated proofs, bundled anonymous `verify_standalone.py`, and mandatory `Declarations` before `References`)

## Core contributions of Version 2.4

1. **Fixed-Parameter Two-Step Birth Saturation, Blackwell Non-Simulability, & Three-Step Parameter Boundary.** Proves across the strict parameter domain of $\mathcal{M}$ that for the four founder states $\{\theta_0 H, \theta_0 D, \theta_1 H, \theta_1 D\}$ executing their hereditary programs autonomously at fixed parameters, two birth censuses $(B_1, B_2)$ exhaust the probability law of the infinite birth stream $(B_t)_{t\ge 1}$ while erasing initial repair expenditure ($R_1 = 0$ vs. $3$); shows that $(B_1, B_2)$ and $(B_1, R_1)$ are mutually non-simulable statistical experiments under Markov post-processing [@blackwell1953; @barnettCrutchfield2015]; and exhibits an exact three-step parameter-identifiability boundary ($\theta_1 D$ with $\delta = 1/8$ vs. $\delta' = 1/4$: identical $(B_1, B_2)$ joint law on $\{0,1\} \times \{0,1,2\}$, yet $\mathbb{E}[B_3] = 377/512$ vs. $351/512$; Proposition 3, Figure 1b).
2. **Typed Explanatory Preservation, Reachable-Fiber Belief Descent, & Calibrated Objecthood Checks.** Establishes countable-protocol predictive minimality (Proposition 1) and closed-test Bayes–Bellman belief-quotient descent (Proposition 2, contrasting full-simplex invariance [@poupartBoutilier2003] with merged-pair matching on reachable sets via an explicit 3-state cyclic counterexample), calibrating three diagnostic checks for relational objecthood vis-à-vis liberalized pattern realism and symmetrical fission while separating fast-timescale paid endogenous repair (Table 3, 3a) from slow-timescale reciprocal constraint closure (3b).
3. **Explicit Blanket Scope, Formal $\mathcal{M}_{\mathrm{vote}}$ vs. $\mathcal{M}_{\mathrm{bypass}}$ Transitions, & Engineered-Register Discrimination.** Formalizes $\tau$-blind Markov lumpability versus von Neumann's syntactic–gate separation (Proposition 4), clarifies why local mediation $(r_H, r_D) \to (d_t, g_t, a_t) \to B_t$ does not assume stationary Friston blankets while still erasing $R_1$ on output-sufficient interfaces [@friston2013; @bruineberg2022], gives explicit transition rules for $\mathcal{M}_{\mathrm{vote}}$ versus $\mathcal{M}_{\mathrm{bypass}}$ from $(\theta_0, D)$ (matching on $((B_t, R_t))_{t\ge 1}$ at $b_{\mathrm{boot}}=1$ while splitting into $0$ vs. $b > 0$ under $\mathrm{do}(b_{\mathrm{boot}}=0)$; @rubenstein2017), and formulates a four-arm test on an engineered fault-tolerant register with bacterial `MutS–MutL–MutH` repair retained as qualitative motivation.
4. **Full-Policy Ceiling, Subcritical Finite-Births Corollary, & Calibrated Four-Rung Purpose.** Benchmarks autonomous hereditary execution against the public-history growth ceiling $\rho_* = \max\{1, \lambda_0, \lambda_1\}$ (Theorem 1, Figure 2b), proves that subcritical regimes ($\max\{\lambda_0, \lambda_1\} < 1$) satisfy $\mathbb{E}_\pi[\sum_{t\ge 1} B_t] < \infty$ across all $\pi \in \Pi_{\mathrm{pub}}$ (so attaining $\rho_* = 1$ preserves only frozen tokens), and stratifies four bearer-indexed grounds of purpose—presenting slow reciprocal closure and Rung 3 selection history as distinct candidate grounds requiring independent philosophical defense in response to Corti (2023)—across **98 verified external scholarly works**.

## Author contributions and AI disclosure

Degui Qian conceived the philosophical problem, core framework, regenerative model $\mathcal{M}$, and competing-mechanism design, directed all revisions, independently verified every proof, exact rational calculation, and all 98 references, and bears sole academic and legal responsibility. **ChatGPT 6 Astra** provided adversarial referee-style stress-testing and mathematical/conceptual critique (quantifier scopes, reachable-set conditions, fixed-parameter saturation and the three-step $\delta \in \{1/8, 1/4\}$ boundary witness, the subcritical finite-births bound, and Section 6 mechanism specification); **Gemini 4 Carbon** implemented exact `fractions.Fraction` verification (`verify_standalone.py`, `validate.py`) and vector figures (`generate_figures.py`), harmonized prose and formatting across editions, and audited BibTeX/TeX builds under human verification.

## Reproducible build and verification

```bash
python3 verify_standalone.py
python3 build.py
python3 validate.py
shasum -a 256 -c SHA256SUMS
```
