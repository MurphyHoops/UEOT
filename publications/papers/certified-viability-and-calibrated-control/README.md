# Pure-Kernel Verified Controller Synthesis, Fixed-Sample Impossibility, and Calibrated Post-Selection Risk under Partial Observation

**Degui Qian · Version 1.2 (Standalone Master Edition & *Journal of Automated Reasoning* Single-Blind Submission Package) · November 2026**

A self-contained mathematical, control-theoretic, and interactive-theorem-proving research article prepared for submission to the *Journal of Automated Reasoning* (or *ACM Transactions on Computational Logic* / *IEEE Transactions on Automatic Control*), establishing pure-kernel Lean 4 verified controller synthesis, fixed-sample exact-support impossibility, candidate-count-free calibrated post-selection risk bounds, binary-observation measurable belief quotients, and prepaid fault-mechanism minimax regret.

## Deliverables

- **Master Complete Edition (v1.2):**
  - [Typeset master manuscript (PDF, with vector Figures 1–2)](manuscript.pdf)
  - [Markdown manuscript source](manuscript.md) · [Generated LaTeX source](manuscript.tex) · [Verified external bibliography (83 entries)](references.bib)
  - [Zero-dependency standalone referee verifier (`verify_standalone.py`)](verify_standalone.py) · [Programmatic vector figure generator](generate_figures.py) & [Vector/300-DPI Figures 1–2](figures/)
  - [Chinese abstract and formal contribution synopsis](ABSTRACT_ZH.md) · [Claim, self-contained proof, and Lean 4 correspondence matrix](CLAIM_MATRIX.md)
  - [Archived pure-kernel Lean 4 formalization (Apache-2.0, Zenodo DOI: 10.5281/zenodo.24433585)](https://doi.org/10.5281/zenodo.24433585)
  - [Build receipt](BUILD_RECEIPT.json) · [Editorial/arithmetic/DP validation](VALIDATION.json) · [Checksums](SHA256SUMS)
- **Portal-Ready Single-Blind Journal Package (`submissions/jar/`):**
  - [*Journal of Automated Reasoning* (Springer Nature) submission guide & manifest](submissions/jar/SUBMISSION_GUIDE_AND_MANIFEST.md)
  - [Single-blind referee manuscript PDF (`jar_manuscript.pdf`)](submissions/jar/jar_manuscript.pdf) · [Zero-dependency verifier (`submissions/jar/verify_standalone.py`)](submissions/jar/verify_standalone.py) · [Optional Title/Declarations Summary PDF (`jar_title_page.pdf`)](submissions/jar/jar_title_page.pdf) · [Tailored Cover Letter](submissions/jar/cover_letter.md) · [JAR compliance receipt (`VALIDATION_JAR.json`)](submissions/jar/VALIDATION_JAR.json)

## Core contributions

1. **Executable trace-support controller synthesis and infinite-trajectory safety semantics (Theorems 1–3).** Without requiring finite enumeration of the observation type $Y$ at the Lean interface, identifies positive-mass posterior supports with combinatorial trace-support recursion, proves König-type finite-action compactness $(\forall T,\,\exists\pi_T) \iff (\exists\pi_\infty)$ (contrasting finite qualitative action signatures with a countable-state countdown compactness failure), connects killed substochastic matrix powers $Q_K^T$ to Kolmogorov infinite-trajectory safety $\mathbb{P}(\forall n,\,X_n\in K)$, and proves soundness and completeness of the computable controller synthesizer `synthesize : Option (Program X Y A)`.
2. **Fixed-sample zero-support impossibility, calibrated post-selection risk, and multi-abstraction savings (Theorems 4–5 & §4.3).** Proves that no randomized fixed-sample black-box rule has uniform power above $\alpha$ to certify exact zero transition leakage, and verifies the rational computable `NoisyFiniteRiskOracle` decoupling sample-free perpetual safety in $K$ (under $I_0 = \operatorname{supp}(p_0)$ and $R = \operatorname{supp}(P)$) from calibrated finite-horizon risk across arbitrary finite candidate families under a single simultaneous row-calibration event—bounding unconditional joint failure $\mathbb{P}_J(\mathrm{selectedAccepts} \land E) \le \min\{1, \alpha_N + (1-\alpha_N)\beta\}$ without candidate-count union bounds, mapping exact integer-binomial operating curves ($u_N \propto N^{-1/2}$), and demonstrating $4$-state controllers and $72\times$–$147\times$ faster macro-reference verification on a $12$-state multi-abstraction benchmark.
3. **Measurable belief quotients, prepaid fault minimax regret, and GCD-free pure-kernel `decide` (Theorems 6–7 & Section 7).** Characterizes binary-observation Giry belief quotients via `ClosedTests`, establishes analytically the $H=2$ common optimum $13/16$ and exact $\{S,G\}$ fault distinguishability $\Delta_{3,B} = r^2(1-r)\mathbf{1}_{B\ge c}$, proves full-history randomized minimax regret $R^* = 3/128 < 1/32$, and introduces unnormalized integer-scaled dynamic programming (`UBelief`, `csolveInt`) eliminating `native_decide` (`Lean.ofReduceBool`) across all 1,051 compiled Lean 4 modules (1,030 declaration-defining modules audited across 19,987 constants and 13,004 theorems).

## Reproducible build and verification

From this directory:

```bash
python3 build.py
python3 verify_standalone.py
python3 validate.py
shasum -a 256 -c SHA256SUMS
```

- `build.py` regenerates Figures 1–2, compiles both the master `manuscript.pdf` and the single-blind *JAR* package (`submissions/jar/jar_manuscript.pdf` + `jar_title_page.pdf` + `verify_standalone.py`) via Pandoc and `latexmk -xelatex`, renders PNG inspection pages, verifies zero TeX/citation errors, zero missing glyphs, and zero overfull boxes, and writes `BUILD_RECEIPT.json`.
- `verify_standalone.py` uses **only the Python 3 standard library** (reading and writing zero external files, runnable from any directory) to independently verify exact arbitrary-precision integer binomial witness operating curves (`math.comb` + `Fraction`), the 12-state multi-abstraction benchmark (Table 3), and the full 7-action rational POMDP dynamic program (Theorem 7).
- `validate.py` verifies abstract and body word budgets, absence of undefined abbreviations in the abstract, 1-to-1 citation parity and zero BibTeX warnings across all 83 external BibTeX entries, single-blind *JAR* metadata and Zenodo DOI presence, and invokes `verify_standalone.py`, writing `VALIDATION.json`, `submissions/jar/VALIDATION_JAR.json`, and `SHA256SUMS`.
