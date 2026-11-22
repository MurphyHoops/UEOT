# Pure-Kernel Verified Controller Synthesis, Fixed-Sample Impossibility, and Calibrated Post-Selection Risk under Partial Observation

**Degui Qian · Version 1.0 (Standalone Master Edition & *Journal of Automated Reasoning* Double-Anonymous Submission Package) · November 2026**

A self-contained mathematical, control-theoretic, and interactive-theorem-proving research article prepared for submission to the *Journal of Automated Reasoning* (or *ACM Transactions on Computational Logic* / *IEEE Transactions on Automatic Control*), establishing pure-kernel Lean 4 verified controller synthesis, fixed-sample exact-support impossibility, candidate-count-free calibrated post-selection risk bounds, standard-Borel observable belief quotients, and prepaid fault-mechanism minimax regret.

## Deliverables

- **Master Complete Edition (v1.0):**
  - [Typeset master manuscript (PDF, with vector Figures 1–2)](manuscript.pdf)
  - [Markdown manuscript source](manuscript.md) · [Generated LaTeX source](manuscript.tex) · [Verified external bibliography (80 entries)](references.bib)
  - [Programmatic vector figure generator](generate_figures.py) & [Vector/300-DPI Figures 1–2](figures/)
  - [Chinese abstract and formal contribution synopsis](ABSTRACT_ZH.md) · [Claim, self-contained proof, and Lean 4 correspondence matrix](CLAIM_MATRIX.md)
  - [Archived pure-kernel Lean 4 formalization (Apache-2.0, Zenodo DOI: 10.5281/zenodo.24433585)](https://doi.org/10.5281/zenodo.24433585)
  - [Build receipt](BUILD_RECEIPT.json) · [Editorial/arithmetic validation](VALIDATION.json) · [Checksums](SHA256SUMS)
- **Portal-Ready Double-Anonymous Journal Package (`submissions/jar/`):**
  - [*Journal of Automated Reasoning* (Springer Nature) submission guide & manifest](submissions/jar/SUBMISSION_GUIDE_AND_MANIFEST.md)
  - [Double-anonymous manuscript PDF (`jar_blinded_manuscript.pdf`)](submissions/jar/jar_blinded_manuscript.pdf) · [Separate Title Page PDF (`jar_title_page.pdf`)](submissions/jar/jar_title_page.pdf) · [Tailored Cover Letter](submissions/jar/cover_letter.md) · [JAR compliance receipt (`VALIDATION_JAR.json`)](submissions/jar/VALIDATION_JAR.json)

## Core contributions

1. **Strictly standalone archival formal-methods article.** Written with zero reliance on unpublished internal manuscripts or bespoke project acronyms. Every mathematical definition, theorem, counterexample, and rational identity is proved self-containedly in Appendix A.1–A.6 while mapping directly to pure-kernel verified Lean 4 (v4.33.1 / Mathlib) declarations.
2. **Non-circular trace-support viability, König quantifier exchange, and computable synthesis (Theorems 1–3).** Identifies positive-mass posterior supports with combinatorial trace-support recursion without assuming finite observation spaces, proves $(\forall T,\,\exists\pi_T) \iff (\exists\pi_\infty)$ for finite actions, connects substochastic killed matrix powers to Kolmogorov infinite-trajectory safety, and proves soundness and completeness of the purely computable controller synthesizer `synthesize : Option (Program X Y A)`.
3. **Fixed-sample zero-support impossibility and candidate-free post-selection calibration (Theorems 4–5).** Proves that no randomized fixed-sample black-box rule has uniform power above $\alpha$ to certify exact zero transition leakage, and verifies the rational computable `NoisyFiniteRiskOracle` establishing $\Pr_J(\mathrm{selectedAccepts} \land E) \le \min\{1, \alpha_N + (1-\alpha_N)\beta\}$ without candidate-count union bounds.
4. **Standard-Borel belief quotients, prepaid fault minimax regret, and greatest-common-divisor-free pure-kernel `decide` (Theorems 6–7 & Section 7).** Characterizes measurable Markov belief quotients via `ClosedTests`, establishes exact $\{S,G\}$ fault distinguishability $\Delta_{3,B} = r^2(1-r)\mathbf{1}_{B\ge c}$ and randomized minimax regret $R^* = 3/128 < 1/32$, and introduces unnormalized integer-scaled dynamic programming (`csolveInt`) eliminating `native_decide` (`Lean.ofReduceBool`) across all 1,051 Lean 4 modules.

## Reproducible build and verification

From this directory:

```bash
python3 build.py
python3 validate.py
shasum -a 256 -c SHA256SUMS
```

- `build.py` regenerates Figures 1–2, compiles both the master `manuscript.pdf` and the double-anonymous *JAR* package (`submissions/jar/jar_blinded_manuscript.pdf` + `jar_title_page.pdf`) via Pandoc and `latexmk -xelatex`, renders PNG inspection pages, verifies zero TeX/citation errors, zero missing glyphs, and zero overfull boxes, and writes `BUILD_RECEIPT.json`.
- `validate.py` verifies abstract and body word budgets, absence of undefined abbreviations in the abstract, 1-to-1 citation parity and zero BibTeX warnings across all 80 external BibTeX entries, strict double-anonymous blinding on `jar_blinded_manuscript.pdf`, and exact rational/exponential checks for all printed numerical identities, writing `VALIDATION.json`, `submissions/jar/VALIDATION_JAR.json`, and `SHA256SUMS`.
