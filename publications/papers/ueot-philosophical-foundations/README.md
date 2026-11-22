# What Prediction Leaves Out: Relational Objecthood and the Grounds of Purpose

**Degui Qian · Version 2.3 (Standalone Master Edition & Three Journal Submission Packages) · November 2026**

A self-contained philosophical and mathematical research article examining when successful predictive representations justify ontological claims about what persists as an individual and teleological claims about what its activity is for.

## Master deliverables and journal submission folders

- **Master Complete Edition (v2.3):**
  - [Typeset master manuscript (PDF, with Figures 1–3)](manuscript.pdf)
  - [Markdown source](manuscript.md) · [LaTeX source](manuscript.tex) · [Verified bibliography (98 entries)](references.bib)
  - [Programmatic vector figure generator](generate_figures.py) & [Vector/300-DPI Figures 1–3](figures/)
  - [Chinese abstract and structural synopsis](ABSTRACT_ZH.md) · [Claim and proof matrix](CLAIM_MATRIX.md)
  - [Companion pure-kernel Lean 4 formalization archive (Apache-2.0, Zenodo DOI: 10.5281/zenodo.24433585)](https://doi.org/10.5281/zenodo.24433585)
  - [Build receipt](BUILD_RECEIPT.json) · [Editorial/arithmetic validation](VALIDATION.json) · [Checksums](SHA256SUMS)
- **Three Uncompressed, Portal-Ready Journal Submission Packages (`submissions/`):**
  1. [**`submissions/bjps/`**](submissions/bjps/SUBMISSION_GUIDE_AND_MANIFEST.md) — *The British Journal for the Philosophy of Science* (Triple-anonymous, UK English `en-GB`, **12pt Times New Roman, 1.5x spacing, 1-in margins**, unbroken single-page tables, post-abstract AI Statement + complete 5-stage Appendix B prompt/workflow log, strictly $\le 24$ pages excl. Title/Abstract/References and $\le 10,000$ words)
  2. [**`submissions/philosophy-of-science/`**](submissions/philosophy-of-science/SUBMISSION_GUIDE_AND_MANIFEST.md) — *Philosophy of Science* (Double-anonymous, US English `en-US`, Page 1 Title $\to$ 96-word Abstract ($\le 100$ words) $\to$ Section 1, total manuscript incl. abstract & 98 references strictly $\le 9,500$ words)
  3. [**`submissions/synthese/`**](submissions/synthese/SUBMISSION_GUIDE_AND_MANIFEST.md) — *Synthese* (Double-anonymous Springer two-file split: separate `synthese_title_page.pdf` + blinded `synthese_blinded_manuscript.pdf` with 6 keywords, integrated proofs, and mandatory `Declarations` before `References`)

## Core contributions of Version 2.3

1. **Two-Step Birth Saturation, Incomparable Protocol Refinements, & Forward-Confluence Condition.** Proves across the full strict parameter domain of $\mathcal{M}$ that two birth censuses $(B_1, B_2)$ already achieve the full resolution of the infinite birth stream $(B_t)_{t\ge 1}$ while erasing initial repair expenditure ($R_1 = 0$ vs. $3$), and that extending birth censuses versus adjoining first-step calorimetry produces *mutually incomparable three-class refinements over protocol probability laws* (Proposition 3, Figure 1b)—separating distributional identifiability from single-run overlap and stating the exact post-step confluence condition under which history is erased.
2. **Typed Explanatory Preservation, Reachable-Fiber Belief Descent, & Calibrated Objecthood Checks.** Establishes countable-protocol predictive minimality (Proposition 1) and closed-test Bayes–Bellman belief-quotient descent (Proposition 2, contrasting full-simplex invariance [@poupartBoutilier2003] with merged-pair matching on reachable sets via an explicit 3-state cyclic counterexample), calibrating three diagnostic checks for relational objecthood vis-à-vis liberalized pattern realism and symmetrical fission while separating fast-timescale paid endogenous repair (Table 3, 3a) from slow-timescale reciprocal constraint closure (3b).
3. **Action-Mediated Output Counterexample & Same-Damage Mechanism Discrimination.** Formalizes $\tau$-blind Markov lumpability versus von Neumann's gap between decoded symbolic instructions and physical gate actuation (Proposition 4), specifies the full sensory–active mediation path $(r_H, r_D) \to (d_t, g_t, a_t) \to B_t$ in output-only Markov-blanket evaluations, and contrasts two rival recovery mechanisms under *identical initial damage* ($\mathcal{M}_{\mathrm{vote}}$ vs. $\mathcal{M}_{\mathrm{bypass}}$) tested via $\mathrm{do}(b_{\mathrm{boot}}=0)$ [@rubenstein2017].
4. **Full-Policy Ceiling vs. Autonomous Hereditary Attainment & Calibrated Four-Rung Purpose.** Benchmarks autonomous multi-generational execution of fixed hereditary programs $\theta_i$ against the full public-history growth ceiling $\rho_* = \max\{1, \lambda_0, \lambda_1\}$ (Theorem 1, Figure 2b) and stratifies four bearer-indexed grounds of purpose—supplying an operational conditional standard at Rung 2 while pinpointing where Corti's (2023) intrinsic-normativity challenge retains force—across **98 verified external scholarly works**.

## Reproducible build and verification

```bash
python3 build.py
python3 validate.py
shasum -a 256 -c SHA256SUMS
```
