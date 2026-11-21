# What Prediction Leaves Out: Relational Objecthood and the Grounds of Purpose

**Degui Qian · Version 2.0 (Standalone Journal Submission Edition) · November 2026**

A self-contained philosophical and mathematical research article examining when successful predictive representations justify ontological claims about what persists as an individual and teleological claims about what its activity is for.

## Manuscript deliverables

- [Typeset journal manuscript (PDF, 30 pages)](manuscript.pdf)
- [Markdown manuscript source](manuscript.md)
- [Generated LaTeX source](manuscript.tex)
- [Verified external scholarly bibliography (93 entries)](references.bib)
- [Chinese abstract and structural synopsis](ABSTRACT_ZH.md)
- [Claim and formal proof matrix](CLAIM_MATRIX.md)
- [Build receipt](BUILD_RECEIPT.json) and [editorial/arithmetic validation](VALIDATION.json)

## Core contributions of Version 2.0

1. **Strictly standalone foundational article.** Written as an independent, self-contained inaugural article with zero reliance on unpublished internal manuscripts or external repository snapshots. Every formal definition, proposition, counterexample, and theorem used in the philosophical argument is proved in full in the article's Mathematical Appendix.
2. **Typed Principle of Explanatory Preservation & Constrained Relational Objecthood.** Establishes countable-protocol predictive minimality (Proposition 1) and closed-test Bayes–Bellman belief-quotient descent (Proposition 2), and defends three jointly exclusionary criteria for relational objecthood—non-trivial predictive–control compression, counterfactual intervention invariance, and realization-cost/constraint accountability—against both pure compressionism and unconstrained Markov-blanket metaphysics.
3. **Unified regenerative model and four sharp separations.** Presents a single stochastic repair–reproduction model $\mathcal{M}$ proving: (i) the 2–3–4 protocol-relative predictive separation and infinite-horizon erasure of paid repair expenditure (Proposition 3); (ii) lawful silent-tag quotients versus von Neumann's gap between decoded symbolic instructions and physical gate actuation (Proposition 4); (iii) minimal destructive cut-set reconstruction (Proposition 5), finite-memory versus memoryless viability separation, and fixed-sample zero-violation certification impossibility (Proposition 6); and (iv) dual-criterion affine gauge underdetermination plus a local rank-three smooth bottleneck obstruction (Proposition 7).
4. **Full-policy growth ceiling and Four-Rung Grounds of Purpose.** Proves the exact expected population growth ceiling $\rho_* = \max\{1, \lambda_0, \lambda_1\}$ and necessary-and-sufficient joint realization conditions from a damaged founder (Theorem 1), isolating organism-versus-lineage trade-offs, critical finite-deadline deficits ($11/12 < 1$), and single-population stochastic extinction ($243/2048$). Formulates a four-rung stratification of purposive grounds engaging contemporary philosophy of biology, cognitive science, and normativity across **93 verified external scholarly works**.

## Reproducible build and verification

From this directory (with Python 3, Pandoc, XeLaTeX, BibTeX, Latexmk, and Poppler utilities installed):

```bash
python3 build.py
python3 validate.py
```

- `build.py` compiles `manuscript.md` + `references.bib` via Pandoc and `latexmk -xelatex`, verifying zero LaTeX/citation errors, zero missing glyphs, and zero overfull boxes, and writes `BUILD_RECEIPT.json`.
- `validate.py` verifies abstract and main-body word budgets, 1-to-1 citation parity across all 93 external BibTeX entries, absence of unpublished self-citations or internal project jargon, PDF text extraction integrity, and exact rational arithmetic for all printed model identities, writing `VALIDATION.json`.
