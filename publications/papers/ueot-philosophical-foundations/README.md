# What Prediction Leaves Out: Relational Objecthood and the Grounds of Purpose

**Degui Qian · Version 2.1 (Standalone Master Edition & Three Journal Submission Packages) · November 2026**

A self-contained philosophical and mathematical research article examining when successful predictive representations justify ontological claims about what persists as an individual and teleological claims about what its activity is for.

## Master deliverables and journal submission folders

- **Master Complete Edition (v2.1):**
  - [Typeset master manuscript (PDF, 32 pages, with Figures 1–3)](manuscript.pdf)
  - [Markdown source](manuscript.md) · [LaTeX source](manuscript.tex) · [Verified bibliography (93 entries)](references.bib)
  - [Programmatic vector figure generator](generate_figures.py) & [Vector/300-DPI Figures 1–3](figures/)
  - [Chinese abstract and structural synopsis](ABSTRACT_ZH.md) · [Claim and proof matrix](CLAIM_MATRIX.md)
  - [Build receipt](BUILD_RECEIPT.json) · [Editorial/arithmetic validation](VALIDATION.json)
- **Three Uncompressed, Portal-Ready Journal Submission Packages (`submissions/`):**
  1. [**`submissions/bjps/`**](submissions/bjps/SUBMISSION_GUIDE_AND_MANIFEST.md) — *The British Journal for the Philosophy of Science* (Triple-anonymous, UK English `en-GB`, concise abstract, self-contained manuscript + 93 references strictly $\le 10,000$ words, optional expanded online appendix, separate Title Page & Cover Letter)
  2. [**`submissions/philosophy-of-science/`**](submissions/philosophy-of-science/SUBMISSION_GUIDE_AND_MANIFEST.md) — *Philosophy of Science* (Double-anonymous, US English `en-US`, Page 1 Title $\to$ $\le 100$-word Abstract $\to$ Section 1, total manuscript incl. abstract & 93 references strictly $\le 9,500$ words, optional online supplement & Portal Metadata/Cover Note)
  3. [**`submissions/synthese/`**](submissions/synthese/SUBMISSION_GUIDE_AND_MANIFEST.md) — *Synthese* (Double-anonymous Springer two-file split: separate `synthese_title_page.pdf` + blinded `synthese_blinded_manuscript.pdf` with 150–250-word abstract, 6 keywords, integrated proofs, and mandatory `Declarations` before `References`)

## Core contributions of Version 2.1

1. **Strictly standalone foundational article with Forward-Marginalization Asymmetry.** Written as an independent, self-contained inaugural article with zero reliance on unpublished internal manuscripts or external repository snapshots. Diagnoses the structural *forward-marginalization asymmetry* explaining why predictive compression erases modal, energetic, and genealogical grounds, with every formal definition, proposition, counterexample, and theorem proved in full in the Mathematical Appendix.
2. **Typed Principle of Explanatory Preservation & Constrained Relational Objecthood.** Establishes countable-protocol predictive minimality (Proposition 1) and the exact two-condition equivalence for closed-test Bayes–Bellman belief-quotient descent (Proposition 2), defending three jointly exclusionary criteria for relational objecthood—non-trivial predictive–control compression, counterfactual intervention invariance, and realization-cost/constraint accountability—against pure compressionism and unconstrained Markov-blanket metaphysics (Figure 3).
3. **Unified regenerative model, biological realizations, and four sharp separations.** Presents a single stochastic repair–reproduction model $\mathcal{M}$ with internal parity/gate diagnostics and intact-template replication (Figure 1a), grounded in bacterial methyl-directed DNA mismatch repair (`MutS–MutL–MutH`), proving: (i) the non-monotonic 2–3–3–4 predictive quotient diamond lattice and infinite-horizon erasure of paid repair expenditure (Proposition 3, Figure 1b); (ii) lawful silent-tag quotients versus von Neumann's gap between decoded symbolic instructions and physical gate actuation (Proposition 4); (iii) minimal destructive cut-set reconstruction (Proposition 5), finite-memory versus memoryless viability separation (Figure 2a), and fixed-sample zero-violation certification impossibility (Proposition 6); and (iv) dual-criterion affine gauge underdetermination plus a local rank-three smooth bottleneck obstruction (Proposition 7).
4. **Full-policy growth ceiling and Four-Rung Grounds of Purpose.** Proves the exact expected population growth ceiling $\rho_* = \max\{1, \lambda_0, \lambda_1\}$ and necessary-and-sufficient joint realization conditions from a damaged founder (Theorem 1, Figure 2b)—matching bacterial persister dormancy (`1`), iteroparous maintenance (`care`), and high-fecundity proliferation (`bloom`)—isolating organism-versus-lineage trade-offs, critical finite-deadline deficits ($11/12 < 1$), and single-population stochastic extinction ($243/2048$). Formulates a four-rung stratification of purposive grounds engaging contemporary philosophy of biology, cognitive science, and normativity across **93 verified external scholarly works**.

## Reproducible build and verification

From this directory (with Python 3, Matplotlib/NumPy for figure regeneration, Pandoc, XeLaTeX, BibTeX, Latexmk, and Poppler utilities installed):

```bash
python3 generate_figures.py
python3 build.py
python3 validate.py
```

- `build.py` compiles `manuscript.md` + `references.bib` via Pandoc and `latexmk -xelatex`, verifying zero LaTeX/citation errors, zero missing glyphs, and zero overfull boxes, and writes `BUILD_RECEIPT.json`.
- `validate.py` verifies abstract and main-body word budgets, 1-to-1 citation parity across all 93 external BibTeX entries, absence of unpublished self-citations or internal project jargon, PDF text extraction integrity, and exact rational arithmetic for all printed model identities, writing `VALIDATION.json`.
