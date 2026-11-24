# Separating Fluctuation Attenuation from Signed Causal Response in Correlated Quantum Baths

Standalone journal manuscript package targeting ***Physical Review A* (APS)**, complete with zero-dependency exact numerical verification, programmatic vector figures, and reproducible PDF/LaTeX builds.

## Repository Contents
- `manuscript.md`: Master standalone manuscript (Sections 1–7 + Appendices A–E).
- `references.bib`: Verified 61-entry scholarly BibTeX bibliography.
- `verify_standalone.py`: Zero-dependency Python 3 stdlib verifier independently reproducing all algebraic identities, global Lipschitz constants, 8-cell stopped Bell distributions, exact rational Duhamel cutoff bounds $B_K$, and $\mathbb{R} \times S^1$ Klein–Gordon field vs. two-mode results.
- `generate_figures.py`: Generates vector PDF + 300-DPI PNG figures in `figures/`.
- `template.tex` & `layout.lua`: XeLaTeX / Pandoc typesetting configuration.
- `build.py`: Reproducible builder compiling `manuscript.pdf`, `submissions/pra/pra_manuscript.pdf`, rendered page PNGs, and `BUILD_RECEIPT.json`.
- `validate.py`: Integrity, citation-parity, TeX/BibTeX log, PDF text, and verification runner producing `VALIDATION.json`, `submissions/pra/VALIDATION_PRA.json`, and `SHA256SUMS`.
- `submissions/pra/`: Ready-to-upload *Physical Review A* single-anonymous submission package (`pra_manuscript.pdf`, `pra_manuscript.tex`, `references.bib`, `figures/`, `verify_standalone.py`, `cover_letter.md`, `SUBMISSION_GUIDE_AND_MANIFEST.md`).
- `CLAIM_MATRIX.md`, `ABSTRACT_ZH.md`, `COPYRIGHT_AND_LICENSE.md`.

## Quick Verification & Build
```bash
python3 verify_standalone.py
python3 build.py
python3 validate.py
shasum -a 256 -c SHA256SUMS
```
