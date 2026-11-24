# Separating Fluctuation Attenuation from Signed Causal Response in Correlated Quantum Baths

Standalone journal manuscript package targeting ***Physical Review A* (APS)**, complete with zero-dependency mathematical and finite-Fock unitary verification, TrueType vector figures, and reproducible PDF/LaTeX builds.

## Repository Contents
- `manuscript.md`: Master standalone manuscript (Sections 1–7 + Appendices A–E, including Tables 1–3 and Theorems 1–3).
- `references.bib`: Verified 72-entry scholarly BibTeX bibliography (1-to-1 citation parity enforced).
- `verify_standalone.py`: Zero-dependency Python 3 standard-library verifier (`< 0.25s`) independently reproducing finite-Fock Schrödinger unitary evolution (`K=12` vacuum & `K=8` thermal), Theorem 1 fiber admissibility, Theorem 2 global Lipschitz bounds (plus 500-pair random/corner stress checks), stopped Bell witness splits ($\eta=0.96$) and degraded-visibility falsification ($\eta=0.65$), aligned-$Y$ discrimination ($0.605581355419$), exact rational Duhamel cutoff bounds $B_K$, $\mathbb{R} \times S^1$ Klein–Gordon field series, and two-qubit swap thermodynamics ($\Sigma \approx 0.35499$).
- `generate_figures.py`: Generates TrueType-embedded (`pdf.fonttype=42`, `stix` math) vector PDF + 300-DPI PNG figures in `figures/`.
- `template.tex` & `layout.lua`: XeLaTeX (`Times New Roman` + `STIX Two Math`) and Pandoc Lua filter (floating `tabularx` tables, formal `amsthm` theorems/remarks, Unicode PDF bookmarks).
- `build.py`: Reproducible builder executing `verify_standalone.py`, figure generation, Pandoc, `latexmk -xelatex`, PNG rasterization, PRA bundle sync, and `BUILD_RECEIPT.json`.
- `validate.py`: Integrity, 1-to-1 citation parity, BibTeX schema, PRA bundle parity, `.log`/`.blg`/`.out` audit, `pdftotext` checks, numerical literal parity, and `--check` read-only verifier producing `VALIDATION.json`, `submissions/pra/VALIDATION_PRA.json`, and `SHA256SUMS`.
- `submissions/pra/`: Complete *Physical Review A* single-anonymous submission package (`pra_manuscript.pdf`, `pra_manuscript.tex`, `references.bib`, `figures/`, `verify_standalone.py`, `cover_letter.md`, `SUBMISSION_GUIDE_AND_MANIFEST.md`).
- `CLAIM_MATRIX.md`, `ABSTRACT_ZH.md`, `COPYRIGHT_AND_LICENSE.md`.

## Quick Verification & Build
```bash
python3 verify_standalone.py
python3 build.py
python3 validate.py
shasum -a 256 -c SHA256SUMS
```
