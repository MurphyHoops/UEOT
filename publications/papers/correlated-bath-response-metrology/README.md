# Separating Fluctuation Attenuation from Signed Causal Response in Correlated Quantum Baths

Standalone journal manuscript package targeting ***Physical Review A*** **(APS)**, complete with zero-dependency mathematical and finite-Fock unitary verification, TrueType vector figures, and dual-engine (`xelatex` + `pdflatex`/`bibtex`) reproducible PDF/LaTeX builds.

## Repository Contents
- `manuscript.md`: Master standalone manuscript (Sections 1–7 + Appendices A–E, including Tables 1–3 and Theorems 1–3).
- `references.bib`: Verified 79-entry scholarly BibTeX bibliography (1-to-1 citation parity enforced).
- `verify_standalone.py`: Zero-dependency Python 3 standard-library verifier (`< 0.6s`) independently reproducing finite-Fock Schrödinger unitary evolution (`K=12` vacuum & `K=8, 12` thermal convergence), Theorem 1 fiber admissibility, calibration inverse round-trip & Theorem 2 global Lipschitz bounds (32 corners + 500 random + 300 shared-$\delta$ pairs), stopped Bell witness splits ($\eta=0.96$), parameter-free $\mathrm{f,ZZ}^-$ ($\eta=0.65$), aligned-$Y$ discrimination ($0.605581355419$), exact rational Duhamel cutoff bounds $B_K$, constructive rational `Fraction` $LDL^\dagger$ CP/TP repair, $\mathbb{R} \times S^1$ Klein–Gordon field series & tails, and two-qubit swap thermodynamics ($\Sigma \approx 0.35499$).
- `generate_figures.py`: Generates TrueType-embedded (`pdf.fonttype=42`, `stix` math) vector PDF + 300-DPI PNG figures in `figures/`.
- `template.tex` & `layout.lua`: Dual-engine LaTeX template (`xelatex` with `Times New Roman` + `STIX Two Math`, or portable `pdflatex` with `lmodern`) and Pandoc Lua filter (floating `tabularx` tables, formal `amsthm` theorems/remarks, Unicode PDF bookmarks).
- `build.py`: Deterministic builder (`SOURCE_DATE_EPOCH`) executing `verify_standalone.py`, figure generation, Pandoc, `latexmk -xelatex`, PNG rasterization, PRA bundle sync, deterministic `submissions/pra/pra_aps_latex_source.zip`, and `BUILD_RECEIPT.json`.
- `validate.py`: Integrity, 1-to-1 citation parity, BibTeX schema, PRA bundle parity, `.log`/`.blg` & stale-`.out` removal audit, decompressed PDF `/Outlines` Unicode check, `pdftotext` checks, live numerical parity, isolated temp-directory `pdflatex` + `bibtex` compilation test of `pra_aps_latex_source.zip`, and `--check` read-only verifier producing `VALIDATION.json`, `submissions/pra/VALIDATION_PRA.json`, and `SHA256SUMS`.
- `submissions/pra/`: Complete *Physical Review A* single-anonymous submission package (`pra_manuscript.pdf`, `pra_aps_latex_source.zip`, `pra_manuscript.tex`, `references.bib`, `figures/`, `verify_standalone.py`, `cover_letter.md`, `SUBMISSION_GUIDE_AND_MANIFEST.md`, `VALIDATION_PRA.json`).
- `CLAIM_MATRIX.md`, `ABSTRACT_ZH.md`, `COPYRIGHT_AND_LICENSE.md`.

## Quick Verification & Build
```bash
python3 verify_standalone.py
python3 build.py
python3 validate.py
shasum -a 256 -c SHA256SUMS
```
