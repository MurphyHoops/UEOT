# Physical Review A (APS) Submission Guide & Manifest

- **Target Venue**: *Physical Review A* (American Physical Society) — Quantum Information Science / Fundamental Concepts
- **Review Model**: Single-Anonymous (author name, Independent Researcher affiliation, and ORCID included)
- **Primary Upload File**: `pra_manuscript.pdf`
- **Source Bundle Files** (if uploading LaTeX source): `pra_manuscript.tex`, `references.bib`, and `figures/*.pdf` (do **not** upload temporary build artifacts under `submissions/pra/build/` or duplicate `.png` raster figures when submitting LaTeX source)
- **Accompanying Supplemental Verification Script**: `verify_standalone.py` (Python 3 stdlib only; `python3 verify_standalone.py`)

## Pre-Submission Checklist (APS PRA)
1. **PDF Peer-Review Upload**: Upload `pra_manuscript.pdf` directly as the peer-review manuscript PDF cleanly compiled via XeLaTeX with `STIX Two Math`, `Times New Roman`, clickable DOIs, floating APS tables, Unicode PDF bookmarks, and TrueType (`fonttype=42`) vector figures.
2. **Converting `pra_manuscript.tex` to `revtex4-2` at Production Acceptance**:
   Because local TinyTeX uses `article.cls` cleanly without installing `revtex4-2` / `apsrev4-2`, production conversion to `revtex4-2` under `pdflatex` requires these straightforward structural adjustments to `pra_manuscript.tex` (while keeping equations, `references.bib`, and `figures/*.pdf` unchanged):
   - Replace `\documentclass[11pt,letterpaper]{article}` with `\documentclass[aps,pra,reprint,superscriptaddress]{revtex4-2}` (or `preprint` for single-column).
   - Remove `\usepackage[numbers,sort&compress]{natbib}` and `\bibliographystyle{unsrtnat}` (built into `revtex4-2`, switching bibliography style to `apsrev4-2`).
   - Replace XeLaTeX `fontspec`/`unicode-math` blocks with `pdflatex` packages (`\usepackage[utf8]{inputenc}`, `\usepackage[T1]{fontenc}`, `\usepackage{lmodern}` or `newtxtext,newtxmath`) and move `\title`, `\author`, `\affiliation`, and `\begin{abstract}...\end{abstract}` ahead of `\maketitle`.
   - Strip manual section numbers (`1. `, `2.1 `, `Appendix A: `) if using auto-numbered `\section` / `\appendix`, and wrap tables with `revtex4-2`'s standard `ruledtabular` / `tabular` (or retain `tabularx`).
3. **Cover Letter**: Paste `cover_letter.md` (plain UTF-8 text) into the APS submission portal cover-letter field.
4. **AI Disclosure Statement**: Declare substantive LLM assistance (`Gemini 4 Carbon` and `ChatGPT 6 Astra`, directed and verified by Degui Qian) in the APS portal AI-disclosure prompt, matching the in-manuscript *AI Use Disclosure* section.
5. **Data & Scope Declaration**: Confirm synthetic holdout scope (physical hardware uncertified) and exact agreement with persistent unitary evolution (`4.82e-13`).

## Manifest
- `pra_manuscript.pdf`: Compiled APS peer-review manuscript (clean XeLaTeX + STIX Two Math typography, numeric `[numbers,sort&compress]` `natbib` + `unsrtnat`, verified zero Overfull/LaTeX/BibTeX warnings).
- `pra_manuscript.tex`: LaTeX source produced identically from master `manuscript.md`.
- `pra_manuscript.md`: Exact synced copy of `../../manuscript.md`.
- `template_pra.tex` & `layout.lua`: PRA XeLaTeX template and Pandoc Lua float/theorem/bookmark filter.
- `references.bib`: Verified 72-entry BibTeX bibliography.
- `verify_standalone.py`: Zero-dependency Python 3 stdlib verifier (exit `0`, `< 0.25s`, includes direct Fock Schrödinger unitary cross-checks).
- `figures/`: Vector TrueType PDF & 300-DPI PNG figures (`fig1`–`fig3`).
- `VALIDATION_PRA.json`: Machine-readable verification receipt (`python3 ../../validate.py --check`).
