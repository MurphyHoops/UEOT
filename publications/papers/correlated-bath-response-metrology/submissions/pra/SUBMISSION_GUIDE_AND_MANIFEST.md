# Physical Review A (APS) Submission Guide & Manifest

- **Target Venue**: *Physical Review A* (American Physical Society) — Quantum Information Science / Fundamental Concepts
- **Review Model**: Single-Anonymous (author name, Independent Researcher affiliation, and ORCID included)
- **Primary Upload File**: `pra_manuscript.pdf`
- **Source Bundle Archive** (self-contained APS LaTeX source upload): `pra_aps_latex_source.zip` (deterministic archive containing `pra_manuscript.tex`, `references.bib`, and vector `figures/fig1_ramsey_ambiguity_and_causal_break.pdf`, `fig2_cutoff_bounds_and_channel_error.pdf`, `fig3_local_field_microcausality.pdf`—verified clean end-to-end under `pdflatex` + `bibtex`; do **not** upload build logs under `submissions/pra/build/` or duplicate `.png` rasters when submitting LaTeX source)
- **Accompanying Supplemental Verification Script**: `verify_standalone.py` (Python 3 stdlib only; `python3 verify_standalone.py`)

## Pre-Submission Checklist (APS PRA)
1. **PDF Peer-Review Upload**: Upload `pra_manuscript.pdf` directly as the peer-review manuscript PDF compiled via XeLaTeX with `STIX Two Math`, `Times New Roman`, clickable DOIs, floating APS tables, Unicode PDF bookmarks, zero Type 3 fonts, zero Overfull/LaTeX/BibTeX warnings, and TrueType (`fonttype=42`) vector figures.
2. **Peer-Review `pdflatex` Compilation & Production Conversion to `revtex4-2`**:
   - **Zero-edit `pdflatex` portability:** Both `pra_manuscript.tex` and `pra_aps_latex_source.zip` already use `\ifTUTeX` (`iftex`) to switch automatically between XeLaTeX (`fontspec`/`unicode-math`) and portable `pdflatex` (`inputenc`, `fontenc`, `lmodern`, `textcomp`, `upquote`), compiling cleanly with `pdflatex` + `bibtex` without manual edits.
   - **Production conversion to `revtex4-2` upon acceptance:** Replace `\documentclass[11pt,letterpaper]{article}` with `\documentclass[aps,pra,reprint,superscriptaddress]{revtex4-2}`, remove `\usepackage[numbers,sort&compress]{natbib}`, `\bibliographystyle{unsrtnat}`, and packages conflicting with `revtex4-2` (`geometry`, `fancyhdr`, `caption`, and the custom `\doi` macro once switching to `apsrev4-2`), move `\title`, `\author`, `\affiliation`, and `\begin{abstract}...\end{abstract}` ahead of `\maketitle`, and strip manual section numbers (`1. `, `2.1 `, `Appendix A: `) when enabling auto-numbered `\section` / `\appendix`.
3. **Cover Letter**: Paste `cover_letter.md` (plain UTF-8 text) into the APS submission portal cover-letter field.
4. **AI Disclosure Statement**: Declare substantive LLM assistance (Gemini 4 Carbon and ChatGPT 6 Astra, directed and verified by Degui Qian) in the APS portal AI-disclosure prompt, matching the in-manuscript *AI Use Disclosure* section.
5. **Data & Scope Declaration**: Confirm synthetic holdout scope (physical hardware uncertified) and exact agreement with persistent unitary evolution (`4.82e-13`).

## Manifest
- `pra_manuscript.pdf`: Compiled APS peer-review manuscript (clean XeLaTeX + STIX Two Math typography, numeric `[numbers,sort&compress]` `natbib` + `unsrtnat`, verified zero Overfull/LaTeX/BibTeX warnings and zero high-badness underfulls).
- `pra_aps_latex_source.zip`: Deterministic APS LaTeX source archive (`pra_manuscript.tex`, `references.bib`, and `figures/fig1..3.pdf`), tested via isolated temp-directory `pdflatex` + `bibtex` compilation inside `validate.py`.
- `pra_manuscript.tex`: Dual-engine (`xelatex` + `pdflatex`) LaTeX source generated from `pra_manuscript.md` using `template_pra.tex` and `layout.lua`.
- `pra_manuscript.md`: Exact synced copy of `../../manuscript.md`.
- `template_pra.tex` & `layout.lua`: Dual-engine PRA LaTeX template and Pandoc Lua float/theorem/bookmark filter.
- `references.bib`: Verified 79-entry BibTeX bibliography.
- `verify_standalone.py`: Zero-dependency Python 3 stdlib verifier (exit `0`, `< 0.6s`, includes direct `K=8, 12` Fock Schrödinger unitary checks and exact rational $LDL^\dagger$ repair).
- `figures/`: Vector TrueType PDF & 300-DPI PNG figures (`fig1_ramsey_ambiguity_and_causal_break`, `fig2_cutoff_bounds_and_channel_error`, `fig3_local_field_microcausality`).
- `VALIDATION_PRA.json`: Machine-readable verification receipt written by `python3 ../../validate.py` and checked read-only by `python3 ../../validate.py --check`.
