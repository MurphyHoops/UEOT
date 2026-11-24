# Physical Review A (APS) Submission Guide & Manifest

- **Target Venue**: *Physical Review A* (American Physical Society) — Quantum Information / Open Quantum Systems
- **Review Model**: Single-Anonymous (author name, Independent Researcher affiliation, and ORCID included)
- **Primary Upload File**: `pra_manuscript.pdf`
- **LaTeX Source File**: `pra_manuscript.tex` (with `references.bib` and `figures/*.pdf`)
- **Accompanying Supplemental / Verification Script**: `verify_standalone.py` (Python 3 stdlib only; `python3 verify_standalone.py`)

## Pre-Submission Checklist (APS PRA)
1. **PDF & Source**: Upload `pra_manuscript.pdf` as main manuscript PDF (and `pra_manuscript.tex`, `references.bib`, `figures/*.pdf`, `verify_standalone.py` if requested as source/supplemental files). Note: if converting to `revtex4-2` class on Overleaf / full TeXLive prior to production, replace the preamble with `\documentclass[aps,pra,preprint,superscriptaddress]{revtex4-2}` and `\bibliographystyle{apsrev4-2}` while keeping the body and `references.bib` verbatim.
2. **Cover Letter**: Paste `cover_letter.md` into the APS submission portal cover-letter field.
3. **AI Disclosure Statement**: Declare substantive LLM assistance (`Gemini 4 Carbon` and `ChatGPT 6 Astra` for exposition drafting, script organization, and TeX checks, directed and verified by Degui Qian) in the APS portal AI-disclosure prompt, matching the in-manuscript *AI Use Disclosure* section.
4. **Data & Honest Scope Declaration**: Confirm synthetic holdout scope (`device = NOT_CERTIFIED` on hardware) and exact agreement with standard unitary evolution (`4.82e-13`), matching the text and Table 1.

## Manifest
- `pra_manuscript.pdf`: Compiled APS peer-review manuscript (single-column, numeric `[numbers,sort&compress]` `natbib` + `unsrtnat`, verified zero warnings).
- `pra_manuscript.tex`: Clean LaTeX source produced from master `manuscript.md`.
- `pra_manuscript.md`: Source Markdown for PRA build.
- `template_pra.tex`: PRA XeLaTeX template.
- `references.bib`: Verified 61-entry BibTeX bibliography.
- `verify_standalone.py`: Standalone Python 3 stdlib verifier (exit 0).
- `figures/`: Vector PDF & 300-DPI PNG figures (`fig1`–`fig3`).
- `VALIDATION_PRA.json`: Machine-readable verification receipt.
