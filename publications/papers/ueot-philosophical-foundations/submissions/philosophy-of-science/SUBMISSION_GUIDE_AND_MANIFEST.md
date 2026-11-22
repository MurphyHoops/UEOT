# *Philosophy of Science* Submission Package Guide (Version 2.4)

## Portal Upload Checklist (Cambridge University Press / PSA Editorial Manager)

| Upload Item | File to Upload | Verified Status |
|:---|:---|:---|
| **Blinded Manuscript** (Page 1: Title $\to$ Abstract $\to$ Sec 1) | `pos_blinded_manuscript.pdf` | Strictly $\le$ 9,500 total words incl. Abstract, Appendix, Declarations & 98 refs; **0 author/DOI leaks** |
| **Optional Expanded Online Supplement** | `pos_supplementary_appendix.pdf` | Double-anonymous expanded derivations, 3-step parameter witness & competing-mechanism laws |
| **Figures** | `figures/fig1_*.pdf`, `fig2_*.pdf`, `fig3_*.pdf` | Vector `.pdf` + 300-DPI `.png` |
| **Anonymous Reproducibility Scripts** | `verify_standalone.py`, `generate_figures.py` | Zero-dependency Python 3 `fractions.Fraction` verifier (`python3 verify_standalone.py`) & figure script; **0 author/DOI leaks** |
| **Portal Copy-Paste Fields & Cover Note** | `pos_author_metadata_and_cover_note.md` | **95-word** abstract ($\le$ 100 words), named AI disclosure & Zenodo DOI (enter in web portal; do not upload as a PDF) |

## Compliance Summary (`VALIDATION_POS.json`)
- **Double-Anonymous Check (zero author/DOI leaks, zero `[Redacted]` strings):** PASS (`anonymity_leaks = []` across `pos_blinded_manuscript.pdf`, `pos_supplementary_appendix.pdf`, `verify_standalone.py`, and `generate_figures.py`)
- **Abstract Word Limit ($\le$ 100 words):** **95 words** — PASS
- **Total Word Limit ($\le$ 9,500 words incl. Abstract + Text + Appendix + Captions + Declarations + 98 References):** Strictly under 9,500 words — PASS (exact PDF count recorded in `VALIDATION_POS.json`)
- **Standalone Referee Verification (`verify_standalone.py`):** Self-contained Python 3 standard-library script (`python3 verify_standalone.py`) accompanies the anonymous submission package, verifying Proposition 2 reachable-fiber counterexample, Proposition 3 protocol partitions and 3-step $\delta \in \{1/8, 1/4\}$ parameter witness ($377/512$ vs. $351/512$), Theorem 1 growth ceilings and subcritical finite-births bound, and Section 6.2 $\mathcal{M}_{\mathrm{vote}}$ vs. $\mathcal{M}_{\mathrm{bypass}}$ transitions
- **Cambridge Generative AI Transparency:** Concise anonymized declaration included before `References` in `pos_blinded_manuscript.pdf` and `pos_supplementary_appendix.pdf`; full named attribution (**Degui Qian** conceiving the framework, formal models, and proofs and verifying all calculations and 98 citations; **ChatGPT 6 Astra** providing adversarial stress-testing and formal/conceptual critique; **Gemini 4 Carbon** implementing `verify_standalone.py` and `generate_figures.py`, auditing BibTeX/TeX builds, and assisting with prose formatting) recorded in `pos_author_metadata_and_cover_note.md`
- **TeX / Font / BibTeX / Overfull Check:** PASS (`0` errors, `0` BibTeX warnings across 98 entries, `0` missing glyphs, `0` overfull boxes)
