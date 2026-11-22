# *Philosophy of Science* Submission Package Guide

## Portal Upload Checklist (Cambridge University Press / PSA Editorial Manager)

| Upload Item | File to Upload | Verified Status |
|:---|:---|:---|
| **Blinded Manuscript** (Page 1: Title $\to$ Abstract $\to$ Sec 1) | `pos_blinded_manuscript.pdf` | Strictly $\le$ 9,500 total words incl. Abstract, Appendix, Declarations & 96 refs; **0 author/DOI leaks** |
| **Optional Expanded Online Supplement** | `pos_supplementary_appendix.pdf` | Double-anonymous expanded derivations |
| **Figures** | `figures/fig1_*.pdf`, `fig2_*.pdf`, `fig3_*.pdf` | Vector `.pdf` + 300-DPI `.png` |
| **Portal Copy-Paste Fields & Cover Note** | `pos_author_metadata_and_cover_note.md` | **96-word** abstract ($\le$ 100 words), named AI disclosure & Zenodo DOI |

## Compliance Summary (`VALIDATION_POS.json`)
- **Double-Anonymous Check (zero author/DOI leaks, zero `[Redacted]` strings):** PASS (`anonymity_leaks = []` across both `pos_blinded_manuscript.pdf` and `pos_supplementary_appendix.pdf`)
- **Abstract Word Limit ($\le$ 100 words):** **96 words** — PASS
- **Total Word Limit ($\le$ 9,500 words incl. Abstract + Text + Appendix + Captions + Declarations + 96 References):** Strictly under 9,500 words — PASS (exact PDF count recorded in `VALIDATION_POS.json`)
- **Cambridge Generative AI Transparency:** Concise anonymized declaration included before `References` in `pos_blinded_manuscript.pdf`; full named attribution (**Degui Qian** directing **Gemini 4 Carbon** and **ChatGPT 6 Astra**) recorded in `pos_author_metadata_and_cover_note.md`
- **TeX / Font / BibTeX / Overfull Check:** PASS (`0` errors, `0` BibTeX warnings across 96 entries, `0` missing glyphs, `0` overfull boxes)
