# *BJPS* Submission Package Guide

## Portal Upload Checklist (*The British Journal for the Philosophy of Science*)

| Upload Item | File to Upload | Verified Status |
|:---|:---|:---|
| **Blinded Manuscript** (triple-anonymous) | `bjps_blinded_manuscript.pdf` | **12pt Times New Roman, 1.5x spacing, 1-in margins**, unbroken single-page tables; strictly $\le$ **24 pages** (excl. Title/Abstract/Refs) & $\le$ 10,000 words; post-abstract **AI Statement** on Page 1; **0 author/DOI leaks** |
| **Online Supplementary Technical Appendix** | `bjps_online_technical_appendix.pdf` | Triple-anonymous expanded derivations (Appendix A) + complete 5-stage BSPS/BJPS AI tool/division-of-labour/exact-prompt log (Appendix B) |
| **Figures** | `figures/fig1_*.pdf`, `fig2_*.pdf`, `fig3_*.pdf` | Vector `.pdf` + 300-DPI `.png` |
| **Author Metadata / Cover Letter** (for portal fields only; do NOT attach to blinded PDF) | `bjps_title_page.pdf` / `cover_letter.md` | Unblinded author metadata, AI disclosure, & Zenodo DOI |

## Compliance Summary (`VALIDATION_BJPS.json`)
- **Triple-Anonymous Check:** PASS (`anonymity_leaks = []` across both `bjps_blinded_manuscript.pdf` and `bjps_online_technical_appendix.pdf`)
- **Official *BJPS* Typography & Unbroken Tables:** **12pt Times New Roman**, **1.5 line spacing**, **1-inch margins** (`TimesNewRomanPSMT` verified embedded; `table4_unbroken_on_single_page = true`)
- **Strict 24-Page Limit (Main Text + Figures 1–3 + Tables 1–4 + Inline Appendix, excl. Title/Abstract/References):** Strictly $\le 24$ pages (`bjps_counted_pages` verified automatically in `VALIDATION_BJPS.json`)
- **British English (`en-GB`) Consistency:** PASS (`0` US `-ize`/`realizability` spellings)
- **BSPS/BJPS AI Policy Compliance:** Concise anonymised **AI Statement** placed **immediately after the Abstract** on Page 1 of `bjps_blinded_manuscript.pdf`, linked to the complete five-stage anonymised tool/division-of-labour/exact-prompt log in Appendix B of `bjps_online_technical_appendix.pdf`; full named attribution (**Degui Qian** directing **Gemini 4 Carbon** and **ChatGPT 6 Astra**) recorded on `bjps_title_page.pdf` and `cover_letter.md`
- **TeX / Font / BibTeX / Overfull Check:** PASS (`0` errors, `0` BibTeX warnings across 98 entries, `0` missing glyphs, `0` overfull boxes)
