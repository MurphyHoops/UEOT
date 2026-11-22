# *BJPS* Submission Package Guide

## Portal Upload Checklist (*The British Journal for the Philosophy of Science*)

| Upload Item | File to Upload | Verified Status |
|:---|:---|:---|
| **Blinded Manuscript** (triple-anonymous) | `bjps_blinded_manuscript.pdf` | Strictly $\le$ 10,000 words incl. Appendix, captions, AI note & 93 refs; **0 author/DOI leaks** |
| **Optional Expanded Online Supplement** | `bjps_online_technical_appendix.pdf` | Triple-anonymous expanded derivations |
| **Figures** | `figures/fig1_*.pdf`, `fig2_*.pdf`, `fig3_*.pdf` | Vector `.pdf` + 300-DPI `.png` |
| **Author Metadata / Cover Letter** (for portal fields only; do NOT attach to blinded PDF) | `bjps_title_page.pdf` / `cover_letter.md` | Unblinded author metadata, AI disclosure, & Zenodo DOI |

## Compliance Summary (`VALIDATION_BJPS.json`)
- **Triple-Anonymous Check:** PASS (`anonymity_leaks = []` across both `bjps_blinded_manuscript.pdf` and `bjps_online_technical_appendix.pdf`)
- **British English (`en-GB`) Consistency:** PASS (`0` US `-ize`/`realizability` spellings)
- **Abstract Length:** **169 words** ($\le$ 300 words)
- **Total Word Count (incl. Text + Self-Contained Appendix + Captions + AI Note + 93 References, excl. Abstract):** Strictly under *BJPS*'s firm **10,000-word** auto-return limit (exact PDF count recorded in `VALIDATION_BJPS.json`)
- **BSPS Generative AI Transparency:** Concise strictly anonymized statement included in `bjps_blinded_manuscript.pdf` and `bjps_online_technical_appendix.pdf`; full named attribution (**Degui Qian** directing **Gemini 4 Carbon** and **ChatGPT 6 Astra**) recorded on `bjps_title_page.pdf` and `cover_letter.md`
- **TeX / Font / BibTeX / Overfull Check:** PASS (`0` errors, `0` BibTeX warnings, `0` missing glyphs, `0` overfull boxes)
