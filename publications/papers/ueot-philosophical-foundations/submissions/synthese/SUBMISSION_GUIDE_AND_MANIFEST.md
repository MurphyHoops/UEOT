# *Synthese* Submission Package Guide

## Portal Upload Checklist (Springer Nature SNAPP — Double-Anonymous Review)

| Upload Slot | File to Upload | Verified Status |
|:---|:---|:---|
| **Title Page** (unblinded) | `synthese_title_page.pdf` (`.tex` included) | **1 page**, full author metadata, Zenodo DOIs, & Springer AI disclosure |
| **Blinded Manuscript** | `synthese_blinded_manuscript.pdf` (or `.tex` + `.bib`) | Referee line numbers (`lineno`), **0 author/DOI leaks**, 0 TeX/BibTeX warnings, 0 overfull boxes |
| **Figures (Vector / High-Res)** | `figures/fig1_*.pdf`, `fig2_*.pdf`, `fig3_*.pdf` (`.png` 300-DPI also supplied) | 3 figures embedded & supplied standalone |
| **Cover Letter** | `cover_letter.md` | Tailored for *Synthese* (with Springer Nature AI disclosure) |

## Compliance Summary (`VALIDATION_SYNTHESE.json`)
- **Double-Anonymous Blinding:** PASS (`anonymity_leaks = []`, zero occurrences of `Degui`, `Qian`, `MurphyHoops`, `24433585`, `24433584`, `Single-authored`, or `sole author` in blinded PDF text and metadata)
- **Abstract Length:** **196 words** (required: 150–250 words)
- **Keywords Count:** **6 keywords** (required: 4–6 keywords)
- **Springer Mandatory Declarations & AI Transparency:** Placed immediately before `References` in anonymized form in `synthese_blinded_manuscript.pdf` and in full named form on the 1-page `synthese_title_page.pdf` (research directed by **Degui Qian** and completed with **Gemini 4 Carbon** and **ChatGPT 6 Astra**)
- **Bibliography Parity:** **93/93** verified external scholarly works resolved (`0` missing, `0` unused, `0` BibTeX warnings)
