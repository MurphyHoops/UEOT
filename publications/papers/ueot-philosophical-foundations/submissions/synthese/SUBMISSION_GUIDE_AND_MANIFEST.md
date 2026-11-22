# *Synthese* Submission Package Guide (Version 2.4)

## Portal Upload Checklist (Springer Nature SNAPP — Double-Anonymous Review)

| Upload Slot | File to Upload | Verified Status |
|:---|:---|:---|
| **Title Page** (unblinded) | `synthese_title_page.pdf` (`.tex` included) | **1 page**, full author metadata, Zenodo DOIs, & audited Springer AI disclosure |
| **Blinded Manuscript** | `synthese_blinded_manuscript.pdf` (or `.tex` + `.bib`) | Referee line numbers (`lineno`), **0 author/DOI leaks**, 0 TeX/BibTeX warnings, 0 overfull boxes |
| **Figures (Vector / High-Res)** | `figures/fig1_*.pdf`, `fig2_*.pdf`, `fig3_*.pdf` (`.png` 300-DPI also supplied) | 3 figures embedded & supplied standalone |
| **Anonymous Referee Verification Code** | `verify_standalone.py`, `generate_figures.py` | Zero-dependency Python 3 standard-library exact rational verifier (`python3 verify_standalone.py`), **0 author/DOI leaks** |
| **Cover Letter** | `cover_letter.md` | Tailored for *Synthese* (with audited Springer Nature AI & code disclosure) |

## Compliance Summary (`VALIDATION_SYNTHESE.json`)
- **Double-Anonymous Blinding:** PASS (`anonymity_leaks = []`, zero author-name, account-handle, or archival-DOI identifiers in blinded PDF text, PDF metadata, and bundled `verify_standalone.py` / `generate_figures.py`)
- **Abstract Length:** **235 words** (required: 150–250 words)
- **Keywords Count:** **6 keywords** (required: 4–6 keywords)
- **Springer Mandatory Declarations & AI Transparency:** Placed immediately before `References` in anonymized form in `synthese_blinded_manuscript.pdf` and in full named form on the 1-page `synthese_title_page.pdf` (**Degui Qian** conceived the philosophical problem, core framework, and regenerative model, directed all revisions, verified all proofs, exact rational calculations, and 98 references, and bears sole responsibility; **ChatGPT 6 Astra** provided adversarial referee-style stress-testing and mathematical/conceptual critique; **Gemini 4 Carbon** implemented exact `fractions.Fraction` verification in `verify_standalone.py` and `validate.py`, programmatic vector figures in `generate_figures.py`, multi-edition formatting, and BibTeX/TeX build checks)
- **Bibliography Parity:** **98/98** verified external scholarly works resolved (`0` missing, `0` unused, `0` BibTeX warnings)
