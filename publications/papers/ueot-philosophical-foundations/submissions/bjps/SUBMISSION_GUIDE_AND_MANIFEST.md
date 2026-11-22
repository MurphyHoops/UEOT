# *BJPS* Submission Package Guide (Version 2.4)

## Portal Upload Checklist (*The British Journal for the Philosophy of Science*)

| Upload Item | File to Upload | Verified Status |
|:---|:---|:---|
| **Blinded Manuscript** (triple-anonymous) | `bjps_blinded_manuscript.pdf` | **12pt Times New Roman, 1.5x spacing, 1-in margins**, unbroken single-page tables; strictly $\le$ **24 pages** (excl. Title/Abstract/Refs) & $\le$ 10,000 words; post-abstract **AI Statement** on Page 1; **0 author/DOI leaks** |
| **Online Supplementary Technical Appendix** | `bjps_online_technical_appendix.pdf` | Triple-anonymous expanded derivations (Appendix A) + audited 5-stage BSPS/BJPS AI tool/exact-prompt/AI-output/human-audit log (Appendix B); **0 author/DOI leaks** |
| **Anonymous Referee Verification & Figure Scripts** | `verify_standalone.py`, `generate_figures.py` | Triple-anonymised; `python3 verify_standalone.py` verifies all rational fractions, 4-founder laws, 3-step $\delta \in \{1/8, 1/4\}$ split (`377/512` vs `351/512`), subcritical finite-birth bounds, and $\mathcal{M}_{\mathrm{vote}}$ vs $\mathcal{M}_{\mathrm{bypass}}$ interventions using **only the Python 3 standard library** |
| **Figures** | `figures/fig1_*.pdf`, `fig2_*.pdf`, `fig3_*.pdf` | Vector `.pdf` + 300-DPI `.png` (**0 identifying metadata**) |
| **Author Metadata / Cover Letter** (for portal fields only; do NOT attach to blinded PDF) | `bjps_title_page.pdf` / `cover_letter.md` | 1-page unblinded author metadata, AI disclosure, & Zenodo DOIs |

## Compliance Summary (`VALIDATION_BJPS.json`)
- **Triple-Anonymous Check:** PASS (`anonymity_leaks = []` across `bjps_blinded_manuscript.pdf`, `bjps_online_technical_appendix.pdf`, `verify_standalone.py`, and `generate_figures.py`)
- **Official *BJPS* Typography & Unbroken Tables:** **12pt Times New Roman**, **1.5 line spacing**, **1-inch margins** (`TimesNewRomanPSMT` verified embedded; `table4_unbroken_on_single_page = true`)
- **Strict 24-Page & 10,000-Word Ceilings:** Strictly $\le 24$ counted pages excluding Title/Abstract/References and $\le 10,000$ words excluding Abstract (`bjps_counted_pages` and `pdf_words_excl_abstract_incl_refs` verified automatically in `VALIDATION_BJPS.json`)
- **British English (`en-GB`) Consistency:** PASS (`0` US `-ize`/`realizability`/`programs`/`fiber` spellings; `0` insider or deprecated tokens)
- **Anonymous Referee Reproducibility:** Self-contained, triple-anonymised Python 3 standard-library script `verify_standalone.py` bundled directly in the submission directory (`python3 verify_standalone.py`) alongside `generate_figures.py`
- **BSPS/BJPS AI Policy Compliance:** Concise anonymised **AI Statement** placed **immediately after the Abstract** on Page 1 of `bjps_blinded_manuscript.pdf`, linked to the complete five-stage anonymised log (`Complete Step-by-Step Workflow and Exact Prompts Producing Relied-Upon Outputs`) in Appendix B of `bjps_online_technical_appendix.pdf` recording for each stage the tool used (**ChatGPT 6 Astra** adversarial stress-testing vs **Gemini 4 Carbon** verification/figure scripting, BibTeX audit, and `en-GB`/TeX formatting), exact prompt, AI output, and human derivation/audit; full named attribution (**Degui Qian**) recorded on `bjps_title_page.pdf` and `cover_letter.md`
- **TeX / Font / BibTeX / Overfull Check:** PASS (`0` errors, `0` BibTeX warnings across 98 entries, `0` missing glyphs, `0` overfull boxes)
