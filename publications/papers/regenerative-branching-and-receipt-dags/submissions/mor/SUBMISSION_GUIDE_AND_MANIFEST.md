# *Mathematics of Operations Research* (INFORMS) Submission Package Guide

## 1. Portal Upload Checklist (ScholarOne / INFORMS *MOR*)

*Mathematics of Operations Research* enforces **double-anonymous peer review**, US Letter (`11pt`, `1-inch` margins, `1.5` line spacing, `<= 40` pages excluding references), a blinded Title Page followed on **Page 2** by a single-paragraph abstract of **at most 150 words** (`0` equations, `0` citations, `0` undefined abbreviations), **3–5 keywords**, mandatory **MSC 2020** and **OR/MS** subject classifications, and numbered **`amsplain`** references (`[1]`).

| Upload Slot | File to Upload | Verified Status |
|:---|:---|:---|
| **Blinded Main Manuscript** | `mor_blinded_manuscript.pdf` (`.tex` + `.bib` included) | **0 author/DOI leaks**, anonymized Generative AI & mathematical-guidance disclosure included, US Letter `11pt` / `1in` / `1.5` spacing with line numbers, Page 1 blinded Title Page + Page 2 **140-word** Abstract, numbered `amsplain` citations, `<= 40` pages excl. references, 0 TeX/BibTeX warnings, 0 overfull boxes |
| **Anonymized Reproducibility Code** | `verify_standalone.py`, `generate_figures.py` | **0 author/DOI leaks**, zero-dependency Python 3 standard-library verifier (`python3 verify_standalone.py` & `--benchmark-timings`) reproducing Table 3, $\binom{H+1}{3}$ lower bounds, and `1,440` DP checks |
| **Unblinded Title Page (Editor-Only Slot)** | `mor_title_page.pdf` (`.tex` included) | Upload **solely** in ScholarOne's Editor-only / non-referee Title Page designation (verify exclusion in the merged ScholarOne reviewer proof PDF); 1-page author metadata, Funding, Competing Interests, named AI disclosure, and Zenodo v1.0.0 Lean library DOI (`10.5281/zenodo.24433585`) |
| **Figures (Vector / 300-DPI)** | `figures/fig1_*.pdf`, `fig2_*.pdf`, `fig3_*.pdf` (`.png` also supplied) | 3 programmatic vector figures matching Section 2–6 notation |
| **Cover Letter** | `cover_letter.md` | Tailored to *MOR* Stochastic Models / Dynamic Programming areas with transparent INFORMS Generative AI, Lean library DOI, and bundled Python script disclosures |

## 2. Automated Compliance Summary (`VALIDATION_MOR.json`)

- **Double-Anonymous, AI-Disclosure & Standalone Verifier Check:** `PASS` (`anonymity_leaks = []` across PDF, metadata, `verify_standalone.py`, and `generate_figures.py`; `ai_disclosure_in_blinded_manuscript = true`; `standalone_verifier_pass = true`)
- **Abstract Word Count & Placement:** **140 words** on **Page 2** following blinded Title Page (official *MOR* limit: **up to 150 words**, single paragraph)
- **Equations / Citations in Abstract:** **0** (`$` count = `0`, `@` count = `0`)
- **Keywords Count:** **5 keywords** (required: 3–5 keywords)
- **Subject Classifications:**
  - **MSC 2020:** `Primary: 90C40, 93E20; Secondary: 60J85, 62C10, 68V15`
  - **OR/MS:** `Dynamic programming/optimal control: Markov, Bayesian; Probability: branching processes; Reliability: maintenance/repairs`
- **Bibliography Style & Parity:** Numbered `amsplain.bst` (`[1]`), **99/99** verified external scholarly works resolved (`0` missing, `0` unused, `0` BibTeX warnings)

## 3. Secondary Journal & Preprint Options

- **arXiv Preprint:** Primary `math.OC` (Optimization and Control), cross-listed to `math.PR` (Probability), `cs.LO` (Logic in Computer Science), `cs.AI`.
- **Secondary Journal Targets:** *Advances in Applied Probability* (Applied Probability Trust) · *Operations Research* (INFORMS) · *Journal of Mathematical Biology* (Springer).
