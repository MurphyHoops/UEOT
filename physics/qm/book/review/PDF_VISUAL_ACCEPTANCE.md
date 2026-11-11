# Final PDF acceptance — publication 3.7

Both complete PDFs were actually compiled from the frozen bilingual manuscripts
with three successful XeLaTeX passes. Each contains 67 chapters and appendices
A–F. The last two auxiliary-file identities agree. Neither final log contains
missing-character, overfull-box, undefined-reference or rerun warnings. All
embedded PDF fonts were extracted and hashed; both PDFs contain 73 chapter and
appendix bookmarks, with no invalid internal links detected.

| Edition | Physical PDF pages | PDF SHA-256 | Actual full-page review coverage |
|---|---:|---|---:|
| Chinese | 267 | `b102ae01d9212babebfff6fafc12e6785809d32f199bf4c66b42d9fb6c8673a4` | 26 distinct pages |
| English | 312 | `c4a83dead20fe701196dcc2a3f6fde69693e4c06eb03e9802499165d0a865240` | 39 distinct pages |

The main editor actually viewed all 579 pages on seventeen overview sheets.
Separately, the main editor, empirical reviewer B and bilingual reviewer C
opened the listed 65 distinct full-page images at 110 dpi. The
[machine-readable visual record](../evidence/v3.7/pdf-visual-review.json) lists
every sheet, image hash, page and reviewer. This is not a claim that all 579 pages
were read at full resolution. Scientific and translation reading has its own
source-bound reports.

The English checks cover contents, long formulas, bridge assumptions,
generation-counting premises, source-file tables, the stable-result registry,
Quantum Darwinism and QDRR evidence, statistical thresholds, collapse-model
limitations, chapter 66 costs and error budgets, code and the audit inventory.
The corresponding Chinese inspection covers the same kinds of risks.

## Repairs actually observed

The English result registry now allocates 24%, 10% and 66% of its available
width to ID, chapter and result text. A five-column source table gives its
filename column adequate space. The English edition uses Latin Modern text
fonts and DejaVu Sans Mono, with CJK fallback for original Chinese source titles.
This removes the excessive apostrophe advances from the earlier CJK text font.
Three-letter minimum hyphen fragments eliminate the observed single-letter
breaks. Actual glyphs are present for text proof-end marks, tensor symbols and
Greek letters in code. C independently re-opened the revised pages and closed
the two visual findings; B re-opened the final English experimental-risk pages.

The Chinese final rebuild used exactly the same TeX bytes as the earlier reviewed
layout. Before transferring any observations, the main editor compared all 267
old and final pages as 110-dpi RGB pixels: every pair was identical. Final
overview PNGs and all selected final Chinese PNGs were also byte-identical to
the corresponding reviewed images. B and C independently checked the pixel
identity of their previously opened pages. The
[pixel-equivalence receipt](../evidence/v3.7/zh-pdf-pixel-equivalence.json) records
this transfer; it does not invent additional page viewing.

## Documentation clarification and limits

Appendix E.2 describes the inherited CJK template default. For the final English
edition this is overridden by `build/header.en.tex`; the
[README reproduction section](../README.md#reproduction), build receipts and
[embedded-font inventory](../evidence/v3.7/pdf-technical-check.json) state the
actual per-language choices. This is a nonblocking typesetting clarification,
not an alteration of a scientific formula or claim.

The [empirical visual review](PDF_EMPIRICAL_VISUAL_REVIEW.md) and
[editorial visual review](PDF_EDITORIAL_VISUAL_REVIEW.md) retain the earlier
observations and final scoped conclusions. Internal AI visual review is not
external human peer review. Neither rendering nor a clean typesetting log
establishes mathematical correctness or empirical support.
