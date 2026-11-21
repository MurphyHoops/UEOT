# Actual PDF and visual review

**Edition:** Version 1.0, 11 November 2026  
**Reviewer:** coordinating assistant; internal preparation review  
**PDF:** `manuscript.pdf` — 21 A4 pages  
**PDF SHA-256:** `eea14e0db1e99b360a80f9a603a2cc221d316c3ccdcfb5c17f095cd3e94f8e1c`  
**Manuscript SHA-256:** `58c905e593130e89d7c5d50187d52d91e21fb9116be84422356fb0213658c4e5`

## Work actually performed

The PDF was compiled with the commands and tool versions in [BUILD_RECEIPT.json](BUILD_RECEIPT.json), then rendered to 21 PNG images using Poppler at 100 dpi. Three contact sheets covering every page were opened and visually inspected. Full-page images of pages **1, 5, 6, 11, 12, 13, 18, 19, 20, and 21** were also opened and inspected in detail. This record does not claim that every page received the same enlarged examination.

The retained contact sheets are [pages 1–9](review/visual/contact-final-1.png), [pages 10–18](review/visual/contact-final-2.png), and [pages 19–21](review/visual/contact-final-3.png). They were produced from the final PDF identified above. The companion [geometry record](review/visual/layout-geometry-final.json) records the same PDF hash.

## Defect found and corrected

The first typesetting split the compact predictive-class comparison table across pages 5 and 6. The publication's small Pandoc layout filter now reserves sufficient space before that table. After rebuilding, **Table 1, all three rows, and its caption are together on page 6**. The final PDF was rendered and inspected again after this correction. No manuscript argument was changed by this layout adjustment.

## Findings

| Element | Actual observation |
| --- | --- |
| First page | Complete two-line title, named author, date/version, 223-word abstract, keywords, and opening text; no overlap |
| Main text | Consistent hierarchy, indentation, readable spacing, and ordinary paragraph continuation across pages |
| Table 1 | Three task rows and caption readable together on page 6; no column clipping |
| Mathematics | Displayed definitions, parameter tuples, growth bounds, and attainment conditions readable in the inspected pages; symbols present |
| Citation rendering | Author–year citations resolved; no extracted `??` or `[?]` markers |
| End matter | Conclusion, sources/evidence/assistance disclosure, copyright notice, and complete references present |
| References | Two final pages; long DOI/source links wrap within the text area, without overfull lines |
| Headers and footers | Running title/version after the first page, first-page plain style, and consecutive page numbers; text positions also verified in the PDF |
| Page boundaries | No text blocks outside a 10-point page safety inset in the automated geometry check; no clipping or collisions visible in the inspected images |
| Build diagnostics | No undefined reference/citation errors, missing-glyph reports, or overfull boxes in the final build receipt |

The geometry check is a supplementary guard, not a substitute for visual inspection. The result is a readable research-manuscript edition, not compliance with an unnamed journal's house style or evidence of journal acceptance.

## Reproduction

After following the build instructions in [README.md](README.md), render the PDF with:

```bash
pdftoppm -r 100 -png manuscript.pdf build/page
```

Inspect the resulting pages, especially the table and the bibliography. A different TeX/font environment can alter line breaking or pagination; the recorded checks apply to this edition's exact PDF bytes.
