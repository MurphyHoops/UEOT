# Empirical PDF visual review — final bilingual publication 3.7

**Decision: PASS for the 20 selected final-edition pages described below.** No blocking clipping, overlap, missing glyph or unreadable equation/table was observed. English acceptance is based on 10 newly opened page images of the final Latin-typeset PDF. Chinese acceptance reuses 10 previously viewed pages through the inspected pixel-equivalence record. This is an internal independently assigned review, not external peer review.

## 1. Final PDF identities

| Language | Final PDF | Physical pages | SHA-256 | Final page coverage |
|---|---|---:|---|---|
| Chinese | `UEOT_PHYSICS.pdf` | 267 | `b102ae01d9212babebfff6fafc12e6785809d32f199bf4c66b42d9fb6c8673a4` | 10 selected pages |
| English | `UEOT_PHYSICS.en.pdf` | 312 | `c4a83dead20fe701196dcc2a3f6fde69693e4c06eb03e9802499165d0a865240` | 10 selected pages |

Both final files were independently hashed at `ueot-physics-final/physics/qm/book`; the hashes match their final evidence identities. Every listed English PNG was actually opened at full-page size after the typography rebuild. Every listed Chinese PNG had been actually opened in the first visual pass. All inspected PNG bytes match their render-manifest entries. Physical page indices and printed footer labels were read separately. No PDF was rebuilt, modified or rasterized by agent B.

## 2. Chinese observation reuse and its exact limit

The first inspected Chinese PDF was `d86eb21a80f3efa20d80afef0fcb3b9afb7c31a0857d93b66e73fd07199a2b86` (267 pages). The final Chinese PDF is `b102ae01d9212babebfff6fafc12e6785809d32f199bf4c66b42d9fb6c8673a4` (267 pages). Root reports that the rebuild expanded the font inventory in the build record while leaving the TeX bytes unchanged. The visual reuse does not rely on that explanation alone.

Root’s `zh-pdf-pixel-equivalence.json`, SHA-256 `4706b10db5f06150a68edf198cb3066d410132f9450a1237da2a6d9e1062697f`, records an actual RGB comparison of all 267 pages at 110 dpi. Agent B inspected the complete 267-entry record, checked its two PDF identities and page coverage, and confirmed that every recorded prior/final pixel hash agrees. Agent B also independently decoded the 10 previously viewed PNGs to RGB and confirmed their pixel hashes against the corresponding equivalence entries. This binds the observed images to the final Chinese artifact at the recorded raster settings. Agent B did not rerun the 267-page rendering comparison or visually read the other 257 Chinese pages.

| Physical PDF page | Printed page | Preserved actual observation |
|---:|---:|---|
| 33 | 29 | §§8.3–8.5: finite-sample formulas, n ≥ 762, hardware caveats and first experiment-table rows are clear. |
| 34 | 30 | §8.5 continuation: repeated table header, remaining studies, postselection and no-QDRR-data limits are readable. |
| 105 | 101 | §§39.4–39.6: decimal thresholds, n = 188, binomial tail and calibration limitations are legible. |
| 108 | 104 | §§40.2–40.3: stochastic equation, units, bounded-integrand statement and absorption formulas fit without overlap. |
| 111 | 107 | §§41.1–41.3: dilation equation and ordinary-environment boundary are clear; the collapse-study paragraph begins beneath its heading. |
| 112 | 108 | §41.3 continuation: total-noise/residual-background distinction and unavailable UEOT-strength mapping are readable. |
| 121 | 117 | §§46.1–46.3: conditional-null assumption, correlated-trial bound and likelihood-ratio expression are complete. |
| 218 | 214 | §§66.9–66.11: positive-acceptance premise, p_G/c, mu/p, truncation formula and resource budget are clear. |
| 220 | 216 | C-FCOND-01 and §§66.14–66.15: inverse-root counterexample, Pauli cost condition, complex matrices and 117/4096 are legible. |
| 221 | 217 | §§66.15–66.16: 5608/117, 39/(39+sqrt(565)), action-library limits and proof/non-hardware boundaries are clear. |

## 3. Final English pages freshly inspected

The previous English PDF, `3cfdca1e502c1cb1e08d3a72e25982fd651e5c6d88d02cceee6990840d98871b`, had 340 pages. The Latin-body typography revision produced the final 312-page PDF identified in §1. The earlier page-number observations were not transferred mechanically. The following new full-page images were actually opened and reviewed:

| Physical PDF page | Printed page | New actual observation |
|---:|---:|---|
| 37 | 33 | §§8.1–8.2: full inverse, coherent-pullback identities and retained-record condition are legible; tomography begins with a complete displayed formula. |
| 38 | 34 | §§8.2–8.5: sampling formulas, n ≥ 762 and projection/noise qualifications are clear; section 8.5 begins with its introductory paragraph. |
| 39 | 35 | §8.5 continuation: the complete five-study table fits with clear columns; postselection, raw-count and no-new-QDRR-data limitations remain visible below it. |
| 119 | 115 | §§39.4–39.5: 0.0428932188, 0.0158446719, zero events in n = 188 trials and the binomial-tail formula are readable with calibration limitations. |
| 122 | 118 | §§40.2–40.3: the stochastic equation, gamma units, ensemble equation, bounded-integrand statement and standard-source attribution are legible. |
| 126 | 122 | §§41.1–41.2: the dilation formula and model-class limits are readable; complete reversal and ordinary environmental/control errors remain distinct. |
| 127 | 123 | §41.3: all three collapse-study references, total-noise/residual-background distinction and undefined UEOT-strength mapping are clear in complete paragraphs. |
| 138 | 134 | §46.1: conditional-null premise, p_star, correlated-trial bound and zero accepted events in 188 trials are legible; arbitrary-drift limits remain visible. |
| 259 | 255 | P-FCOND-11 and §66.13: the Kraus error bound, matrix expansion, square-root estimates and small-positive-eigenvalue counterexample are clear; numerical-certification caveats remain visible. |
| 260 | 256 | §§66.14–66.15: Pauli operations, original p_G = 1/8, 3 + 3r < 14, no-hardware statement, complex matrices, 117/4096 and the noncommuting-branch matrix fit without clipping. |

## 4. Findings and preserved history

The final English body typography, apostrophes and ordinary hyphenation are readable in this sample. The full experimental-study table, hypothesis conditions, statistical sample sizes, probability denominators and matrix entries remain clear. The paragraphs distinguishing laboratory data from synthetic calculations, total-noise limits from mechanism identification, and stipulated model costs from hardware measurements are visibly present on the inspected pages. The Chinese table repeats its header across the inspected page break. Normal chapter-end whitespace and paragraph continuations do not truncate the inspected claims. No source or layout correction is requested from this review.

The first pass actually opened Chinese pages 33, 34, 105, 108, 111, 112, 121, 218, 220 and 221, and old-English pages 41, 42, 43, 133, 136, 140, 141, 153, 284 and 286. Those observations, image hashes and old PDF identities are preserved in the companion JSON and `visual_history/first-render-PDF_EMPIRICAL_VISUAL_REVIEW.*`. The English final pass opened the 10 pages listed in §3. Thus 30 page images were actually opened across the two checkpoints, while final-edition coverage remains the specified 20-page sample.

The first attempt to bind files queried an official-tree path that still contained the upstream Chinese PDF. That temporary identity issue was resolved by locating the actual build output, and is superseded by the final-file hashes and Chinese pixel-equivalence chain recorded here.

## 5. Scope of the final PASS

This review covers 10 of 267 Chinese pages and 10 of 312 English pages. It does not claim a visual reading of all 579 final pages. Pixel equality across all Chinese pages is an automated rendering-equivalence result, not 267 additional human-style page reviews. Acceptance is limited to the supplied 110-dpi raster appearance; it does not establish equivalence of PDF metadata, links, accessibility tags or behavior in every PDF viewer. It does not provide new scientific evidence, execute historical tests, or replace the separate content and translation audits.

Final closeout: `2026-11-11T06:31:03.981955+00:00`.
