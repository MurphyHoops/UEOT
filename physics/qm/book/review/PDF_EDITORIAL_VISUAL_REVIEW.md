# Final independent editorial PDF visual review

**Status: PASS within the explicitly declared page scope.** C-PDF-01 and C-PDF-02 are closed after actual visual read-back of the revised English pages. Reviewer: native editorial subagent C. Review date: 2026-11-11. This is an internal targeted visual review, not external peer review, full-book page-by-page reading, or new mathematical verification.

## Final PDF identities

The final PDF bytes in the publication worktree were independently hashed. The English identity agrees with the new render manifest, and the Chinese identity agrees with the coordinator's page-pixel-equivalence receipt.

| Language | Final page count | Final SHA-256 |
|---|---:|---|
| Chinese | 267 | `b102ae01d9212babebfff6fafc12e6785809d32f199bf4c66b42d9fb6c8673a4` |
| English | 312 | `c4a83dead20fe701196dcc2a3f6fde69693e4c06eb03e9802499165d0a865240` |

The final files are `ueot-physics-final/physics/qm/book/UEOT_PHYSICS.pdf` and `UEOT_PHYSICS.en.pdf`. Page numbers in this report are **one-based PDF file pages**, not the printed page labels after the front matter.

## Actual final English page coverage

C actually reopened and visually inspected these **20 full-page PNGs** from `physics-review/root/press-visual-en`:

**1, 3, 18, 19, 50, 55, 239, 240, 252, 254, 257, 258, 261, 265, 269, 274, 275, 289, 291, 312.**

The companion JSON records the new PDF identity, render-manifest hash, and individual PNG hashes. Text extraction and geometric metadata did not substitute for viewing the images.

The final TeX preamble was also read. It uses Latin Modern Roman for body text, Latin Modern Sans for sans-serif text, DejaVu Sans Mono for code, and a CJK fallback for preserved Chinese source names. English minimum hyphenation lengths are explicitly 3/3.

### Findings closed by visual read-back

| Finding | Original visible problem | Final evidence and disposition |
|---|---|---|
| C-PDF-01 | Spurious spacing inside possessives, such as `representation’ s`, `nature’ s`, `experiment’ s`, and `article’ s` | Final pages 55, 239, 240, 252, 261, and 274 show ordinary possessive spacing. **CLOSED: fixed and actually viewed.** |
| C-PDF-02 | Single-letter line-break fragments in `statistics`, `node`, and `manuscript` | Final pages 55, 258, and 289 no longer show those fragments. The heading now breaks `statistics` into multi-letter parts; `node` and `manuscript` are not split in the previously defective manner. **CLOSED: fixed and actually viewed.** |

### Other observed final layout

- The cover, edition information, author, contents entries, and chapter starts are legible and retain the 3.7 / 67-chapter / six-appendix identity.
- The long dependency and matrix expressions on page 18, Gaussian formulas on page 50, and conditioning/initialization/error formulas on pages 252, 254, 257, and 258 remain inside the text area. No missing mathematical glyph, collision, or clipping was observed in those views.
- The complete seven-port table on page 19 has readable headers and separated cells.
- **The result-registry column allocation remains satisfactory after the font change.** Pages 265 and 269 keep ID, Chapter, and Result separate; long titles wrap in the Result column, and the twelve Chapter 66 result entries remain legible. The ID/Chapter/Result width repair is accepted within this inspected scope.
- Page 274 presents the CFW-R1 source, long commit identities, and source/main/CI table without overlapping rows or clipped text. Page 275's chapter-end white space is ordinary pagination, not evidence of missing content.
- Build commands on page 289 and the final audit-request list on page 312 are legible and retain visible line ends. Page 291's formal-scope table has readable wrapped headers and separate module/count/responsibility columns.
- Small hollow squares at proof endings are intentional proof-end symbols. They are not missing-glyph boxes.

No clipping, overlapping text, corrupted table, or absent mathematical glyph was found on these 20 pages. This observation is limited to the pages actually viewed.

## Transfer of the Chinese observations

The earlier Chinese PDF had SHA-256 `d86eb21a80f3efa20d80afef0fcb3b9afb7c31a0857d93b66e73fd07199a2b86`. C had actually viewed its nine full pages:

**1, 16, 43, 214, 217, 224, 232, 245, 267.**

The rebuilt Chinese PDF has the new identity stated above. The coordinator's `physics-review/root/zh-pdf-pixel-equivalence.json` records comparison of all 267 old/new pages as **110-dpi RGB rasters**, with every paired pixel hash identical. C read and checked all 267 receipt entries for consecutive coverage and matching paired hashes. C also decoded the nine previously viewed PNGs and independently checked that each RGB pixel hash equals the receipt's prior-page hash. Thus the actual images underlying the nine observations belong to the verified equality relation.

The pixel-equivalence receipt itself has SHA-256 `4706b10db5f06150a68edf198cb3066d410132f9450a1237da2a6d9e1062697f`.

**Chinese disposition: PASS for those same nine pages, transferred through the stated raster-equivalence condition.** C did not reopen the rebuilt Chinese pages and does not claim a new visual reading of them. Neither raster equality nor the coordinator's unchanged-TeX statement is treated as a byte-identity claim for the PDFs or a semantic audit of all their text. Most importantly, the existence of a 267-page equality receipt does not expand C's actual visual-reading scope from nine pages to 267.

## Nonblocking description of the font configuration

Appendix E.2 still contains the generic description of Noto Serif CJK as the main-text default. That describes the Chinese/template default; this final English derivative uses the explicit Latin Modern / DejaVu override observed in its TeX. The coordinator has clarified the language-specific choices in the README reproduction instructions and bound build/derivative records. This narrow typesetting-description clarification is recorded rather than hidden. It is not a mathematical or PDF-visibility defect, and no scientific manuscript change is requested for this closeout.

## Historical observation trail

The first English visual pass examined the 340-page PDF with SHA-256 `3cfdca1e502c1cb1e08d3a72e25982fd651e5c6d88d02cceee6990840d98871b`. Its actual 20-page list was:

**1, 3, 20, 21, 55, 60, 263, 264, 277, 279, 282, 283, 287, 292, 297, 302, 303, 317, 319, 340.**

That pass correctly requested an English punctuation repair; its observations are not relabelled as having been made on the later 312-page PDF. The earlier Chinese pass used the old identity and nine-page list recorded above. The complete initial Markdown/JSON reports are preserved under `checkpoints/pdf-visual-before-latin-font/`, and the current JSON embeds the initial receipt as history. The newer English pass supplies the actual visual closure of both findings.

## Limits of this acceptance

The final acceptance combines 20 pages actually viewed in the final English PDF and nine prior Chinese page observations transferred by documented pixel equality. It does **not** claim that C visually read all 579 final PDF pages. C also does not infer mathematical correctness, execute printed code or audit requests, perform external peer review, or certify remote GitHub delivery from PDF appearance. Source-language completeness and mathematical-payload fidelity remain governed by their separate source-bound reports; unresolved scientific OPEN states are unchanged.
