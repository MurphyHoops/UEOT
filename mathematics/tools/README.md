# Mathematics-only bilingual publication tools

The editable manuscripts are `mathematics/UEOT_MATHEMATICS.md` and
`mathematics/UEOT_MATHEMATICS.en.md`. This tool directory builds only these two
editions. It does not change the philosophy/physics build paths or Lean contracts.

## Build both editions

From the repository root, with Python 3, Pandoc, XeLaTeX, Poppler (`pdfinfo`),
DejaVu fonts, and the standard packages used by the existing book builder:

```bash
python3 mathematics/tools/build_bilingual.py both --download-fonts
```

Select `zh` or `en` for one edition. `--font-dir` supplies the same three pinned
Noto fonts offline. Their existing licenses and hashes remain in `tools/books/`.
The English edition selects English Babel hyphenation and uses its own heading,
contents and figure/table names. Each edition runs three XeLaTeX passes. The builder rejects a run if any manuscript,
filter, preamble or build-script input changes during compilation.

The mathematics-only Lua filter gives theorem anchors both PDF destinations and
LaTeX labels; wraps long literal Lean names without changing their bytes; renders
proof-end marks with the mathematical font; and breaks the long English
mode-of-convergence clause in §39.22 onto a second line. This last change adds only
a `gathered` layout, preserving every mathematical token and text label. Markdown
formula equality is checked before typography. The long Chinese Appendix D title
uses a print-only line break, with the original contents title and destination retained.
The endpoint-table headings in §21.7.6 start with their tables in both editions. The existing shared filter and
font configuration remain unchanged.

The fixed `SOURCE_DATE_EPOCH` is 2026-11-11 00:00:00 UTC. `BUILD.json` and
`BUILD.en.json` bind the source, TeX, PDF, font and preamble identities. A compilation
receipt deliberately says `COMPILED_REQUIRES_VISUAL_REVIEW`; actual visual
acceptance is separate. Binary equality is tested within the recorded environment,
not promised across different TeX/font distributions.

### Optional minimal-runtime repair

A complete TeX installation needs no helper. If a container has the engine and
packages but lacks the XeLaTeX format and CJK runtime files, the isolated helper
can prepare a local tree without changing system TeX or other books:

```bash
python3 mathematics/tools/prepare_tex_runtime.py --output mathematics/tools/.cache/tex-runtime
python3 mathematics/tools/build_bilingual.py both --runtime-dir mathematics/tools/.cache/tex-runtime
```

The helper pins the actual TeX Live 2024 `xecjk` and `ctex` archives by SHA-256;
its runtime receipt records downloads and format generation. See its `--help` for
the exact interface. This is a publishing dependency repair, not a Lean rebuild.

## Validate the final bilingual manuscripts

```bash
python3 mathematics/tools/check_bilingual_structure.py \
  mathematics/UEOT_MATHEMATICS.md mathematics/UEOT_MATHEMATICS.en.md \
  --whitelist mathematics/review/BILINGUAL_EDITION_2026-11-11/formula_text_whitelist.json \
  --output mathematics/review/BILINGUAL_EDITION_2026-11-11/BILINGUAL_STRUCTURE_REPORT.json \
  --map-output mathematics/review/BILINGUAL_EDITION_2026-11-11/BILINGUAL_SECTION_MAP.json
python3 mathematics/tools/validate_bilingual_checker.py \
  --checker mathematics/tools/check_bilingual_structure.py \
  --output mathematics/review/BILINGUAL_EDITION_2026-11-11/STRUCTURE_CHECK_VALIDATION.json
```

The check covers ordered headings, IDs, inline/display formulas, proof-end marks,
code, anchors, source links and prose cross-reference diagnostics. Exact label
translation is explicitly whitelisted; TeX command boundaries are preserved.
`PASS_STRUCTURAL_ONLY` is not semantic certification. The mutation checks include
a natural-language quantifier change that correctly demonstrates this limit.

## Reproduce source identity and PDF evidence

```bash
python3 mathematics/tools/extract_declarations.py
python3 mathematics/tools/build_source_matrix.py
python3 mathematics/tools/audit_identity_reuse.py \
  --output mathematics/review/BILINGUAL_EDITION_2026-11-11/SOURCE_IDENTITY_REUSE.json
python3 mathematics/tools/review_pdf.py mathematics/UEOT_MATHEMATICS.pdf \
  --output-dir /tmp/ueot-review-zh --render
python3 mathematics/tools/review_pdf.py mathematics/UEOT_MATHEMATICS.en.pdf \
  --output-dir /tmp/ueot-review-en --render
```

The first three commands read the specified Git snapshot, current Lean bytes and
historic receipts; they never execute Lean. A full Git history is required. PDF
inspection additionally uses PyMuPDF and Pillow; `pdffonts` reports embedding.
Every page is rendered into a numbered image and a 12-page contact sheet. Inspect
those sheets and selected full-resolution pages, especially any margin candidates.
Mechanical inspection cannot replace viewing the actual layout.

Source links in the PDFs use the repository's relative layout. When reading a
standalone PDF, use the published GitHub source matrix for linked Lean files and
historical contracts. Internal chapter and theorem navigation is self-contained.

## Reuse a recorded visual inspection after a narrow typesetting correction

```bash
python3 mathematics/tools/compare_pdf_renders.py previous.pdf final.pdf \
  --output-dir /tmp/ueot-changed-pages --dpi 150
```

This compares all pages at the declared resolution and saves the changed final
pages for actual inspection. It rejects changed page counts. Pixel identity
permits reuse of the corresponding recorded visual review; it does not establish
mathematical correctness or excuse inspecting the changed pages.
