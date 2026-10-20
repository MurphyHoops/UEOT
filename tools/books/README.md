# Building the two UEOT books

`philosophy/UEOT_PHILOSOPHY.md` and `mathematics/UEOT_MATHEMATICS.md` are separate
editable manuscripts. Each has its own generated `.tex`, `.pdf` and build record.
Changes to either book are reviewed as changes to that book's argument or proof;
document compilation does not change the Lean ledger.

## Reproduce a build

Install Python 3, Pandoc, XeLaTeX and the standard LaTeX packages `fontspec`,
`unicode-math`, `xeCJK`, `fvextra`, `xurl`, `etoolbox` and `fancyhdr`, together with
the DejaVu Latin fonts. Then, from the repository root:

```bash
python3 tools/books/build_books.py all --download-fonts
```

Use `philosophy` or `mathematics` instead of `all` for a single book. The first run
can download three open Noto fonts into the ignored build cache. Their exact
SHA-256 values are pinned in the script and checked before use. To build offline,
provide the same font files with `--font-dir /absolute/font/directory`.
No system font installation or administrator privileges are required for the Noto
fonts. A local TeX package tree can be supplied with `--texmf /absolute/texmf/directory`.

Pandoc regenerates the committed LaTeX from Markdown; XeLaTeX runs three passes
for the table of contents and internal references. The LaTeX is also independently
compilable when the named Noto fonts and standard packages are installed. The
source-date epoch is fixed for reproducible metadata; binary equality across
different TeX distributions is not claimed.

After compilation, inspect the PDFs, including the title, contents, chapter
openings, long tables, mathematical displays and code appendices. `BUILD.json`
deliberately records compilation separately from that visual review. Keep generated
TeX/PDF and Markdown from the same build together in a publication commit.

Font source: [Noto CJK](https://github.com/notofonts/noto-cjk). The font license is
retained in `FONT_LICENSE.txt` (Serif) and `FONT_LICENSE_SANS.txt` (Mono Sans);
fonts are embedded as subsets in the PDFs.
