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
for the table of contents and internal references. Auxiliary files are isolated
by generated-TeX hash, preserving old diagnostics without importing stale locale
macros after an input change. The LaTeX is also independently
compilable when the named font files and standard packages are in the TeX/font search path.
The builder uses explicit font filenames and sets a process-local `OPENTYPEFONTS`
path, so native macOS XeTeX does not require system font registration; DejaVu
files must also be discoverable, for example from the TeX `dejavu` package.
Chinese layout uses xeCJK; the builder suppresses Babel locale import (while
retaining document language metadata), avoiding its chapter-macro rescan on
TeX Live 2026. The
source-date epoch is fixed for reproducible metadata; binary equality across
different TeX distributions is not claimed.

After compilation, inspect the PDFs, including the title, contents, chapter
openings, long tables, mathematical displays and code appendices. `BUILD.json`
deliberately records compilation separately from that visual review. Keep generated
TeX/PDF and Markdown from the same build together in a publication commit.

Font source: [Noto CJK](https://github.com/notofonts/noto-cjk). The font license is
retained in `FONT_LICENSE.txt` (Serif) and `FONT_LICENSE_SANS.txt` (Mono Sans);
fonts are embedded as subsets in the PDFs.
