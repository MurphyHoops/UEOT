#!/usr/bin/env python3
"""Build the separately maintained UEOT philosophy and mathematics books.

Markdown is the editable source. Pandoc produces the committed LaTeX, and
XeLaTeX produces the committed PDF. No theorem or empirical status is inferred
from a successful document build.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import urllib.request
from xml.sax.saxutils import escape

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
CACHE = HERE / ".cache"
BOOKS = {
    "philosophy": ("UEOT_PHILOSOPHY", "UEOT · 哲学著作"),
    "mathematics": ("UEOT_MATHEMATICS", "UEOT · 数学著作"),
}
FONT_SOURCE = "https://raw.githubusercontent.com/notofonts/noto-cjk/main/"
FONTS = {
    "NotoSerifCJKsc-Regular.otf": (
        "Serif/OTF/SimplifiedChinese/NotoSerifCJKsc-Regular.otf",
        "2a2eae2628df83556c54018c41e20fa532c1b862c5256ae8b3f23feb918d12ca"),
    "NotoSerifCJKsc-Bold.otf": (
        "Serif/OTF/SimplifiedChinese/NotoSerifCJKsc-Bold.otf",
        "8af07d4b6c2e82bcc72a30e066eaf295f11b9424f4aad2eaa9fe0e9c3b38fc73"),
    "NotoSansMonoCJKsc-Regular.otf": (
        "Sans/Mono/NotoSansMonoCJKsc-Regular.otf",
        "ec04cc376b34887cedbdf84074e2e226ed2761eeabdcb9173fc1dd7bfd153ef7"),
}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(command: list[str], env: dict[str, str], log: Path) -> None:
    with log.open("wb") as output:
        result = subprocess.run(command, cwd=REPO, env=env,
                                stdout=output, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(f"Command failed ({result.returncode}); inspect {log}")


def font_environment(font_dir: Path, download: bool) -> dict[str, str]:
    font_dir.mkdir(parents=True, exist_ok=True)
    for name, (relative, expected) in FONTS.items():
        target = font_dir / name
        if not target.exists() and download:
            with urllib.request.urlopen(FONT_SOURCE + relative, timeout=90) as response:
                data = response.read()
            if hashlib.sha256(data).hexdigest() != expected:
                raise RuntimeError(f"Downloaded font checksum mismatch: {name}")
            target.write_bytes(data)
        if not target.exists() or sha(target) != expected:
            raise RuntimeError(f"Missing or changed font {target}; use --download-fonts "
                               "or provide the pinned files with --font-dir")
    env = dict(os.environ)
    env["SOURCE_DATE_EPOCH"] = str(int(datetime(2026, 10, 20, tzinfo=timezone.utc).timestamp()))
    env["FORCE_SOURCE_DATE"] = "1"
    env["XDG_CACHE_HOME"] = str(CACHE / "xdg")
    config = CACHE / "fonts.conf"
    config.write_text('<?xml version="1.0"?>\n<!DOCTYPE fontconfig SYSTEM "fonts.dtd">\n'
                      '<fontconfig><include ignore_missing="yes">/etc/fonts/fonts.conf</include>'
                      f'<dir>{escape(str(font_dir.resolve()))}</dir>'
                      f'<cachedir>{escape(str(CACHE / "fontconfig"))}</cachedir>'
                      '</fontconfig>\n')
    env["FONTCONFIG_FILE"] = str(config)
    return env


def build(book: str, env: dict[str, str]) -> dict:
    stem, running_title = BOOKS[book]
    folder = REPO / book
    source, tex, pdf = [folder / (stem + suffix) for suffix in (".md", ".tex", ".pdf")]
    if not source.is_file():
        raise RuntimeError(f"Book manuscript is missing: {source}")
    work = CACHE / book
    work.mkdir(parents=True, exist_ok=True)
    geometry = ("paperwidth=176mm,paperheight=250mm,left=23mm,right=23mm,top=24mm,bottom=24mm"
                if book == "philosophy" else "a4paper,left=24mm,right=24mm,top=25mm,bottom=25mm")
    command = ["pandoc", str(source.relative_to(REPO)), "--from=markdown+raw_tex",
               "--to=latex", "--standalone", "--top-level-division=chapter",
               "--toc", "--toc-depth=2", "--wrap=none", "--no-highlight",
               "--lua-filter=tools/books/print.lua", "--include-in-header=tools/books/preamble.tex",
               "--variable=documentclass:book", "--variable=classoption:oneside",
               "--variable=fontsize:11pt", "--variable=geometry:" + geometry,
               "--variable=mainfont:DejaVu Serif",
               "--variable=monofont:DejaVu Sans Mono",
               "--variable=CJKmainfont:Noto Serif CJK SC",
               "--variable=CJKoptions:AutoFakeSlant=0.15",
               "--variable=colorlinks:true", "--variable=linkcolor:MidnightBlue",
               "--variable=urlcolor:MidnightBlue", "--variable=toccolor:MidnightBlue",
               "--metadata=running-title:" + running_title,
               "--metadata=ueot-book:" + book,
               "--output=" + str(tex.relative_to(REPO))]
    run(command, env, work / "pandoc.log")
    for attempt in range(1, 4):
        run(["xelatex", "-interaction=nonstopmode", "-halt-on-error", "-file-line-error",
             "-output-directory=" + str(work), str(tex.relative_to(REPO))],
            env, work / f"xelatex-{attempt}.log")
    final_log = (work / f"{stem}.log").read_text(errors="replace")
    if "Missing character:" in final_log:
        raise RuntimeError(f"Missing glyphs in {book}; inspect {work / (stem + '.log')}")
    generated = work / (stem + ".pdf")
    if not generated.is_file() or generated.stat().st_size < 1000:
        raise RuntimeError(f"No usable PDF produced for {book}")
    shutil.copyfile(generated, pdf)
    versions = {}
    for tool in ("pandoc", "xelatex"):
        versions[tool] = subprocess.check_output([tool, "--version"], env=env, text=True).splitlines()[0]
    report = {
        "document": book, "status": "COMPILED_REQUIRES_VISUAL_REVIEW",
        "source": str(source.relative_to(REPO)), "source_sha256": sha(source),
        "latex": str(tex.relative_to(REPO)), "latex_sha256": sha(tex),
        "pdf": str(pdf.relative_to(REPO)), "pdf_sha256": sha(pdf),
        "tools": versions, "font_sha256": {name: pair[1] for name, pair in FONTS.items()},
        "overfull_hbox_warnings": final_log.count("Overfull \\hbox"),
        "build_command": ["python3", "tools/books/build_books.py", book],
        "scope": "Document compilation only; mathematical proof status is recorded separately.",
    }
    (folder / "BUILD.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("book", choices=["all", *BOOKS], nargs="?", default="all")
    parser.add_argument("--font-dir", type=Path, default=CACHE / "fonts")
    parser.add_argument("--download-fonts", action="store_true")
    parser.add_argument("--texmf", type=Path, help="Optional local tree of extra TeX packages")
    args = parser.parse_args()
    for tool in ("pandoc", "xelatex"):
        if not shutil.which(tool):
            parser.error(f"Required executable not found: {tool}")
    CACHE.mkdir(parents=True, exist_ok=True)
    env = font_environment(args.font_dir.resolve(), args.download_fonts)
    if args.texmf:
        env["TEXINPUTS"] = str(args.texmf.resolve()) + "//:" + env.get("TEXINPUTS", "")
    for book in BOOKS if args.book == "all" else [args.book]:
        print(json.dumps(build(book, env), ensure_ascii=False), flush=True)


if __name__ == "__main__":
    main()
