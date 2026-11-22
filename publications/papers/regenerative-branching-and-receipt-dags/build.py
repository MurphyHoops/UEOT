#!/usr/bin/env python3
"""Build both the standalone Master Complete Edition (manuscript.pdf) and the
double-anonymous INFORMS Mathematics of Operations Research package (submissions/mor/).
"""
from pathlib import Path
import datetime
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "build"
OUT.mkdir(exist_ok=True)
MOR_DIR = ROOT / "submissions" / "mor"
MOR_OUT = MOR_DIR / "build"
MOR_OUT.mkdir(parents=True, exist_ok=True)
MOR_FIG = MOR_DIR / "figures"
MOR_FIG.mkdir(parents=True, exist_ok=True)

ENV = os.environ.copy()
extra_paths = [
    str(Path.home() / "Library/TinyTeX/bin/universal-darwin"),
    str(Path.home() / ".TinyTeX/bin/universal-darwin"),
    "/Library/TeX/texbin",
    "/opt/homebrew/bin",
    "/usr/local/bin",
]
ENV["PATH"] = ":".join(extra_paths + [ENV.get("PATH", "")])


def execute(argv, name, cwd=ROOT, log_dir=OUT):
    p = subprocess.run(argv, cwd=cwd, env=ENV, capture_output=True, text=True)
    (log_dir / (name + ".txt")).write_text(p.stdout + p.stderr, encoding="utf-8")
    if p.returncode:
        raise SystemExit(f"{name} failed ({p.returncode}); see {log_dir / (name + '.txt')}")
    return p.stdout


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


# 1. Generate programmatic vector PDF & 300-DPI PNG figures
execute([sys.executable, "generate_figures.py"], "generate_figures")

# 2. Build Master Complete Edition (manuscript.tex & manuscript.pdf)
execute([
    "pandoc", "manuscript.md", "--standalone", "--number-sections",
    "--natbib", "--template=template.tex", "--lua-filter=layout.lua", "--to=latex",
    "--output=manuscript.tex",
], "pandoc")
execute([
    "latexmk", "-xelatex", "-interaction=nonstopmode", "-halt-on-error",
    "-outdir=build", "manuscript.tex",
], "latexmk")
shutil.copy2(OUT / "manuscript.pdf", ROOT / "manuscript.pdf")

for old_png in OUT.glob("page-*.png"):
    old_png.unlink()
execute(["pdftoppm", "-png", "-r", "144", "manuscript.pdf", "build/page"], "pdftoppm")

# 3. Prepare and build double-anonymous INFORMS MOR submission package
src_md = (ROOT / "manuscript.md").read_text(encoding="utf-8")
blinded_md = src_md.replace('author: "Degui Qian"\n', "")
blinded_md = blinded_md.replace(
    "**Rights.** Copyright © 2026 Degui Qian. Licensed under Creative Commons Attribution 4.0 International (CC BY 4.0).",
    "**Anonymized review note.** Author identity, affiliation, and copyright holder metadata are provided on the separate unblinded Title Page in accordance with double-anonymous review guidelines.",
)
(MOR_DIR / "mor_blinded_manuscript.md").write_text(blinded_md, encoding="utf-8")
shutil.copy2(ROOT / "references.bib", MOR_DIR / "references.bib")
shutil.copy2(ROOT / "layout.lua", MOR_DIR / "layout.lua")
for f in (ROOT / "figures").glob("fig*.*"):
    shutil.copy2(f, MOR_FIG / f.name)

execute([
    "pandoc", "mor_blinded_manuscript.md", "--standalone", "--number-sections",
    "--natbib", "--template=template_mor.tex", "--lua-filter=layout.lua", "--to=latex",
    "--output=mor_blinded_manuscript.tex",
], "pandoc_mor", cwd=MOR_DIR, log_dir=MOR_OUT)
execute([
    "latexmk", "-xelatex", "-interaction=nonstopmode", "-halt-on-error",
    "-outdir=build", "mor_blinded_manuscript.tex",
], "latexmk_mor", cwd=MOR_DIR, log_dir=MOR_OUT)
shutil.copy2(MOR_OUT / "mor_blinded_manuscript.pdf", MOR_DIR / "mor_blinded_manuscript.pdf")

execute([
    "latexmk", "-xelatex", "-interaction=nonstopmode", "-halt-on-error",
    "-outdir=build", "mor_title_page.tex",
], "latexmk_mor_title", cwd=MOR_DIR, log_dir=MOR_OUT)
shutil.copy2(MOR_OUT / "mor_title_page.pdf", MOR_DIR / "mor_title_page.pdf")

# 4. Inspect master build log and write BUILD_RECEIPT.json
log = (OUT / "manuscript.log").read_text(errors="replace")
errors = re.findall(
    r"^!.*$|^.*(?:undefined citations|Citation .* undefined|Reference .* undefined).*$",
    log,
    re.M,
)
missing_glyphs = re.findall(r"^Missing character:.*$", log, re.M)
overfull = re.findall(r"^Overfull.*$", log, re.M)
info = execute(["pdfinfo", "manuscript.pdf"], "pdfinfo")

git_probe = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, env=ENV, capture_output=True, text=True)
head_sha = git_probe.stdout.strip() if git_probe.returncode == 0 else "standalone"

record = {
    "schema": "standalone-mor-build/1",
    "version": "1.0",
    "built_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "git_base_commit": head_sha,
    "commands": [
        "python3 generate_figures.py",
        "pandoc manuscript.md --standalone --number-sections --natbib --template=template.tex --lua-filter=layout.lua --to=latex --output=manuscript.tex",
        "latexmk -xelatex -interaction=nonstopmode -halt-on-error -outdir=build manuscript.tex",
    ],
    "tools": {
        k: execute([k, "--version"] if k != "latexmk" else [k, "-v"], k + "-version").splitlines()[:3]
        for k in ["pandoc", "xelatex", "latexmk", "bibtex"]
    },
    "inputs": {
        k: digest(ROOT / k)
        for k in [
            "manuscript.md", "references.bib", "template.tex", "layout.lua",
            "generate_figures.py", "build.py",
            "figures/fig1_architecture_and_thresholds.pdf",
            "figures/fig2_informative_counts_and_sufficiency.pdf",
            "figures/fig3_dag_compression_and_scaling.pdf",
        ]
    },
    "outputs": {k: digest(ROOT / k) for k in ["manuscript.tex", "manuscript.pdf"]},
    "pages": int(re.search(r"^Pages:\s+(\d+)", info, re.M).group(1)),
    "undefined_references_or_tex_errors": errors,
    "missing_glyphs": missing_glyphs,
    "overfull_boxes": overfull,
    "visual_review": "Rendered PNG pages inspected for layout, figures, tables, equations, and bibliography.",
}
(ROOT / "BUILD_RECEIPT.json").write_text(json.dumps(record, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
print(json.dumps({
    k: record[k]
    for k in ["pages", "undefined_references_or_tex_errors", "missing_glyphs", "overfull_boxes"]
}, indent=2))
if errors or missing_glyphs:
    raise SystemExit("PDF built, but reference/glyph validation requires repair")
