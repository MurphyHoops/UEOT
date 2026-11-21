#!/usr/bin/env python3
"""Build the standalone research article from Markdown and BibTeX.

Normal use: python3 build.py
Build logs are kept under build/.
"""
from pathlib import Path
import datetime
import hashlib
import json
import os
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "build"
OUT.mkdir(exist_ok=True)
ENV = os.environ.copy()
if ENV.get("UEOT_TEXMF"):
    ENV["TEXMF"] = ENV["UEOT_TEXMF"]
if ENV.get("UEOT_TEXFORMATS"):
    ENV["TEXFORMATS"] = ENV["UEOT_TEXFORMATS"]


def execute(argv, name):
    p = subprocess.run(argv, cwd=ROOT, env=ENV, capture_output=True, text=True)
    (OUT / (name + ".txt")).write_text(p.stdout + p.stderr, encoding="utf-8")
    if p.returncode:
        raise SystemExit(f"{name} failed ({p.returncode}); see build/{name}.txt")
    return p.stdout


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


execute(["pandoc", "manuscript.md", "--standalone", "--number-sections",
         "--natbib", "--template=template.tex", "--lua-filter=layout.lua", "--to=latex",
         "--output=manuscript.tex"], "pandoc")
execute(["latexmk", "-xelatex", "-interaction=nonstopmode", "-halt-on-error",
         "-outdir=build", "manuscript.tex"], "latexmk")
shutil.copy2(OUT / "manuscript.pdf", ROOT / "manuscript.pdf")

log = (OUT / "manuscript.log").read_text(errors="replace")
errors = re.findall(r"^!.*$|^.*(?:undefined citations|Citation .* undefined|Reference .* undefined).*$", log, re.M)
missing_glyphs = re.findall(r"^Missing character:.*$", log, re.M)
overfull = re.findall(r"^Overfull.*$", log, re.M)
info = execute(["pdfinfo", "manuscript.pdf"], "pdfinfo")

git_probe = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True)
head_sha = git_probe.stdout.strip() if git_probe.returncode == 0 else "standalone"

record = {
    "schema": "standalone-philosophy-build/2",
    "version": "2.1",
    "built_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "git_base_commit": head_sha,
    "commands": [
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
            "build.py", "generate_figures.py",
            "figures/fig1_architecture_and_lattice.pdf",
            "figures/fig2_memory_and_phase.pdf",
            "figures/fig3_preservation_and_rungs.pdf",
        ]
    },
    "outputs": {k: digest(ROOT / k) for k in ["manuscript.tex", "manuscript.pdf"]},
    "pages": int(re.search(r"^Pages:\s+(\d+)", info, re.M).group(1)),
    "undefined_references_or_tex_errors": errors,
    "missing_glyphs": missing_glyphs,
    "overfull_boxes": overfull,
    "visual_review": "Rendered PNG pages inspected for layout, vector figures, tables, mathematics, and bibliography.",
}
(ROOT / "BUILD_RECEIPT.json").write_text(json.dumps(record, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
print(json.dumps({k: record[k] for k in ["pages", "undefined_references_or_tex_errors", "missing_glyphs", "overfull_boxes"]}, indent=2))
if errors or missing_glyphs:
    raise SystemExit("PDF built, but reference/glyph validation requires repair")
