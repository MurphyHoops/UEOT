#!/usr/bin/env python3
"""Build the standalone master manuscript and APS Physical Review A submission package."""
from __future__ import annotations

from pathlib import Path
import datetime
import hashlib
import json
import os
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "build"
OUT.mkdir(exist_ok=True)
PRA_DIR = ROOT / "submissions" / "pra"
PRA_OUT = PRA_DIR / "build"
PRA_OUT.mkdir(parents=True, exist_ok=True)

ENV = os.environ.copy()
extra_paths = [
    str(Path.home() / "Library/TinyTeX/bin/universal-darwin"),
    str(Path.home() / ".TinyTeX/bin/universal-darwin"),
    "/Library/TeX/texbin",
    "/opt/homebrew/bin",
    "/usr/local/bin",
]
ENV["PATH"] = ":".join(extra_paths + [ENV.get("PATH", "")])


def execute(argv: list[str], name: str, cwd: Path = ROOT, log_dir: Path = OUT) -> str:
    p = subprocess.run(argv, cwd=cwd, env=ENV, capture_output=True, text=True)
    (log_dir / (name + ".txt")).write_text(p.stdout + p.stderr, encoding="utf-8")
    if p.returncode:
        raise SystemExit(f"{name} failed ({p.returncode}); see {log_dir / (name + '.txt')}")
    return p.stdout


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


execute([sys.executable, "generate_figures.py"], "generate_figures")
execute([
    "pandoc", "manuscript.md", "--standalone",
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

# Sync self-contained APS Physical Review A submission directory
master_md = (ROOT / "manuscript.md").read_text(encoding="utf-8")
(PRA_DIR / "pra_manuscript.md").write_text(master_md, encoding="utf-8")
shutil.copy2(ROOT / "references.bib", PRA_DIR / "references.bib")
shutil.copy2(ROOT / "layout.lua", PRA_DIR / "layout.lua")
shutil.copy2(ROOT / "verify_standalone.py", PRA_DIR / "verify_standalone.py")
(PRA_DIR / "figures").mkdir(exist_ok=True)
for fig_file in (ROOT / "figures").glob("*"):
    if fig_file.is_file():
        shutil.copy2(fig_file, PRA_DIR / "figures" / fig_file.name)

execute([
    "pandoc", "pra_manuscript.md", "--standalone",
    "--natbib", "--template=template_pra.tex", "--lua-filter=layout.lua", "--to=latex",
    "--output=pra_manuscript.tex",
], "pandoc_pra", cwd=PRA_DIR, log_dir=PRA_OUT)
execute([
    "latexmk", "-xelatex", "-interaction=nonstopmode", "-halt-on-error",
    "-outdir=build", "pra_manuscript.tex",
], "latexmk_pra", cwd=PRA_DIR, log_dir=PRA_OUT)
shutil.copy2(PRA_OUT / "pra_manuscript.pdf", PRA_DIR / "pra_manuscript.pdf")

for old_png in PRA_OUT.glob("pra-page-*.png"):
    old_png.unlink()
execute(["pdftoppm", "-png", "-r", "144", "pra_manuscript.pdf", "build/pra-page"], "pdftoppm_pra", cwd=PRA_DIR, log_dir=PRA_OUT)

pdf_pages = len(list(OUT.glob("page-*.png")))
pra_pages = len(list(PRA_OUT.glob("pra-page-*.png")))
receipt = {
    "built_at_utc": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
    "master_pdf_pages": pdf_pages,
    "pra_pdf_pages": pra_pages,
    "sha256": {
        "manuscript.pdf": digest(ROOT / "manuscript.pdf"),
        "submissions/pra/pra_manuscript.pdf": digest(PRA_DIR / "pra_manuscript.pdf"),
        "verify_standalone.py": digest(ROOT / "verify_standalone.py"),
    },
}
(ROOT / "BUILD_RECEIPT.json").write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"status": "BUILT", "master_pages": pdf_pages, "pra_pages": pra_pages}))
