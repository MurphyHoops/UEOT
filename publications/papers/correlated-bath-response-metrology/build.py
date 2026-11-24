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
import zipfile

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "build"
OUT.mkdir(exist_ok=True)
PRA_DIR = ROOT / "submissions" / "pra"
PRA_OUT = PRA_DIR / "build"
PRA_OUT.mkdir(parents=True, exist_ok=True)
FIXED_ZIP_TIME = (2026, 11, 24, 0, 0, 0)
SOURCE_EPOCH = str(int(datetime.datetime(*FIXED_ZIP_TIME, tzinfo=datetime.timezone.utc).timestamp()))

ENV = os.environ.copy()
extra_paths = [
    str(Path.home() / "Library/TinyTeX/bin/universal-darwin"),
    str(Path.home() / ".TinyTeX/bin/universal-darwin"),
    "/Library/TeX/texbin",
    "/opt/homebrew/bin",
    "/usr/local/bin",
]
ENV["PATH"] = ":".join(extra_paths + [ENV.get("PATH", "")])
ENV["PYTHONDONTWRITEBYTECODE"] = "1"
ENV["SOURCE_DATE_EPOCH"] = SOURCE_EPOCH
ENV["FORCE_SOURCE_DATE"] = "1"
ENV["LC_ALL"] = "C"


def preflight_tools() -> None:
    missing = [tool for tool in ("pandoc", "latexmk", "xelatex", "pdflatex", "bibtex", "pdftoppm", "pdfinfo", "pdftotext")
               if shutil.which(tool, path=ENV["PATH"]) is None]
    if missing:
        raise SystemExit(f"Missing required build tools in PATH: {missing}")


def execute(argv: list[str], name: str, cwd: Path = ROOT, log_dir: Path = OUT) -> str:
    p = subprocess.run(argv, cwd=cwd, env=ENV, capture_output=True, text=True, timeout=180)
    log_path = log_dir / (name + ".txt")
    log_path.write_text(p.stdout + p.stderr, encoding="utf-8")
    if p.returncode:
        tail = "\n".join((p.stdout + p.stderr).splitlines()[-25:])
        raise SystemExit(f"{name} failed ({p.returncode}); see {log_path}\n--- tail ---\n{tail}")
    return p.stdout


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def build_aps_source_zip(zip_path: Path) -> None:
    """Create a deterministic, self-contained pdflatex+bibtex archive for APS upload."""
    members = sorted([
        "pra_manuscript.tex",
        "references.bib",
        "figures/fig1_ramsey_ambiguity_and_causal_break.pdf",
        "figures/fig2_cutoff_bounds_and_channel_error.pdf",
        "figures/fig3_local_field_microcausality.pdf",
    ])
    with zipfile.ZipFile(zip_path, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as zf:
        for rel in members:
            zi = zipfile.ZipInfo(rel, date_time=FIXED_ZIP_TIME)
            zi.create_system = 3
            zi.external_attr = 0o100644 << 16
            zf.writestr(zi, (PRA_DIR / rel).read_bytes())


def main() -> None:
    preflight_tools()
    execute([sys.executable, "-B", "verify_standalone.py"], "verify_standalone")
    execute([sys.executable, "-B", "generate_figures.py"], "generate_figures")
    execute([
        "pandoc", "manuscript.md", "--standalone",
        "--natbib", "--template=template.tex", "--lua-filter=layout.lua", "--to=latex",
        "--output=manuscript.tex",
    ], "pandoc")
    execute([
        "latexmk", "-xelatex", "-interaction=nonstopmode", "-halt-on-error",
        "-outdir=build", "manuscript.tex",
    ], "latexmk")
    (OUT / "manuscript.out").unlink(missing_ok=True)
    shutil.copy2(OUT / "manuscript.pdf", ROOT / "manuscript.pdf")

    for old_png in OUT.glob("page-*.png"):
        old_png.unlink()
    execute(["pdftoppm", "-png", "-r", "144", "manuscript.pdf", "build/page"], "pdftoppm")

    master_md = (ROOT / "manuscript.md").read_text(encoding="utf-8")
    (PRA_DIR / "pra_manuscript.md").write_text(master_md, encoding="utf-8")
    shutil.copy2(ROOT / "references.bib", PRA_DIR / "references.bib")
    shutil.copy2(ROOT / "layout.lua", PRA_DIR / "layout.lua")
    shutil.copy2(ROOT / "verify_standalone.py", PRA_DIR / "verify_standalone.py")
    pra_fig_dir = PRA_DIR / "figures"
    pra_fig_dir.mkdir(exist_ok=True)
    for stale in pra_fig_dir.glob("*"):
        if stale.is_file():
            stale.unlink()
    for fig_file in (ROOT / "figures").glob("*"):
        if fig_file.is_file():
            shutil.copy2(fig_file, pra_fig_dir / fig_file.name)

    execute([
        "pandoc", "pra_manuscript.md", "--standalone",
        "--natbib", "--template=template_pra.tex", "--lua-filter=layout.lua", "--to=latex",
        "--output=pra_manuscript.tex",
    ], "pandoc_pra", cwd=PRA_DIR, log_dir=PRA_OUT)
    execute([
        "latexmk", "-xelatex", "-interaction=nonstopmode", "-halt-on-error",
        "-outdir=build", "pra_manuscript.tex",
    ], "latexmk_pra", cwd=PRA_DIR, log_dir=PRA_OUT)
    (PRA_OUT / "pra_manuscript.out").unlink(missing_ok=True)
    shutil.copy2(PRA_OUT / "pra_manuscript.pdf", PRA_DIR / "pra_manuscript.pdf")

    for old_png in PRA_OUT.glob("pra-page-*.png"):
        old_png.unlink()
    execute(["pdftoppm", "-png", "-r", "144", "pra_manuscript.pdf", "build/pra-page"], "pdftoppm_pra", cwd=PRA_DIR, log_dir=PRA_OUT)

    aps_zip = PRA_DIR / "pra_aps_latex_source.zip"
    build_aps_source_zip(aps_zip)

    pdf_pages = len(list(OUT.glob("page-*.png")))
    pra_pages = len(list(PRA_OUT.glob("pra-page-*.png")))
    tracked_for_receipt = [
        "manuscript.md",
        "references.bib",
        "layout.lua",
        "template.tex",
        "generate_figures.py",
        "verify_standalone.py",
        "figures/fig1_ramsey_ambiguity_and_causal_break.pdf",
        "figures/fig2_cutoff_bounds_and_channel_error.pdf",
        "figures/fig3_local_field_microcausality.pdf",
        "manuscript.tex",
        "manuscript.pdf",
        "submissions/pra/template_pra.tex",
        "submissions/pra/pra_manuscript.tex",
        "submissions/pra/pra_manuscript.pdf",
        "submissions/pra/pra_aps_latex_source.zip",
    ]
    receipt = {
        "built_at_utc": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "source_date_epoch": int(SOURCE_EPOCH),
        "master_pdf_pages": pdf_pages,
        "pra_pdf_pages": pra_pages,
        "sha256": {rel: digest(ROOT / rel) for rel in tracked_for_receipt},
    }
    (ROOT / "BUILD_RECEIPT.json").write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": "BUILT", "master_pages": pdf_pages, "pra_pages": pra_pages, "aps_source_zip": aps_zip.name}))


if __name__ == "__main__":
    main()
