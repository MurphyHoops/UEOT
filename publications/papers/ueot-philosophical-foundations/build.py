#!/usr/bin/env python3
"""Build the standalone master article and all three journal submission packages
(Synthese, BJPS, and Philosophy of Science) from Markdown, LaTeX, and BibTeX.

Normal use: python3 build.py
Build logs are kept under build/ and submissions/*/build/.
"""
from __future__ import annotations

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

SYN_DIR = ROOT / "submissions" / "synthese"
BJPS_DIR = ROOT / "submissions" / "bjps"
POS_DIR = ROOT / "submissions" / "philosophy-of-science"
for sub in (SYN_DIR, BJPS_DIR, POS_DIR):
    (sub / "build").mkdir(parents=True, exist_ok=True)

ENV = os.environ.copy()
extra_paths = [
    str(Path.home() / "Library/TinyTeX/bin/universal-darwin"),
    str(Path.home() / ".TinyTeX/bin/universal-darwin"),
    "/Library/TeX/texbin",
    "/opt/homebrew/bin",
    "/usr/local/bin",
]
ENV["PATH"] = ":".join(extra_paths + [ENV.get("PATH", "")])

if ENV.get("UEOT_TEXMF"):
    ENV["TEXMF"] = ENV["UEOT_TEXMF"]
if ENV.get("UEOT_TEXFORMATS"):
    ENV["TEXFORMATS"] = ENV["UEOT_TEXFORMATS"]


def execute(argv: list[str], name: str, cwd: Path = ROOT, log_dir: Path = OUT) -> str:
    p = subprocess.run(argv, cwd=cwd, env=ENV, capture_output=True, text=True)
    (log_dir / (name + ".txt")).write_text(p.stdout + p.stderr, encoding="utf-8")
    if p.returncode:
        raise SystemExit(f"{name} failed ({p.returncode}); see {log_dir / (name + '.txt')}")
    return p.stdout


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


# 1. Regenerate vector PDF & 300-DPI PNG figures
execute([sys.executable, "generate_figures.py"], "generate_figures")

# 2. Build Master Edition
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

# 3. Sync shared assets (references.bib, layout.lua, generate_figures.py, figures/*) across all 3 journal packages
for sub in (SYN_DIR, BJPS_DIR, POS_DIR):
    shutil.copy2(ROOT / "references.bib", sub / "references.bib")
    shutil.copy2(ROOT / "layout.lua", sub / "layout.lua")
    shutil.copy2(ROOT / "generate_figures.py", sub / "generate_figures.py")
    (sub / "figures").mkdir(exist_ok=True)
    for fig_file in (ROOT / "figures").glob("*"):
        if fig_file.is_file():
            shutil.copy2(fig_file, sub / "figures" / fig_file.name)

# 4. Generate & compile Synthese double-anonymous package
master_md = (ROOT / "manuscript.md").read_text(encoding="utf-8")
syn_md = master_md
for strip_line in ('author: "Degui Qian"\n', 'date: "November 2026"\n', 'version: "2.1"\n'):
    syn_md = syn_md.replace(strip_line, "", 1)

syn_declarations = """# Declarations {.unnumbered}

**Funding.** The author(s) received no external funding, grants, or financial support for the research, authorship, or preparation of this manuscript.

**Conflicts of interest / Competing interests.** The author(s) declare no financial or non-financial competing interests relevant to the content of this article.

**Availability of data and material.** Not applicable. No empirical datasets were generated or analyzed; all mathematical models, proofs, and rational witness calculations are self-contained in the text and Appendix.

**Code availability.** Reproducible Python scripts used to generate Figures 1–3 and verify exact rational arithmetic accompany the submission package; to preserve double-anonymous peer review, the permanent archival DOI of the companion Apache-2.0 Lean 4 formalizations is recorded on the separate unblinded Title Page.

**Author contributions and AI disclosure.** This research and manuscript were directed by the human author(s) and completed with Gemini 4 Carbon and ChatGPT 6 Astra across philosophical analysis, mathematical derivation, algebraic and formal cross-checking, bibliographic verification, and manuscript preparation. In accordance with Springer Nature authorship and generative AI policies, AI systems are not listed as co-authors; the human author(s) defined the philosophical theses, conceptual architecture, and mathematical models, audited and verified every argument, proof, rational calculation, and scholarly citation, and bear sole academic and legal responsibility for the entire work (full named attribution is provided on the separate unblinded Title Page).
"""
ack_idx = syn_md.index("# Acknowledgements and declarations {.unnumbered}")
syn_md = syn_md[:ack_idx] + syn_declarations
(SYN_DIR / "synthese_blinded_manuscript.md").write_text(syn_md, encoding="utf-8")

execute([
    "pandoc", "synthese_blinded_manuscript.md", "--standalone", "--number-sections",
    "--natbib", "--template=template_synthese.tex", "--lua-filter=layout.lua", "--to=latex",
    "--output=synthese_blinded_manuscript.tex",
], "pandoc_synthese", cwd=SYN_DIR, log_dir=SYN_DIR / "build")
execute([
    "latexmk", "-xelatex", "-interaction=nonstopmode", "-halt-on-error",
    "-outdir=build", "synthese_blinded_manuscript.tex",
], "latexmk_synthese", cwd=SYN_DIR, log_dir=SYN_DIR / "build")
shutil.copy2(SYN_DIR / "build" / "synthese_blinded_manuscript.pdf", SYN_DIR / "synthese_blinded_manuscript.pdf")

execute([
    "latexmk", "-xelatex", "-interaction=nonstopmode", "-halt-on-error",
    "-outdir=build", "synthese_title_page.tex",
], "latexmk_synthese_title", cwd=SYN_DIR, log_dir=SYN_DIR / "build")
shutil.copy2(SYN_DIR / "build" / "synthese_title_page.pdf", SYN_DIR / "synthese_title_page.pdf")

# 5. Compile BJPS triple-anonymous package
for stem in ("bjps_blinded_manuscript", "bjps_online_technical_appendix"):
    execute([
        "pandoc", f"{stem}.md", "--standalone", "--number-sections",
        "--natbib", "--template=template_bjps.tex", "--lua-filter=layout.lua", "--to=latex",
        f"--output={stem}.tex",
    ], f"pandoc_{stem}", cwd=BJPS_DIR, log_dir=BJPS_DIR / "build")
    execute([
        "latexmk", "-xelatex", "-interaction=nonstopmode", "-halt-on-error",
        "-outdir=build", f"{stem}.tex",
    ], f"latexmk_{stem}", cwd=BJPS_DIR, log_dir=BJPS_DIR / "build")
    shutil.copy2(BJPS_DIR / "build" / f"{stem}.pdf", BJPS_DIR / f"{stem}.pdf")

execute([
    "latexmk", "-xelatex", "-interaction=nonstopmode", "-halt-on-error",
    "-outdir=build", "bjps_title_page.tex",
], "latexmk_bjps_title", cwd=BJPS_DIR, log_dir=BJPS_DIR / "build")
shutil.copy2(BJPS_DIR / "build" / "bjps_title_page.pdf", BJPS_DIR / "bjps_title_page.pdf")

# 6. Compile Philosophy of Science double-anonymous package
for stem in ("pos_blinded_manuscript", "pos_supplementary_appendix"):
    execute([
        "pandoc", f"{stem}.md", "--standalone", "--number-sections",
        "--natbib", "--template=template_pos.tex", "--lua-filter=layout.lua", "--to=latex",
        f"--output={stem}.tex",
    ], f"pandoc_{stem}", cwd=POS_DIR, log_dir=POS_DIR / "build")
    execute([
        "latexmk", "-xelatex", "-interaction=nonstopmode", "-halt-on-error",
        "-outdir=build", f"{stem}.tex",
    ], f"latexmk_{stem}", cwd=POS_DIR, log_dir=POS_DIR / "build")
    shutil.copy2(POS_DIR / "build" / f"{stem}.pdf", POS_DIR / f"{stem}.pdf")

log = (OUT / "manuscript.log").read_text(errors="replace")
errors = re.findall(r"^!.*$|^.*(?:undefined citations|Citation .* undefined|Reference .* undefined).*$", log, re.M)
missing_glyphs = re.findall(r"^Missing character:.*$", log, re.M)
overfull = re.findall(r"^Overfull.*$", log, re.M)
info = execute(["pdfinfo", "manuscript.pdf"], "pdfinfo")

git_probe = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, env=ENV, capture_output=True, text=True)
head_sha = git_probe.stdout.strip() if git_probe.returncode == 0 else "standalone"

record = {
    "schema": "standalone-philosophy-build/3",
    "version": "2.2",
    "built_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "git_base_commit": head_sha,
    "commands": [
        "python3 generate_figures.py",
        "pandoc manuscript.md --standalone --number-sections --natbib --template=template.tex --lua-filter=layout.lua --to=latex --output=manuscript.tex",
        "latexmk -xelatex -interaction=nonstopmode -halt-on-error -outdir=build manuscript.tex",
        "compile submissions/{synthese,bjps,philosophy-of-science}/*",
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
            "submissions/synthese/template_synthese.tex",
            "submissions/synthese/synthese_title_page.tex",
            "submissions/bjps/template_bjps.tex",
            "submissions/bjps/bjps_blinded_manuscript.md",
            "submissions/bjps/bjps_online_technical_appendix.md",
            "submissions/bjps/bjps_title_page.tex",
            "submissions/philosophy-of-science/template_pos.tex",
            "submissions/philosophy-of-science/pos_blinded_manuscript.md",
            "submissions/philosophy-of-science/pos_supplementary_appendix.md",
        ]
    },
    "outputs": {
        k: digest(ROOT / k)
        for k in [
            "manuscript.tex", "manuscript.pdf",
            "submissions/synthese/synthese_blinded_manuscript.md",
            "submissions/synthese/synthese_blinded_manuscript.tex",
            "submissions/synthese/synthese_blinded_manuscript.pdf",
            "submissions/synthese/synthese_title_page.pdf",
            "submissions/bjps/bjps_blinded_manuscript.tex",
            "submissions/bjps/bjps_blinded_manuscript.pdf",
            "submissions/bjps/bjps_online_technical_appendix.tex",
            "submissions/bjps/bjps_online_technical_appendix.pdf",
            "submissions/bjps/bjps_title_page.pdf",
            "submissions/philosophy-of-science/pos_blinded_manuscript.tex",
            "submissions/philosophy-of-science/pos_blinded_manuscript.pdf",
            "submissions/philosophy-of-science/pos_supplementary_appendix.tex",
            "submissions/philosophy-of-science/pos_supplementary_appendix.pdf",
        ]
    },
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
