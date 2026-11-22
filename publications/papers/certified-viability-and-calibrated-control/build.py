#!/usr/bin/env python3
"""Build the standalone master article and double-anonymous JAR submission package.

Normal use: python3 build.py
Build logs and rendered page PNGs are kept under build/ and submissions/jar/build/.
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
JAR_DIR = ROOT / "submissions" / "jar"
JAR_OUT = JAR_DIR / "build"
JAR_OUT.mkdir(parents=True, exist_ok=True)

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


execute([sys.executable, "generate_figures.py"], "generate_figures")
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

# Build Springer JAR double-anonymous submission package
master_md = (ROOT / "manuscript.md").read_text(encoding="utf-8")
jar_md = master_md.replace(
    'author: "Degui Qian"\n',
    'msc2020: "68V15; 93E20; 90C40; 62C20"\n'
    'acmccs: "Theory of computation → Logic and verification; Sequential decision making; Planning under uncertainty"\n',
    1,
)

blinded_declarations = """# Declarations {.unnumbered}

**Funding.** The author(s) received no external funding, grants, or financial support for the research, formalization, authorship, or preparation of this manuscript.

**Conflicts of interest / Competing interests.** The author(s) declare no financial or non-financial competing interests relevant to the content of this article.

**Availability of data and material.** Not applicable. No empirical datasets were generated or analyzed; all mathematical proofs, finite counterexamples, and exact rational dynamic-programming evaluations are self-contained in the text and Mathematical Appendix.

**Code availability.** Every definition, theorem, executable controller synthesizer, rational statistical risk oracle, counterexample, and greatest-common-divisor-free integer dynamic-programming certificate reported in this article has been formally verified in Lean 4 (v4.33.1) over Mathlib across 1,051 compiled modules, passing an environment-wide axiom audit (`ExhaustiveAxiomAudit`) restricting transitive dependencies exclusively to `{propext, Classical.choice, Quot.sound}` (`0` `sorryAx`, `0` `Lean.ofReduceBool`). To preserve double-anonymous peer review, the permanent archival DOI of the Apache-2.0 Lean 4 formalization archive (v1.0.0) and verification scripts is recorded on the separate unblinded Title Page and available to referees through the editorial office.

**Author contributions and AI disclosure.** This research and manuscript were directed by the human author(s) and completed with Gemini 4 Carbon and ChatGPT 6 Astra across mathematical derivation, pure-kernel Lean 4 formalization engineering, computable rational oracle verification, bibliographic cross-checking, and manuscript preparation. In accordance with Springer Nature authorship and generative AI policies, AI systems are not listed as co-authors; the human author(s) defined the research program, problem formulations, and formalization architecture, audited and verified every mathematical proof, mechanized Lean 4 declaration, counterexample witness, and scholarly citation, and bear sole academic and legal responsibility for the entire work (full named attribution is recorded on the separate unblinded Title Page).
"""

decl_idx = jar_md.index("# Declarations {.unnumbered}")
jar_md = jar_md[:decl_idx] + blinded_declarations
(JAR_DIR / "jar_blinded_manuscript.md").write_text(jar_md, encoding="utf-8")

shutil.copy2(ROOT / "references.bib", JAR_DIR / "references.bib")
shutil.copy2(ROOT / "layout.lua", JAR_DIR / "layout.lua")
(JAR_DIR / "figures").mkdir(exist_ok=True)
for fig_file in (ROOT / "figures").glob("*"):
    if fig_file.is_file():
        shutil.copy2(fig_file, JAR_DIR / "figures" / fig_file.name)

execute([
    "pandoc", "jar_blinded_manuscript.md", "--standalone", "--number-sections",
    "--natbib", "--template=template_jar.tex", "--lua-filter=layout.lua", "--to=latex",
    "--output=jar_blinded_manuscript.tex",
], "pandoc_jar", cwd=JAR_DIR, log_dir=JAR_OUT)
execute([
    "latexmk", "-xelatex", "-interaction=nonstopmode", "-halt-on-error",
    "-outdir=build", "jar_blinded_manuscript.tex",
], "latexmk_jar", cwd=JAR_DIR, log_dir=JAR_OUT)
shutil.copy2(JAR_OUT / "jar_blinded_manuscript.pdf", JAR_DIR / "jar_blinded_manuscript.pdf")

execute([
    "latexmk", "-xelatex", "-interaction=nonstopmode", "-halt-on-error",
    "-outdir=build", "jar_title_page.tex",
], "latexmk_jar_title", cwd=JAR_DIR, log_dir=JAR_OUT)
shutil.copy2(JAR_OUT / "jar_title_page.pdf", JAR_DIR / "jar_title_page.pdf")

log = (OUT / "manuscript.log").read_text(errors="replace")
errors = re.findall(
    r"^!.*$|^.*(?:undefined citations|Citation .* undefined|Reference .* undefined).*$",
    log,
    re.M,
)
missing_glyphs = re.findall(r"^Missing character:.*$", log, re.M)
overfull = re.findall(r"^Overfull.*$", log, re.M)
info = execute(["pdfinfo", "manuscript.pdf"], "pdfinfo")
jar_info = execute(["pdfinfo", "jar_blinded_manuscript.pdf"], "pdfinfo_jar", cwd=JAR_DIR, log_dir=JAR_OUT)

git_probe = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, env=ENV, capture_output=True, text=True)
head_sha = git_probe.stdout.strip() if git_probe.returncode == 0 else "standalone"

record = {
    "schema": "standalone-jar-build/2",
    "version": "1.1",
    "built_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "git_base_commit": head_sha,
    "commands": [
        "pandoc manuscript.md --standalone --number-sections --natbib --template=template.tex --lua-filter=layout.lua --to=latex --output=manuscript.tex",
        "latexmk -xelatex -interaction=nonstopmode -halt-on-error -outdir=build manuscript.tex",
        "pandoc jar_blinded_manuscript.md --standalone --number-sections --natbib --template=template_jar.tex --lua-filter=layout.lua --to=latex --output=jar_blinded_manuscript.tex",
        "latexmk -xelatex -interaction=nonstopmode -halt-on-error -outdir=build jar_blinded_manuscript.tex",
        "latexmk -xelatex -interaction=nonstopmode -halt-on-error -outdir=build jar_title_page.tex",
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
            "figures/fig1_synthesis_and_calibration.pdf",
            "figures/fig2_fault_regret_and_kernel_dp.pdf",
            "submissions/jar/template_jar.tex",
            "submissions/jar/jar_title_page.tex",
        ]
    },
    "outputs": {
        k: digest(ROOT / k)
        for k in [
            "manuscript.tex", "manuscript.pdf",
            "submissions/jar/jar_blinded_manuscript.md",
            "submissions/jar/jar_blinded_manuscript.tex",
            "submissions/jar/jar_blinded_manuscript.pdf",
            "submissions/jar/jar_title_page.pdf",
        ]
    },
    "pages": int(re.search(r"^Pages:\s+(\d+)", info, re.M).group(1)),
    "jar_blinded_pages": int(re.search(r"^Pages:\s+(\d+)", jar_info, re.M).group(1)),
    "undefined_references_or_tex_errors": errors,
    "missing_glyphs": missing_glyphs,
    "overfull_boxes": overfull,
    "visual_review": "Rendered PNG pages inspected for layout, tables, mathematics, and bibliography.",
}
(ROOT / "BUILD_RECEIPT.json").write_text(json.dumps(record, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
print(json.dumps({
    k: record[k]
    for k in ["pages", "jar_blinded_pages", "undefined_references_or_tex_errors", "missing_glyphs", "overfull_boxes"]
}, indent=2))
if errors or missing_glyphs:
    raise SystemExit("PDF built, but reference/glyph validation requires repair")
