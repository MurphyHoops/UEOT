#!/usr/bin/env python3
"""Validate standalone journal manuscript integrity, citation parity, TeX/BibTeX cleanliness,
PDF text hygiene, and exact standalone mathematical verification."""
from __future__ import annotations

import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
PRA_DIR = ROOT / "submissions" / "pra"
sys.path.insert(0, str(ROOT))
import verify_standalone  # noqa: E402

ENV = os.environ.copy()
ENV["PATH"] = ":".join([
    str(Path.home() / "Library/TinyTeX/bin/universal-darwin"),
    "/Library/TeX/texbin",
    "/opt/homebrew/bin",
    "/usr/local/bin",
    ENV.get("PATH", ""),
])


def sha(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def check_bib_and_citations() -> dict:
    bib_text = (ROOT / "references.bib").read_text(encoding="utf-8")
    bib_keys = set(re.findall(r"@\w+\{([^,]+),", bib_text))
    md_text = (ROOT / "manuscript.md").read_text(encoding="utf-8")
    cited_keys = set(re.findall(r"@([A-Za-z][A-Za-z0-9_]*)", md_text))
    # Remove any non-citation false matches if any, e.g. email? None in manuscript.
    missing = sorted(cited_keys - bib_keys)
    unused = sorted(bib_keys - cited_keys)
    assert not missing, f"Missing BibTeX keys: {missing}"
    assert not unused, f"Uncited BibTeX keys: {unused}"
    return {"bib_entries": len(bib_keys), "cited_keys": len(cited_keys), "missing": [], "unused": []}


def check_forbidden_jargon() -> dict:
    forbidden = ["UEOT", "MurphyHoops", "C-QMEM", "P-ROB", "C-QSEL", "P-MICRO", "P-FIELD", "? No—", "or True", "observed.json", "Paper 4"]
    checked_files = [
        ROOT / "manuscript.md",
        ROOT / "references.bib",
        ROOT / "verify_standalone.py",
        ROOT / "generate_figures.py",
        PRA_DIR / "pra_manuscript.md",
        PRA_DIR / "cover_letter.md",
        PRA_DIR / "SUBMISSION_GUIDE_AND_MANIFEST.md",
    ]
    hits = {}
    for fp in checked_files:
        txt = fp.read_text(encoding="utf-8")
        found = [tok for tok in forbidden if tok in txt]
        if found:
            hits[fp.name] = found
    assert not hits, f"Forbidden internal tokens detected: {hits}"
    return {"checked_files": len(checked_files), "clean": True}


def check_tex_logs() -> dict:
    logs = {
        "master_latexmk": ROOT / "build" / "latexmk.txt",
        "master_blg": ROOT / "build" / "manuscript.blg",
        "pra_latexmk": PRA_DIR / "build" / "latexmk_pra.txt",
        "pra_blg": PRA_DIR / "build" / "pra_manuscript.blg",
    }
    report = {}
    for label, p in logs.items():
        assert p.exists(), f"Missing log {p}"
        txt = p.read_text(encoding="utf-8", errors="replace")
        overfull = [ln for ln in txt.splitlines() if "Overfull \\" in ln]
        undef = [ln for ln in txt.splitlines() if ("undefined" in ln.lower() and "There were" not in ln and "citation" in ln.lower()) or "Warning--" in ln]
        bib_warn = [ln for ln in txt.splitlines() if "Warning--" in ln or "I didn't find a database entry" in ln]
        assert not overfull, f"{label} has Overfull boxes: {overfull[:5]}"
        assert not bib_warn, f"{label} has BibTeX warnings: {bib_warn[:5]}"
        assert "There were undefined references" not in txt and "There were undefined citations" not in txt, f"{label} has undefined refs/cites"
        report[label] = {"overfull": len(overfull), "bib_warnings": len(bib_warn)}
    return report


def check_pdf_text(pdf_path: Path) -> dict:
    assert pdf_path.exists(), f"Missing PDF {pdf_path}"
    info = subprocess.run(["pdfinfo", str(pdf_path)], env=ENV, capture_output=True, text=True, check=True).stdout
    txt = subprocess.run(["pdftotext", str(pdf_path), "-"], env=ENV, capture_output=True, text=True, check=True).stdout
    pages_m = re.search(r"Pages:\s+(\d+)", info)
    pages = int(pages_m.group(1)) if pages_m else 0
    assert pages >= 10, f"Unexpectedly few pages in {pdf_path}: {pages}"
    assert "[?]" not in txt and "??" not in txt, f"Unresolved citation/ref glyphs in {pdf_path}"
    for leak in ["UEOT", "MurphyHoops", "P-QMEM"]:
        assert leak not in txt, f"Internal token '{leak}' leaked into {pdf_path}"
    return {"pages": pages, "chars": len(txt), "clean_glyphs": True}


def write_sha256sums() -> int:
    targets = []
    for p in sorted(ROOT.rglob("*")):
        if not p.is_file():
            continue
        rel = p.relative_to(ROOT).as_posix()
        if rel.startswith("build/") or rel.startswith("submissions/pra/build/"):
            continue
        if rel in {"SHA256SUMS", "VALIDATION.json"} or rel.startswith("."):
            continue
        targets.append((sha(p), rel))
    lines = [f"{h}  {rel}" for h, rel in targets]
    (ROOT / "SHA256SUMS").write_text("\n".join(lines) + "\n", encoding="utf-8")
    return len(targets)


def main() -> None:
    standalone_res = verify_standalone.run_all_standalone_checks()
    bib_res = check_bib_and_citations()
    jargon_res = check_forbidden_jargon()
    log_res = check_tex_logs()
    master_pdf = check_pdf_text(ROOT / "manuscript.pdf")
    pra_pdf = check_pdf_text(PRA_DIR / "pra_manuscript.pdf")
    now = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")

    pra_val = {
        "validated_at_utc": now,
        "status": "PASS",
        "venue": "Physical Review A (APS)",
        "review_model": "single-anonymous",
        "pra_pdf": pra_pdf,
        "citations": bib_res,
        "tex_logs": {k: v for k, v in log_res.items() if k.startswith("pra_")},
        "jargon_audit": jargon_res,
        "standalone_verifier": standalone_res,
    }
    (PRA_DIR / "VALIDATION_PRA.json").write_text(json.dumps(pra_val, indent=2) + "\n", encoding="utf-8")

    val = {
        "validated_at_utc": now,
        "status": "PASS",
        "citations": bib_res,
        "jargon_audit": jargon_res,
        "tex_logs": log_res,
        "master_pdf": master_pdf,
        "pra_pdf": pra_pdf,
        "standalone_verifier": standalone_res,
    }
    val["sha256sums_file_count"] = write_sha256sums()
    (ROOT / "VALIDATION.json").write_text(json.dumps(val, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": "PASS", "bib": bib_res, "master_pdf": master_pdf, "pra_pdf": pra_pdf}, indent=2))


if __name__ == "__main__":
    main()
