#!/usr/bin/env python3
"""Comprehensive validator for standalone manuscript integrity, 1-to-1 BibTeX parity,
PRA submission bundle parity, TeX/PDF logs, bookmarks, and standalone verification."""
from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import zlib

ROOT = Path(__file__).resolve().parent
PRA_DIR = ROOT / "submissions" / "pra"
ENV = os.environ.copy()
ENV["PATH"] = ":".join([
    str(Path.home() / "Library/TinyTeX/bin/universal-darwin"),
    str(Path.home() / ".TinyTeX/bin/universal-darwin"),
    "/Library/TeX/texbin",
    "/opt/homebrew/bin",
    "/usr/local/bin",
    ENV.get("PATH", ""),
])


def sha(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def check_bib_and_citations() -> dict:
    bib_text = (ROOT / "references.bib").read_text(encoding="utf-8")
    raw_keys = re.findall(r"@(\w+)\{([^,\s]+),", bib_text)
    assert len(raw_keys) == len({k for _, k in raw_keys}), "Duplicate BibTeX keys detected"
    bib_keys = {k for _, k in raw_keys}
    # Parse each BibTeX block for required schema and DOI/ISBN coverage
    blocks = re.split(r"(?=^@\w+\{)", bib_text, flags=re.MULTILINE)
    for blk in blocks:
        blk = blk.strip()
        if not blk or blk.startswith("%"):
            continue
        m_hdr = re.match(r"@(\w+)\{([^,\s]+),", blk)
        assert m_hdr, f"Malformed BibTeX block: {blk[:60]}"
        k = m_hdr.group(2)
        for req in ("author", "title", "year"):
            assert re.search(rf"\b{req}\s*=", blk), f"Missing {req} in BibTeX entry {k}"
        assert re.search(r"\b(doi|isbn)\s*=", blk), f"Missing doi/isbn in BibTeX entry {k}"

    md_text = (ROOT / "manuscript.md").read_text(encoding="utf-8")
    # Match citations inside [@k1; @k2] or standalone @key (not preceded by word chars)
    cited_keys = set(re.findall(r"(?<![A-Za-z0-9_])@([A-Za-z][A-Za-z0-9_]*)", md_text))
    missing = sorted(cited_keys - bib_keys)
    unused = sorted(bib_keys - cited_keys)
    assert not missing, f"Missing BibTeX keys: {missing}"
    assert not unused, f"Uncited BibTeX keys: {unused}"
    return {"bib_entries": len(bib_keys), "cited_keys": len(cited_keys), "missing": [], "unused": []}


def check_forbidden_jargon() -> dict:
    forbidden = [
        r"\bUEOT\b", r"MurphyHoops", r"C-QMEM", r"P-ROB", r"C-QSEL", r"P-MICRO",
        r"P-FIELD", r"\? No—", r"\bor True\b", r"observed\.json", r"\bPaper 4\b", r"\b0\.391\b", r"\b0\.400\b",
    ]
    checked_files = [
        ROOT / "manuscript.md",
        ROOT / "references.bib",
        ROOT / "verify_standalone.py",
        ROOT / "generate_figures.py",
        ROOT / "CLAIM_MATRIX.md",
        ROOT / "README.md",
        ROOT / "ABSTRACT_ZH.md",
        ROOT / "template.tex",
        PRA_DIR / "pra_manuscript.md",
        PRA_DIR / "cover_letter.md",
        PRA_DIR / "SUBMISSION_GUIDE_AND_MANIFEST.md",
        PRA_DIR / "template_pra.tex",
    ]
    hits = {}
    for fp in checked_files:
        txt = fp.read_text(encoding="utf-8")
        found = [pat for pat in forbidden if re.search(pat, txt)]
        if found:
            hits[fp.name] = found
    assert not hits, f"Forbidden tokens detected: {hits}"
    return {"checked_files": len(checked_files), "clean": True}


def check_pra_parity_and_receipt() -> dict:
    pairs = [
        ("manuscript.md", "submissions/pra/pra_manuscript.md"),
        ("references.bib", "submissions/pra/references.bib"),
        ("layout.lua", "submissions/pra/layout.lua"),
        ("verify_standalone.py", "submissions/pra/verify_standalone.py"),
    ]
    for src, dst in pairs:
        assert sha(ROOT / src) == sha(ROOT / dst), f"Parity mismatch between {src} and {dst}"
    root_figs = sorted(p.name for p in (ROOT / "figures").glob("*") if p.is_file())
    pra_figs = sorted(p.name for p in (PRA_DIR / "figures").glob("*") if p.is_file())
    assert root_figs == pra_figs, f"Figure directory mismatch: {root_figs} vs {pra_figs}"
    for fn in root_figs:
        assert sha(ROOT / "figures" / fn) == sha(PRA_DIR / "figures" / fn), f"Figure mismatch {fn}"

    receipt = json.loads((ROOT / "BUILD_RECEIPT.json").read_text(encoding="utf-8"))
    for rel, expected_sha in receipt["sha256"].items():
        assert sha(ROOT / rel) == expected_sha, f"BUILD_RECEIPT mismatch for {rel}"
    return {"parity": "EXACT", "figure_count": len(root_figs), "receipt_verified": True}


def extract_pdf_outline_titles(pdf_path: Path) -> list[str]:
    data = pdf_path.read_bytes()
    chunks = [data]
    for m in re.finditer(rb"stream\r?\n(.*?)\r?\nendstream", data, flags=re.DOTALL):
        try:
            chunks.append(zlib.decompress(m.group(1)))
        except zlib.error:
            pass
    titles: list[str] = []
    for ch in chunks:
        for m in re.finditer(rb"/Title\s*\(([^)]*)\)", ch):
            raw = m.group(1)
            titles.append(
                raw[2:].decode("utf-16-be", errors="replace") if raw.startswith(b"\xfe\xff") else raw.decode("latin1")
            )
        for m in re.finditer(rb"/Title\s*<([0-9A-Fa-f]+)>", ch):
            raw = bytes.fromhex(m.group(1).decode("ascii"))
            titles.append(
                raw[2:].decode("utf-16-be", errors="replace") if raw.startswith(b"\xfe\xff") else raw.decode("utf-8", errors="replace")
            )
    return titles


def check_tex_logs_and_outlines() -> dict:
    tex_logs = {
        "master_log": ROOT / "build" / "manuscript.log",
        "pra_log": PRA_DIR / "build" / "pra_manuscript.log",
    }
    bib_logs = {
        "master_blg": ROOT / "build" / "manuscript.blg",
        "pra_blg": PRA_DIR / "build" / "pra_manuscript.blg",
    }
    tex_sources = {
        "master_tex": ROOT / "manuscript.tex",
        "pra_tex": PRA_DIR / "pra_manuscript.tex",
    }
    pdf_outlines = {
        "master_pdf_outlines": ROOT / "manuscript.pdf",
        "pra_pdf_outlines": PRA_DIR / "pra_manuscript.pdf",
    }
    for stale_out in (ROOT / "build" / "manuscript.out", PRA_DIR / "build" / "pra_manuscript.out"):
        assert not stale_out.exists(), f"Stale bookmark file {stale_out} should be removed on build"
    report = {}
    for label, p in tex_logs.items():
        assert p.exists(), f"Missing log {p}"
        txt = p.read_text(encoding="utf-8", errors="replace")
        overfull = [ln for ln in txt.splitlines() if "Overfull \\" in ln]
        missing_ch = [ln for ln in txt.splitlines() if "Missing character:" in ln]
        bad_warn = [
            ln for ln in txt.splitlines()
            if ("LaTeX Warning:" in ln or "Float too large" in ln or "multiply-defined labels" in ln)
            and "bookmark" not in ln.lower()
        ]
        underfull = [ln for ln in txt.splitlines() if "Underfull \\" in ln]
        high_underfull = [ln for ln in underfull if re.search(r"badness\s+([3-9]\d{3}|1\d{4})", ln)]
        assert not overfull, f"{label} has Overfull boxes: {overfull[:5]}"
        assert not missing_ch, f"{label} has Missing characters: {missing_ch[:5]}"
        assert not bad_warn, f"{label} has LaTeX warnings: {bad_warn[:5]}"
        assert "There were undefined references" not in txt and "There were undefined citations" not in txt
        report[label] = {
            "overfull": 0,
            "missing_chars": 0,
            "warnings": 0,
            "underfull_total": len(underfull),
            "high_badness_underfull": len(high_underfull),
        }

    for label, p in bib_logs.items():
        assert p.exists(), f"Missing {p}"
        txt = p.read_text(encoding="utf-8", errors="replace")
        bib_warn = [ln for ln in txt.splitlines() if "Warning--" in ln or "I didn't find a database entry" in ln]
        assert not bib_warn, f"{label} has BibTeX warnings: {bib_warn[:5]}"
        report[label] = {"bib_warnings": 0}

    for label, p in tex_sources.items():
        assert p.exists(), f"Missing TeX source {p}"
        txt = p.read_text(encoding="utf-8", errors="replace")
        assert "\ufffd" not in txt, f"Replacement character U+FFFD in {p}"

    for label, p in pdf_outlines.items():
        titles = extract_pdf_outline_titles(p)
        assert len(titles) >= 20, f"Unexpectedly few outline entries in {p}: {len(titles)}"
        bad_titles = [
            t for t in titles
            if "\ufffd" in t or "\\mathbb" in t or "textbackslash" in t
        ]
        assert not bad_titles, f"{label} has malformed PDF outline titles: {bad_titles[:5]}"
        assert any("ℝ × S¹" in t for t in titles), f"{label} missing Unicode cylinder symbol in outlines"
        report[label] = {"clean_bookmarks": True, "outline_count": len(titles)}
    return report


def check_pdf_text(pdf_path: Path) -> dict:
    assert pdf_path.exists(), f"Missing PDF {pdf_path}"
    info = subprocess.run(["pdfinfo", str(pdf_path)], env=ENV, capture_output=True, text=True, check=True).stdout
    txt = subprocess.run(["pdftotext", str(pdf_path), "-"], env=ENV, capture_output=True, text=True, check=True).stdout
    pages_m = re.search(r"Pages:\s+(\d+)", info)
    pages = int(pages_m.group(1)) if pages_m else 0
    assert pages >= 10, f"Unexpectedly few pages in {pdf_path}: {pages}"
    assert "[?]" not in txt and "??" not in txt, f"Unresolved citation/ref glyphs in {pdf_path}"
    assert "[@" not in txt and "Fig.~" not in txt and ";\\" not in txt, (
        f"Unrendered Markdown/TeX artifact found in {pdf_path}"
    )
    double_hdr = re.findall(r"^(?:0\.\d+[ \t]+\d+|\d+(?:\.\d+)*[ \t]+\d+(?:\.\d+)*\.)", txt, flags=re.MULTILINE)
    assert not double_hdr, f"Double-numbered headings in {pdf_path}: {double_hdr[:5]}"
    for leak in ("UEOT", "MurphyHoops", "P-QMEM", "0.391", "0.400"):
        assert leak not in txt, f"Disallowed token '{leak}' leaked into {pdf_path}"
    return {"pages": pages, "chars": len(txt), "clean_glyphs": True, "double_headings": 0}


def check_manuscript_numeric_parity() -> dict:
    md_text = (ROOT / "manuscript.md").read_text(encoding="utf-8")
    required_literals = [
        "0.730531651137",
        "0.360071794945",
        "0.735275955165",
        "0.119850748164",
        "0.147616987004",
        "51.240115",
        "7.413297",
        "0.411787",
        "0.067589",
        "0.033892297103",
        "0.035357047207",
        "0.046090140885",
        "0.047554890989",
        "0.027602916940",
        "0.149701",
        "-0.008630",
        "4/32",
        "0/68",
        "0.605581355419",
    ]
    missing = [lit for lit in required_literals if lit not in md_text]
    assert not missing, f"Missing expected exact figures in manuscript.md: {missing}"
    return {"verified_literals": len(required_literals)}


def run_cli_verifier() -> dict:
    p = subprocess.run([sys.executable, str(ROOT / "verify_standalone.py")], env=ENV, capture_output=True, text=True, check=True)
    res = json.loads(p.stdout)
    assert res.get("status") == "PASS"
    return res


def compute_sha256_manifest() -> list[tuple[str, str]]:
    targets = []
    for p in sorted(ROOT.rglob("*")):
        if not p.is_file():
            continue
        rel = p.relative_to(ROOT).as_posix()
        if rel.startswith("build/") or rel.startswith("submissions/pra/build/") or "__pycache__/" in rel:
            continue
        if rel in {"SHA256SUMS", "VALIDATION.json"} or rel.startswith("."):
            continue
        targets.append((sha(p), rel))
    return targets


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true", help="Read-only check against existing SHA256SUMS & VALIDATION*.json")
    args = parser.parse_args()

    if any(shutil.which(t, path=ENV["PATH"]) is None for t in ("pdfinfo", "pdftotext")):
        raise SystemExit("Missing pdfinfo/pdftotext in PATH")

    standalone_res = run_cli_verifier()
    bib_res = check_bib_and_citations()
    jargon_res = check_forbidden_jargon()
    parity_res = check_pra_parity_and_receipt()
    log_res = check_tex_logs_and_outlines()
    master_pdf = check_pdf_text(ROOT / "manuscript.pdf")
    pra_pdf = check_pdf_text(PRA_DIR / "pra_manuscript.pdf")
    numeric_res = check_manuscript_numeric_parity()

    if args.check:
        expected_lines = (ROOT / "SHA256SUMS").read_text(encoding="utf-8").splitlines()
        actual_lines = [f"{h}  {rel}" for h, rel in compute_sha256_manifest()]
        assert actual_lines == expected_lines, "SHA256SUMS mismatch under --check mode"
        print(json.dumps({"status": "PASS_READONLY", "bib": bib_res, "parity": parity_res, "numeric": numeric_res}, indent=2))
        return

    now = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    pra_val = {
        "validated_at_utc": now,
        "status": "PASS",
        "venue": "Physical Review A (APS)",
        "review_model": "single-anonymous",
        "pra_pdf": pra_pdf,
        "citations": bib_res,
        "bundle_parity": parity_res,
        "tex_logs": {k: v for k, v in log_res.items() if k.startswith("pra_")},
        "jargon_audit": jargon_res,
        "numeric_parity": numeric_res,
        "standalone_verifier": standalone_res,
    }
    (PRA_DIR / "VALIDATION_PRA.json").write_text(json.dumps(pra_val, indent=2) + "\n", encoding="utf-8")

    targets = compute_sha256_manifest()
    (ROOT / "SHA256SUMS").write_text("\n".join(f"{h}  {rel}" for h, rel in targets) + "\n", encoding="utf-8")

    val = {
        "validated_at_utc": now,
        "status": "PASS",
        "citations": bib_res,
        "bundle_parity": parity_res,
        "jargon_audit": jargon_res,
        "tex_logs": log_res,
        "master_pdf": master_pdf,
        "pra_pdf": pra_pdf,
        "numeric_parity": numeric_res,
        "sha256sums_file_count": len(targets),
        "standalone_verifier": standalone_res,
    }
    (ROOT / "VALIDATION.json").write_text(json.dumps(val, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": "PASS", "bib": bib_res, "parity": parity_res, "master_pdf": master_pdf, "pra_pdf": pra_pdf}, indent=2))


if __name__ == "__main__":
    main()
