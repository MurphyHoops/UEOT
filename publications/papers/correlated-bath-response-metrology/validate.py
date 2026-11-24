#!/usr/bin/env python3
"""Comprehensive validator for standalone manuscript integrity, 1-to-1 BibTeX parity,
PRA submission bundle parity, dual-engine (XeLaTeX + pdfLaTeX) ZIP round-trip, TeX/PDF logs,
Unicode bookmarks, numeric/retraction parity, and standalone verification."""
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
import tempfile
import zipfile
import zlib

ROOT = Path(__file__).resolve().parent
PRA_DIR = ROOT / "submissions" / "pra"
FIXED_ZIP_TIME = (2026, 11, 24, 0, 0, 0)
EXPECTED_BIB_ENTRIES = 79
EXPECTED_RECEIPT_COUNT = 15
EXPECTED_ZIP_MEMBERS = [
    "figures/fig1_ramsey_ambiguity_and_causal_break.pdf",
    "figures/fig2_cutoff_bounds_and_channel_error.pdf",
    "figures/fig3_local_field_microcausality.pdf",
    "pra_manuscript.tex",
    "references.bib",
]

ENV = os.environ.copy()
ENV["PATH"] = ":".join([
    str(Path.home() / "Library/TinyTeX/bin/universal-darwin"),
    str(Path.home() / ".TinyTeX/bin/universal-darwin"),
    "/Library/TeX/texbin",
    "/opt/homebrew/bin",
    "/usr/local/bin",
    ENV.get("PATH", ""),
])
ENV["PYTHONDONTWRITEBYTECODE"] = "1"
ENV["LC_ALL"] = "C"


def sha(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def sha_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def check_bib_and_citations() -> dict:
    raw_bib = (ROOT / "references.bib").read_text(encoding="utf-8")
    bib_lines = [ln for ln in raw_bib.splitlines() if not ln.lstrip().startswith("%")]
    bib_text = "\n".join(bib_lines)

    blocks = re.split(r"(?=^@\w+\{)", bib_text, flags=re.MULTILINE)
    raw_keys: list[str] = []
    for blk in blocks:
        blk = blk.strip()
        if not blk:
            continue
        m_hdr = re.match(r"^@(\w+)\{([^,\s]+),", blk)
        assert m_hdr, f"Malformed BibTeX block: {blk[:60]}"
        etype, k = m_hdr.group(1).lower(), m_hdr.group(2)
        if etype in {"comment", "string", "preamble"}:
            continue
        raw_keys.append(k)
        for req in ("author", "title", "year"):
            assert re.search(rf"\b{req}\s*=", blk, flags=re.IGNORECASE), (
                f"Missing {req} in BibTeX entry {k}"
            )
        assert re.search(r"\b(doi|isbn)\s*=", blk, flags=re.IGNORECASE), (
            f"Missing doi/isbn in BibTeX entry {k}"
        )

    assert len(raw_keys) == len(set(raw_keys)), "Duplicate BibTeX keys detected"
    bib_keys = set(raw_keys)
    assert len(bib_keys) == EXPECTED_BIB_ENTRIES, (
        f"Expected {EXPECTED_BIB_ENTRIES} BibTeX entries, found {len(bib_keys)}"
    )

    md_text = (ROOT / "manuscript.md").read_text(encoding="utf-8")
    cited_keys = set(
        re.findall(r"(?<![A-Za-z0-9_])@([A-Za-z][A-Za-z0-9_]*(?:[:\-][A-Za-z0-9_]+)*)", md_text)
    )
    missing = sorted(cited_keys - bib_keys)
    unused = sorted(bib_keys - cited_keys)
    assert not missing, f"Missing BibTeX keys: {missing}"
    assert not unused, f"Uncited BibTeX keys: {unused}"
    return {"bib_entries": len(bib_keys), "cited_keys": len(cited_keys), "missing": [], "unused": []}


def check_forbidden_jargon() -> dict:
    forbidden = [
        r"\bUEOT\b",
        r"MurphyHoops",
        r"C-QMEM",
        r"P-QMEM",
        r"P-ROB",
        r"C-QSEL",
        r"P-MICRO",
        r"P-FIELD",
        r"\? No—",
        r"\bor True\b",
        r"observed\.json",
        r"\bPaper 4\b",
        r"NOT_CERTIFIED",
        r"Cram\\'er",
        r"Cram'er",
        r"Cram\\textquotesingle",
        r"\b0\.391\b",
        r"\b0\.400\b",
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
    hits: dict[str, list[str]] = {}
    for fp in checked_files:
        txt = fp.read_text(encoding="utf-8")
        found = [pat for pat in forbidden if re.search(pat, txt)]
        if found:
            hits[fp.name] = found
    assert not hits, f"Forbidden tokens detected: {hits}"

    retracted_patterns = [
        r"(?:\\le|<=|≤)\s*0\.0276(?![0-9])",
        r"(?:\\le|<=|≤)\s*0\.033892(?![0-9])",
        r"(?:\\le|<=|≤)\s*0\.035357(?![0-9])",
        r"(?:\\le|<=|≤)\s*0\.046090(?![0-9])",
        r"2\.485477\s*(?:\\times|×|e-12)",
        r"\b0\.149701(?![0-9])",
        r"-0\.008630(?![0-9])",
        r"0\.956228",
        r"0\.149700906569",
        r"0\.218613103394",
        r"-0\.008629740905",
        r"`0\.017009`",
        r"\$0\.017009\$",
        r"\$B_\{16\}\s*=",
        r"\bincommensurate\b",
        r"super-exponential",
        r"6\\times 10\^4",
        r"6×10",
        r"annihilates cross-terms",
        r"routinely conflates",
    ]
    retracted_files = [
        ROOT / "manuscript.md",
        ROOT / "CLAIM_MATRIX.md",
        ROOT / "ABSTRACT_ZH.md",
        ROOT / "README.md",
        PRA_DIR / "cover_letter.md",
        PRA_DIR / "SUBMISSION_GUIDE_AND_MANIFEST.md",
    ]
    retracted_hits: dict[str, list[str]] = {}
    for fp in retracted_files:
        txt = fp.read_text(encoding="utf-8")
        found = [pat for pat in retracted_patterns if re.search(pat, txt)]
        if found:
            retracted_hits[fp.name] = found
    assert not retracted_hits, f"Retracted inward-rounded bounds detected: {retracted_hits}"
    return {
        "checked_files": len(checked_files),
        "retracted_checked_files": len(retracted_files),
        "clean": True,
    }


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
    assert len(receipt["sha256"]) == EXPECTED_RECEIPT_COUNT, (
        f"Expected {EXPECTED_RECEIPT_COUNT} BUILD_RECEIPT entries, found {len(receipt['sha256'])}"
    )
    for rel, expected_sha in receipt["sha256"].items():
        assert sha(ROOT / rel) == expected_sha, f"BUILD_RECEIPT mismatch for {rel}"

    aps_zip = PRA_DIR / "pra_aps_latex_source.zip"
    assert aps_zip.exists(), f"Missing APS source bundle {aps_zip}"
    with zipfile.ZipFile(aps_zip, "r") as zf:
        infos = zf.infolist()
        names = [zi.filename for zi in infos]
        assert names == EXPECTED_ZIP_MEMBERS, f"APS ZIP member mismatch: {names}"
        for zi in infos:
            assert zi.date_time == FIXED_ZIP_TIME, f"Non-deterministic ZIP timestamp for {zi.filename}: {zi.date_time}"
            assert (zi.external_attr >> 16) == 0o100644, (
                f"Unexpected ZIP permissions for {zi.filename}: {oct(zi.external_attr >> 16)}"
            )
            assert sha_bytes(zf.read(zi.filename)) == sha(PRA_DIR / zi.filename), (
                f"APS ZIP content mismatch for {zi.filename}"
            )

    return {
        "parity": "EXACT",
        "figure_count": len(root_figs),
        "receipt_verified": True,
        "receipt_count": len(receipt["sha256"]),
        "aps_zip_verified": True,
        "aps_zip_members": len(EXPECTED_ZIP_MEMBERS),
    }


def _decode_pdf_literal(buf: bytes, start: int) -> tuple[bytes, int]:
    """Decode a balanced PDF literal string starting immediately after '('."""
    out = bytearray()
    depth = 1
    i = start
    n = len(buf)
    simple_escapes = {
        ord("n"): ord("\n"),
        ord("r"): ord("\r"),
        ord("t"): ord("\t"),
        ord("b"): ord("\b"),
        ord("f"): ord("\f"),
        ord("("): ord("("),
        ord(")"): ord(")"),
        ord("\\"): ord("\\"),
    }
    while i < n and depth > 0:
        b = buf[i]
        if b == 0x5C:  # backslash
            i += 1
            if i >= n:
                break
            esc = buf[i]
            if esc == 0x0D:  # \r or \r\n line continuation
                i += 1
                if i < n and buf[i] == 0x0A:
                    i += 1
                continue
            if esc == 0x0A:  # \n line continuation
                i += 1
                continue
            if esc in simple_escapes:
                out.append(simple_escapes[esc])
                i += 1
            elif 48 <= esc <= 55:  # octal \d, \dd, or \ddd
                oct_digits = bytearray([esc])
                i += 1
                for _ in range(2):
                    if i < n and 48 <= buf[i] <= 55:
                        oct_digits.append(buf[i])
                        i += 1
                    else:
                        break
                out.append(int(oct_digits.decode("ascii"), 8) & 0xFF)
            else:
                out.append(esc)
                i += 1
        elif b == 0x28:  # '('
            out.append(b)
            depth += 1
            i += 1
        elif b == 0x29:  # ')'
            depth -= 1
            if depth == 0:
                i += 1
                break
            out.append(b)
            i += 1
        else:
            out.append(b)
            i += 1
    return bytes(out), i


def _bytes_to_outline_str(raw: bytes) -> str:
    if raw.startswith(b"\xfe\xff"):
        return raw[2:].decode("utf-16-be", errors="replace")
    if raw.startswith(b"\xff\xfe"):
        return raw[2:].decode("utf-16-le", errors="replace")
    try:
        return raw.decode("utf-8")
    except UnicodeDecodeError:
        return raw.decode("latin1")


def _decode_pdf_string_token(buf: bytes, start: int) -> str | None:
    stripped = buf[start:].lstrip()
    if stripped.startswith(b"("):
        raw, _ = _decode_pdf_literal(stripped, 1)
        return _bytes_to_outline_str(raw)
    if stripped.startswith(b"<"):
        end_hex = stripped.find(b">", 1)
        if end_hex != -1:
            hex_clean = re.sub(rb"\s+", b"", stripped[1:end_hex])
            if len(hex_clean) % 2 == 0 and re.fullmatch(rb"[0-9A-Fa-f]*", hex_clean):
                raw = bytes.fromhex(hex_clean.decode("ascii"))
                return _bytes_to_outline_str(raw)
    return None


def extract_pdf_outline_titles(pdf_path: Path) -> list[str]:
    data = pdf_path.read_bytes()
    objs: dict[int, bytes] = {}
    for m in re.finditer(rb"(?<![0-9])(\d+)\s+\d+\s+obj\b(.*?)\bendobj", data, flags=re.DOTALL):
        objs[int(m.group(1))] = m.group(2)

    chunks = [data]
    for m in re.finditer(rb"(<<(.*?)>>\s*)?stream(?:\r\n|\n)(.*?)(?:\r\n|\n)?endstream", data, flags=re.DOTALL):
        hdr = m.group(2) or b""
        raw = m.group(3)
        dec: bytes | None = None
        for cand in (raw, raw.rstrip(b"\r\n")):
            try:
                dec = zlib.decompress(cand)
                break
            except zlib.error:
                pass
        if dec is None:
            continue
        chunks.append(dec)
        if b"/ObjStm" in hdr:
            n_m = re.search(rb"/N\s+(\d+)", hdr)
            f_m = re.search(rb"/First\s+(\d+)", hdr)
            if n_m and f_m:
                n_obj = int(n_m.group(1))
                first = int(f_m.group(1))
                toks = [int(x) for x in dec[:first].split()]
                if len(toks) >= 2 * n_obj:
                    pairs = [(toks[2 * i], toks[2 * i + 1]) for i in range(n_obj)]
                    for i, (oid, off) in enumerate(pairs):
                        end = first + pairs[i + 1][1] if i + 1 < len(pairs) else len(dec)
                        objs[oid] = dec[first + off : end]

    titles: list[str] = []
    search_bufs = chunks if not objs else [data] + chunks[1:]
    for ch in search_bufs:
        for m in re.finditer(rb"/Title\s*(?:(\d+)\s+\d+\s+R|(?=[(<]))", ch):
            if m.group(1):
                target = objs.get(int(m.group(1)))
                if target is not None:
                    decoded = _decode_pdf_string_token(target, 0)
                    if decoded is not None:
                        titles.append(decoded)
            else:
                decoded = _decode_pdf_string_token(ch, m.end())
                if decoded is not None:
                    titles.append(decoded)
    return titles


def audit_tex_log(log_path: Path, label: str) -> dict:
    assert log_path.exists(), f"Missing log {log_path}"
    txt = log_path.read_text(encoding="utf-8", errors="replace")
    lines = txt.splitlines()
    overfull = [ln for ln in lines if "Overfull \\" in ln]
    missing_ch = [ln for ln in lines if "Missing character:" in ln]
    bad_warn = [
        ln for ln in lines
        if ("LaTeX Warning:" in ln or "Float too large" in ln or "multiply-defined labels" in ln)
        and "bookmark" not in ln.lower()
    ]
    underfull = [ln for ln in lines if "Underfull \\" in ln]
    high_underfull = [ln for ln in underfull if re.search(r"badness\s+([3-9]\d{3}|1\d{4})", ln)]
    assert not overfull, f"{label} has Overfull boxes: {overfull[:5]}"
    assert not missing_ch, f"{label} has Missing characters: {missing_ch[:5]}"
    assert not bad_warn, f"{label} has LaTeX warnings: {bad_warn[:5]}"
    assert not high_underfull, f"{label} has high-badness Underfull boxes: {high_underfull[:5]}"
    assert "There were undefined references" not in txt and "There were undefined citations" not in txt, (
        f"{label} has undefined references or citations"
    )
    return {
        "overfull": 0,
        "missing_chars": 0,
        "warnings": 0,
        "underfull_total": len(underfull),
        "high_badness_underfull": 0,
    }


def audit_blg_log(blg_path: Path, label: str) -> dict:
    assert blg_path.exists(), f"Missing {blg_path}"
    txt = blg_path.read_text(encoding="utf-8", errors="replace")
    bib_warn = [ln for ln in txt.splitlines() if "Warning--" in ln or "I didn't find a database entry" in ln]
    assert not bib_warn, f"{label} has BibTeX warnings: {bib_warn[:5]}"
    return {"bib_warnings": 0}


def audit_pdf_outlines(pdf_path: Path, label: str) -> dict:
    titles = extract_pdf_outline_titles(pdf_path)
    assert len(titles) >= 20, f"Unexpectedly few outline entries in {pdf_path}: {len(titles)}"
    bad_titles = [t for t in titles if "\ufffd" in t or "\\mathbb" in t or "textbackslash" in t]
    assert not bad_titles, f"{label} has malformed PDF outline titles: {bad_titles[:5]}"
    assert any("ℝ × S¹" in t for t in titles), f"{label} missing Unicode cylinder symbol in outlines: {titles}"
    return {"clean_bookmarks": True, "outline_count": len(titles)}


def check_pdf_text(pdf_path: Path) -> dict:
    assert pdf_path.exists(), f"Missing PDF {pdf_path}"
    info = subprocess.run(["pdfinfo", str(pdf_path)], env=ENV, capture_output=True, text=True, check=True).stdout
    txt = subprocess.run(["pdftotext", str(pdf_path), "-"], env=ENV, capture_output=True, text=True, check=True).stdout
    pages_m = re.search(r"Pages:\s+(\d+)", info)
    pages = int(pages_m.group(1)) if pages_m else 0
    assert pages >= 10, f"Unexpectedly few pages in {pdf_path}: {pages}"
    assert "[?]" not in txt and "??" not in txt, f"Unresolved citation/ref glyphs in {pdf_path}"
    assert "[@" not in txt and "Fig.~" not in txt and ";\\" not in txt and "\ufffd" not in txt, (
        f"Unrendered Markdown/TeX artifact or U+FFFD found in {pdf_path}"
    )
    double_hdr = re.findall(r"^(?:0\.\d+[ \t]+\d+|\d+(?:\.\d+)*[ \t]+\d+(?:\.\d+)*\.)", txt, flags=re.MULTILINE)
    assert not double_hdr, f"Double-numbered headings in {pdf_path}: {double_hdr[:5]}"
    for pat in (
        r"\bUEOT\b", r"MurphyHoops", r"P-QMEM", r"C-QMEM", r"P-ROB", r"C-QSEL",
        r"P-MICRO", r"P-FIELD", r"\bPaper 4\b", r"observed\.json", r"NOT_CERTIFIED",
        r"Cram'er", r"Cram’er", r"(?<![0-9.])0\.391(?![0-9])", r"(?<![0-9.])0\.400(?![0-9])",
    ):
        assert not re.search(pat, txt), f"Disallowed token matching '{pat}' leaked into {pdf_path}"
    return {"pages": pages, "chars": len(txt), "clean_glyphs": True, "double_headings": 0}


def check_pra_latex_source_zip_roundtrip() -> dict:
    aps_zip = PRA_DIR / "pra_aps_latex_source.zip"
    with tempfile.TemporaryDirectory(prefix="pra_aps_zip_check_") as tmp:
        tmpdir = Path(tmp)
        with zipfile.ZipFile(aps_zip, "r") as zf:
            zf.extractall(tmpdir)
        for cmd in (
            ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "pra_manuscript.tex"],
            ["bibtex", "pra_manuscript"],
        ):
            proc = subprocess.run(cmd, cwd=tmpdir, env=ENV, capture_output=True, text=True, timeout=180)
            assert proc.returncode == 0, (
                f"APS ZIP round-trip command {cmd} failed ({proc.returncode}):\n"
                + "\n".join((proc.stdout + proc.stderr).splitlines()[-30:])
            )
        for _ in range(4):
            proc = subprocess.run(
                ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "pra_manuscript.tex"],
                cwd=tmpdir, env=ENV, capture_output=True, text=True, timeout=180,
            )
            assert proc.returncode == 0, (
                f"APS ZIP round-trip pdflatex failed ({proc.returncode}):\n"
                + "\n".join((proc.stdout + proc.stderr).splitlines()[-30:])
            )
            cur_log = (tmpdir / "pra_manuscript.log").read_text(encoding="utf-8", errors="replace")
            if "Label(s) may have changed" not in cur_log and "Rerun to get" not in cur_log:
                break
        log_summary = audit_tex_log(tmpdir / "pra_manuscript.log", "pra_pdflatex_zip_roundtrip")
        blg_summary = audit_blg_log(tmpdir / "pra_manuscript.blg", "pra_pdflatex_zip_blg")
        pdf_summary = check_pdf_text(tmpdir / "pra_manuscript.pdf")
        outlines_summary = audit_pdf_outlines(tmpdir / "pra_manuscript.pdf", "pra_pdflatex_zip_outlines")
    return {
        "engine": "pdflatex+bibtex",
        **log_summary,
        **blg_summary,
        "pages": pdf_summary["pages"],
        "chars": pdf_summary["chars"],
        "clean_glyphs": pdf_summary["clean_glyphs"],
        "double_headings": pdf_summary["double_headings"],
        **outlines_summary,
    }


def check_tex_logs_and_outlines() -> dict:
    for stale_out in (ROOT / "build" / "manuscript.out", PRA_DIR / "build" / "pra_manuscript.out"):
        assert not stale_out.exists(), f"Stale bookmark file {stale_out} should be removed on build"
    report: dict[str, dict] = {}
    report["master_log"] = audit_tex_log(ROOT / "build" / "manuscript.log", "master_log")
    report["pra_log"] = audit_tex_log(PRA_DIR / "build" / "pra_manuscript.log", "pra_log")
    report["master_blg"] = audit_blg_log(ROOT / "build" / "manuscript.blg", "master_blg")
    report["pra_blg"] = audit_blg_log(PRA_DIR / "build" / "pra_manuscript.blg", "pra_blg")

    for p in (ROOT / "manuscript.tex", PRA_DIR / "pra_manuscript.tex"):
        assert p.exists(), f"Missing TeX source {p}"
        txt = p.read_text(encoding="utf-8", errors="replace")
        assert "\ufffd" not in txt, f"Replacement character U+FFFD in {p}"

    report["master_pdf_outlines"] = audit_pdf_outlines(ROOT / "manuscript.pdf", "master_pdf_outlines")
    report["pra_pdf_outlines"] = audit_pdf_outlines(PRA_DIR / "pra_manuscript.pdf", "pra_pdf_outlines")
    report["pra_pdflatex_zip_roundtrip"] = check_pra_latex_source_zip_roundtrip()
    return report


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
        "5.394627",
        "0.411787",
        "0.067589",
        "0.033892297103",
        "0.035357047207",
        "0.046090140885",
        "0.047554890989",
        "0.027602916940",
        "0.017009045852",
        "0.017008956708",
        "0.149700906576",
        "0.218613103395",
        "-0.008629740897",
        "0.042360239409",
        "0.077417775085",
        "0.099369592453",
        "0.149700906568",
        "-0.008629740906",
        "0.042360239412",
        "0.956227",
        "0.017010",
        "\\frac{27}{64}",
        "\\frac{343}{512}",
        "0.574747436923",
        "0.492640660220",
        "4/32",
        "0/68",
        "0.605581355419",
        "2.485478",
        "720{,}000",
        "408{,}000",
        "6{,}766.5",
        "10{,}828.8",
    ]
    missing = [lit for lit in required_literals if lit not in md_text]
    assert not missing, f"Missing expected exact figures in manuscript.md: {missing}"
    return {"verified_literals": len(required_literals)}


def run_cli_verifier() -> dict:
    p = subprocess.run(
        [sys.executable, "-B", str(ROOT / "verify_standalone.py")],
        env=ENV, capture_output=True, text=True, check=True,
    )
    res = json.loads(p.stdout)
    assert res.get("status") == "PASS"
    return res


def compute_sha256_manifest() -> list[tuple[str, str]]:
    targets: list[tuple[str, str]] = []
    for p in ROOT.rglob("*"):
        if not p.is_file():
            continue
        rel = p.relative_to(ROOT).as_posix()
        if rel.startswith("build/") or rel.startswith("submissions/pra/build/") or "__pycache__/" in rel:
            continue
        if rel in {"SHA256SUMS", "VALIDATION.json"} or any(part.startswith(".") for part in Path(rel).parts):
            continue
        targets.append((sha(p), rel))
    targets.sort(key=lambda item: item[1])
    return targets


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true", help="Read-only check against existing SHA256SUMS & VALIDATION*.json")
    args = parser.parse_args()

    missing_tools = [t for t in ("pdfinfo", "pdftotext", "pdflatex", "bibtex") if shutil.which(t, path=ENV["PATH"]) is None]
    if missing_tools:
        raise SystemExit(f"Missing required tools in PATH: {missing_tools}")

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
        val_json = json.loads((ROOT / "VALIDATION.json").read_text(encoding="utf-8"))
        pra_val_json = json.loads((PRA_DIR / "VALIDATION_PRA.json").read_text(encoding="utf-8"))
        assert val_json.get("status") == "PASS", "VALIDATION.json status is not PASS"
        assert pra_val_json.get("status") == "PASS", "VALIDATION_PRA.json status is not PASS"
        assert val_json.get("standalone_verifier") == standalone_res, "VALIDATION.json standalone_verifier stale"
        assert pra_val_json.get("standalone_verifier") == standalone_res, "VALIDATION_PRA.json standalone_verifier stale"
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
    print(json.dumps({
        "status": "PASS",
        "bib": bib_res,
        "parity": parity_res,
        "master_pdf": master_pdf,
        "pra_pdf": pra_pdf,
        "pra_pdflatex_zip_roundtrip": log_res["pra_pdflatex_zip_roundtrip"],
    }, indent=2))


if __name__ == "__main__":
    main()
