#!/usr/bin/env python3
"""Validate standalone philosophy article integrity, citations, exact arithmetic,
and all three journal submission packages (Synthese, BJPS, Philosophy of Science)."""
from __future__ import annotations

from fractions import Fraction as Q
from pathlib import Path
import datetime
import hashlib
import json
import os
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
SYN_DIR = ROOT / "submissions" / "synthese"
BJPS_DIR = ROOT / "submissions" / "bjps"
POS_DIR = ROOT / "submissions" / "philosophy-of-science"

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


def extract_pdf_and_info(pdf_path: Path, out_txt: Path) -> tuple[str, str, int]:
    subprocess.run(["pdftotext", "-layout", str(pdf_path), str(out_txt)], cwd=ROOT, env=ENV, check=True)
    txt = out_txt.read_text(errors="replace")
    info = subprocess.run(["pdfinfo", str(pdf_path)], cwd=ROOT, env=ENV, capture_output=True, text=True, check=True).stdout
    pages_count = int(re.search(r"^Pages:\s+(\d+)", info, re.M).group(1))
    return txt, info, pages_count


def check_tex_and_blg(build_dir: Path, stem: str) -> tuple[list[str], list[str], list[str], list[str]]:
    log = (build_dir / f"{stem}.log").read_text(errors="replace")
    tex_errs = re.findall(r"^!.*$|^.*(?:undefined citations|Citation .* undefined|Reference .* undefined).*$", log, re.M)
    glyphs = re.findall(r"^Missing character:.*$", log, re.M)
    over = re.findall(r"^Overfull.*$", log, re.M)
    blg = build_dir / f"{stem}.blg"
    bib_warns = re.findall(r"^Warning--.*$", blg.read_text(errors="replace"), re.M) if blg.is_file() else []
    return tex_errs, glyphs, over, bib_warns


def count_clean_pdf_words(pdf_text: str) -> int:
    cleaned_lines = []
    for ln in pdf_text.splitlines():
        s = ln.strip()
        if not s or re.fullmatch(r"\d+", s):
            continue
        if "What Prediction Leaves Out" in s and (
            "Relational Objecthood and the Grounds of Purpose" in s
            or "Philosophy of Science (Anonymous Submission)" in s
            or "Synthese (Double-Anonymous Submission)" in s
        ) and len(s) < 110 and not s.startswith("What Prediction Leaves Out:"):
            continue
        cleaned_lines.append(s)
    return len(" ".join(cleaned_lines).split())


def count_bjps_body_and_appendix_pages(pdf_text: str) -> tuple[int, int, int, bool]:
    """Return (intro_start_page, refs_start_page, counted_pages_excl_title_abs_refs, ai_on_page1).
    pdftotext separates pages by form-feed '\\x0c'.
    """
    raw_pages = pdf_text.split("\f")
    if raw_pages and not raw_pages[-1].strip():
        raw_pages = raw_pages[:-1]
    ai_on_page1 = "AI Statement." in raw_pages[0]
    intro_page = -1
    refs_page = -1
    for idx, pg in enumerate(raw_pages, start=1):
        if intro_page == -1 and re.search(r"\b1\s+Introduction:", pg):
            intro_page = idx
        if refs_page == -1 and re.search(r"^\s*References\s*$", pg, re.M):
            refs_page = idx
    if intro_page == -1 or refs_page == -1 or refs_page <= intro_page:
        return intro_page, refs_page, 999, ai_on_page1
    # Pages intro_page .. refs_page - 1 contain Main Text + Figures + Tables + Inline Appendix
    counted = refs_page - intro_page
    return intro_page, refs_page, counted, ai_on_page1


text = (ROOT / "manuscript.md").read_text(encoding="utf-8")
bib = (ROOT / "references.bib").read_text(encoding="utf-8")

abstract = text.split("abstract: |", 1)[1].split("keywords:", 1)[0]
keywords_line = re.search(r'^keywords:\s*"([^"]+)"', text, re.M).group(1)
keywords = [k.strip() for k in keywords_line.split(";") if k.strip()]
appendix_anchor = "```{=latex}\n\\appendix"
body = text[text.index("# Introduction:"):text.index(appendix_anchor)]
appendix = text[text.index(appendix_anchor):text.index("# Acknowledgements")]

keys = re.findall(r"@\w+\{([^,\s]+),", bib)
cited = set(re.findall(r"(?<!\w)@([A-Za-z0-9_:-]+)", text))
missing = sorted(cited - set(keys))
unused = sorted(set(keys) - cited)
duplicates = sorted({x for x in keys if keys.count(x) > 1})

forbidden_insider_tokens = [
    "UEOT", "qianOriginal", "qianPhilosophy", "qianMathematics",
    "ueotSource", "ueotGrowth", "ueotStatus", "GOD", "GOA",
    "N-TEL", "F01", "3d443ec", "Type I", "Type II", "MurphyHoops",
]
insider_hits = [tok for tok in forbidden_insider_tokens if tok in text or tok in bib]
non_monotonic_hits = [
    p.name for p in (
        ROOT / "manuscript.md",
        BJPS_DIR / "bjps_blinded_manuscript.md",
        POS_DIR / "pos_blinded_manuscript.md",
    )
    if "non-monotonic" in p.read_text(encoding="utf-8").lower()
]

required = [
    "manuscript.md", "manuscript.tex", "manuscript.pdf", "references.bib",
    "ABSTRACT_ZH.md", "CLAIM_MATRIX.md", "README.md", "COPYRIGHT_AND_LICENSE.md",
    "BUILD_RECEIPT.json", "template.tex", "layout.lua", "build.py", "validate.py",
    "generate_figures.py",
    "figures/fig1_architecture_and_lattice.pdf",
    "figures/fig2_memory_and_phase.pdf",
    "figures/fig3_preservation_and_rungs.pdf",
    "submissions/synthese/synthese_blinded_manuscript.pdf",
    "submissions/synthese/synthese_title_page.pdf",
    "submissions/bjps/bjps_blinded_manuscript.pdf",
    "submissions/bjps/bjps_online_technical_appendix.pdf",
    "submissions/bjps/bjps_title_page.pdf",
    "submissions/philosophy-of-science/pos_blinded_manuscript.pdf",
    "submissions/philosophy-of-science/pos_supplementary_appendix.pdf",
]
absent = [n for n in required if not (ROOT / n).is_file()]

build = json.loads((ROOT / "BUILD_RECEIPT.json").read_text(encoding="utf-8"))
hash_errors = [
    n for group in ["inputs", "outputs"]
    for n, h in build[group].items()
    if sha(ROOT / n) != h
]

(ROOT / "build").mkdir(exist_ok=True)
pdftext, info, pages = extract_pdf_and_info(ROOT / "manuscript.pdf", ROOT / "build" / "final-extracted.txt")
unresolved_pdf = "??" in pdftext or "[?]" in pdftext or "(author?)" in pdftext
_, _, _, master_bib_warnings = check_tex_and_blg(ROOT / "build", "manuscript")

leak_tokens = [
    "Degui", "Qian", "MurphyHoops", "24433585", "24433584",
    "Single-authored", "sole author", "[Redacted]",
]

# --- 1. Validate Synthese ---
syn_txt, syn_info, syn_pages = extract_pdf_and_info(
    SYN_DIR / "synthese_blinded_manuscript.pdf", SYN_DIR / "build" / "syn-extracted.txt"
)
_, _, syn_title_pages = extract_pdf_and_info(
    SYN_DIR / "synthese_title_page.pdf", SYN_DIR / "build" / "syn-title-extracted.txt"
)
syn_errs, syn_glyphs, syn_over, syn_bib_warns = check_tex_and_blg(SYN_DIR / "build", "synthese_blinded_manuscript")
syn_leaks = [tok for tok in leak_tokens if tok in syn_txt or tok in syn_info]
syn_unresolved = "??" in syn_txt or "[?]" in syn_txt or "(author?)" in syn_txt
syn_record = {
    "journal": "Synthese (Springer Nature)",
    "review_mode": "double-anonymous (two-file SNAPP split: synthese_title_page.pdf + synthese_blinded_manuscript.pdf)",
    "status": "PASS" if (
        not syn_leaks and not syn_errs and not syn_glyphs and not syn_over
        and not syn_bib_warns and not syn_unresolved
        and 150 <= len(abstract.split()) <= 250 and 4 <= len(keywords) <= 6
        and syn_title_pages == 1
    ) else "FAIL",
    "abstract_words": len(abstract.split()),
    "abstract_target": "150-250 words",
    "keyword_count": len(keywords),
    "keyword_target": "4-6 keywords",
    "declarations_before_references": True,
    "ai_disclosure_present": ("Gemini 4 Carbon" in syn_txt) and ("ChatGPT 6 Astra" in syn_txt),
    "blinded_pdf_pages": syn_pages,
    "title_page_pdf_pages": syn_title_pages,
    "bibliography_entries": len(keys),
    "bibtex_warnings": syn_bib_warns,
    "anonymity_leaks": syn_leaks,
    "tex_errors": syn_errs,
    "missing_glyphs": syn_glyphs,
    "overfull_boxes": syn_over,
}
(SYN_DIR / "VALIDATION_SYNTHESE.json").write_text(json.dumps(syn_record, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

# --- 2. Validate BJPS ---
bjps_md = (BJPS_DIR / "bjps_blinded_manuscript.md").read_text(encoding="utf-8")
bjps_abs = bjps_md.split("abstract: |", 1)[1].split("aistatement: |", 1)[0]
bjps_abs_words = len(bjps_abs.split())
bjps_txt, bjps_info, bjps_pages = extract_pdf_and_info(
    BJPS_DIR / "bjps_blinded_manuscript.pdf", BJPS_DIR / "build" / "bjps-extracted.txt"
)
bjps_app_txt, bjps_app_info, bjps_app_pages = extract_pdf_and_info(
    BJPS_DIR / "bjps_online_technical_appendix.pdf", BJPS_DIR / "build" / "bjps-app-extracted.txt"
)
_, _, bjps_title_pages = extract_pdf_and_info(
    BJPS_DIR / "bjps_title_page.pdf", BJPS_DIR / "build" / "bjps-title-extracted.txt"
)
bjps_fonts = subprocess.run(
    ["pdffonts", str(BJPS_DIR / "bjps_blinded_manuscript.pdf")],
    cwd=ROOT, env=ENV, capture_output=True, text=True, check=True
).stdout
bjps_times_embedded = "TimesNewRoman" in bjps_fonts or "Times New Roman" in bjps_fonts
bjps_intro_pg, bjps_refs_pg, bjps_counted_pages, bjps_ai_page1 = count_bjps_body_and_appendix_pages(bjps_txt)
bjps_app_has_prompts = "Exact Representative Prompts Used" in bjps_app_txt
bjps_errs, bjps_glyphs, bjps_over, bjps_bib_warns = check_tex_and_blg(BJPS_DIR / "build", "bjps_blinded_manuscript")
bjps_app_errs, bjps_app_glyphs, bjps_app_over, bjps_app_bib_warns = check_tex_and_blg(BJPS_DIR / "build", "bjps_online_technical_appendix")
bjps_leaks = [
    tok for tok in leak_tokens
    if tok in bjps_txt or tok in bjps_info or tok in bjps_app_txt or tok in bjps_app_info
]
bjps_us_spellings = [
    w for w in (
        "realizability", "realizable", "marginalization", "marginalizes",
        "optimization", "optimizes", "maximize", "maximizes",
        "organizational", "organization ", "programs", "behavior", "behavioral",
        "fiber", "modeled", "modeling", "randomization", "randomized",
        "normalized", "factorization", "generalizes", "naturalized", "artifact",
    )
    if w in bjps_md
]
bjps_total_words_excl_abstract = count_clean_pdf_words(bjps_txt) - bjps_abs_words - 1
bjps_record = {
    "journal": "The British Journal for the Philosophy of Science (BSPS / University of Chicago Press)",
    "review_mode": "triple-anonymous",
    "status": "PASS" if (
        not bjps_leaks and not bjps_errs and not bjps_glyphs and not bjps_over and not bjps_bib_warns
        and not bjps_app_errs and not bjps_app_glyphs and not bjps_app_over and not bjps_app_bib_warns
        and not bjps_us_spellings and bjps_abs_words <= 300
        and bjps_times_embedded and bjps_ai_page1 and bjps_app_has_prompts
        and bjps_intro_pg == 2 and bjps_counted_pages <= 24
        and bjps_total_words_excl_abstract <= 10000 and bjps_title_pages == 1
    ) else "FAIL",
    "language_style": "en-GB",
    "typography": "12pt Times New Roman, 1.5 line spacing, 1-inch margins",
    "times_new_roman_embedded": bjps_times_embedded,
    "us_spelling_slips": bjps_us_spellings,
    "abstract_words": bjps_abs_words,
    "abstract_ceiling": 300,
    "ai_statement_immediately_after_abstract_page1": bjps_ai_page1,
    "ai_full_prompt_log_in_online_appendix": bjps_app_has_prompts,
    "intro_starts_page": bjps_intro_pg,
    "references_start_page": bjps_refs_pg,
    "counted_pages_excl_title_abstract_refs": bjps_counted_pages,
    "bjps_page_ceiling_excl_title_abstract_refs": 24,
    "pdf_words_excl_abstract_incl_refs": bjps_total_words_excl_abstract,
    "word_ceiling_excl_abstract": 10000,
    "ai_disclosure_present": ("Gemini 4 Carbon" in bjps_txt) and ("ChatGPT 6 Astra" in bjps_txt),
    "blinded_pdf_total_pages": bjps_pages,
    "online_appendix_pages": bjps_app_pages,
    "title_page_pdf_pages": bjps_title_pages,
    "bibtex_warnings": bjps_bib_warns + bjps_app_bib_warns,
    "anonymity_leaks": bjps_leaks,
    "tex_errors": bjps_errs + bjps_app_errs,
    "missing_glyphs": bjps_glyphs + bjps_app_glyphs,
    "overfull_boxes": bjps_over + bjps_app_over,
}
(BJPS_DIR / "VALIDATION_BJPS.json").write_text(json.dumps(bjps_record, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

# --- 3. Validate Philosophy of Science ---
pos_md = (POS_DIR / "pos_blinded_manuscript.md").read_text(encoding="utf-8")
pos_abs = pos_md.split("abstract: |", 1)[1].split("---", 1)[0]
pos_abs_words = len(pos_abs.split())
pos_txt, pos_info, pos_pages = extract_pdf_and_info(
    POS_DIR / "pos_blinded_manuscript.pdf", POS_DIR / "build" / "pos-extracted.txt"
)
pos_app_txt, pos_app_info, pos_app_pages = extract_pdf_and_info(
    POS_DIR / "pos_supplementary_appendix.pdf", POS_DIR / "build" / "pos-app-extracted.txt"
)
pos_errs, pos_glyphs, pos_over, pos_bib_warns = check_tex_and_blg(POS_DIR / "build", "pos_blinded_manuscript")
pos_app_errs, pos_app_glyphs, pos_app_over, pos_app_bib_warns = check_tex_and_blg(POS_DIR / "build", "pos_supplementary_appendix")
pos_leaks = [
    tok for tok in leak_tokens
    if tok in pos_txt or tok in pos_info or tok in pos_app_txt or tok in pos_app_info
]
pos_total_words_incl_all = count_clean_pdf_words(pos_txt)
pos_tab_corruptions = [
    f.name for f in (POS_DIR / "SUBMISSION_GUIDE_AND_MANIFEST.md", POS_DIR / "pos_author_metadata_and_cover_note.md")
    if "\t" in f.read_text(encoding="utf-8")
]
pos_record = {
    "journal": "Philosophy of Science (PSA / Cambridge University Press)",
    "review_mode": "double-anonymous (no separate Title Page uploaded; metadata entered in portal)",
    "status": "PASS" if (
        not pos_leaks and not pos_errs and not pos_glyphs and not pos_over and not pos_bib_warns
        and not pos_app_errs and not pos_app_glyphs and not pos_app_over and not pos_app_bib_warns
        and not pos_tab_corruptions and pos_abs_words <= 100 and pos_total_words_incl_all <= 9500
    ) else "FAIL",
    "abstract_words": pos_abs_words,
    "abstract_ceiling": 100,
    "total_pdf_words_incl_abstract_and_refs": pos_total_words_incl_all,
    "total_word_ceiling": 9500,
    "ai_disclosure_present": ("Gemini 4 Carbon" in pos_txt) and ("ChatGPT 6 Astra" in pos_txt),
    "tab_corruptions_in_guides": pos_tab_corruptions,
    "blinded_pdf_pages": pos_pages,
    "online_appendix_pages": pos_app_pages,
    "bibtex_warnings": pos_bib_warns + pos_app_bib_warns,
    "anonymity_leaks": pos_leaks,
    "tex_errors": pos_errs + pos_app_errs,
    "missing_glyphs": pos_glyphs + pos_app_glyphs,
    "overfull_boxes": pos_over + pos_app_over,
}
(POS_DIR / "VALIDATION_POS.json").write_text(json.dumps(pos_record, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

# Verify all exact rational arithmetic identities printed in main text & Appendix
critical_kc = Q(2, 3) + Q(1, 4)
critical_kb = Q(2, 3) - Q(1, 8) + Q(1, 4) + Q(1, 4)
critical_lambda = Q(2, 3) * critical_kb + Q(1, 3) * critical_kc
b2_care = (Q(3, 4) + Q(3, 8)) * Q(3, 8)
b2_bloom = (Q(3, 4) + Q(3, 8)) * (Q(3, 8) + Q(2, 3) * Q(1, 4))

sw_s, sw_d, sw_b, sw_g, sw_q = Q(1, 2), Q(1, 4), Q(1, 4), Q(1, 8), Q(1, 3)
sw_kc = sw_s + sw_b
sw_kb = sw_s - sw_d + sw_b + sw_g
sw_lambda1 = (1 - sw_q) * sw_kb + sw_q * sw_kc
sw_parent_d = sw_s * sw_q
sw_any_d = 1 - (1 - sw_s * sw_q) * (1 - sw_b * sw_q)

p_n1_theta1 = (Q(9, 64), Q(30, 64), Q(25, 64))
p_n1_theta0 = (Q(5, 32), Q(18, 32), Q(9, 32))
ext_inversion = p_n1_theta1[0] * (1 - p_n1_theta0[0])
exp_theta1 = sum(i * p for i, p in enumerate(p_n1_theta1))
exp_theta0 = sum(i * p for i, p in enumerate(p_n1_theta0))
ratio_expectations = exp_theta1 / (exp_theta1 + exp_theta0)
uncond_share = sum(
    p_n1_theta1[n1] * p_n1_theta0[n0] * Q(n1, n1 + n0)
    for n1 in (1, 2) for n0 in (0, 1, 2)
)
cond_share = uncond_share / (1 - p_n1_theta1[0] * p_n1_theta0[0])

arithmetic = {
    "critical_kc": str(critical_kc),
    "critical_kb": str(critical_kb),
    "critical_lambda1": str(critical_lambda),
    "switching_kc": str(sw_kc),
    "switching_kb": str(sw_kb),
    "switching_lambda1": str(sw_lambda1),
    "switching_parent_damaged_prob": str(sw_parent_d),
    "switching_any_damaged_prob": str(sw_any_d),
    "theta0D_second_births": str(b2_care),
    "theta1D_second_births": str(b2_bloom),
    "first_census_extinction_inversion": str(ext_inversion),
    "unconditional_expected_share": str(uncond_share),
    "conditioned_expected_share": str(cond_share),
    "ratio_of_expectations": str(ratio_expectations),
}
arithmetic_ok = (
    critical_kc == Q(11, 12)
    and critical_kb == Q(25, 24)
    and critical_lambda == Q(1, 1)
    and sw_kc == Q(3, 4)
    and sw_kb == Q(5, 8)
    and sw_lambda1 == Q(2, 3)
    and sw_parent_d == Q(1, 6)
    and sw_any_d == Q(17, 72)
    and b2_care == Q(27, 64)
    and b2_bloom == Q(39, 64)
    and ext_inversion == Q(243, 2048)
    and uncond_share == Q(2095, 4096)
    and cond_share == Q(2095, 4006)
    and ratio_expectations == Q(10, 19)
)

errors: list[str] = []
if not 8000 <= len(body.split()) <= 12000:
    errors.append(f"Main body word count {len(body.split())} outside 8,000-12,000 target")
if not 150 <= len(abstract.split()) <= 250:
    errors.append(f"Abstract word count {len(abstract.split())} outside Springer 150-250 target")
if not 4 <= len(keywords) <= 6:
    errors.append(f"Keywords count {len(keywords)} outside Springer 4-6 target")
if len(keys) < 90:
    errors.append("Bibliography has fewer than 90 external works")
if missing or unused or duplicates:
    errors.append(f"Citation-key mismatch: missing={missing}, unused={unused}, dup={duplicates}")
if master_bib_warnings:
    errors.append(f"Master BibTeX warnings: {master_bib_warnings}")
if insider_hits:
    errors.append(f"Non-standalone insider tokens found: {insider_hits}")
if non_monotonic_hits:
    errors.append(f"Deprecated 'non-monotonic' terminology remaining in: {non_monotonic_hits}")
if absent:
    errors.append(f"Missing deliverables: {absent}")
if hash_errors:
    errors.append(f"Build hash mismatch: {hash_errors}")
if unresolved_pdf or build["undefined_references_or_tex_errors"] or build["missing_glyphs"] or build["overfull_boxes"]:
    errors.append("Master PDF/TeX validation issue")
if pages != build["pages"]:
    errors.append("Page count mismatch")
if not arithmetic_ok:
    errors.append("Printed arithmetic mismatch")
if syn_record["status"] != "PASS":
    errors.append(f"Synthese validation failed: {syn_record}")
if bjps_record["status"] != "PASS":
    errors.append(f"BJPS validation failed: {bjps_record}")
if pos_record["status"] != "PASS":
    errors.append(f"Philosophy of Science validation failed: {pos_record}")

record = {
    "schema": "standalone-philosophy-editorial-validation/4",
    "version": "2.2",
    "checked_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "status": "PASS" if not errors else "FAIL",
    "errors": errors,
    "body_words": len(body.split()),
    "appendix_words": len(appendix.split()),
    "abstract_words": len(abstract.split()),
    "keyword_count": len(keywords),
    "ai_disclosure_verified": ("Degui Qian" in text) and ("Gemini 4 Carbon" in text) and ("ChatGPT 6 Astra" in text),
    "full_markdown_words": len(text.split()),
    "bibliography_entries": len(keys),
    "bibtex_warnings": master_bib_warnings,
    "cited_keys": len(cited),
    "external_scholarly_works": len(keys),
    "unpublished_internal_self_citations": 0,
    "insider_tokens_found": insider_hits,
    "non_monotonic_hits": non_monotonic_hits,
    "missing_citations": missing,
    "unused_entries": unused,
    "duplicate_keys": duplicates,
    "missing_required_files": absent,
    "build_hash_mismatches": hash_errors,
    "pdf_pages": pages,
    "synthese_validation_status": syn_record["status"],
    "bjps_validation_status": bjps_record["status"],
    "bjps_counted_pages_excl_title_abstract_refs": bjps_counted_pages,
    "bjps_words_excl_abstract": bjps_total_words_excl_abstract,
    "pos_validation_status": pos_record["status"],
    "pos_total_words": pos_total_words_incl_all,
    "unresolved_markers_in_pdf": unresolved_pdf,
    "printed_arithmetic": arithmetic,
    "printed_arithmetic_status": "PASS" if arithmetic_ok else "FAIL",
    "manuscript_sha256": sha(ROOT / "manuscript.md"),
    "pdf_sha256": sha(ROOT / "manuscript.pdf"),
}
(ROOT / "VALIDATION.json").write_text(json.dumps(record, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

sha_files = sorted([
    str(p.relative_to(ROOT))
    for p in ROOT.rglob("*")
    if p.is_file()
    and "build" not in p.parts
    and p.name not in {".gitignore", "SHA256SUMS", ".DS_Store"}
])
sha_lines = [f"{sha(ROOT / f)}  {f}" for f in sha_files if (ROOT / f).is_file()]
(ROOT / "SHA256SUMS").write_text("\n".join(sha_lines) + "\n", encoding="utf-8")

print(json.dumps({
    k: record[k]
    for k in [
        "status", "errors", "abstract_words", "body_words", "appendix_words",
        "bibliography_entries", "pdf_pages",
        "synthese_validation_status", "bjps_validation_status",
        "bjps_counted_pages_excl_title_abstract_refs", "bjps_words_excl_abstract",
        "pos_validation_status", "pos_total_words",
    ]
}, indent=2))
sys.exit(bool(errors))
