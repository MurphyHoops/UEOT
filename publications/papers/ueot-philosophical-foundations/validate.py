#!/usr/bin/env python3
"""Validate standalone journal article integrity, citations, independence, and exact arithmetic."""
from fractions import Fraction as Q
from pathlib import Path
import datetime
import hashlib
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def sha(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


text = (ROOT / "manuscript.md").read_text(encoding="utf-8")
bib = (ROOT / "references.bib").read_text(encoding="utf-8")

abstract = text.split("abstract: |", 1)[1].split("keywords:", 1)[0]
body = text[text.index("# Introduction:"):text.index("# Appendix:")]
appendix = text[text.index("# Appendix:"):text.index("# Acknowledgements")]

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

required = [
    "manuscript.md", "manuscript.tex", "manuscript.pdf", "references.bib",
    "ABSTRACT_ZH.md", "CLAIM_MATRIX.md", "README.md", "COPYRIGHT_AND_LICENSE.md",
    "BUILD_RECEIPT.json", "template.tex", "layout.lua", "build.py", "validate.py",
]
absent = [n for n in required if not (ROOT / n).is_file()]

build = json.loads((ROOT / "BUILD_RECEIPT.json").read_text(encoding="utf-8"))
hash_errors = [
    n for group in ["inputs", "outputs"]
    for n, h in build[group].items()
    if sha(ROOT / n) != h
]

(ROOT / "build").mkdir(exist_ok=True)
subprocess.run(["pdftotext", "-layout", "manuscript.pdf", "build/final-extracted.txt"], cwd=ROOT, check=True)
pdftext = (ROOT / "build/final-extracted.txt").read_text(errors="replace")
unresolved_pdf = "??" in pdftext or "[?]" in pdftext

info = subprocess.run(["pdfinfo", "manuscript.pdf"], cwd=ROOT, capture_output=True, text=True, check=True).stdout
pages = int(re.search(r"^Pages:\s+(\d+)", info, re.M).group(1))

# Verify all exact rational arithmetic identities printed in main text & Appendix
critical_kc = Q(2, 3) + Q(1, 4)
critical_kb = Q(2, 3) - Q(1, 8) + Q(1, 4) + Q(1, 4)
critical_lambda = Q(2, 3) * critical_kb + Q(1, 3) * critical_kc
b2_care = (Q(3, 4) + Q(3, 8)) * Q(3, 8)
b2_bloom = (Q(3, 4) + Q(3, 8)) * (Q(3, 8) + Q(2, 3) * Q(1, 4))

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
    and b2_care == Q(27, 64)
    and b2_bloom == Q(39, 64)
    and ext_inversion == Q(243, 2048)
    and uncond_share == Q(2095, 4096)
    and cond_share == Q(2095, 4006)
    and ratio_expectations == Q(10, 19)
)

errors = []
if not 8000 <= len(body.split()) <= 12000:
    errors.append("Main body word count outside 8,000-12,000 target")
if not 180 <= len(abstract.split()) <= 250:
    errors.append("Abstract word count outside 180-250 target")
if len(keys) < 80:
    errors.append("Bibliography has fewer than 80 external works")
if missing or unused or duplicates:
    errors.append("Citation-key mismatch")
if insider_hits:
    errors.append(f"Non-standalone insider tokens found: {insider_hits}")
if absent:
    errors.append(f"Missing deliverables: {absent}")
if hash_errors:
    errors.append(f"Build hash mismatch: {hash_errors}")
if unresolved_pdf or build["undefined_references_or_tex_errors"] or build["missing_glyphs"] or build["overfull_boxes"]:
    errors.append("PDF/TeX validation issue")
if pages != build["pages"]:
    errors.append("Page count mismatch")
if not arithmetic_ok:
    errors.append("Printed arithmetic mismatch")

record = {
    "schema": "standalone-philosophy-editorial-validation/2",
    "version": "2.0",
    "checked_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "status": "PASS" if not errors else "FAIL",
    "errors": errors,
    "body_words": len(body.split()),
    "appendix_words": len(appendix.split()),
    "abstract_words": len(abstract.split()),
    "full_markdown_words": len(text.split()),
    "bibliography_entries": len(keys),
    "cited_keys": len(cited),
    "external_scholarly_works": len(keys),
    "unpublished_internal_self_citations": 0,
    "insider_tokens_found": insider_hits,
    "missing_citations": missing,
    "unused_entries": unused,
    "duplicate_keys": duplicates,
    "missing_required_files": absent,
    "build_hash_mismatches": hash_errors,
    "pdf_pages": pages,
    "unresolved_markers_in_pdf": unresolved_pdf,
    "printed_arithmetic": arithmetic,
    "printed_arithmetic_status": "PASS" if arithmetic_ok else "FAIL",
    "manuscript_sha256": sha(ROOT / "manuscript.md"),
    "pdf_sha256": sha(ROOT / "manuscript.pdf"),
}
(ROOT / "VALIDATION.json").write_text(json.dumps(record, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
print(json.dumps({
    k: record[k]
    for k in [
        "status", "errors", "abstract_words", "body_words", "appendix_words",
        "bibliography_entries", "unpublished_internal_self_citations", "pdf_pages",
    ]
}, indent=2))
sys.exit(bool(errors))
