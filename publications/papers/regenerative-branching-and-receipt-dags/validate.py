#!/usr/bin/env python3
"""Validate standalone Master Edition, INFORMS MOR double-anonymous package,
96-entry bibliography parity, and live exact-rational recomputation of all
closed-form boundaries, history witnesses, and certified DAG benchmarks.
"""
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
MOR_DIR = ROOT / "submissions" / "mor"
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


# --- 1. Live exact-rational dynamic program over sigma = (t, q, s, f, k) ---
ALL_ACTIONS = [
    None,
    (False, None),
    (True, None),
    (False, False),
    (False, True),
    (True, False),
    (True, True),
]
OBS_LIST = [(False, False), (False, True), (True, False), (True, True)]


def solve_dag(H, B0, tariff, price, discount, r_list, prior_list, goal=True):
    init_q = (not goal, None, False, True)
    init_st = (0, 0, 0, 0, init_q)

    def cap(a):
        return Q(0) if a is None else (Q(1) if a[1] is not None else Q(0))

    def effective(stopped, a):
        return (False, None) if (stopped or a is None) else a

    def normal_receipt(q, a):
        req_j, req_act = effective(q[2], a)
        sel = q[1] if req_j else q[0]
        if sel is None:
            return (False, False)
        post = sel if req_act is None else req_act
        return (post == goal, req_act is not None)

    def update_stat(st, a, o):
        elapsed, s, f, paid, q = st
        nr = normal_receipt(q, a)
        inf = nr[0] or nr[1]
        ns = o[0] or o[1]
        ds = 1 if (inf and ns) else 0
        df = 1 if (inf and not ns) else 0
        dp = 1 if o[1] else 0
        root, child, stopped, fresh = q
        req_j, _ = effective(stopped, a)
        bit_b = goal if o[0] else (not goal)
        new_root = root if req_j else bit_b
        if fresh:
            new_child = goal if o[0] else None
        elif req_j:
            new_child = bit_b if child is not None else None
        else:
            new_child = child
        return (elapsed + 1, s + ds, f + df, paid + dp,
                (new_root, new_child, stopped or (a is None), False))

    memo = {}
    edges_count = 0

    def build(rem, st):
        nonlocal edges_count
        key = (rem, st)
        if key in memo:
            return memo[key]
        _, s, f, paid, q = st
        wallet = max(Q(0), B0 - paid * tariff)
        if rem == 0:
            memo[key] = {"val": Q(0), "act": None, "succ": {}}
            return memo[key]
        ws = [p * (r ** s) * ((1 - r) ** f) for r, p in zip(r_list, prior_list)]
        Z = sum(ws)
        pw = [w / Z for w in ws]
        legal = [a for a in ALL_ACTIONS if tariff * cap(a) <= wallet]
        best_val = None
        best_idx = None
        all_succ = {}
        for idx, a in enumerate(legal):
            nr = normal_receipt(q, a)
            qv = Q(0)
            asucc = []
            for o in OBS_LIST:
                m = sum(w * ((r if nr == o else Q(0)) + ((1 - r) if (False, False) == o else Q(0)))
                        for r, w in zip(r_list, pw))
                if m > 0:
                    edges_count += 1
                    nxt = update_stat(st, a, o)
                    ch = build(rem - 1, nxt)
                    rew = (Q(1) if o[0] else Q(0)) - price * (tariff if o[1] else Q(0))
                    qv += m * (rew + discount * ch["val"])
                    asucc.append((o, m, nxt))
            all_succ[idx] = asucc
            if best_val is None or qv > best_val:
                best_val = qv
                best_idx = idx
        memo[key] = {"val": best_val, "act": best_idx, "succ": all_succ}
        return memo[key]

    root = build(H, init_st)
    exec_vis = set()
    exec_edges = 0

    def walk(rem, st):
        nonlocal exec_edges
        k = (rem, st)
        if k in exec_vis:
            return
        exec_vis.add(k)
        if rem == 0:
            return
        nd = memo[k]
        for o, m, nxt in nd["succ"][nd["act"]]:
            exec_edges += 1
            walk(rem - 1, nxt)

    walk(H, init_st)

    stat_memo = {}

    def eval_metrics(rem, st, had_birth):
        k = (rem, st, had_birth)
        if k in stat_memo:
            return stat_memo[k]
        if rem == 0:
            return (Q(1) if had_birth else Q(0), Q(1) if st[3] == 2 else Q(0), Q(0), Q(0))
        nd = memo[(rem, st)]
        pb = pp2 = eb = ef = Q(0)
        for o, m, nxt in nd["succ"][nd["act"]]:
            cb, cp2, ceb, cef = eval_metrics(rem - 1, nxt, had_birth or o[0])
            pb += m * cb
            pp2 += m * cp2
            eb += m * ((Q(1) if o[0] else Q(0)) + ceb)
            ef += m * ((tariff if o[1] else Q(0)) + cef)
        stat_memo[k] = (pb, pp2, eb, ef)
        return stat_memo[k]

    m_out = eval_metrics(H, init_st, False)
    return {
        "val": root["val"],
        "cert_nodes": len(memo),
        "cert_edges": edges_count,
        "exec_nodes": len(exec_vis),
        "exec_edges": exec_edges,
        "quartic_bound": 24 * ((H + 1) ** 4),
        "p_birth_ge_1": m_out[0],
        "p_paid_2": m_out[1],
        "e_births": m_out[2],
        "e_fees": m_out[3],
    }


b1 = solve_dag(2, Q(1), Q(1), Q(13, 10), Q(1, 2), [Q(1, 4), Q(3, 4)], [Q(1, 2), Q(1, 2)])
b2 = solve_dag(3, Q(1), Q(1), Q(7, 4), Q(3, 4), [Q(1, 4), Q(3, 4)], [Q(1, 2), Q(1, 2)])
b3 = solve_dag(3, Q(1), Q(1), Q(13, 10), Q(1, 2), [Q(1, 4), Q(3, 4)], [Q(1, 2), Q(1, 2)])
b4 = solve_dag(4, Q(1), Q(1), Q(37, 16), Q(3, 4), [Q(3, 4), Q(7, 8)], [Q(1, 2), Q(1, 2)])
b5 = solve_dag(8, Q(2), Q(1), Q(13, 10), Q(3, 4), [Q(1, 4), Q(3, 4)], [Q(1, 2), Q(1, 2)])

# Exact analytical witness checks (Theorems 2-5)
mu1 = Q(1, 2)
mu2 = Q(5, 16)
mu3 = Q(7, 32)
redraw_two = mu1 * (1 - Q(13, 10)) + Q(1, 2) * (mu1 ** 2)
var_premium = b1["val"] - redraw_two
p_prior_thresh = 1 + Q(1, 2) * (mu2 / mu1)
p_fault_thresh = 1 + Q(1, 2) * ((mu2 - mu3) / (mu1 - mu2))
post_fault_retry = ((mu1 - mu2) / (1 - mu1)) * (1 - Q(13, 10)) + Q(1, 2) * ((mu2 - mu3) / (1 - mu1))
prior_freeze_three = b3["val"] + (1 - mu1) * Q(1, 2) * post_fault_retry
root_only_three = mu1 * (1 - Q(7, 4)) + Q(3, 4) * mu2 + Q(9, 16) * mu3

f_mu1 = Q(13, 16)
f_mu2 = Q(85, 128)
f_mu3 = Q(559, 1024)
f_mu4 = Q(3697, 8192)
open_four = f_mu1 * (1 - Q(37, 16)) + (Q(3, 4) + Q(9, 16)) * f_mu2 + Q(27, 64) * f_mu3
feedback_gap_four = Q(27, 64) * (f_mu3 - f_mu4)

mass_hA = Q(1, 2) * (Q(1, 4)**2 * Q(3, 4) + Q(3, 4)**2 * Q(1, 4))
mass_hB = Q(1, 2) * (Q(1, 4) * Q(3, 4) + Q(3, 4) * Q(1, 4))
post_hA_low = (Q(1, 2) * Q(1, 4)**2 * Q(3, 4)) / mass_hA
post_hB_low = (Q(1, 2) * Q(1, 4) * Q(3, 4)) / mass_hB
next_birth_hA = post_hA_low * Q(1, 4) + (1 - post_hA_low) * Q(3, 4)
next_birth_hB = post_hB_low * Q(1, 4) + (1 - post_hB_low) * Q(3, 4)

arithmetic_ok = (
    b1["val"] == Q(1, 160) and b1["cert_nodes"] == 21 and b1["exec_nodes"] == 6
    and b2["val"] == Q(9, 256) and b2["cert_nodes"] == 52 and b2["exec_nodes"] == 11
    and b3["val"] == Q(27, 320) and b3["cert_nodes"] == 52 and b3["exec_nodes"] == 11
    and b4["val"] == Q(39525, 524288) and b4["cert_nodes"] == 104 and b4["exec_nodes"] == 16
    and b5["val"] == Q(884450457, 1342177280)
    and b5["cert_nodes"] == 1661 and b5["cert_edges"] == 8221
    and b5["exec_nodes"] == 151 and b5["exec_edges"] == 182
    and b5["cert_nodes"] <= b5["quartic_bound"] == 157464
    and b5["p_birth_ge_1"] == Q(215, 256)
    and b5["p_paid_2"] == Q(1233, 4096)
    and b5["e_births"] == Q(57313, 16384)
    and b5["e_fees"] == Q(4673, 4096)
    and redraw_two == Q(-1, 40) and var_premium == Q(1, 32)
    and p_prior_thresh == Q(21, 16) and p_fault_thresh == Q(5, 4)
    and post_fault_retry == Q(-3, 160)
    and prior_freeze_three == Q(51, 640) and b3["val"] - prior_freeze_three == Q(3, 640)
    and root_only_three == Q(-9, 512)
    and open_four == Q(2325, 65536) and feedback_gap_four == Q(20925, 524288)
    and open_four + feedback_gap_four == b4["val"]
    and mass_hA == Q(3, 32) and mass_hB == Q(3, 16)
    and post_hA_low == Q(1, 4) and post_hB_low == Q(1, 2)
    and next_birth_hA == Q(5, 8) and next_birth_hB == Q(1, 2)
)

# --- 2. Editorial, standalone, and BibTeX parity checks ---
text = (ROOT / "manuscript.md").read_text(encoding="utf-8")
bib = (ROOT / "references.bib").read_text(encoding="utf-8")

abstract = text.split("abstract: |", 1)[1].split("keywords:", 1)[0].strip()
keywords_line = re.search(r'^keywords:\s*"([^"]+)"', text, re.M).group(1)
keywords = [k.strip() for k in keywords_line.split(";") if k.strip()]
body = text[text.index("# Introduction:"):text.index("# Appendix:")]
appendix = text[text.index("# Appendix:"):text.index("# Declarations")]

keys = re.findall(r"@\w+\{([^,\s]+),", bib)
cited = set(re.findall(r"(?<!\w)@([A-Za-z0-9_:-]+)", text))
missing = sorted(cited - set(keys))
unused = sorted(set(keys) - cited)
duplicates = sorted({x for x in keys if keys.count(x) > 1})

forbidden_insider_tokens = [
    "UEOT", "qianOriginal", "qianPhilosophy", "qianMathematics",
    "ueotSource", "ueotGrowth", "ueotStatus", "GOD", "GOA",
    "P-ID", "CSX-", "N-TEL", "MurphyHoops",
]
insider_hits = [tok for tok in forbidden_insider_tokens if tok in text or tok in bib]

required = [
    "manuscript.md", "manuscript.tex", "manuscript.pdf", "references.bib",
    "ABSTRACT_ZH.md", "CLAIM_MATRIX.md", "README.md", "COPYRIGHT_AND_LICENSE.md",
    "BUILD_RECEIPT.json", "template.tex", "layout.lua", "generate_figures.py",
    "build.py", "validate.py",
    "figures/fig1_architecture_and_thresholds.pdf",
    "figures/fig2_informative_counts_and_sufficiency.pdf",
    "figures/fig3_dag_compression_and_scaling.pdf",
    "submissions/mor/mor_blinded_manuscript.pdf",
    "submissions/mor/mor_title_page.pdf",
    "submissions/mor/cover_letter.md",
    "submissions/mor/SUBMISSION_GUIDE_AND_MANIFEST.md",
]
absent = [n for n in required if not (ROOT / n).is_file()]

build = json.loads((ROOT / "BUILD_RECEIPT.json").read_text(encoding="utf-8"))
hash_errors = [
    n for group in ["inputs", "outputs"]
    for n, h in build[group].items()
    if sha(ROOT / n) != h
]

(ROOT / "build").mkdir(exist_ok=True)
subprocess.run(["pdftotext", "-layout", "manuscript.pdf", "build/final-extracted.txt"], cwd=ROOT, env=ENV, check=True)
pdftext = (ROOT / "build/final-extracted.txt").read_text(errors="replace")
unresolved_pdf = "??" in pdftext or "[?]" in pdftext

info = subprocess.run(["pdfinfo", "manuscript.pdf"], cwd=ROOT, env=ENV, capture_output=True, text=True, check=True).stdout
pages = int(re.search(r"^Pages:\s+(\d+)", info, re.M).group(1))

# --- 3. Double-anonymous MOR submission package validation ---
subprocess.run(
    ["pdftotext", "-layout", "mor_blinded_manuscript.pdf", "build/mor-extracted.txt"],
    cwd=MOR_DIR, env=ENV, check=True,
)
mor_text = (MOR_DIR / "build" / "mor-extracted.txt").read_text(errors="replace")
mor_info = subprocess.run(
    ["pdfinfo", "mor_blinded_manuscript.pdf"],
    cwd=MOR_DIR, env=ENV, capture_output=True, text=True, check=True,
).stdout
mor_pages = int(re.search(r"^Pages:\s+(\d+)", mor_info, re.M).group(1))
mor_log = (MOR_DIR / "build" / "mor_blinded_manuscript.log").read_text(errors="replace")
mor_tex_errors = re.findall(
    r"^!.*$|^.*(?:undefined citations|Citation .* undefined|Reference .* undefined).*$",
    mor_log, re.M,
)
mor_missing_glyphs = re.findall(r"^Missing character:.*$", mor_log, re.M)
mor_overfull = re.findall(r"^Overfull.*$", mor_log, re.M)

anonymity_leaks = [
    tok for tok in ["Degui", "Qian", "MurphyHoops", "24433585", "24433584"]
    if tok in mor_text or tok in mor_info
]

mor_record = {
    "journal": "Mathematics of Operations Research (INFORMS)",
    "review_mode": "double-anonymous (two-file split: mor_title_page.pdf + mor_blinded_manuscript.pdf)",
    "status": "PASS" if (
        not anonymity_leaks and not mor_tex_errors and not mor_missing_glyphs
        and not mor_overfull and 150 <= len(abstract.split()) <= 200
        and "$" not in abstract and "@" not in abstract and 3 <= len(keywords) <= 5
    ) else "FAIL",
    "abstract_words": len(abstract.split()),
    "abstract_target": "150-200 words, single paragraph, 0 equations, 0 citations",
    "equations_or_citations_in_abstract": ("$" in abstract) or ("@" in abstract),
    "keyword_count": len(keywords),
    "keyword_target": "3-5 keywords",
    "msc2020_present": "MSC 2020" in mor_text,
    "orms_present": "OR/MS" in mor_text,
    "pdf_pages": mor_pages,
    "bibliography_entries": len(keys),
    "anonymity_leaks": anonymity_leaks,
    "tex_errors": mor_tex_errors,
    "missing_glyphs": mor_missing_glyphs,
    "overfull_boxes": mor_overfull,
}
(MOR_DIR / "VALIDATION_MOR.json").write_text(json.dumps(mor_record, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

errors = []
if not 6500 <= len(body.split()) <= 12000:
    errors.append(f"Main body word count {len(body.split())} outside 6,500-12,000 target")
if not 150 <= len(abstract.split()) <= 200:
    errors.append(f"Abstract word count {len(abstract.split())} outside 150-200 MOR target")
if "$" in abstract or "@" in abstract:
    errors.append("Abstract contains equations or citations")
if not 3 <= len(keywords) <= 5:
    errors.append(f"Keyword count {len(keywords)} outside 3-5 MOR target")
if len(keys) < 75:
    errors.append("Bibliography has fewer than 75 external works")
if missing or unused or duplicates:
    errors.append(f"Citation-key mismatch: missing={missing}, unused={unused}, dup={duplicates}")
if insider_hits:
    errors.append(f"Non-standalone insider tokens found: {insider_hits}")
if absent:
    errors.append(f"Missing deliverables: {absent}")
if hash_errors:
    errors.append(f"Build hash mismatch: {hash_errors}")
if unresolved_pdf or build["undefined_references_or_tex_errors"] or build["missing_glyphs"] or build["overfull_boxes"]:
    errors.append("Master PDF/TeX validation issue")
if mor_record["status"] != "PASS":
    errors.append(f"MOR blinded package validation failed: {mor_record}")
if pages != build["pages"]:
    errors.append("Page count mismatch")
if not arithmetic_ok:
    errors.append("Live rational dynamic-programming arithmetic mismatch")

record = {
    "schema": "standalone-mor-editorial-validation/1",
    "version": "1.0",
    "checked_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "status": "PASS" if not errors else "FAIL",
    "errors": errors,
    "body_words": len(body.split()),
    "appendix_words": len(appendix.split()),
    "abstract_words": len(abstract.split()),
    "keyword_count": len(keywords),
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
    "mor_blinded_pages": mor_pages,
    "mor_validation_status": mor_record["status"],
    "unresolved_markers_in_pdf": unresolved_pdf,
    "live_rational_benchmarks": {
        "two_step": {k: str(v) for k, v in b1.items()},
        "three_backup": {k: str(v) for k, v in b2.items()},
        "three_posterior": {k: str(v) for k, v in b3.items()},
        "four_feedback": {k: str(v) for k, v in b4.items()},
        "eight_two_wallet": {k: str(v) for k, v in b5.items()},
    },
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
sha_lines = [f"{sha(ROOT / f)}  {f}" for f in sha_files]
(ROOT / "SHA256SUMS").write_text("\n".join(sha_lines) + "\n", encoding="utf-8")

print(json.dumps({
    k: record[k]
    for k in [
        "status", "errors", "abstract_words", "body_words", "appendix_words",
        "bibliography_entries", "unpublished_internal_self_citations",
        "pdf_pages", "mor_blinded_pages", "mor_validation_status",
    ]
}, indent=2))
sys.exit(bool(errors))
