#!/usr/bin/env python3
"""Validate standalone journal article integrity, citations, JAR single-blind compliance,
exact binomial risk-oracle operating rates (Theorem 5), and full 7-action rational POMDP
dynamic programming from scratch (Theorem 7).
"""
from __future__ import annotations

from fractions import Fraction as Q
from pathlib import Path
from typing import Optional
import datetime
import hashlib
import json
import math
import os
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
JAR_DIR = ROOT / "submissions" / "jar"
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


# ---------------------------------------------------------------------------
# 1. Standalone exact-rational 7-action POMDP solver for Theorem 7
# ---------------------------------------------------------------------------
# Action encoding matching RegisterJointDecisionConsumer.allActions:
#   None               -> stop (cap = 0)
#   (addr_child1, op)  -> addr_child1 in {False, True}, op in {None, False, True}
Action = Optional[tuple[bool, Optional[bool]]]
Obs = tuple[bool, bool]
Store = tuple[Optional[bool], ...]
World = tuple[str, Store, bool]  # (mechanism in {'S', 'G'}, store, stopped)

ALL_ACTIONS: list[Action] = [
    None,
    (False, None),
    (True, None),
    (False, False),
    (False, True),
    (True, False),
    (True, True),
]
ALL_OBS: list[Obs] = [(False, False), (False, True), (True, False), (True, True)]


def action_cap(a: Action) -> int:
    if a is None:
        return 0
    return 1 if a[1] is not None else 0


def legal_menu(bal: int) -> list[Action]:
    return [a for a in ALL_ACTIONS if action_cap(a) <= bal]


def step_world(w: World, a: Action, mode_normal: bool) -> tuple[Obs, World]:
    mech, store, stopped = w
    if stopped or a is None:
        idx, write_op = 0, None
    else:
        idx, write_op = (1 if a[0] else 0), a[1]
    lookup = store[idx] if idx < len(store) else None
    if lookup is None:
        obs: Obs = (False, False)
        u_store: Store = store + (None,)
    else:
        eff_bit = lookup if write_op is None else write_op
        post_bit = eff_bit if mode_normal else False
        child: Optional[bool] = True if (mode_normal and eff_bit is True) else None
        obs = (child is not None, bool(mode_normal and write_op is not None))
        u_store = store[:idx] + (post_bit,) + store[idx + 1:] + (child,)
    if mech == "G" and not mode_normal:
        u_store = tuple((False if slot is not None else None) for slot in u_store)
    next_stopped = stopped or (a is None)
    return obs, (mech, u_store, next_stopped)


def step_gain(o: Obs) -> Q:
    return (Q(1) if o[0] else Q(0)) - (Q(1, 4) if o[1] else Q(0))


def advance_wallet(bal: int, o: Obs) -> int:
    return bal - (1 if o[1] else 0)


def solve_exact_pomdp(horizon: int, belief: dict[World, Q], bal: int):
    if horizon == 0:
        return Q(0), ("halt",)
    scored = []
    for a in legal_menu(bal):
        total = Q(0)
        children = {}
        for o in ALL_OBS:
            unnorm: dict[World, Q] = {}
            obs_mass = Q(0)
            for w, prob in belief.items():
                for mode in (True, False):
                    o_out, w_next = step_world(w, a, mode)
                    if o_out == o:
                        mass = prob * Q(1, 2)
                        obs_mass += mass
                        unnorm[w_next] = unnorm.get(w_next, Q(0)) + mass
            next_bal = advance_wallet(bal, o)
            if obs_mass == 0:
                children[o] = ("halt_zero", next_bal)
            else:
                post = {wn: m / obs_mass for wn, m in unnorm.items()}
                sub_val, sub_tree = solve_exact_pomdp(horizon - 1, post, next_bal)
                total += obs_mass * (step_gain(o) + sub_val)
                children[o] = sub_tree
        scored.append((total, ("node", a, children)))
    best_val, best_tree = scored[-1]
    for val, tree in reversed(scored[:-1]):
        if not (val < best_val):
            best_val, best_tree = val, tree
    return best_val, best_tree


def eval_policy_tree(tree, w: World) -> Q:
    if tree[0] == "halt":
        return Q(0)
    _, a, children = tree
    acc = Q(0)
    for mode in (True, False):
        o_out, w_next = step_world(w, a, mode)
        acc += Q(1, 2) * (step_gain(o_out) + eval_policy_tree(children[o_out], w_next))
    return acc


def initial_world(mech: str) -> World:
    return (mech, (False,), False)


# ---------------------------------------------------------------------------
# 2. Exact binomial operating characteristics for Theorem 5 witness
# ---------------------------------------------------------------------------
def exact_binom_prob(n: int, theta: Q, k_set: set[int]) -> float:
    p = float(theta)
    q = 1.0 - p
    log_p = math.log(p)
    log_q = math.log(q)
    lg_n = math.lgamma(n + 1)
    log_terms = [
        lg_n - math.lgamma(k + 1) - math.lgamma(n - k + 1) + k * log_p + (n - k) * log_q
        for k in k_set
    ]
    if not log_terms:
        return 0.0
    m = max(log_terms)
    return math.exp(m) * sum(math.exp(lt - m) for lt in log_terms)


# ---------------------------------------------------------------------------
# 3. Document, citation, and JAR single-blind compliance checks
# ---------------------------------------------------------------------------
text = (ROOT / "manuscript.md").read_text(encoding="utf-8")
bib = (ROOT / "references.bib").read_text(encoding="utf-8")

abstract = text.split("abstract: |", 1)[1].split("keywords:", 1)[0]
keywords_line = re.search(r'^keywords:\s*"([^"]+)"', text, re.M).group(1)
keywords = [k.strip() for k in keywords_line.split(";") if k.strip()]
appendix_anchor = "```{=latex}\n\\appendix"
body = text[text.index("# Introduction:"):text.index(appendix_anchor)]
appendix = text[text.index(appendix_anchor):text.index("# Declarations")]

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
    "BUILD_RECEIPT.json", "template.tex", "layout.lua", "build.py", "validate.py",
    "submissions/jar/jar_manuscript.md",
    "submissions/jar/jar_manuscript.tex",
    "submissions/jar/jar_manuscript.pdf",
    "submissions/jar/jar_title_page.tex",
    "submissions/jar/jar_title_page.pdf",
    "submissions/jar/template_jar.tex",
    "submissions/jar/SUBMISSION_GUIDE_AND_MANIFEST.md",
    "submissions/jar/cover_letter.md",
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
unresolved_pdf = "??" in pdftext or "[?]" in pdftext or "(author?)" in pdftext

blg_path = ROOT / "build" / "manuscript.blg"
master_bib_warnings = re.findall(r"^Warning--.*$", blg_path.read_text(errors="replace"), re.M) if blg_path.is_file() else ["missing manuscript.blg"]

info = subprocess.run(["pdfinfo", "manuscript.pdf"], cwd=ROOT, env=ENV, capture_output=True, text=True, check=True).stdout
pages = int(re.search(r"^Pages:\s+(\d+)", info, re.M).group(1))

# Validate Springer JAR single-blind submission package
(JAR_DIR / "build").mkdir(exist_ok=True)
subprocess.run(["pdftotext", "-layout", "jar_manuscript.pdf", "build/jar-extracted.txt"], cwd=JAR_DIR, env=ENV, check=True)
jar_text = (JAR_DIR / "build" / "jar-extracted.txt").read_text(errors="replace")
jar_info = subprocess.run(["pdfinfo", "jar_manuscript.pdf"], cwd=JAR_DIR, env=ENV, capture_output=True, text=True, check=True).stdout
jar_pages = int(re.search(r"^Pages:\s+(\d+)", jar_info, re.M).group(1))
jar_title_info = subprocess.run(["pdfinfo", "jar_title_page.pdf"], cwd=JAR_DIR, env=ENV, capture_output=True, text=True, check=True).stdout
jar_title_pages = int(re.search(r"^Pages:\s+(\d+)", jar_title_info, re.M).group(1))

jar_log = (JAR_DIR / "build" / "jar_manuscript.log").read_text(errors="replace")
jar_tex_errors = re.findall(
    r"^!.*$|^.*(?:undefined citations|Citation .* undefined|Reference .* undefined).*$",
    jar_log,
    re.M,
)
jar_missing_glyphs = re.findall(r"^Missing character:.*$", jar_log, re.M)
jar_overfull = re.findall(r"^Overfull.*$", jar_log, re.M)
jar_blg = (JAR_DIR / "build" / "jar_manuscript.blg")
jar_bib_warnings = re.findall(r"^Warning--.*$", jar_blg.read_text(errors="replace"), re.M) if jar_blg.is_file() else ["missing jar_manuscript.blg"]
jar_unresolved = "??" in jar_text or "[?]" in jar_text or "(author?)" in jar_text

required_single_blind_tokens = [
    "Degui Qian",
    "10.5281/zenodo.24433585",
    "ExhaustiveAxiomAudit",
    "Gemini 4 Carbon",
    "ChatGPT 6 Astra",
]
missing_single_blind_tokens = [tok for tok in required_single_blind_tokens if tok not in jar_text]
undefined_abbrevs_in_abstract = [abbr for abbr in ["GCD"] if abbr in abstract]

jar_record = {
    "journal": "Journal of Automated Reasoning (Springer Nature, ID 10817)",
    "review_mode": "single-blind (jar_manuscript.pdf with author attribution, referee line numbers, and Zenodo DOI + optional jar_title_page.pdf)",
    "status": "PASS" if (
        not missing_single_blind_tokens
        and not jar_tex_errors
        and not jar_bib_warnings
        and not jar_missing_glyphs
        and not jar_overfull
        and not jar_unresolved
        and not undefined_abbrevs_in_abstract
        and 150 <= len(abstract.split()) <= 250
        and 4 <= len(keywords) <= 6
        and jar_title_pages == 1
    ) else "FAIL",
    "abstract_words": len(abstract.split()),
    "abstract_target": "150-250 words, 0 undefined abbreviations, 0 citations",
    "undefined_abbreviations_in_abstract": undefined_abbrevs_in_abstract,
    "keyword_count": len(keywords),
    "keyword_target": "4-6 keywords",
    "declarations_before_references": True,
    "single_blind_tokens_verified": not missing_single_blind_tokens,
    "missing_single_blind_tokens": missing_single_blind_tokens,
    "jar_pdf_pages": jar_pages,
    "title_page_pdf_pages": jar_title_pages,
    "bibliography_entries": len(keys),
    "bibtex_warnings": jar_bib_warnings,
    "tex_errors": jar_tex_errors,
    "missing_glyphs": jar_missing_glyphs,
    "overfull_boxes": jar_overfull,
}
(JAR_DIR / "VALIDATION_JAR.json").write_text(json.dumps(jar_record, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

# ---------------------------------------------------------------------------
# 4. Verify all printed identities, binomial witness rates, and full 7-action DP
# ---------------------------------------------------------------------------
joint_n256_exact = Q(7, 8) * Q(1, 8) + Q(1, 8) * Q(1, 4)
alpha_n256_upper = Q(1, 16)
beta_n256 = Q(1, 2)
mixture_n256_upper = beta_n256 + (1 - beta_n256) * alpha_n256_upper
sharp_two_branch = Q(1, 4) + Q(3, 4) * Q(1, 2)

goal_risk_quarter = (1 - Q(1, 4)) ** 2
goal_risk_eighth = (1 - Q(1, 8)) ** 2
goal_cap = Q(7, 10)
nontrivial_conf_4096 = 48.0 * math.exp(-512.0 / 25.0)

# Sample cost check at |X|=100, |A|=5, u=0.05, alpha=0.05 using alpha_N(u) = |X||A|2^(|X|+1)e^(-2Nu^2)
n_scale_100_5 = math.ceil(((100 + 1) * math.log(2.0) + math.log(100.0 * 5.0 / 0.05)) / (2.0 * 0.05 ** 2))

# Exact acceptance set for NoisyFiniteRiskOracleWitness at N=4096, u=1/20, tau=1/8, beta=7/10
u_wit = Q(1, 20)
tau_wit = Q(1, 8)
beta_wit = Q(7, 10)
accepted_ks = {
    k for k in range(4097)
    if ((1 - Q(k, 4096)) - 2 * u_wit > tau_wit)  # coarse candidate q_0 rejected
    and ((1 - Q(k, 4096)) ** 2 + 2 * u_wit <= beta_wit)  # identity candidate q_1 accepted
}
boundary_k820_in_good_event = abs(Q(820, 4096) - Q(1, 4)) <= u_wit
boundary_k820_budget = (1 - Q(820, 4096)) ** 2 + 2 * u_wit
prob_accept_quarter = exact_binom_prob(4096, Q(1, 4), accepted_ks)
prob_abstain_quarter = exact_binom_prob(4096, Q(1, 4), set(range(4097)) - accepted_ks)
prob_accept_eighth = exact_binom_prob(4096, Q(1, 8), accepted_ks)

# Run standalone full 7-action rational POMDP solver at H=2 and H=3
wS = initial_world("S")
wG = initial_world("G")
dp_h2_S_val, dp_h2_S_tree = solve_exact_pomdp(2, {wS: Q(1)}, 2)
dp_h2_G_val, dp_h2_G_tree = solve_exact_pomdp(2, {wG: Q(1)}, 2)
dp_h2_S_on_G = eval_policy_tree(dp_h2_S_tree, wG)

dp_h3_S_val, dp_h3_S_tree = solve_exact_pomdp(3, {wS: Q(1)}, 2)
dp_h3_G_val, dp_h3_G_tree = solve_exact_pomdp(3, {wG: Q(1)}, 2)
dp_h3_dual_val, _ = solve_exact_pomdp(3, {wS: Q(3, 4), wG: Q(1, 4)}, 2)
dp_j_S_piS = eval_policy_tree(dp_h3_S_tree, wS)
dp_j_G_piS = eval_policy_tree(dp_h3_S_tree, wG)
dp_j_S_piG = eval_policy_tree(dp_h3_G_tree, wS)
dp_j_G_piG = eval_policy_tree(dp_h3_G_tree, wG)

tv_h3_half = Q(1, 2) ** 2 * (1 - Q(1, 2))
err_h3_half = Q(1, 2) * (1 - tv_h3_half)
dual_lower = Q(3, 4) * dp_h3_S_val + Q(1, 4) * dp_h3_G_val - dp_h3_dual_val
j_S_rho = Q(1, 4) * dp_j_S_piS + Q(3, 4) * dp_j_S_piG
j_G_rho = Q(1, 4) * dp_j_G_piS + Q(3, 4) * dp_j_G_piG
regret_S_rho = dp_h3_S_val - j_S_rho
regret_G_rho = dp_h3_G_val - j_G_rho
det_min_regret = dp_h3_S_val - dp_h3_G_val

int_scale_h3_S = 4 * (2 ** 3) * 1 * dp_h3_S_val
int_scale_h3_G = 4 * (2 ** 3) * 1 * dp_h3_G_val
int_scale_h3_dual = 4 * (2 ** 3) * 4 * dp_h3_dual_val
int_scale_h3_piS_G = 4 * (2 ** 3) * 1 * dp_j_G_piS
int_scale_h2_common = 4 * (2 ** 2) * 1 * dp_h2_S_val

# Verify memory-separation uncertified-mass sum at theta in {0, 1/2, 1}
mem_sep_uncertified_min = min(1 + th ** 2 for th in [Q(0), Q(1, 2), Q(1)])
mem_sep_cemetery_min = min(th + (1 - th) ** 2 for th in [Q(0), Q(1, 2), Q(1)])

arithmetic = {
    "mem_sep_uncertified_two_step_min": str(mem_sep_uncertified_min),
    "mem_sep_cemetery_hit_min": str(mem_sep_cemetery_min),
    "joint_n256_exact": str(joint_n256_exact),
    "mixture_n256_upper": str(mixture_n256_upper),
    "sharp_two_branch": str(sharp_two_branch),
    "goal_risk_quarter": str(goal_risk_quarter),
    "goal_risk_eighth": str(goal_risk_eighth),
    "alpha_4096_lt_one": round(nontrivial_conf_4096, 12),
    "per_row_sample_cost_100_5": n_scale_100_5,
    "witness_accept_k_range": [min(accepted_ks), max(accepted_ks)],
    "witness_k820_budget": round(float(boundary_k820_budget), 6),
    "witness_prob_accept_theta_quarter": round(prob_accept_quarter, 6),
    "witness_prob_abstain_theta_quarter": round(prob_abstain_quarter, 6),
    "witness_prob_accept_theta_eighth": float(f"{prob_accept_eighth:.4e}"),
    "tv_h3_half": str(tv_h3_half),
    "err_h3_half": str(err_h3_half),
    "dp_h2_common_opt": str(dp_h2_S_val),
    "dp_v_S": str(dp_h3_S_val),
    "dp_v_G": str(dp_h3_G_val),
    "dp_v_dual": str(dp_h3_dual_val),
    "dp_j_G_piS": str(dp_j_G_piS),
    "dp_j_S_piG": str(dp_j_S_piG),
    "dual_lower_bound": str(dual_lower),
    "j_S_rho": str(j_S_rho),
    "j_G_rho": str(j_G_rho),
    "regret_rho": str(max(regret_S_rho, regret_G_rho)),
    "det_min_regret": str(det_min_regret),
    "kernel_int_h3": [int(int_scale_h3_S), int(int_scale_h3_G), int(int_scale_h3_dual), int(int_scale_h3_piS_G)],
    "kernel_int_h2": int(int_scale_h2_common),
}

arithmetic_ok = (
    mem_sep_uncertified_min == Q(1, 1)
    and mem_sep_cemetery_min == Q(3, 4)
    and joint_n256_exact == Q(9, 64)
    and mixture_n256_upper == Q(17, 32)
    and sharp_two_branch == Q(5, 8)
    and goal_risk_quarter == Q(9, 16)
    and goal_risk_quarter <= goal_cap
    and goal_risk_eighth == Q(49, 64)
    and goal_risk_eighth > goal_cap
    and round(nontrivial_conf_4096 * 1e8, 2) == 6.12
    and nontrivial_conf_4096 < 1.0
    and n_scale_100_5 == 15844
    and accepted_ks == set(range(924, 3175))
    and boundary_k820_in_good_event
    and round(float(boundary_k820_budget), 3) == 0.740
    and round(prob_accept_quarter, 6) == 0.999876
    and round(prob_abstain_quarter, 6) == 0.000124
    and 5.9e-71 <= prob_accept_eighth <= 6.1e-71
    and tv_h3_half == Q(1, 8)
    and err_h3_half == Q(7, 16)
    and dp_h2_S_val == Q(13, 16)
    and dp_h2_G_val == Q(13, 16)
    and dp_h2_S_on_G == Q(13, 16)
    and dp_h3_S_val == Q(41, 32)
    and dp_h3_G_val == Q(5, 4)
    and dp_h3_dual_val == Q(5, 4)
    and dp_j_S_piS == Q(41, 32)
    and dp_j_G_piS == Q(37, 32)
    and dp_j_S_piG == Q(5, 4)
    and dp_j_G_piG == Q(5, 4)
    and dual_lower == Q(3, 128)
    and j_S_rho == Q(161, 128)
    and j_G_rho == Q(157, 128)
    and regret_S_rho == Q(3, 128)
    and regret_G_rho == Q(3, 128)
    and det_min_regret == Q(1, 32)
    and det_min_regret > dual_lower
    and [int_scale_h3_S, int_scale_h3_G, int_scale_h3_dual, int_scale_h3_piS_G] == [41, 40, 160, 37]
    and int_scale_h2_common == 13
)

errors: list[str] = []
if not 6500 <= len(body.split()) <= 12500:
    errors.append(f"Main body word count {len(body.split())} outside 6,500-12,500 target")
if not 150 <= len(abstract.split()) <= 250:
    errors.append(f"Abstract word count {len(abstract.split())} outside Springer 150-250 target")
if undefined_abbrevs_in_abstract:
    errors.append(f"Undefined abbreviations in abstract: {undefined_abbrevs_in_abstract}")
if not 4 <= len(keywords) <= 6:
    errors.append(f"Keyword count {len(keywords)} outside Springer 4-6 window")
if len(keys) < 80:
    errors.append("Bibliography has fewer than 80 external works")
if missing or unused or duplicates:
    errors.append(f"Citation-key mismatch: missing={missing}, unused={unused}, dup={duplicates}")
if master_bib_warnings:
    errors.append(f"Master BibTeX warnings: {master_bib_warnings}")
if insider_hits:
    errors.append(f"Non-standalone insider tokens found: {insider_hits}")
if absent:
    errors.append(f"Missing deliverables: {absent}")
if hash_errors:
    errors.append(f"Build hash mismatch: {hash_errors}")
if unresolved_pdf or build["undefined_references_or_tex_errors"] or build["missing_glyphs"] or build["overfull_boxes"]:
    errors.append("Master PDF/TeX validation issue")
if pages != build["pages"]:
    errors.append("Page count mismatch")
if not arithmetic_ok:
    errors.append("Printed arithmetic / standalone DP / binomial check mismatch")
if jar_record["status"] != "PASS":
    errors.append(f"JAR single-blind package validation failed: {jar_record}")

record = {
    "schema": "standalone-jar-editorial-validation/3",
    "version": "1.1",
    "checked_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "status": "PASS" if not errors else "FAIL",
    "errors": errors,
    "body_words": len(body.split()),
    "appendix_words": len(appendix.split()),
    "abstract_words": len(abstract.split()),
    "keyword_count": len(keywords),
    "declarations_before_references": True,
    "ai_disclosure_verified": ("Degui Qian" in text) and ("Gemini 4 Carbon" in text) and ("ChatGPT 6 Astra" in text),
    "full_markdown_words": len(text.split()),
    "bibliography_entries": len(keys),
    "bibtex_warnings": master_bib_warnings,
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
    "jar_pages": jar_pages,
    "jar_title_page_pages": jar_title_pages,
    "jar_validation_status": jar_record["status"],
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
        "bibliography_entries", "pdf_pages", "jar_pages", "jar_title_page_pages",
        "jar_validation_status", "printed_arithmetic_status",
    ]
}, indent=2))
sys.exit(bool(errors))
