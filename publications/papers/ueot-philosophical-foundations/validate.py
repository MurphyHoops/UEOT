#!/usr/bin/env python3
"""Check publication integrity, references, scope, and small printed arithmetic.

This is document validation, not a Lean proof run or an empirical test.
Requires a built PDF and the completed companion files. See the publication
rights notice for the scope of the supplied reproduction utilities.
"""
from pathlib import Path
from fractions import Fraction as Q
import datetime
import hashlib
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
BASE = "3d443ec29eb17af1fc00699a74e2d42d73516d81"
PREFIX = "publications/papers/ueot-philosophical-foundations/"

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

text = (ROOT/"manuscript.md").read_text(encoding="utf-8")
bib = (ROOT/"references.bib").read_text(encoding="utf-8")
body = text[text.index("# Introduction:"):text.index("# Sources, evidence, and assistance")]
abstract = text.split("abstract: |",1)[1].split("keywords:",1)[0]
keys = re.findall(r"@\w+\{([^,\s]+),", bib)
cited = set(re.findall(r"(?<!\w)@([A-Za-z0-9_:-]+)",text))
missing = sorted(cited-set(keys))
unused = sorted(set(keys)-cited)
duplicates = sorted({x for x in keys if keys.count(x)>1})
required = ["manuscript.md","manuscript.tex","manuscript.pdf","references.bib",
    "ABSTRACT_ZH.md","CLAIM_MATRIX.md","PRIOR_ART_AND_NOVELTY_REVIEW.md",
    "REVIEW.md","SOURCE_MANIFEST.json","README.md","COPYRIGHT_AND_LICENSE.md",
    "REFERENCE_VERIFICATION.md","FORMAL_CLAIM_EVIDENCE_MATRIX.md",
    "MATHEMATICAL_SUPPORT_AND_LIMITS.md","ORIGINAL_TO_CURRENT_CLAIM_MATRIX.md",
    "PHILOSOPHICAL_THESIS_AUDIT.md","STRONGEST_OBJECTIONS.md",
    "BUILD_RECEIPT.json","VISUAL_REVIEW.md","DELIVERY_STATUS.md",
    "review/FULL_MANUSCRIPT_PHILOSOPHICAL_REVIEW.md",
    "review/FULL_MANUSCRIPT_SCIENTIFIC_REVIEW.md","review/RED_TEAM_REVIEW.md",
    "review/ROUND2_PHILOSOPHICAL_REVIEW.md","review/ROUND2_SCIENTIFIC_REVIEW.md",
    "review/ROUND2_RED_TEAM_REVIEW.md","review/FINAL_EDITORIAL_CHECK.md",
    "review/REFERENCES_VERIFIED.bib"]
absent = [n for n in required if not (ROOT/n).is_file()]
build = json.loads((ROOT/"BUILD_RECEIPT.json").read_text())
hash_errors = [n for group in ["inputs","outputs"] for n,h in build[group].items() if sha(ROOT/n)!=h]

(ROOT/"build").mkdir(exist_ok=True)
subprocess.run(["pdftotext","-layout","manuscript.pdf","build/final-extracted.txt"],cwd=ROOT,check=True)
pdftext=(ROOT/"build/final-extracted.txt").read_text(errors="replace")
unresolved_pdf = "??" in pdftext or "[?]" in pdftext
info = subprocess.run(["pdfinfo","manuscript.pdf"],cwd=ROOT,capture_output=True,text=True,check=True).stdout
pages=int(re.search(r"^Pages:\s+(\d+)",info,re.M).group(1))

source_manifest=json.loads((ROOT/"SOURCE_MANIFEST.json").read_text())
repo_probe=subprocess.run(["git","rev-parse","--show-toplevel"],cwd=ROOT,capture_output=True,text=True)
source_result={"status":"NOT_RUN_STANDALONE_PACKAGE","checked":0,"mismatches":[]}
scope_result={"status":"NOT_RUN_STANDALONE_PACKAGE"}
if repo_probe.returncode==0:
    repo=Path(repo_probe.stdout.strip())
    if (repo/"docs/REPOSITORY_BRANCH_GOVERNANCE.md").exists():
        mismatches=[]
        for e in source_manifest["sources"]:
            p=repo/e["path"]
            raw=p.read_bytes() if p.exists() else subprocess.run(["git","show",BASE+":"+e["path"]],cwd=repo,capture_output=True,check=True).stdout
            if hashlib.sha256(raw).hexdigest()!=e["sha256"]:
                mismatches.append(e["path"])
        source_result={"status":"PASS" if not mismatches else "FAIL","checked":len(source_manifest["sources"]),"mismatches":mismatches}
        changed=subprocess.run(["git","diff","--name-only",BASE],cwd=repo,capture_output=True,text=True,check=True).stdout.splitlines()
        untracked=subprocess.run(["git","ls-files","--others","--exclude-standard"],cwd=repo,capture_output=True,text=True,check=True).stdout.splitlines()
        paths=sorted(set(changed+untracked)); outside=[p for p in paths if not p.startswith(PREFIX)]
        scope_result={"status":"PASS" if not outside else "FAIL","changed_or_untracked_paths":paths,"outside_publication_directory":outside}

# Check printed example arithmetic; this does not replace any general theorem.
critical_kc=Q(2,3)+Q(1,4)
critical_kb=Q(2,3)-Q(1,8)+Q(1,4)+Q(1,4)
critical_lambda=Q(2,3)*critical_kb+Q(1,3)*critical_kc
b2care=(Q(3,4)+Q(3,8))*Q(3,8)
b2bloom=(Q(3,4)+Q(3,8))*(Q(3,8)+Q(2,3)*Q(1,4))
arithmetic={"critical_kc":str(critical_kc),"critical_kb":str(critical_kb),"critical_lambda1":str(critical_lambda),"theta0D_second_births":str(b2care),"theta1D_second_births":str(b2bloom)}
arithmetic_ok=critical_kc==Q(11,12) and critical_lambda==1 and b2care==Q(27,64) and b2bloom==Q(39,64)
errors=[]
if not 8000<=len(body.split())<=12000: errors.append("Body word count outside target")
if not 180<=len(abstract.split())<=250: errors.append("Abstract word count outside target")
if missing or unused or duplicates: errors.append("Citation-key mismatch")
if absent: errors.append("Missing deliverables")
if hash_errors: errors.append("Build hash mismatch")
if unresolved_pdf or build["undefined_references_or_tex_errors"] or build["missing_glyphs"] or build["overfull_boxes"]: errors.append("PDF/TeX validation issue")
if pages!=build["pages"]: errors.append("Page count mismatch")
if source_result["status"]=="FAIL" or scope_result["status"]=="FAIL": errors.append("Protected source or change scope mismatch")
if not arithmetic_ok: errors.append("Printed arithmetic mismatch")
record={
 "schema":"ueot-philosophy-editorial-validation/1",
 "checked_at_utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),
 "status":"PASS" if not errors else "FAIL",
 "scope":"Document integrity and editorial arithmetic only; not external peer review or a scientific proof run",
 "errors":errors,
 "word_count_convention":"Whitespace-delimited Markdown from Introduction heading through Conclusion; excludes abstract, bibliography and assistance/source notice",
 "body_words":len(body.split()),"abstract_words":len(abstract.split()),"full_markdown_words":len(text.split()),
 "bibliography_entries":len(keys),"cited_keys":len(cited),"external_works":20,"ueot_source_records":7,
 "missing_citations":missing,"unused_entries":unused,"duplicate_keys":duplicates,
 "missing_required_files":absent,"build_hash_mismatches":hash_errors,
 "pdf_pages":pages,"unresolved_markers_in_pdf":unresolved_pdf,
 "protected_sources":source_result,"git_change_scope":scope_result,
 "printed_arithmetic":arithmetic,"printed_arithmetic_status":"PASS" if arithmetic_ok else "FAIL",
 "manuscript_sha256":sha(ROOT/"manuscript.md"),"pdf_sha256":sha(ROOT/"manuscript.pdf"),
 "new_lean_invocations":0,"new_empirical_experiments":0,
 "remote_delivery":"See DELIVERY_STATUS.md; local document PASS is not a PR or remote publication claim"
}
(ROOT/"VALIDATION.json").write_text(json.dumps(record,ensure_ascii=False,indent=2)+"\n")
print(json.dumps({k:record[k] for k in ["status","errors","body_words","abstract_words","bibliography_entries","pdf_pages"]},indent=2))
sys.exit(bool(errors))
