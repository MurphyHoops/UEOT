#!/usr/bin/env python3
"""Independent book-3.8 increment identity and evidence-scope checks.

Does not import the production publication verifier, mutate metadata, run Lean,
or infer scientific truth from token counts. The default permits unfinished
metadata and reports it as PENDING; --require-complete makes pending integration
items an unsuccessful release check. All old result dictionaries must remain
exact even in preparation mode.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import sys


NEW_IDS = ["P-OPT-02", "P-OPT-03", "P-MICRO-01", "C-MICRO-01",
           "P-MICRO-02", "P-ROB-01", "C-ROB-01", "P-ROB-02", "P-MICRO-03"]
EXPECTED_TITLES = {
 "P-OPT-02": ("P-OPT-02（正维有限复系统中的四种事件等价）。",
              "P-OPT-02 (Four equivalent identities for events in positive-dimensional finite complex systems)."),
 "P-OPT-03": ("P-OPT-03（逐可见标签的组合相容性）。",
              "P-OPT-03 (Composition respects identity at every visible label)."),
 "P-MICRO-01": ("P-MICRO-01（微观来源到完整适应 CQ 的截断桥）。",
                "P-MICRO-01 (A microscopic bridge to complete adaptive CQ truncation)."),
 "C-MICRO-01": ("C-MICRO-01（平均能量保持不保证逐分支截断）。",
                "C-MICRO-01 (Mean-energy preservation does not imply branchwise truncation)."),
 "P-MICRO-02": ("P-MICRO-02（正常迹类后选择和完整准备记录）。",
                "P-MICRO-02 (Normal trace-class postselection and complete preparation records)."),
 "P-ROB-01": ("P-ROB-01（同一参数集上的部署误差与分离）。",
              "P-ROB-01 (Deployment error and separation on one parameter set)."),
 "C-ROB-01": ("C-ROB-01（逐参数可实现不推出一次鲁棒部署）。",
              "C-ROB-01 (Pointwise realizability does not imply one robust deployment)."),
 "P-ROB-02": ("P-ROB-02（同一原源的精确设计区间证书）。",
              "P-ROB-02 (An exact design-region certificate for the same source)."),
 "P-MICRO-03": ("P-MICRO-03（单激发边缘混合，完整记录不遗忘）。",
                "P-MICRO-03 (Single-excitation marginal mixing without full-record forgetting).")
}
NEW_LEAN_FILE = "formalization/ueot-qm/UEOTQM/OperationalEquivalence.lean"
EXPECTED_LEAN_NAMES = {
 "P-OPT-02": ["contextStatistics_iff_singleStatistics", "singleStatistics_iff_map_eq",
              "contextStatistics_iff_choi_eq"],
 "P-OPT-03": ["labelled_comp_congr", "labelled_sum_congr"]
}


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def result_objects(dossier):
    return [row for chapter in dossier.get("chapters", [])
            for row in chapter.get("numbered_results", [])]


def actual_results(text):
    """Independent anchor-to-statement scan, before any appendix registry."""
    body=text.split('<a id="appendix-a"></a>',1)[0]
    pieces=re.split(r'(?m)^(<a id="[a-z0-9-]+"></a>)\s*$',body)
    chapter=None
    found=[]
    for index,part in enumerate(pieces):
        if not part.startswith('<a id="'):
            continue
        anchor=re.fullmatch(r'<a id="([a-z0-9-]+)"></a>',part).group(1)
        after=pieces[index+1] if index+1<len(pieces) else ""
        if anchor.startswith("ch-"):
            chapter=int(anchor[3:]);continue
        title=re.match(r'\s*\*\*(.*?)\*\*',after,re.S)
        if title is None or "\n" in title.group(1):
            raise ValueError("Result anchor lacks one immediate bold statement: "+anchor)
        rid=anchor.upper()
        if not re.match(re.escape(rid)+r'(?=$|[^A-Za-z0-9_-])',title.group(1)):
            raise ValueError("Anchor/statement ID mismatch: "+anchor)
        found.append({"id":rid,"chapter":chapter,"title":title.group(1),"anchor":anchor})
    return found


def chapter67(text):
    marker='<a id="ch-67"></a>'
    if text.count(marker)!=1:
        raise ValueError("Expected exactly one chapter-67 anchor")
    return text.split(marker,1)[1].split('<a id="appendix-a"></a>',1)[0]


def display_blocks(text):
    # This increment deliberately uses isolated $$ fences, not an approximate
    # TeX normalization. Any new display syntax needs explicit review.
    lines=text.splitlines(); result=[]; active=None
    for line in lines:
        if line.strip()=="$$":
            if active is None:active=[]
            else:result.append("\n".join(active));active=None
        elif active is not None:active.append(line)
    if active is not None:raise ValueError("Unclosed display-math fence")
    return result


def strip_lean_comments(text):
    out=[];i=0;depth=0
    while i<len(text):
        if text.startswith("/-",i):depth+=1;i+=2
        elif depth and text.startswith("-/",i):depth-=1;i+=2
        elif depth:i+=1
        elif text.startswith("--",i):
            end=text.find("\n",i);i=len(text) if end<0 else end
        else:out.append(text[i]);i+=1
    return "".join(out)


def scope_text(row):
    values=[row.get(k) for k in ["verification_scope","formal_scope","paper_only","limits",
                                 "type_responsibility","formal"] if row.get(k)]
    return json.dumps(values,ensure_ascii=False)


def binding_rows(row):
    out=list(row.get("formal_bindings", []))
    formal=row.get("formal",{})
    if isinstance(formal,dict):out.extend(formal.get("source_bindings",[]))
    return out


def inspect(repo):
    checks=[];pending=[];inputs={};mapping=[]
    def read(rel):
        path=repo/rel;raw=path.read_bytes();inputs[rel]=digest(raw)
        return raw.decode("utf-8")
    def check(name,ok,detail=None):
        if not ok:raise ValueError(name+(": "+str(detail) if detail else ""))
        checks.append({"name":name,"status":"PASS","detail":detail})
    book="physics/qm/book/"
    old=json.loads(read(book+"evidence/v3.8/prior/CHAPTER_DOSSIER.json"))
    current=json.loads(read(book+"CHAPTER_DOSSIER.json"))
    old_results=result_objects(old);now_results=result_objects(current)
    old_ids=[r["id"] for r in old_results]
    check("immutable prior contains 173 unique result objects",len(old_ids)==len(set(old_ids))==173)
    now_by_id={r["id"]:r for r in now_results}
    check("current dossier has no duplicate result IDs",len(now_by_id)==len(now_results))
    check("every inherited result object is exactly preserved",
          all(r["id"] in now_by_id and now_by_id[r["id"]]==r for r in old_results))
    check("inherited dossier order is preserved",
          [r for r in now_results if r["id"] in old_ids]==old_results)
    extra=[r["id"] for r in now_results if r["id"] not in old_ids]
    check("no unregistered extra result IDs",not(set(extra)-set(NEW_IDS)),extra)
    if extra!=NEW_IDS:pending.append("Current dossier does not yet contain all nine ordered chapter-67 result records")
    if str(current.get("edition"))!="3.8":pending.append("Current dossier edition is not yet 3.8")
    languages={"zh":read(book+"UEOT_PHYSICS.md"),"en":read(book+"UEOT_PHYSICS.en.md")}
    parsed={lang:actual_results(text) for lang,text in languages.items()}
    chunks={lang:chapter67(text) for lang,text in languages.items()}
    for lang,text in languages.items():
        ids=[r["id"] for r in parsed[lang]]
        check(lang+" actual book has inherited 173 IDs then exactly nine new IDs",ids==old_ids+NEW_IDS)
        check(lang+" complete chapter sequence is 0 through 67",
              list(map(int,re.findall(r'^# (\d+)\.',text,re.M)))==list(range(68)))
        check(lang+" chapter-67 sections are complete and unique",
              re.findall(r'^## (67\.\d+)\b',chunks[lang],re.M)==["67."+str(n) for n in range(1,13)])
        check(lang+" version explicitly declares 3.8", bool(re.search(r'^version:\s*"3\.8"\s*$',text,re.M)))
        anchors=re.findall(r'<a id="([^"]+)"></a>',text)
        check(lang+" stable anchors are unique",len(anchors)==len(set(anchors)))
        for rid in NEW_IDS:
            row=next(r for r in parsed[lang] if r["id"]==rid)
            check(lang+" exact new title "+rid,row["title"]==EXPECTED_TITLES[rid][0 if lang=="zh" else 1])
            check(lang+" new result is in chapter 67 "+rid,row["chapter"]==67)
    for z,e in zip(parsed["zh"][-9:],parsed["en"][-9:]):
        mapping.append({"id":z["id"],"chapter":67,"zh_title":z["title"],"en_title":e["title"]})
    displays={lang:display_blocks(chunks[lang]) for lang in chunks}
    check("chapter-67 displays are exactly bilingual-identical",displays["zh"]==displays["en"])
    check("chapter-67 has twelve reviewed display blocks",len(displays["zh"])==12)
    joined="\n".join(displays["zh"])
    for literal in ["3673/102400", "1447/102400", "65/4096+1/50", "1369/2500", "49/50"]:
        check("reviewed display constant "+literal,literal in joined)
    check("Chinese explicitly separates trace-class paper proof from finite Lean",
          "书面证明" in chunks["zh"] and "Lean" in chunks["zh"] and "自动扩域" in chunks["zh"])
    check("English explicitly separates analytic/finite machine scope",
          "paper" in chunks["en"].lower() and "Lean" in chunks["en"] and
          ("extend" in chunks["en"].lower() or "enlarge" in chunks["en"].lower()))
    check("both languages explicitly mark synthetic records",
          "合成" in chunks["zh"] and "synthetic" in chunks["en"].lower())
    check("both languages retain actual preparation failure",
          "准备失败" in chunks["zh"] and "preparation-failure" in chunks["en"])

    # This validates explicit evidence boundaries and source declarations; it
    # does not replace the separately executed Lean compiler/axiom auditor.
    lean_source=read(NEW_LEAN_FILE);lean_code=strip_lean_comments(lean_source)
    check("new Lean source has no sorry or new axiom declaration",
          not re.search(r'\bsorry\b|(?m:^\s*axiom\s)',lean_code))
    decls=set(re.findall(r'(?m)^\s*(?:theorem|lemma|def|abbrev|structure)\s+([A-Za-z0-9_\u0080-\uffff]+)',lean_code))
    for rid,names in EXPECTED_LEAN_NAMES.items():
        for name in names:check("actual declared bridge "+name,name in decls)
    for rid in NEW_IDS:
        if rid not in now_by_id:continue
        row=now_by_id[rid];kinds=row.get("verification_kind",[])
        scope=scope_text(row)
        if not row.get("verification_scope") and not row.get("type_responsibility"):
            pending.append(rid+" needs explicit verification/type responsibility")
        if rid not in EXPECTED_LEAN_NAMES:
            check(rid+" does not classify its analytic increment as Lean accepted","lean" not in kinds)
        elif "lean" in kinds:
            bindings=binding_rows(row)
            if not bindings:
                pending.append(rid+" declares lean but has no explicit formal bindings")
            audit_refs=[]
            if row.get("formal_audit_ref"):audit_refs.append(row["formal_audit_ref"])
            for binding in bindings:
                if binding.get("actual_named_audit_receipt"):
                    audit_refs.append(binding["actual_named_audit_receipt"])
            if not audit_refs:
                pending.append(rid+" declares lean but has no actual compiler/axiom receipt reference")
            for ref in sorted(set(audit_refs)):
                if not (repo/ref).exists():
                    pending.append(rid+" actual machine receipt not yet present: "+ref)
                else:
                    read(ref)  # Bind exact receipt bytes; do not re-execute Lean.
            for binding in bindings:
                path=binding.get("file",binding.get("path"))
                if not path:
                    pending.append(rid+" has a formal binding without a source path");continue
                if not (repo/path).exists():
                    pending.append(rid+" missing formal source "+path);continue
                source=read(path)
                expected=binding.get("sha256")
                if expected:check(rid+" binding source identity "+path,expected==digest(source.encode()))
                names=([binding["declaration"]] if binding.get("declaration") else binding.get("declarations",[]))
                for name in names:
                    short=name.rsplit(".",1)[-1]
                    check(rid+" bound name occurs in actual source "+name,
                          bool(re.search(r'\b(?:theorem|lemma|def|abbrev|structure)\s+'+re.escape(short)+r'\b',strip_lean_comments(source))))
            if rid=="P-OPT-03" and not row.get("paper_only") and "paper" not in scope.lower() and "书面" not in scope:
                pending.append("P-OPT-03 must distinguish elementary Lean congruences from the paper full OPT/tree quotient")
    map_rel=book+"PHYSICS_RESULT_MAPPING.md"
    if (repo/map_rel).exists():
        map_text=read(map_rel)
        if not all(rid in map_text for rid in NEW_IDS):
            pending.append("Derived bilingual result mapping has not yet received all nine new IDs")
    else:pending.append("Derived bilingual result mapping is absent")

    changed=[p for p,h in inputs.items() if digest((repo/p).read_bytes())!=h]
    check("all consumed bytes remained stable during this check",not changed,changed)
    return {"schema":"ueot_physics.v3.8.increment-independent/1",
            "status":"PASS" if not pending else "CONTENT_PASS_METADATA_PENDING",
            "executed_at_utc":datetime.now(timezone.utc).isoformat(),
            "prior_result_count":173,"new_result_count":9,"total_result_count":182,
            "historical_result_object_identity":"EXACTLY_PRESERVED",
            "historical_result_objects_sha256":digest(json.dumps(old_results,ensure_ascii=False,sort_keys=True,separators=(",",":")).encode()),
            "new_result_mapping":mapping,
            "chapter67_display_math":{"count":12,"bilingual_literal_identity":True,
                                       "sha256":[digest(x.encode()) for x in displays["zh"]]},
            "checks":checks,"pending_integration":pending,"consumed_sha256":inputs,
            "limits":["Textual identity and scope validation, not proof of theorem truth",
                      "No new Lean execution or axiom acceptance inferred by this checker",
                      "No PDF visual acceptance, remote publication or hardware verification"]}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root",type=Path,required=True)
    parser.add_argument("--output",type=Path,required=True)
    parser.add_argument("--require-complete",action="store_true")
    args=parser.parse_args()
    try:
        report=inspect(args.repo_root.resolve())
    except (ValueError,KeyError,FileNotFoundError,json.JSONDecodeError) as exc:
        report={"schema":"ueot_physics.v3.8.increment-independent/1","status":"FAIL",
                "error":str(exc),"executed_at_utc":datetime.now(timezone.utc).isoformat()}
    report["checker_sha256"]=digest(Path(__file__).read_bytes())
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,ensure_ascii=False,indent=2)+"\n")
    print(json.dumps({k:report[k] for k in ["status","pending_integration","error"] if k in report},ensure_ascii=False))
    if report["status"]=="FAIL":return 2
    if args.require_complete and report.get("pending_integration"):return 3
    return 0


if __name__=="__main__":sys.exit(main())
