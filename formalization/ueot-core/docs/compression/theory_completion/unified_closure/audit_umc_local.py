#!/usr/bin/env python3
"""UMC local exact-head and canonical-source audit; no network/push operations.

This complements the already merged immutable UMC mission validator. It
does NOT purport to certify empirical facts, semantic completeness, or
cross-theorem source independence merely from a static scan.
"""
from pathlib import Path
from collections import Counter
import argparse
import json
import os
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[5]
CORE = ROOT / "formalization/ueot-core"
PROOFS = CORE / "UEOT/V3/Compression/TheoryCompletion/UnifiedClosure"
CANON = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure."
OUT = HERE / "UMC_LOCAL_EXACT_HEAD_AUDIT_V4.json"

def run(cmd, cwd=ROOT):
    p = subprocess.run(cmd, cwd=str(cwd), text=True,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if p.returncode:
        raise RuntimeError(f"EXIT {p.returncode}: {' '.join(map(str,cmd))}\n{p.stdout[-3500:]}")
    return p.stdout

def no_lean_comments(text):
    o=[]; i=0; depth=0; string=False; esc=False; line=False
    while i < len(text):
        c=text[i]; pair=text[i:i+2]
        if line:
            if c=="\n": line=False; o.append("\n")
            else: o.append(" ")
            i+=1; continue
        if depth:
            if pair=="/-":depth+=1;o.extend("  ");i+=2;continue
            if pair=="-/":depth-=1;o.extend("  ");i+=2;continue
            o.append("\n" if c=="\n" else " ");i+=1;continue
        if string:
            if esc:esc=False
            elif c=="\\":esc=True
            elif c=='"':string=False
            o.append("\n" if c=="\n" else " ");i+=1;continue
        if pair=="/-":depth=1;o.extend("  ");i+=2;continue
        if pair=="--":line=True;o.extend("  ");i+=2;continue
        if c=='"':string=True;o.append(" ");i+=1;continue
        o.append(c);i+=1
    if depth:raise RuntimeError("unterminated Lean block comment")
    return "".join(o)

def baseline_main_ref():
    """Use local main or fetched origin/main; a detached CI PR has no main.

    Fail closed if neither exists: diff-scope governance must not be
    silently bypassed by comparing against HEAD itself.
    """
    for candidate in ("refs/heads/main", "refs/remotes/origin/main"):
        p=subprocess.run(["git","rev-parse","--verify","--quiet",candidate],
                         cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.DEVNULL)
        if p.returncode == 0:
            return candidate
    raise RuntimeError("main baseline unavailable: fetch origin main before auditing")



def active_research_branch():
    """Recover original PR branch in detached Actions checkouts; fail closed."""
    p = subprocess.run(["git","symbolic-ref","--quiet","--short","HEAD"],
                       cwd=ROOT,capture_output=True,text=True)
    if p.returncode == 0 and p.stdout.strip():
        return p.stdout.strip()
    return os.environ.get("GITHUB_HEAD_REF") or os.environ.get("HEAD_REF") or None


def validate_tc_local_scope(baseline, branch, changed):
    """Supplement the immutable-base policy, never broaden its path authority.

    Existing file edits under TC must be authorized by the *base* governance
    registry. Newly added TC research artifacts may be additive L1. Unknown
    branch identities may not claim narrow L2 authorizations.
    """
    public_root="formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion.lean"
    owned_prefixes=(
        "formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/",
        "formalization/ueot-core/docs/compression/theory_completion/unified_closure/",
        "formalization/ueot-core/docs/compression/theory_completion/knowledge/",
    )
    baseline_files=set(run(["git","-c","core.quotePath=false","ls-tree",
                            "-r","--name-only",baseline,"--",*owned_prefixes]).splitlines())
    policy_path="formalization/ueot-core/docs/compression/COMPRESSION_RESEARCH_TRACKS.json"
    policy=json.loads(run(["git","show",f"{baseline}:{policy_path}"]))
    authorized=set(policy["tracks"]["TC"].get("mutable_existing_exact_paths",[]))
    if branch:
        for record in policy.get("l2_existing_path_exceptions",[]):
            if record.get("track")!="TC" or record.get("temporary") is not True:
                continue
            if any(isinstance(pattern,str) and re.fullmatch(pattern,branch)
                   for pattern in record.get("branch_patterns",[])):
                authorized.update(record.get("paths",[]))
    violations=[
        path for path in changed
        if not (
            path==public_root or
            (path.startswith(owned_prefixes) and
             (path not in baseline_files or path in authorized))
        )
    ]
    if violations:
        raise RuntimeError("out-of-scope existing-path changes under immutable "
                           "TC source policy: "+str(violations))


def audit(full):
    atlas=json.loads((HERE/"UMC_00_SOURCE_ATLAS_V1.json").read_text())
    if len(atlas['records'])!=106 or len({r['pid'] for r in atlas['records']})!=106:
        raise RuntimeError("missing or duplicate frozen P-ID")
    if any(not r['document_referenced_locations'] for r in atlas['records']):
        raise RuntimeError("source atlas contains an unmapped PID")
    for row in atlas['records']:
        for hit in row['document_referenced_locations']:
            f=ROOT/hit['path']
            lines=f.read_text().splitlines()
            pos=hit['line']
            if not (f.is_file() and 0<pos<=len(lines)):
                raise RuntimeError("invalid sourced declaration location: "+row['pid'])
            name=hit['symbol'].split('.')[-1]
            if not re.search(r'\b(theorem|lemma)\s+'+re.escape(name)+r'\b',
                             lines[pos-1]):
                raise RuntimeError("sourced declaration changed: "+row['pid']+" "+name)
    files=sorted(PROOFS.glob('*.lean'))
    if len(files)<22:raise RuntimeError("UMC local modules incomplete")
    found=[]
    forbidden=re.compile(r"\b(sorry|admit|native_decide)\b|"
                         r"^\s*(?:axiom|opaque)\s",re.M)
    cloudscan=re.compile(r"^\s*(?:axiom|opaque)\s|\b(sorry|admit|native_decide)\b",re.M)
    for p in files:
        text=p.read_text()
        code=no_lean_comments(text)
        if forbidden.search(code) or cloudscan.search(text):
            raise RuntimeError("forbidden escape, including cloud's raw scanner: "+p.name)
        for m in re.finditer(r'^\s*(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_]*)', code,re.M):
            found.append(CANON+m.group(1))
    if len(found)<90 or len(set(found))!=len(found):
        raise RuntimeError("unexpected missing/duplicate UMC theorem names")
    rootfile=CORE/"UEOT/V3/Compression/TheoryCompletion.lean"
    imports=[x for x in rootfile.read_text().splitlines() if
             x.startswith("import "+CANON)]
    if len(imports)!=len(files) or set(x.split()[-1] for x in imports)!={
          CANON+p.stem for p in files}:
        raise RuntimeError("public root misses local proof modules")
    # Git quotes non-ASCII report filenames by default. Disable C-style
    # path escaping for the ACL check; otherwise a valid Chinese-named
    # research report is incorrectly classified as outside Track TC.
    baseline=baseline_main_ref()
    only=run(["git","-c","core.quotePath=false","diff",baseline,"--name-only"]).splitlines()
    validate_tc_local_scope(baseline,active_research_branch(),only)
    # Every local research stage must be explicitly assessed and no stage
    # may silently acquire an unconditional FULL claim via this L1 lane.
    stages=json.loads((HERE/"UMC_LOCAL_STAGE_RESULTS_V3.json").read_text())
    if {x['id'] for x in stages.get('stages',[])} != {
          f'UMC-{n:02}' for n in range(7)} or len(stages.get('stages',[]))!=7:
        raise RuntimeError('seven-stage research evidence incomplete')
    if (stages.get('strong_mathematical_closure') != 'NOT_ESTABLISHED' or
        any(x.get('global_full_stage_claim') or not x.get('independent_open_ports')
            for x in stages['stages'])):
        raise RuntimeError('local report masks unresolved scientific obligations')
    for stage in stages['stages']:
        for name in stage.get('symbols',[]):
            if name not in found:
                raise RuntimeError('stage cites missing local theorem: '+name)
    global_dag=json.loads((HERE/"UMC_GLOBAL_MODULE_DAG_V4.json").read_text())
    if (global_dag.get('cycles_detected') or global_dag.get('missing_internal_imports')
        or global_dag['not_reachable_from_UEOT_root']
        or global_dag['reachable_from_UEOT_root'] != global_dag['total_Lean_modules']):
        raise RuntimeError('entire first-party Lean import graph not closed')
    # Exact current source accounting; an older passing receipt cannot hide
    # new modules, missing modules, or modified source bytes.
    from hashlib import sha256
    current_sources = sorted([CORE / 'UEOT.lean', *list((CORE/'UEOT').rglob('*.lean'))])
    actual_modules = {
        f.relative_to(CORE).with_suffix('').as_posix().replace('/', '.'): f
        for f in current_sources
    }
    if set(actual_modules) != set(global_dag['entries']):
        raise RuntimeError('stale global DAG: module paths disagree with current source')
    digest = sha256()
    for name, path in sorted(actual_modules.items()):
        data = path.read_bytes()
        digest.update(name.encode('utf-8'))
        digest.update(bytes([0]))
        digest.update(data)
        digest.update(bytes([0]))
    # The generator encodes literal zero separators; match them exactly.
    if digest.hexdigest() != global_dag.get('source_tree_sha256'):
        raise RuntimeError('stale global DAG: source fingerprint mismatch')
    if global_dag['total_Lean_modules'] != len(actual_modules):
        raise RuntimeError('stale global DAG: incorrect total modules')
    if global_dag['category_counts'].get('UMC_New_Bridges') != len(files):
        raise RuntimeError('stale global DAG: UMC module count mismatch')
    source_atlas=Counter(r['mapping_status'] for r in atlas['records'])
    axioms_result="NOT_RUN"
    if full:
        import tempfile
        with tempfile.TemporaryDirectory(prefix="ueot-umc-lean-") as td:
            source=Path(td)/"UMCAxiomAudit.lean"
            source.write_text("import UEOT.V3.Compression.TheoryCompletion\n"+
                              "".join("#print axioms "+n+"\n" for n in found))
            printed=run(["lake","env","lean",str(source)],cwd=CORE)
            count=printed.count("depends on axioms")+printed.count("does not depend on any axioms")
            if count!=len(found):
                raise RuntimeError(f"unexpected axiom output {count}/{len(found)}")
            cleaned=re.sub(r"'[^']+' (?:does not depend on any axioms|depends on axioms: \[[^]]*\])","",printed,flags=re.S)
            if cleaned.strip():
                raise RuntimeError("unrecognized axiom audit output: "+cleaned[:700])
            for chunk in re.findall(r"depends on axioms: \[([^]]*)\]",printed,re.S):
                actual={x.strip() for x in chunk.split(",") if x.strip()}
                if not actual.issubset({"propext","Classical.choice","Quot.sound"}):
                    raise RuntimeError("additional nonstandard axiom found: "+str(actual))
            axioms_result=f"{count}/{len(found)}_LEAN_STANDARD_AXIOMS"
        build=run(["lake","build","UEOT"],cwd=CORE)
        if "Build completed successfully" not in build:
            raise RuntimeError("full Lean build missing success marker")
    result={
      # A committed receipt cannot embed its own HEAD SHA: that would
      # invalidate the receipt by changing the HEAD on every commit.
      # Exact verified Git identity is printed by the CLI after validation.
      "canonical_main":run(["git","rev-parse",baseline]).strip(),
      "research_modules":len(files),"UMC_theorems_and_lemmas":len(found),
      "source_PIDs_located":len(atlas["records"]),
      "source_provenance":dict(source_atlas),
      "UMC_axioms":axioms_result,
      "full_Lean":("PASS" if full else "NOT_RUN"),
      "public_root_imports":len(imports),
      "global_first_party_Lean_modules":global_dag['total_Lean_modules'],
      "full_import_dag_acyclic_reachable_complete":True,
      "frozen_source_impact":"NONE",
      "claim":"CONDITIONAL_COMMON_PROCESS_CONSTRUCTION_AND_BOUNDARIES",
      "global_strong_unified_closure":"NOT_ESTABLISHED",
      "scientific_external_evidence":"UNVERIFIED",
      "cloud_push":"FORBIDDEN_BY_THIS_LOCAL_TASK",
      "epistemic_scope":"Proof validity is conditional on actual theorem premises; file/declaration index is not an independent semantic audit."
    }
    # Fast checks are transient: preserve the committed full-axiom receipt.
    if full:
        OUT.write_text(json.dumps(result,indent=2,ensure_ascii=False)+"\n")
    return result

if __name__=="__main__":
    ap=argparse.ArgumentParser()
    ap.add_argument("--full",action="store_true")
    args=ap.parse_args()
    try:
        value=audit(args.full)
    except Exception as e:
        print("UMC_LOCAL_AUDIT_FAIL",str(e),file=sys.stderr)
        sys.exit(1)
    print("UMC_LOCAL_AUDIT_PASS",json.dumps(value,sort_keys=True))
    print("UMC_VERIFIED_GIT_HEAD",run(["git", "rev-parse", "HEAD"]).strip())
