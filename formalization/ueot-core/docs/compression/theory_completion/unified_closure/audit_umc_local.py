#!/usr/bin/env python3
"""UMC local exact-head and canonical-source audit; no network/push operations.

This complements the already merged immutable UMC mission validator. It
does NOT purport to certify empirical facts, semantic completeness, or
cross-theorem source independence merely from a static scan.
"""
from pathlib import Path
from collections import Counter
from hashlib import sha256
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
    """Prefer fetched origin/main; use local main only for offline fallback.

    Fail closed if neither exists: diff-scope governance must not be
    silently bypassed by comparing against HEAD itself.
    """
    for candidate in ("refs/remotes/origin/main", "refs/heads/main"):
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


def validate_global_source_dag(core=None, dag_path=None):
    """Read-only source freshness gate, independent of UMC scientific-stage claims.

    Both the full UMC audit and the mandatory freshness regression use this
    exact check. A receipt-writer unit test must not be its accidental caller.
    Explicit paths support small adversarial fixtures without touching source.
    """
    core = CORE if core is None else Path(core)
    dag_path = (HERE / "UMC_GLOBAL_MODULE_DAG_V4.json"
                if dag_path is None else Path(dag_path))
    umc_count = len(list((core / "UEOT/V3/Compression/TheoryCompletion/UnifiedClosure").glob("*.lean")))
    global_dag=json.loads(dag_path.read_text())
    if (global_dag.get('cycles_detected') or global_dag.get('missing_internal_imports')
        or global_dag['not_reachable_from_UEOT_root']
        or global_dag['reachable_from_UEOT_root'] != global_dag['total_Lean_modules']):
        raise RuntimeError('entire UEOT Lean import graph not closed')
    # Exact current source accounting; an older passing receipt cannot hide
    # new modules, missing modules, or modified source bytes.
    current_sources = sorted([core / 'UEOT.lean', *list((core/'UEOT').rglob('*.lean'))])
    actual_modules = {
        f.relative_to(core).with_suffix('').as_posix().replace('/', '.'): f
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
    if global_dag['category_counts'].get('UMC_New_Bridges') != umc_count:
        raise RuntimeError('stale global DAG: UMC module count mismatch')
    return global_dag


def write_audit_receipt(result, *, full, output=None):
    """Write only an explicit new full receipt; historical OUT is immutable."""
    if not full or output is None:
        return
    target = Path(output)
    historical = {path.resolve() for path in HERE.glob("UMC_LOCAL_EXACT_HEAD_AUDIT_V*.json")}
    historical.add(OUT.resolve())
    if target.resolve() in historical:
        raise RuntimeError("HISTORICAL_UMC_RECEIPT_IS_IMMUTABLE")
    target.write_text(json.dumps(result,indent=2,ensure_ascii=False)+"\n")


def discover_umc_theorem_candidates(files):
    """Reuse FKRG's existing lexical discovery, including nested namespaces.

    The result is a candidate list only. Full verification enumerates compiled
    source modules independently and does not trust this list for axiom scope.
    """
    knowledge = HERE.parent / "knowledge"
    sys.path.insert(0, str(knowledge))
    import fkrg
    found = []
    for path in files:
        module = path.relative_to(CORE).with_suffix("").as_posix().replace("/", ".")
        declarations, _ = fkrg.extract(module, path)
        found.extend(row[5] for row in declarations
                     if row[3] in ("theorem", "lemma")
                     and not row[5].startswith("private@"))
    return found


def render_native_umc_audit(source_modules):
    """Compiler-source-module census and transitive native axiom rejection."""
    lines = [
        "import UEOT.V3.Compression.TheoryCompletion",
        "import Lean.Util.CollectAxioms",
        "import Lean.Elab.Command",
        "open Lean Elab Command",
        "run_cmd do",
        "  let env ← getEnv",
        "  let sourceModules : Array Name := #[",
        *[f"    `{module}," for module in sorted(source_modules)],
        "  ]",
        "  for sourceModule in sourceModules do",
        "    unless env.header.moduleNames.contains sourceModule do",
        '      throwError s!"UMC_COMPILED_SOURCE_MODULE_MISSING {sourceModule}"',
        "  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]",
        "  let mut rows : Array Json := #[]",
        "  for (name, info) in env.constants.toList do",
        "    if let .thmInfo _ := info then",
        "      if let some idx := env.getModuleIdxFor? name then",
        "        let sourceModule := env.header.moduleNames[idx]!",
        "        if sourceModules.contains sourceModule then",
        "          let actual ← Lean.collectAxioms name",
        "          let unexpected := actual.filter fun ax => !allowed.contains ax",
        "          unless unexpected.isEmpty do",
        '            throwError s!"UMC_NONSTANDARD_AXIOM {name}: {unexpected}"',
        "          rows := rows.push <| Json.mkObj [",
        '            ("name", toJson name.toString),',
        '            ("source_module", toJson sourceModule.toString),',
        '            ("is_private", toJson (Lean.privateToUserName? name).isSome),',
        '            ("axioms", toJson (actual.map Name.toString))]',
        '  unless rows.size > 0 do throwError "UMC_NATIVE_SCOPE_EMPTY"',
        "  let report := Json.mkObj [",
        '    ("schema", toJson "UMC_NATIVE_AXIOM_CENSUS_V1"),',
        '    ("source_modules", toJson (sourceModules.map Name.toString)),',
        '    ("theorems", toJson rows)]',
        '  liftIO <| IO.println ("UMC_NATIVE_AUDIT_JSON " ++ report.compress)',
    ]
    return "\n".join(lines) + "\n"


def parse_native_umc_audit(printed, source_modules, source_candidates, stage_symbols):
    """Validate the one structured record produced by an exit-zero Lean run.

    No human `#print axioms` formatting or logical namespace-prefix guessing is
    used. Private and other native constants remain in the verification scope.
    """
    marker = "UMC_NATIVE_AUDIT_JSON "
    lines = [line for line in printed.splitlines() if line.strip()]
    if len(lines) != 1 or not lines[0].startswith(marker):
        raise RuntimeError("unrecognized native UMC audit output")
    report = json.loads(lines[0][len(marker):])
    if report.get("schema") != "UMC_NATIVE_AXIOM_CENSUS_V1":
        raise RuntimeError("unsupported native UMC audit schema")
    expected = set(source_modules)
    reported = report.get("source_modules", [])
    if len(reported) != len(expected) or set(reported) != expected:
        raise RuntimeError("native UMC compiled module scope mismatch")
    rows = report.get("theorems", [])
    if not rows or not isinstance(rows, list):
        raise RuntimeError("empty native UMC theorem census")
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    names = set()
    public_names = set()
    private_count = 0
    for row in rows:
        name = row.get("name")
        if not isinstance(name, str) or not name or name in names:
            raise RuntimeError("missing or duplicate native UMC theorem name")
        if row.get("source_module") not in expected:
            raise RuntimeError("native UMC theorem outside compiled source scope")
        if type(row.get("is_private")) is not bool:
            raise RuntimeError("invalid native UMC private-name classification")
        actual = row.get("axioms")
        if not isinstance(actual, list) or any(not isinstance(a, str) for a in actual):
            raise RuntimeError("invalid native UMC axiom report")
        if not set(actual).issubset(allowed):
            raise RuntimeError("additional nonstandard axiom found: " + str(actual))
        names.add(name)
        private_count += row["is_private"]
        if not row["is_private"]:
            public_names.add(name)
    missing_stage = sorted(set(stage_symbols) - names)
    if missing_stage:
        raise RuntimeError("stage cites missing compiled local theorem: " + str(missing_stage))
    confirmed_source = set(source_candidates) & public_names
    return {
        "theorem_constants": len(rows),
        "private_theorem_constants": private_count,
        "confirmed_public_source_candidates": len(confirmed_source),
        "other_native_public_constants": len(rows) - private_count - len(confirmed_source),
        "source_modules": len(expected),
        "scope_authority": "Lean compiled source modules, including private and generated theorem constants",
        "other_native_public_scope": "Native nonprivate constants outside the FKRG source candidate list; typically generated, not inferred to be source declarations",
    }


def audit(full, *, output=None):
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
    found = discover_umc_theorem_candidates(files)
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
    global_dag=validate_global_source_dag()
    source_atlas=Counter(r['mapping_status'] for r in atlas['records'])
    axioms_result="NOT_RUN"
    native_census=None
    if full:
        # Rebuild first: native inspection must not read stale compiled modules.
        build=run(["lake","build","UEOT"],cwd=CORE)
        if "Build completed successfully" not in build:
            raise RuntimeError("full Lean build missing success marker")
        source_modules=[p.relative_to(CORE).with_suffix("").as_posix().replace("/", ".")
                        for p in files]
        import tempfile
        with tempfile.TemporaryDirectory(prefix="ueot-umc-lean-") as td:
            source=Path(td)/"UMCAxiomAudit.lean"
            source.write_text(render_native_umc_audit(source_modules))
            printed=run(["lake","env","lean",str(source)],cwd=CORE)
            native_census=parse_native_umc_audit(
                printed,source_modules,found,
                [name for stage in stages["stages"] for name in stage.get("symbols",[])])
            count=native_census["theorem_constants"]
            axioms_result=f"{count}/{count}_LEAN_STANDARD_AXIOMS"
    result={
      # A committed receipt cannot embed its own HEAD SHA: that would
      # invalidate the receipt by changing the HEAD on every commit.
      # Exact verified Git identity is printed by the CLI after validation.
      "canonical_main":run(["git","rev-parse",baseline]).strip(),
      "research_modules":len(files),"UMC_theorems_and_lemmas":len(found),
      "source_PIDs_located":len(atlas["records"]),
      "source_provenance":dict(source_atlas),
      "UMC_axioms":axioms_result,
      "UMC_source_count_authority":"FKRG_LEXICAL_PUBLIC_CANDIDATES",
      "UMC_native_census":native_census,
      "full_Lean":("PASS" if full else "NOT_RUN"),
      "public_root_imports":len(imports),
      "global_bundled_Lean_modules":global_dag['total_Lean_modules'],
      "full_import_dag_acyclic_reachable_complete":True,
      "frozen_source_impact":"NONE",
      "claim":"CONDITIONAL_COMMON_PROCESS_CONSTRUCTION_AND_BOUNDARIES",
      "global_strong_unified_closure":"NOT_ESTABLISHED",
      "scientific_external_evidence":"UNVERIFIED",
      "publication_actions":"NOT_PERFORMED_BY_THIS_READ_ONLY_AUDIT",
      "epistemic_scope":"Proof validity is conditional on actual theorem premises; file/declaration index is not an independent semantic audit."
    }
    # Fast checks are transient: preserve the committed full-axiom receipt.
    write_audit_receipt(result, full=full, output=output)
    return result

if __name__=="__main__":
    ap=argparse.ArgumentParser()
    ap.add_argument("--full",action="store_true")
    ap.add_argument("--output",type=Path,help="Optional new full receipt; historical receipt is immutable")
    args=ap.parse_args()
    try:
        value=audit(args.full,output=args.output)
    except Exception as e:
        print("UMC_LOCAL_AUDIT_FAIL",str(e),file=sys.stderr)
        sys.exit(1)
    print("UMC_LOCAL_AUDIT_PASS",json.dumps(value,sort_keys=True))
    print("UMC_VERIFIED_GIT_HEAD",run(["git", "rev-parse", "HEAD"]).strip())
