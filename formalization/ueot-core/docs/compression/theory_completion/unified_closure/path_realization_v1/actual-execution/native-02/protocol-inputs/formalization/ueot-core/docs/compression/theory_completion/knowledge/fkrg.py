#!/usr/bin/env python3
"""FKRG v1: fresh lexical source discovery + kernel symbol verification.

Source-derived indexes are NEVER normative mathematical proofs or alternate ledgers.
Use 'lean-check' for actual resolved Lean symbols and types before theorem reuse.
"""
import argparse
from collections import defaultdict
from hashlib import sha256
import json
from pathlib import Path
import os
import re
import sqlite3
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
CORE = HERE.parents[3]
REPO = CORE.parents[1]
TASKS = HERE / "FKRG_TASKS.json"
DEFAULT_DB = Path(os.environ.get("UEOT_FKRG_DB", "/tmp/ueot-fkrg-index.sqlite3"))
INDEX_SCHEMA = "FKRG_V2"

sys.path.insert(0, str(HERE.parent / "unified_closure"))
from audit_umc_local import no_lean_comments

# The extractor is a composition: declaration matching *and* imported Lean
# comment removal. Both source files are effective parser inputs.
COMMENT_PARSER_PATH = Path(sys.modules[no_lean_comments.__module__].__file__).resolve()


def extractor_fingerprint():
    h = sha256()
    for label, path in (("fkrg.py", Path(__file__).resolve()),
                        ("lean-comment-parser", COMMENT_PARSER_PATH)):
        h.update(label.encode("ascii"))
        h.update(b"\x00")
        h.update(path.read_bytes())
        h.update(b"\x00")
    return h.hexdigest()


# Attributes and qualified names are part of valid Lean declarations.
# This is a lexical candidate extractor; semantic equivalence is not claimed.
DECL = re.compile(
    r"^\s*(?:(?:@\[[^\]\n]*\]|private|protected|noncomputable|unsafe|irreducible|partial)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|inductive)\s+"
    r"([A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*)\b"
)
SCOPE = re.compile(r"^\s*(namespace|section|end)\b(?:\s+(\S+))?")
IMPORT = re.compile(r"^\s*import\s+(\S+)")

def git(*args):
    p = subprocess.run(["git", *args],cwd=REPO,capture_output=True,text=True)
    if p.returncode: raise RuntimeError(p.stderr or p.stdout)
    return p.stdout.strip()

def sources():
    fs = [CORE / "UEOT.lean", *(CORE / "UEOT").rglob("*.lean")]
    return {p.relative_to(CORE).with_suffix("").as_posix().replace("/", "."):p
            for p in fs if p.is_file()}

def fingerprint(mapping):
    h=sha256()
    for name,path in sorted(mapping.items()):
        h.update(name.encode()); h.update(bytes([0]))
        h.update(path.read_bytes()); h.update(bytes([0]))
    return h.hexdigest()

def extract(module,path):
    raw=path.read_text(encoding="utf-8")
    lines=raw.splitlines()
    code=no_lean_comments(raw).splitlines()
    ns=""; stack=[]; declarations=[]; imports=[]
    for i,line in enumerate(code):
        im=IMPORT.match(line)
        if im: imports.append(im.group(1))
        match=SCOPE.match(line)
        if match:
            op,arg=match.groups()
            if op=="namespace":
                stack.append(ns)
                ns=(ns+"." if ns else "")+(arg or "")
            elif op=="section":stack.append(ns)
            elif op=="end" and stack:ns=stack.pop()
        m=DECL.match(line)
        if not m: continue
        kind,local_qualified=m.groups()
        simple=local_qualified.rsplit(".",1)[-1]
        # Lean elaborates private names to mangled, module-unique constants:
        # two source-private helpers may have the SAME apparent user name.
        # Never index them as publicly reusable declarations.
        is_private = re.search(r"\bprivate\b",line[:m.start(1)]) is not None
        candidate = (f"private@{module}:{i+1}:{local_qualified}" if is_private else
                     (ns+"." if ns else "")+local_qualified)
        snippet=" ".join(x.strip() for x in lines[i:min(i+6,len(lines))])
        before="\n".join(lines[max(0,i-12):i])
        pos=before.rfind("/--")
        doc=before[pos:].split("-/")[0][3:].strip() if pos>=0 and "-/" in before[pos:] else ""
        declarations.append((module,str(path.relative_to(REPO)),i+1,kind,simple,
                             candidate,snippet[:1600],doc[:1600]))
    return declarations,imports

def build(db):
    mapping=sources()
    db.parent.mkdir(parents=True,exist_ok=True)
    new=db.with_name(db.name+".new")
    if new.exists():new.unlink()
    c=sqlite3.connect(new)
    try:
        c.executescript("""
        CREATE TABLE meta(key TEXT PRIMARY KEY,value TEXT);
        CREATE TABLE modules(name TEXT PRIMARY KEY,path TEXT,imports_json TEXT);
        CREATE TABLE declarations(id INTEGER PRIMARY KEY,module TEXT,path TEXT,
          line INTEGER,kind TEXT,simple TEXT,candidate TEXT,excerpt TEXT,doc TEXT);
        CREATE INDEX idx_candidate ON declarations(candidate);
        CREATE INDEX idx_simple ON declarations(simple);
        CREATE VIRTUAL TABLE search USING fts5(simple,candidate,excerpt,doc,path,
          content='declarations',content_rowid='id');
        """)
        count=0
        for name,path in sorted(mapping.items()):
            entries,imports=extract(name,path)
            c.execute("INSERT INTO modules VALUES(?,?,?)",
                      (name,str(path.relative_to(REPO)),json.dumps(imports)))
            c.executemany("""INSERT INTO declarations
              (module,path,line,kind,simple,candidate,excerpt,doc)
              VALUES(?,?,?,?,?,?,?,?)""",entries)
            count+=len(entries)
        c.execute("INSERT INTO search(search) VALUES('rebuild')")
        meta={"schema":INDEX_SCHEMA,
              # Source-only fingerprints are insufficient: fixed extractor
              # code must invalidate databases made by the old parser.
              "extractor_sha256":extractor_fingerprint(),
              "source_tree_sha256":fingerprint(mapping),
              "module_count":str(len(mapping)),"declaration_count":str(count),
              "git_head_at_build":git("rev-parse","HEAD"),
              "type_authority":"LEXICAL_CANDIDATES_REQUIRE_KERNEL_VERIFICATION"}
        c.executemany("INSERT INTO meta VALUES (?,?)",meta.items())
        c.commit()
    finally:c.close()
    new.replace(db)
    print("INDEX_BUILT",json.dumps(meta,ensure_ascii=False))

def fresh(db):
    if not db.is_file():raise RuntimeError("INDEX_MISSING: run build")
    c=sqlite3.connect(db);c.row_factory=sqlite3.Row
    meta=dict(c.execute("SELECT key,value FROM meta").fetchall())
    live=sources()
    if (meta.get("schema")!=INDEX_SCHEMA or
        meta.get("extractor_sha256")!=extractor_fingerprint() or
        meta.get("source_tree_sha256")!=fingerprint(live) or
        int(meta.get("module_count","0"))!=len(live)):
        c.close();raise RuntimeError("STALE_INDEX: source or extractor dependency changed, run build")
    return c,meta

def find(c,query,limit,details):
    terms=re.findall(r"\w+",query)
    rows=[]
    if terms:
        q=" OR ".join('"'+t+'"' for t in terms[:12])
        try:
            rows=c.execute("""SELECT d.* FROM search JOIN declarations d ON d.id=search.rowid
                 WHERE search MATCH ? ORDER BY bm25(search) LIMIT ?""",(q,limit)).fetchall()
        except sqlite3.OperationalError:pass
    if not rows:
        pat="%"+query.lower()+"%"
        rows=c.execute("""SELECT * FROM declarations WHERE lower(simple) LIKE ?
            OR lower(candidate) LIKE ? OR lower(excerpt) LIKE ? OR lower(doc) LIKE ?
            LIMIT ?""",(pat,pat,pat,pat,limit)).fetchall()
    for row in rows:
        print(f"{row['candidate']} [{row['kind']}] {row['path']}:{row['line']}")
        if details:print("  SOURCE_EXCERPT:",row["excerpt"][:350])
    print("CANDIDATES",len(rows),"LEXICAL_NOT_LOGICAL_EQUIVALENCE")

def show(c,symbol):
    rows=c.execute("SELECT * FROM declarations WHERE candidate=? OR simple=? LIMIT 40",
                   (symbol,symbol)).fetchall()
    if not rows:raise RuntimeError("NO_CANDIDATE")
    for r in rows:print(json.dumps(dict(r),ensure_ascii=False,indent=2))

def lean_check(c,symbol):
    if symbol.startswith("private@"):
        raise RuntimeError("PRIVATE_LEAN_DECLARATION_NOT_PUBLICLY_REUSABLE")
    rows=c.execute("SELECT 1 FROM declarations WHERE candidate=? LIMIT 1",(symbol,)).fetchall()
    if not rows:raise RuntimeError("NO_LEXICAL_FULL_NAME; run show")
    with tempfile.TemporaryDirectory(prefix="fkrg-kernel-") as tmp:
        file=Path(tmp)/"Check.lean"
        file.write_text("import UEOT\n#check @"+symbol+"\n")
        p=subprocess.run(["lake","env","lean",str(file)],cwd=CORE,capture_output=True,text=True)
        print(p.stdout[-7000:])
        if p.returncode:raise RuntimeError("LEAN_CHECK_FAILED: "+p.stderr[-2000:])
    print("LEAN_SYMBOL_ELABORATED")

def preflight(c,meta,task_id,output):
    tasks=json.loads(TASKS.read_text())["tasks"]
    t=tasks[task_id]
    found=[];missing=[]
    for sym in t["reuse_symbols"]:
        r=c.execute("SELECT path,line,candidate FROM declarations WHERE candidate=?",
                    (sym,)).fetchall()
        if r:found.extend(dict(x) for x in r)
        else:missing.append(sym)
    result={"task":task_id,"source_tree_sha256":meta["source_tree_sha256"],
      "git_head":git("rev-parse","HEAD"),"reusable_candidates":found,
      "missing":missing,"new_obligations":t["new_obligations"],
      "known_boundaries":t["known_boundaries"],
      "result":"BLOCK_MISSING" if missing else "CANDIDATES_FOUND_KERNEL_CHECK_REQUIRED"}
    if output:Path(output).write_text(json.dumps(result,ensure_ascii=False,indent=2)+"\n")
    print(json.dumps(result,ensure_ascii=False,indent=2))
    if missing:raise RuntimeError("PREFLIGHT_MISSING_REFERENCES")

def impact(c,sym):
    m=c.execute("SELECT DISTINCT module FROM declarations WHERE candidate=?",(sym,)).fetchall()
    if not m:raise RuntimeError("UNKNOWN_CANDIDATE")
    for row in m:
        module=row["module"]
        dependents=[]
        for x in c.execute("SELECT name,imports_json FROM modules"):
            if module in json.loads(x["imports_json"]):dependents.append(x["name"])
        print(json.dumps({"symbol":sym,"module":module,"importing_modules":dependents,
          "scope":"IMPORT_DAG_NOT_DECLARATION_PROOF_DAG"},ensure_ascii=False,indent=2))

def optional_ref(name):
    """Missing remote-tracking refs are normal in offline/detached clones."""
    p=subprocess.run(["git","rev-parse","--verify","--quiet",name],
                     cwd=REPO,capture_output=True,text=True)
    return p.stdout.strip() if p.returncode==0 else None

def status(db):
    try:
        c,meta=fresh(db);c.close();state="FRESH"
    except RuntimeError as e:state=str(e);meta={}
    tasks=json.loads(TASKS.read_text())["tasks"]
    print(json.dumps({"branch":git("branch","--show-current") or "(detached)",
      "head":git("rev-parse","HEAD"),
      "cached_origin_main":optional_ref("refs/remotes/origin/main"),
      "index_state":state,"index":meta,
      "tasks":{k:{"status":v["status"],"next_action":v["next_action"]}
         for k,v in tasks.items()},
      "remote_ci":"NOT_CHECKED_OFFLINE","full_ueot_closure":"NOT_ESTABLISHED"},
      ensure_ascii=False,indent=2))

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--db",type=Path,default=DEFAULT_DB)
    sub=ap.add_subparsers(dest="cmd",required=True)
    for cmd in ["build","status","verify-index"]:sub.add_parser(cmd)
    x=sub.add_parser("find");x.add_argument("query");x.add_argument("--limit",type=int,default=20);x.add_argument("--details",action="store_true")
    for cmd in ["show","lean-check","impact"]:sub.add_parser(cmd).add_argument("symbol")
    x=sub.add_parser("preflight");x.add_argument("--task",required=True);x.add_argument("--output",type=Path)
    a=ap.parse_args()
    if a.cmd=="build":build(a.db);return
    if a.cmd=="status":status(a.db);return
    c,meta=fresh(a.db)
    try:
        if a.cmd=="verify-index":print("INDEX_FRESH",json.dumps(meta))
        elif a.cmd=="find":find(c,a.query,a.limit,a.details)
        elif a.cmd=="show":show(c,a.symbol)
        elif a.cmd=="lean-check":lean_check(c,a.symbol)
        elif a.cmd=="impact":impact(c,a.symbol)
        elif a.cmd=="preflight":preflight(c,meta,a.task,a.output)
    finally:c.close()

if __name__=="__main__":
    try:main()
    except (RuntimeError,KeyError,ValueError,sqlite3.DatabaseError) as e:
        print("FKRG_ERROR",str(e),file=sys.stderr);sys.exit(2)
