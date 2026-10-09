#!/usr/bin/env python3
"""Read the Lean elaborator's ACTUAL proof bodies for all 106 canonically
indexed theorem constants, not just source text, imports, or lexical names.

Only DIRECT referenced first-party UEOT constants are reported. This is
not a transitive semantic equivalence audit or a scientific certification.
Never edits frozen sources or counted governance.
"""
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
import json
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
LEAN_ROOT = HERE.parents[3]
ATLAS = HERE / "UMC_00_SOURCE_ATLAS_V1.json"
OUT = HERE / "UMC_CORE_106_ELABORATED_DECL_DAG_V1.json"
PREFIX = "UMC_TRUE_DEP|"

def canonical_selection():
    source = json.loads(ATLAS.read_text())
    records = []
    for r in source["records"]:
        choices = r["document_referenced_locations"]
        assert choices, (r["pid"], "no literal cited theorem")
        e = next((a for a in choices
                  if a["reference_kind"] == "CANONICAL_COUNTED_LEDGER"),
                 choices[0])
        records.append({"pid": r["pid"], "name": e["symbol"],
                        "source": e["path"], "line": e["line"]})
    assert len(records) == len({r["pid"] for r in records}) == 106
    return records

def main():
    records = canonical_selection()
    names = ",\n".join(
        '    (\x60' + r["name"] + ', "' + r["pid"] + '")'
        for r in records)
    lean = """import UEOT
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let names : Array (Name × String) := #[
""" + names + """
  ]
  for (name, pid) in names do
    match env.find? name with
    | some (.thmInfo decl) =>
        let proof := (decl.value.getUsedConstants.toList.filter
          fun x => x.toString.startsWith "UEOT.").map toString
        let statement := (decl.type.getUsedConstants.toList.filter
          fun x => x.toString.startsWith "UEOT.").map toString
        liftIO <| IO.println s!"UMC_TRUE_DEP|{pid}|{name}|{String.intercalate "," proof}|{String.intercalate "," statement}"
    | some _ => throwError "canonical symbol is not theorem: {name}"
    | none => throwError "canonical symbol missing: {name}"
"""
    with tempfile.TemporaryDirectory(prefix="umc-106-elaborated-dag-") as t:
        file = Path(t) / "Audit.lean"
        file.write_text(lean)
        p = subprocess.run(["lake", "env", "lean", str(file)],
                           cwd=LEAN_ROOT, capture_output=True, text=True,
                           timeout=300)
    rows = {}
    for line in p.stdout.splitlines():
        if not line.startswith(PREFIX):
            continue
        parts = line.split("|", 4)
        if len(parts) != 5:
            raise ValueError(("invalid Lean log line", line[:400]))
        _, pid, name, proof, statement = parts
        if pid in rows or not name:
            raise ValueError(("duplicate/missing", pid))
        rows[pid] = {
            "name": name,
            "proof_direct_ueot_constants": sorted(set(filter(None, proof.split(",")))),
            "type_direct_ueot_constants": sorted(set(filter(None, statement.split(",")))),
        }
    if p.returncode or set(rows) != {r["pid"] for r in records}:
        print("UMC_DEP_AUDIT_ERROR", p.returncode, len(rows),
              (p.stdout+p.stderr)[-1800:])
        return 1
    canon_by_name = {r["name"]: r["pid"] for r in records}
    report = []
    for r in records:
        x = rows[r["pid"]]
        direct_counted = sorted({canon_by_name[n] for n in x["proof_direct_ueot_constants"]
                                 if n in canon_by_name and n != r["name"]})
        report.append({**r, **x,
                       "direct_counted_pid_deps": direct_counted,
                       "direct_local_proof_constant_count": len(x["proof_direct_ueot_constants"]),
                       "direct_local_type_constant_count": len(x["type_direct_ueot_constants"]),
                       "scientific_semantic_revalidation": "NOT_PERFORMED"})
    edges = {r["pid"]: r["direct_counted_pid_deps"] for r in report}
    visiting, done = set(), set()
    def visit(node):
        if node in visiting:
            raise ValueError("cyclic direct proof dependency: " + node)
        if node in done:
            return
        visiting.add(node)
        for dep in edges[node]:
            visit(dep)
        visiting.remove(node)
        done.add(node)
    for node in edges:
        visit(node)
    usage = Counter(ref for row in report
                    for ref in row["proof_direct_ueot_constants"])
    result = {
        "schema": 1,
        "scope": "LEAN_ENV_ELABORATED_ONE_HOP_PROOF_AND_TYPE_CONSTANTS_FOR_106_COUNTED_SYMBOLS",
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "checked_count": 106,
        "root": "UEOT",
        "proof_direct_counted_edges": sum(len(x) for x in edges.values()),
        "direct_counted_graph_acyclic": True,
        "local_first_party_reuse_top20": usage.most_common(20),
        "records": report,
        "limits": [
            "Not a transitive theorem derivation DAG, only direct constant occurrences",
            "A proof may depend on imported non-UEOT Mathlib and Lean constants not listed here",
            "A kernel-checked proof can still formalize a scientific claim with stronger or different premises",
            "This does not audit external physical data, model truth, or independent source semantics"
        ]
    }
    OUT.write_text(json.dumps(result,ensure_ascii=False,indent=2)+"\n")
    print("UMC_106_TRUE_DEP_AUDIT_PASS",json.dumps({
        "records":106,"direct_counted_edges":result["proof_direct_counted_edges"],
        "direct_counted_graph_acyclic":True,
        "top_first_party_reuse":result["local_first_party_reuse_top20"][:5]}))
    return 0

if __name__ == "__main__":
    sys.exit(main())
