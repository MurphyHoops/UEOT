#!/usr/bin/env python3
"""Check all 106 indexed canonical theorem symbols with the Lean elaborator.

This verifies that documented declaration names typecheck in the full UEOT
root and records AXIOM dependency output. It CANNOT establish semantic
equivalence of each statement to natural-language claims or remove required
premises. It never edits frozen Lean sources or counted governance ledgers.
"""
from pathlib import Path
import json
import re
import subprocess
import sys
import tempfile
from datetime import datetime, timezone

HERE = Path(__file__).resolve().parent
LEAN_ROOT = HERE.parents[3]  # formalization/ueot-core
ATLAS = HERE / "UMC_00_SOURCE_ATLAS_V1.json"
OUT = HERE / "UMC_CORE_106_ELABORATION_AUDIT_V1.json"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

def main():
    source = json.loads(ATLAS.read_text())
    records = source["records"]
    assert len(records) == 106 and len({r["pid"] for r in records}) == 106
    selected = []
    for r in records:
        entries = r["document_referenced_locations"]
        assert entries, r["pid"]
        entry = next((x for x in entries if x["reference_kind"] == "CANONICAL_COUNTED_LEDGER"), entries[0])
        selected.append({"pid": r["pid"], "symbol": entry["symbol"], "source_path": entry["path"],
                         "source_line": entry["line"], "source_kind": entry["reference_kind"],
                         "source_status": r["final_disposition"]})
    seen = set()
    # Multiple P-IDs may cite the same Lean declaration. Execute only once
    # but retain every P-ID record; shared symbols are NOT independent proofs.
    unique = []
    for r in selected:
        if r["symbol"] not in seen:
            unique.append(r["symbol"])
            seen.add(r["symbol"])
    with tempfile.TemporaryDirectory(prefix="ueot-106-lean-check-") as t:
        src = Path(t) / "Audit.lean"
        src.write_text("import UEOT\n\n" + "".join(
            f"#check {name}\n#print axioms {name}\n" for name in unique))
        proc = subprocess.run(["lake", "env", "lean", str(src)], cwd=LEAN_ROOT,
                              capture_output=True, text=True, timeout=300)
    raw = proc.stdout + "\n" + proc.stderr
    errors = re.findall(r"^.*?error:.*$", raw, flags=re.MULTILINE)
    # Each '#print axioms' line starts with a quote and contains its symbol.
    axiom_segments = {}
    for m in re.finditer(r"'([^'\n]+)' depends on axioms: \[([^]]*)\]", raw):
        name = m.group(1)
        axioms = [a.strip() for a in m.group(2).split(",") if a.strip()]
        axiom_segments[name] = axioms
    for m in re.finditer(r"'([^'\n]+)' does not depend on any axioms", raw):
        axiom_segments[m.group(1)] = []
    for r in selected:
        r["lean_elaboration"] = "CHECKED" if proc.returncode == 0 else "NOT_CERTIFIED"
        r["axioms"] = axiom_segments.get(r["symbol"])
        r["semantic_equivalence_to_source"] = "NOT_INDEPENDENTLY_REVIEWED"
        r["custom_axiom_dependencies"] = sorted(set(r["axioms"] or []) - ALLOWED)
    result = {
        "schema": 1,
        "scope": "106_CANONICAL_LEDGER_SYMBOL_ELABORATION_AND_AXIOMS_NOT_SEMANTIC_CERTIFICATION",
        "generated_utc": datetime.now(timezone.utc).isoformat(),
        "input": str(ATLAS.relative_to(LEAN_ROOT)),
        "root_import": "UEOT",
        "theorems_count": len(records),
        "unique_symbols_count": len(unique),
        "lean_exit_code": proc.returncode,
        "axiom_printouts_parsed": len(axiom_segments),
        "custom_axiom_dependent_pid_count": sum(bool(r["custom_axiom_dependencies"]) for r in selected),
        "errors": errors[:60],
        "records": selected,
    }
    OUT.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    print("UEOT_106_ELABORATION", json.dumps({
        "theorems": result["theorems_count"], "unique_symbols": result["unique_symbols_count"],
        "lean_exit_code": proc.returncode, "axiom_printouts_parsed": len(axiom_segments),
        "custom_axiom_dependent_pids": result["custom_axiom_dependent_pid_count"],
        "errors": errors[:5]}, ensure_ascii=False))
    if proc.returncode != 0:
        print("LEAN_DEBUG_TAIL", raw[-2800:])
    return 0 if proc.returncode == 0 and len(axiom_segments) == len(unique) else 1

if __name__ == "__main__":
    sys.exit(main())
