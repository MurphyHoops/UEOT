"""Verify actual Lean axiom reports against the reviewed standard foundation."""

import json
from collections import Counter
from pathlib import Path
import re

root = Path(__file__).resolve().parents[1]
requested = re.findall(r"^#print axioms (\S+)$", (root / "scripts/AxiomAudit.lean").read_text(), re.M)
output = (root / "axiom-audit.log").read_text()
reports = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", output)
if any(count != 1 for count in Counter(requested).values()):
    raise RuntimeError("Duplicate axiom-audit requests")
if any(count != 1 for count in Counter(name for name, _ in reports).values()):
    raise RuntimeError("Duplicate actual Lean axiom reports")
actual = {name: sorted(a.strip() for a in axioms.split(",") if a.strip())
          for name, axioms in reports}
allowed = {"propext", "Classical.choice", "Quot.sound"}
if set(actual) != set(requested):
    raise RuntimeError(f"Missing or unexpected Lean axiom reports: {set(actual) ^ set(requested)}")
for name, axioms in actual.items():
    if not set(axioms) <= allowed:
        raise RuntimeError(f"Unreviewed axiom dependency in {name}: {set(axioms) - allowed}")
receipt = {"schema": "ueot_qm.axiom_audit.v1", "status": "PASS",
           "declaration_count": len(actual), "allowed_foundation": sorted(allowed),
           "declarations": actual}
(root / "proof-axioms.json").write_text(json.dumps(receipt, indent=2) + "\n")
print(f"PASS: {len(actual)} actual Lean axiom reports use only the reviewed standard foundation")
