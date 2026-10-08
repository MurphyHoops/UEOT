#!/usr/bin/env python3
"""Reproducible lexical/import audit over EVERY first-party UEOT Lean source.

We read/hash full contents, enumerate declarations and internal UEOT imports,
and check reachability from public UEOT.lean. This is NOT a substitute for
semantic proof review, kernel validation or a scientific novelty claim.

Run: python3 formalization/ueot-core/scripts/audit_sisc_global_inventory.py
"""
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[3]
PKG = ROOT / "formalization" / "ueot-core"
OUTPUT = PKG / "docs" / "compression" / "theory_completion" / "scientific_closure" / "SISC_GLOBAL_LEAN_INVENTORY_V5.json"
DECL = re.compile(r"^\s*(?:(?:private|protected|noncomputable|local|unsafe)\s+)*"
                  r"(theorem|lemma|def|abbrev|structure|class|inductive|instance|axiom|opaque)\s+([^\s(:]+)")
IMPORT = re.compile(r"^\s*import\s+(UEOT(?:\.\w+)+)\s*$", re.MULTILINE)


def sources():
    return sorted([PKG / "UEOT.lean", *list((PKG / "UEOT").rglob("*.lean")),
                   PKG / "lakefile.lean", *list((PKG / "scripts").glob("*.lean"))])


def main():
    modules = {}
    root = None
    for p in sources():
        text = p.read_text(encoding="utf-8")  # Entire source, not only head or filename.
        rel = p.relative_to(PKG).as_posix()
        module = rel.removesuffix(".lean").replace("/", ".")
        if rel == "UEOT.lean":
            root = module
        declarations = Counter()
        for line in text.splitlines():
            match = DECL.match(line)
            if match:
                declarations[match.group(1)] += 1
        modules[module] = {
            "file": rel,
            "sha256": hashlib.sha256(text.encode()).hexdigest(),
            "lines": len(text.splitlines()),
            "declarations": dict(sorted(declarations.items())),
            "imports_ueot": sorted(set(IMPORT.findall(text))),
        }

    for entry in modules.values():
        entry["imports_local"] = [x for x in entry["imports_ueot"] if x in modules]
    missing = sorted({name for entry in modules.values() for name in entry["imports_ueot"]
                      if name not in modules})
    state, reached, cycles = {}, set(), []

    def dfs(m, path):
        if state.get(m) == 1:
            cycles.append(path + [m])
            return
        if state.get(m) == 2:
            return
        state[m] = 1
        reached.add(m)
        for d in modules[m]["imports_local"]:
            dfs(d, path + [m])
        state[m] = 2

    dfs(root, [])
    group = defaultdict(lambda: {"modules": 0, "lines": 0, "theorems_and_lemmas": 0})
    for name, entry in modules.items():
        if entry["file"].startswith("UEOT/V3/Compression/TheoryCompletion/"):
            key = "TheoryCompletion"
        elif entry["file"].startswith("UEOT/V3/Compression/Objecthood/"):
            key = "Objecthood"
        elif entry["file"].startswith("UEOT/V3/Compression/"):
            key = "CompressionOther"
        elif entry["file"].startswith("UEOT/V3/"):
            key = "V3CoreAndPhysics"
        elif entry["file"].startswith("UEOT/Core/"):
            key = "LegacyCore"
        else:
            key = "PackageEntrypointsAndAudit"
        group[key]["modules"] += 1
        group[key]["lines"] += entry["lines"]
        group[key]["theorems_and_lemmas"] += (
            entry["declarations"].get("theorem", 0) + entry["declarations"].get("lemma", 0))

    result = {
        "scope": "first_party_ueot_lean_files_plus_package_scripts_excluding_lake_and_cos_test",
        "root": root,
        "total_files": len(modules),
        "total_lines": sum(m["lines"] for m in modules.values()),
        "theorem_lemma_declaration_count": sum(
            m["declarations"].get("theorem", 0) + m["declarations"].get("lemma", 0)
            for m in modules.values()),
        "reachable_from_public_root": len(reached),
        "unreached_modules": sorted(set(modules) - reached),
        "missing_local_ueot_imports": missing,
        "import_cycles": cycles,
        "groups": dict(sorted(group.items())),
        "modules": dict(sorted(modules.items())),
        "limitations": [
            "Lexical declarations may miss multiline/attribute/macro-generated declarations.",
            "File/content/import audit does not establish theorem statement correctness.",
            "This is an inventory of first-party package Lean, not all external Mathlib/Lean files.",
            "Module hashes attest local source bytes, not remote scientific review.",
        ],
    }
    if missing or cycles:
        raise RuntimeError(f"Import integrity failed: missing={missing}, cycles={cycles}")
    OUTPUT.write_text(json.dumps(result, ensure_ascii=False, indent=2, sort_keys=True) + "\n")
    print("SOURCE_FILES", result["total_files"])
    print("SOURCE_LINES", result["total_lines"])
    print("THEOREM_LEMMA_DECLARATIONS_LEXICAL", result["theorem_lemma_declaration_count"])
    print("PUBLIC_ROOT_REACHABLE", result["reachable_from_public_root"])
    print("UNREACHED_COUNT", len(result["unreached_modules"]))
    print("CYCLES", len(cycles))
    for key, value in sorted(group.items()):
        print("GROUP", key, json.dumps(value, sort_keys=True))
    print("MANIFEST", OUTPUT.relative_to(ROOT))


if __name__ == "__main__":
    main()
