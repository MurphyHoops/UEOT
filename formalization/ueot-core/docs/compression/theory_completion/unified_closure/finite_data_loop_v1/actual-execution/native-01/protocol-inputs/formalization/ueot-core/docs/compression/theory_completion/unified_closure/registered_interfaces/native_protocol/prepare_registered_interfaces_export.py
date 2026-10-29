#!/usr/bin/env python3
"""One-off staging helper: prepare native evidence for the registered-interfaces overlay.

The generated exporter remains pending until Lean actually executes it. Native
ownership, types, direct constants and axiom closure are collected independently
for every compiled theorem, including private and generated constants.

This script never edits the repository and never marks an overlay PASS. Run it
only after root has integrated the new public Lean modules and built UEOT.
Existing 659-module evidence and all seven overlays are independently verified
through the existing navigator; source hashes are recorded only at invocation.
"""
from __future__ import annotations

import argparse
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

CORE_PREFIX = "formalization/ueot-core/"
SCOPE = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure"
SCOPE_CONFIG = json.loads((Path(__file__).with_name("SOURCE_SCOPE.json")).read_text())
STEMS = tuple(SCOPE_CONFIG["stems"])
HISTORICAL_PUBLIC_REPAIRS = tuple(SCOPE_CONFIG["historical_public_repairs"])
EXPECTED_NEW_PUBLIC = SCOPE_CONFIG["expected_new_public_source_theorems"]

HISTORICAL_MODULES = 659
HISTORICAL_THEOREMS = 4094


def import_file(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def prepare(repo: Path, output: Path, base_ref: str) -> dict:
    repo = repo.resolve()
    output = output.resolve()
    if output.is_relative_to(repo):
        raise RuntimeError("TEMPORARY_OUTPUT_MUST_BE_OUTSIDE_REPOSITORY")
    baseline_ref = subprocess.check_output(
        ["git", "rev-parse", "--verify", base_ref + "^{commit}"],
        cwd=repo, text=True).strip()
    core = repo / CORE_PREFIX
    knowledge = core / "docs/compression/theory_completion/knowledge"
    reuse = import_file("registered_interfaces_existing_reuse", knowledge / "reuse/fkrg_reuse.py")
    existing = reuse.load(verify_source=False)
    if len(existing["modules"]) != HISTORICAL_MODULES or len(existing["graph"]) != HISTORICAL_THEOREMS:
        raise RuntimeError("EXPECTED_IMMUTABLE_659_MODULE_4094_THEOREM_BASE")
    if len(existing["overlays"]) != 7:
        raise RuntimeError("EXPECTED_SEVEN_PRIOR_OVERLAYS")
    extractor = import_file("registered_interfaces_existing_fkrg", knowledge / "fkrg.py")
    added_paths = {
        CORE_PREFIX + (SCOPE + "." + stem).replace(".", "/") + ".lean"
        for stem in STEMS
    }
    historical_paths = {item["path"] for item in existing["modules"]}
    current = reuse.live_source_paths()
    if len(STEMS) != 7 or len(current) != SCOPE_CONFIG["expected_complete_source_modules"]:
        raise RuntimeError("EXPECTED_SEVEN_NEW_AND_666_TOTAL_SOURCE_MODULES")
    if current != historical_paths | added_paths:
        raise RuntimeError("INTEGRATE_FINAL_PUBLIC_IMPORTS_FIRST: " + json.dumps({
            "missing": sorted((historical_paths | added_paths) - current),
            "unexpected": sorted(current - (historical_paths | added_paths)),
        }))
    prior_overrides = {}
    for overlay in existing["overlays"]:
        prior_overrides.update(overlay.get("source_hash_overrides", {}))
    allowed_override = CORE_PREFIX + "UEOT/V3/Compression/TheoryCompletion.lean"
    source_overrides = {}
    for item in existing["modules"]:
        path = item["path"]
        actual = sha256((repo / path).read_bytes()).hexdigest()
        expected = prior_overrides.get(path, item["content_sha256"])
        if actual != expected:
            if path != allowed_override:
                raise RuntimeError("UNEXPECTED_HISTORICAL_LEAN_SOURCE_DRIFT: " + path)
            source_overrides[path] = actual
    modules, public, private = [], [], []
    for path in sorted(added_paths):
        source = repo / path
        module = source.relative_to(core).with_suffix("").as_posix().replace("/", ".")
        modules.append({"module": module, "path": path,
                        "content_sha256": sha256(source.read_bytes()).hexdigest(),
                        "source_origin": "UEOT_MAINTAINED"})
        declarations, _ = extractor.extract(module, source)
        for row in declarations:
            if row[3] not in ("theorem", "lemma"):
                continue
            item = {"name": row[5], "module": module, "path": path,
                    "line": row[2], "source_origin": "UEOT_MAINTAINED",
                    "registration_kind": ("new_source_private_lexical" if row[5].startswith("private@")
                                          else "new_source_public")}
            (private if row[5].startswith("private@") else public).append(item)
    if len(public) != EXPECTED_NEW_PUBLIC or len({item["name"] for item in public}) != len(public):
        raise RuntimeError("EMPTY_OR_DUPLICATE_PUBLIC_SOURCE_CANDIDATES")
    if any(item["name"] in existing["graph"] for item in public):
        raise RuntimeError("NEW_OVERLAY_REDEFINES_REGISTERED_NAME")
    new_public = list(public)
    historical = [dict(item) for item in HISTORICAL_PUBLIC_REPAIRS]
    if len(historical) != 1:
        raise RuntimeError("EXPECTED_ONE_EXPLICIT_HISTORICAL_PUBLIC_REPAIR")
    historical_modules = {row["path"]: row for row in existing["modules"]}
    native_modules = list(modules)
    for item in historical:
        path = item["path"]
        if path not in historical_modules or path in added_paths:
            raise RuntimeError("HISTORICAL_REPAIR_IS_NOT_AN_EXISTING_MODULE")
        source = repo / path
        actual = sha256(source.read_bytes()).hexdigest()
        prior = historical_modules[path]
        if (actual != item["content_sha256"] or
                actual != prior_overrides.get(path, prior["content_sha256"])):
            raise RuntimeError("HISTORICAL_REPAIR_SOURCE_HASH_DRIFT")
        base_bytes = subprocess.check_output(["git", "show", baseline_ref + ":" + path], cwd=repo)
        if sha256(base_bytes).hexdigest() != item["content_sha256"]:
            raise RuntimeError("HISTORICAL_REPAIR_WAS_NOT_PRESENT_AT_ACTUAL_BASE")
        if item["name"] in existing["graph"] or any(x["name"] == item["name"] for x in public):
            raise RuntimeError("HISTORICAL_REPAIR_DUPLICATES_REGISTERED_OR_NEW_NAME")
        # This exact name is deliberately independent of the unchanged frozen
        # fkrg.py word-boundary parser. Native owner/type/visibility confirms it.
        if (item["module"] != prior["module"] or
                item["registration_kind"] != "historical_public_repair"):
            raise RuntimeError("INVALID_EXPLICIT_HISTORICAL_REPAIR_IDENTITY")
        public.append(item)
        if not any(row["module"] == item["module"] for row in native_modules):
            native_modules.append({"module": item["module"], "path": path,
                                   "content_sha256": actual, "source_origin": item["source_origin"]})
    if len(native_modules) != 8 or len(public) != EXPECTED_NEW_PUBLIC + 1:
        raise RuntimeError("EXPECTED_EIGHT_NATIVE_MODULES_AND_53_PUBLIC_REGISTRATIONS")
    prior_names = [item["name"] for overlay in existing["overlays"]
                   for item in overlay["public_theorems"]]
    payload = {
        "status": "PENDING_NATIVE_COMPILATION",
        "baseline_ref": baseline_ref,
        "base_snapshot_modules": HISTORICAL_MODULES,
        "registered_prior_theorems": HISTORICAL_THEOREMS,
        "prior_overlay_count": len(existing["overlays"]),
        "build_environment_sha256": dict(reuse.BUILD_ENVIRONMENT_SHA256),
        "prior_overlay": {"path": reuse.OVERLAY_PATHS[-1].relative_to(repo).as_posix(),
                          "sha256": reuse.OVERLAY_SHA256S[-1]},
        "source_hash_overrides": source_overrides,
        "added_modules": modules,
        "native_audit_modules": native_modules,
        "new_public_source_candidates": new_public,
        "historical_public_repairs": historical,
        "public_source_candidates": public,
        "private_source_candidates": private,
        "source_tree_sha256": extractor.fingerprint(extractor.sources()),
        "candidate_scope": "52 lexical new source candidates plus one explicit unchanged historical public repair. The frozen fkrg.py parser is not repaired. Native ownership, visibility, types and proof terms confirm all 53. Native axiom enumeration covers every theorem constant in seven new modules and the one historical module. The historical registered graph remains 4094 nodes until additive registration.",
    }
    native = render_export(prior_names, public, native_modules, historical)
    output.mkdir(parents=True, exist_ok=True)
    (output / "REGISTERED_INTERFACES_NATIVE_EXPORT.lean").write_text(native)
    payload["exporter_sha256"] = sha256(native.encode()).hexdigest()
    (output / "registered_interfaces_source_preflight.json").write_text(
        json.dumps(payload, ensure_ascii=False, indent=2) + "\n")
    return payload


def render_export(prior: list[str], public: list[dict], modules: list[dict], historical: list[dict]) -> str:
    prior_array = "\n".join(f"    `{name}," for name in prior)
    new_array = "\n".join(f"    (`{item['name']}, `{item['module']})," for item in public)
    module_array = "\n".join(f"    `{item['module']}," for item in modules)
    repair_array = "\n".join(f"    `{item['name']}," for item in historical)
    return NATIVE_TEMPLATE.replace("__PRIOR_NAMES__", prior_array).replace(
        "__NEW_NAMES__", new_array).replace("__NEW_MODULES__", module_array).replace(
        "__HISTORICAL_REPAIR_NAMES__", repair_array)


NATIVE_TEMPLATE = r'''import UEOT
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command Meta
set_option maxHeartbeats 0

private def registeredInterfacesEvidenceName (s : String) : Name :=
  (s.splitOn ".").foldl (fun n part => Name.str n part) Name.anonymous

run_cmd do
  let env ← getEnv
  let graph ← liftIO <| IO.FS.readFile
    "docs/compression/theory_completion/knowledge/audits/2026-10-10/all_3793_theorem_direct_reuse_graph.csv"
  let baseNames := (graph.splitOn "\n").drop 1 |>.filterMap fun line =>
    if line.isEmpty then none else
      match line.splitOn "," with
      | [] => none
      | name :: _ => some (registeredInterfacesEvidenceName name)
  unless baseNames.length == 3793 do throwError "REGISTERED_INTERFACES_BASE_GRAPH_COUNT"
  let priorNames : Array Name := #[
__PRIOR_NAMES__
  ]
  let newNames : Array (Name × Name) := #[
__NEW_NAMES__
  ]
  let historicalRepairNames : Array Name := #[
__HISTORICAL_REPAIR_NAMES__
  ]
  let sourceModules : Array Name := #[
__NEW_MODULES__
  ]
  for sourceModule in sourceModules do
    unless env.header.moduleNames.contains sourceModule do
      throwError s!"REGISTERED_INTERFACES_SOURCE_MODULE_NOT_IMPORTED {sourceModule}"
  let registered := baseNames ++ priorNames.toList
  unless registered.length == 4094 do throwError "REGISTERED_INTERFACES_REGISTERED_PRIOR_COUNT"
  unless newNames.size == 53 && historicalRepairNames.size == 1 && sourceModules.size == 8 do
    throwError "REGISTERED_INTERFACES_PUBLIC_AND_NATIVE_SCOPE_COUNT"
  let allRegistered := registered ++ (newNames.toList.map Prod.fst)
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut nativeScope : Array Json := #[]
  for (name, info) in env.constants.toList do
    if let .thmInfo decl := info then
      if let some idx := env.getModuleIdxFor? name then
        let sourceModule := env.header.moduleNames[idx]!
        if sourceModules.contains sourceModule then
          let actual ← Lean.collectAxioms name
          unless (actual.filter fun ax => !allowed.contains ax).isEmpty do
            throwError s!"REGISTERED_INTERFACES_NONSTANDARD_AXIOM {name}: {actual}"
          let rendered ← liftTermElabM do ppExpr decl.type
          let constants := decl.value.getUsedConstants.toList
          let theoremDeps := constants.filter fun dep =>
            match env.find? dep with
            | some (.thmInfo _) => true
            | _ => false
          nativeScope := nativeScope.push <| Json.mkObj [
            ("name", toJson name.toString),
            ("source_module", toJson sourceModule.toString),
            ("is_private", toJson (Lean.privateToUserName? name).isSome),
            ("axioms", toJson (actual.map Name.toString)),
            ("type", toJson rendered.pretty),
            ("level_parameters", toJson (decl.levelParams.map Name.toString)),
            ("direct_constants", toJson (constants.map Name.toString)),
            ("direct_theorem_constants", toJson (theoremDeps.map Name.toString))]
  -- The only historical rescan is a direct-proof search for the exact omitted
  -- name. Emit every positive row; do not prefill a supposed singleton caller.
  let mut registeredScanned := 0
  let mut historicalIncoming : Array Json := #[]
  for name in registered do
    let some (.thmInfo decl) := env.find? name
      | throwError s!"REGISTERED_INTERFACES_PRIOR_NOT_THEOREM {name}"
    let constants := decl.value.getUsedConstants.toList
    let hits := constants.filter fun dep => historicalRepairNames.contains dep
    registeredScanned := registeredScanned + 1
    if !hits.isEmpty then
      let some idx := env.getModuleIdxFor? name
        | throwError s!"REGISTERED_INTERFACES_EXISTING_REPAIR_OWNER_MISSING {name}"
      let sourceModule := env.header.moduleNames[idx]!
      let actualDeps := constants.filter fun dep => dep != name && allRegistered.contains dep
      historicalIncoming := historicalIncoming.push <| Json.mkObj [
        ("name", toJson name.toString),
        ("source_module", toJson sourceModule.toString),
        ("direct_constants", toJson (constants.map Name.toString)),
        ("historical_repair_deps", toJson (hits.map Name.toString)),
        ("actual_source_theorem_deps", toJson (actualDeps.map Name.toString))]
  let historicalScan := Json.mkObj [
    ("registered_theorems_scanned", toJson registeredScanned),
    ("historical_public_repair_targets", toJson (historicalRepairNames.map Name.toString)),
    ("incoming_rows", toJson historicalIncoming)]
  let mut cross := 0
  let mut newCross := 0
  let mut repairCross := 0
  let mut internal := 0
  let mut newInternal := 0
  let mut mixedInternal := 0
  let mut repairInternal := 0
  let mut collisions : Array Json := #[]
  let mut rows : Array Json := #[]
  for (name, owner) in newNames do
    let some (.thmInfo decl) := env.find? name | throwError s!"REGISTERED_INTERFACES_NEW_THEOREM_MISSING {name}"
    let some idx := env.getModuleIdxFor? name | throwError s!"REGISTERED_INTERFACES_SOURCE_MODULE_MISSING {name}"
    unless env.header.moduleNames[idx]! == owner do
      throwError s!"REGISTERED_INTERFACES_SOURCE_MODULE_MISMATCH {name}"
    if (Lean.privateToUserName? name).isSome then throwError s!"REGISTERED_INTERFACES_PUBLIC_CANDIDATE_PRIVATE {name}"
    for old in registered do
      let some oldInfo := env.find? old | throwError s!"REGISTERED_INTERFACES_PRIOR_SYMBOL_MISSING {old}"
      let eq ← liftTermElabM do Meta.isDefEq decl.type oldInfo.type
      cross := cross + 1
      if historicalRepairNames.contains name then
        repairCross := repairCross + 1
      else
        newCross := newCross + 1
      if eq then collisions := collisions.push <| toJson [name.toString, old.toString]
    let constants := decl.value.getUsedConstants.toList
    let deps := constants.filter fun dep => dep != name && allRegistered.contains dep
    let rendered ← liftTermElabM do ppExpr decl.type
    rows := rows.push <| Json.mkObj [
      ("name", toJson name.toString),
      ("registration_kind", toJson (if historicalRepairNames.contains name then
        "historical_public_repair" else "new_source_public")),
      ("source_module", toJson owner.toString),
      ("type", toJson rendered.pretty),
      ("level_parameters", toJson (decl.levelParams.map Name.toString)),
      ("source_theorem_deps", toJson (deps.map Name.toString)),
      ("direct_constants", toJson (constants.map Name.toString))]
  for i in [:newNames.size] do
    for j in [i+1:newNames.size] do
      let ni := newNames[i]!.1
      let nj := newNames[j]!.1
      let ci ← getConstInfo ni
      let cj ← getConstInfo nj
      let eq ← liftTermElabM do Meta.isDefEq ci.type cj.type
      internal := internal + 1
      if historicalRepairNames.contains ni && historicalRepairNames.contains nj then
        repairInternal := repairInternal + 1
      else if historicalRepairNames.contains ni || historicalRepairNames.contains nj then
        mixedInternal := mixedInternal + 1
      else
        newInternal := newInternal + 1
      if eq then collisions := collisions.push <| toJson [ni.toString, nj.toString]
  let output := Json.mkObj [
    ("schema", toJson "REGISTERED_INTERFACES_NATIVE_EXPORT_V1"),
    ("registered_prior_theorems", toJson registered.length),
    ("new_source_public_theorem_count", toJson (newNames.size - historicalRepairNames.size)),
    ("historical_public_repair_count", toJson historicalRepairNames.size),
    ("overlay_public_registration_count", toJson newNames.size),
    ("native_audit_modules", toJson (sourceModules.map Name.toString)),
    ("cross_isDefEq_comparisons", toJson cross),
    ("new_source_to_registered_isDefEq_comparisons", toJson newCross),
    ("historical_repair_to_registered_isDefEq_comparisons", toJson repairCross),
    ("internal_isDefEq_comparisons", toJson internal),
    ("new_source_internal_isDefEq_comparisons", toJson newInternal),
    ("new_source_to_historical_repair_isDefEq_comparisons", toJson mixedInternal),
    ("historical_repair_internal_isDefEq_comparisons", toJson repairInternal),
    ("historical_repair_incoming_scan", historicalScan),
    ("collisions", toJson collisions),
    ("public_source_theorems", toJson rows),
    ("all_native_theorem_constants", toJson nativeScope)]
  liftIO <| IO.println ("REGISTERED_INTERFACES_NATIVE_JSON " ++ output.compress)
  unless collisions.isEmpty do throwError "REGISTERED_INTERFACES_OVERLAY_TYPE_COLLISION"
'''


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--base-ref", required=True,
                        help="Actual immutable predecessor Git commit, not a candidate label.")
    args = parser.parse_args()
    result = prepare(args.repo, args.output, args.base_ref)
    print(json.dumps({"status": result["status"], "added_modules": len(result["added_modules"]),
                      "public_candidates": len(result["public_source_candidates"]),
                      "output": str(args.output)}))
