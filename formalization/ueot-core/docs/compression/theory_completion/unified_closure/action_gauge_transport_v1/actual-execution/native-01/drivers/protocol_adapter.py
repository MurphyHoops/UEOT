#!/usr/bin/env python3
"""Reuse immutable predecessor execution code with explicit scope substitutions.

No proof test is removed. The adapted bytes are executed and archived alongside
their exact immutable originals, the substitutions, wrappers and frozen inputs.
The five new modules and predecessor census are fixed here; source/public/hint
counts are frozen before execution and independently checked by the old driver.
"""
from __future__ import annotations

from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import types

if not __debug__:
    raise RuntimeError("OPTIMIZED_PYTHON_DISABLES_REQUIRED_ASSERTIONS")

CORE = "formalization/ueot-core/"
PACKET = CORE + "docs/compression/theory_completion/unified_closure/"
REUSE = CORE + "docs/compression/theory_completion/knowledge/reuse/"
OLD = PACKET + "longterm_control_statistics_v1/native_protocol/"
NEW = PACKET + "action_gauge_transport_v1/native_protocol/"
MODULE_PREFIX = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure."
MODULES = sorted(MODULE_PREFIX + name for name in (
    "FiniteActionRealizability", "FiniteActionRealizabilityWitness",
    "DualDriveLinearGaugeClassification", "DualDriveOperationalAnchors",
    "ConditionedActionTransport"))
PRIOR_MODULES, PRIOR_PUBLIC, PRIOR_OVERLAYS = 703, 4474, 16
PROTOCOL_FILES = ("protocol_adapter.py", "freeze_inputs.py", "full_build.py",
                  "integration_native.py", "register_overlay.py")
ARCHIVE_FILES = ("PROTOCOL_ADAPTATION.json", "FROZEN_INPUTS.json", "protocol_adapter.py")


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(data):
    return sha256(data).hexdigest()


def encoded(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode()


def git(repo, *args):
    return subprocess.check_output(["git", *args], cwd=repo)


def load_python(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def source_corpus(repo):
    core = repo / CORE
    paths = [core / "UEOT.lean", *(core / "UEOT").rglob("*.lean")]
    data = {p.relative_to(repo).as_posix(): p.read_bytes() for p in paths if p.is_file()}
    h = sha256()
    for path, content in sorted(data.items(), key=lambda item: item[0][len(CORE):-5].replace("/", ".")):
        module = path[len(CORE):-5].replace("/", ".")
        h.update(module.encode() + b"\0" + content + b"\0")
    return data, h.hexdigest()


def freeze(repo, base, output):
    repo, output = Path(repo).resolve(), Path(output).resolve()
    require(not output.exists() and not output.is_relative_to(repo),
            "NEW_MANIFEST_OUTSIDE_REPOSITORY_REQUIRED")
    base = git(repo, "rev-parse", "--verify", base + "^{commit}").decode().strip()
    canonical = repo / OLD / "integration_native.py"
    require(canonical.read_bytes() == git(repo, "show", base + ":" + OLD + "integration_native.py"),
            "PREDECESSOR_DRIVER_CHANGED")
    helper = load_python("action_gauge_transport_predecessor", canonical)
    consumer, consumer_sha = helper.load_base_consumer(repo, base, "action_gauge_transport_base_registry")
    old = consumer.load(verify_source=False)
    require((len(old["modules"]), len(old["graph"]), len(old["overlays"])) ==
            (PRIOR_MODULES, PRIOR_PUBLIC, PRIOR_OVERLAYS), "WRONG_PREDECESSOR_CENSUS")
    parser_path = REUSE + "pr_preflight.py"
    require((repo / parser_path).read_bytes() == git(repo, "show", base + ":" + parser_path),
            "IMMUTABLE_DECLARATION_PARSER_CHANGED")
    parser = load_python("action_gauge_transport_freeze_parser", repo / parser_path)
    baseline = parser.corpus(repo, base)
    current, source_sha = source_corpus(repo)
    added = sorted(set(current) - set(baseline))
    require(len(baseline) == PRIOR_MODULES and set(baseline) <= set(current), "BASE_SOURCE_CENSUS_DRIFT")
    require(sorted(p[len(CORE):-5].replace("/", ".") for p in added) == MODULES,
            "EXACT_FIVE_MODULE_SCOPE_REQUIRED")
    baseline_declarations = [d for p, s in baseline.items() for d in parser.declarations(p, s)]
    parser.validate_unique(baseline_declarations, "IMMUTABLE_BASE")
    declarations = [d for p in added for d in parser.declarations(p, current[p].decode())]
    parser.validate_unique(declarations, "ACTION_GAUGE_TRANSPORT_NEW_SOURCE")
    hints = [{**d, "reuse_candidates": parser.candidate_hints(d, baseline_declarations)} for d in declarations]
    manifest = {
        "schema": "ACTION_GAUGE_TRANSPORT_FROZEN_PROTOCOL_INPUTS_V1",
        "state": "FROZEN_SOURCE_ONLY_ACTUAL_BUILD_AND_NATIVE_PENDING",
        "baseline_ref": base, "source_tree_sha256": source_sha,
        "prior_modules": PRIOR_MODULES, "prior_registered_public": PRIOR_PUBLIC,
        "prior_overlays": PRIOR_OVERLAYS, "complete_modules": len(current),
        "new_public": len(declarations), "lexical_hinted": sum(bool(d["reuse_candidates"]) for d in hints),
        "modules": MODULES, "public_source_names": sorted(d["symbol"] for d in declarations),
        "baseline_consumer_sha256": consumer_sha,
        "protocol_files": [{"path": NEW + name, "sha256": digest((repo / NEW / name).read_bytes())}
                           for name in PROTOCOL_FILES],
        "immutable_drivers": [{"path": OLD + name, "sha256": digest((repo / OLD / name).read_bytes())}
                              for name in ("full_build.py", "integration_native.py", "register_overlay.py")],
    }
    require(manifest["complete_modules"] == PRIOR_MODULES + len(MODULES), "MODULE_CENSUS_DRIFT")
    for row in manifest["immutable_drivers"]:
        require((repo / row["path"]).read_bytes() == git(repo, "show", base + ":" + row["path"]),
                "IMMUTABLE_DRIVER_DRIFT: " + row["path"])
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_bytes(encoded(manifest))
    return manifest


def frozen(repo, manifest_path, base):
    repo, manifest_path = Path(repo).resolve(), Path(manifest_path).resolve(strict=True)
    raw = manifest_path.read_bytes()
    data = json.loads(raw)
    actual_base = git(repo, "rev-parse", "--verify", base + "^{commit}").decode().strip()
    require(data["schema"] == "ACTION_GAUGE_TRANSPORT_FROZEN_PROTOCOL_INPUTS_V1" and
            data["state"] == "FROZEN_SOURCE_ONLY_ACTUAL_BUILD_AND_NATIVE_PENDING", "WRONG_FROZEN_INPUTS")
    require(data["baseline_ref"] == actual_base and data["modules"] == MODULES, "FROZEN_SCOPE_MISMATCH")
    require((data["prior_modules"], data["prior_registered_public"], data["prior_overlays"],
             data["complete_modules"]) == (703, 4474, 16, 708), "WRONG_FROZEN_CENSUS")
    for key, expected in (
            ("protocol_files", {NEW + name for name in PROTOCOL_FILES}),
            ("immutable_drivers", {OLD + name for name in
                ("full_build.py", "integration_native.py", "register_overlay.py")})):
        paths = [row["path"] for row in data[key]]
        require(len(paths) == len(set(paths)) and set(paths) == expected,
                "FROZEN_PROTOCOL_PATH_SET_MISMATCH: " + key)
    require(all(isinstance(data[key], int) and not isinstance(data[key], bool) and data[key] >= 0
                for key in ("new_public", "lexical_hinted")) and
            data["lexical_hinted"] <= data["new_public"], "INVALID_FROZEN_PUBLIC_COUNTS")
    names = data["public_source_names"]
    require(isinstance(names, list) and all(isinstance(name, str) and name for name in names) and
            names == sorted(set(names)) and len(names) == data["new_public"],
            "INVALID_FROZEN_PUBLIC_NAME_SET")
    current, source_sha = source_corpus(repo)
    require(len(current) == data["complete_modules"] and source_sha == data["source_tree_sha256"],
            "FROZEN_SOURCE_DRIFT")
    for row in data["protocol_files"]:
        require(digest((repo / row["path"]).read_bytes()) == row["sha256"], "NEW_PROTOCOL_DRIFT")
    for row in data["immutable_drivers"]:
        source = (repo / row["path"]).read_bytes()
        require(source == git(repo, "show", actual_base + ":" + row["path"]) and
                digest(source) == row["sha256"], "IMMUTABLE_PROTOCOL_DRIFT")
    return data, raw


def adapted_driver(kind, repo, manifest_path, base):
    repo = Path(repo).resolve()
    data, manifest_bytes = frozen(repo, manifest_path, base)
    relative = OLD + kind + ".py"
    original = (repo / relative).read_bytes()
    source, substitutions = original.decode(), []

    def replace(old, new, expected=1):
        nonlocal source
        count = source.count(old)
        require(count == expected, "ADAPTATION_ANCHOR_DRIFT: " + old)
        source = source.replace(old, new)
        substitutions.append({"old": old, "new": new, "occurrences": count})

    replace('"LONGTERM_ACTUAL_FULL_BUILD_V1"', '"ACTION_GAUGE_TRANSPORT_ACTUAL_FULL_BUILD_V1"')
    if kind in ("integration_native", "register_overlay"):
        replace('NAME = "LONGTERM_CONTROL_STATISTICS"', 'NAME = "ACTION_GAUGE_TRANSPORT"')
    if kind == "integration_native":
        replace("PRIOR_MODULES, PRIOR_THEOREMS, PRIOR_OVERLAYS = 666, 4147, 8",
                "PRIOR_MODULES, PRIOR_THEOREMS, PRIOR_OVERLAYS = 703, 4474, 16")
        replace('"UNCOUNTED_SAME_SOURCE_LONGTERM_POLICY_AND_ROWWISE_SISC"',
                '"UNCOUNTED_ACTION_REALIZABILITY_GAUGE_AND_CONDITIONED_TRANSPORT"')
        replace('    exporter = helper.render_export(prior, public, modules, [])',
                '    exporter = helper.render_export(prior, public, modules, [])\n'
                '    exporter = exporter.replace("set_option maxHeartbeats 0",\n'
                '        "set_option maxHeartbeats 0\\nset_option maxRecDepth 16384")')
    if kind == "register_overlay":
        replace('PROTOCOL = PACKET + "longterm_control_statistics_v1/native_protocol/"',
                'PROTOCOL = PACKET + "action_gauge_transport_v1/native_protocol/"')
        replace('"longterm_control_statistics_v1"', '"action_gauge_transport_v1"')
        replace('EXPECTED_SOURCE = "60cd5f8ab161c5b51394463c466947a4c6a6c1742ecdcd9c2bbfc41c0c06bd31"',
                'EXPECTED_SOURCE = ' + repr(data["source_tree_sha256"]))
        replace("PRIOR_MODULES, MODULES, PRIOR_PUBLIC, NEW_PUBLIC = 666, 678, 4147, 90",
                f'PRIOR_MODULES, MODULES, PRIOR_PUBLIC, NEW_PUBLIC = 703, 708, 4474, {data["new_public"]}')
        replace("(PRIOR_MODULES, MODULES, PRIOR_PUBLIC, 8)", "(PRIOR_MODULES, MODULES, PRIOR_PUBLIC, 16)")
        replace('require(hinted == 27,', f'require(hinted == {data["lexical_hinted"]},')
        extras = ARCHIVE_FILES + ("integration_native.py", "immutable_integration_native.py", "executed_integration_native.py")
        replace('NATIVE, OVERLAY, "development_lexical_reuse_hints.json")',
                'NATIVE, OVERLAY, "development_lexical_reuse_hints.json", ' +
                ", ".join(repr(n) for n in extras) + ")")
        extras = ARCHIVE_FILES + ("full_build.py", "immutable_full_build.py", "executed_full_build.py")
        replace('for name in ("FULL_BUILD_RECEIPT.json", "full-build.log"):',
                'for name in ("FULL_BUILD_RECEIPT.json", "full-build.log", ' +
                ", ".join(repr(n) for n in extras) + "):")
        anchor = '    provenance = {"schema": NAME + "_REGISTRATION_PROVENANCE_V1", "inputs": inputs,'
        replace(anchor,
                '    for name, content in ADAPTED_REGISTRATION_INPUTS.items():\n'
                '        record("executed_registration_protocol", "executed-memory:" + name,\n'
                '               (archive / "drivers" / name).relative_to(repo), content)\n' + anchor)
    wrapper = repo / NEW / (kind + ".py")
    adapted = source.encode()
    module = types.ModuleType("action_gauge_transport_executed_" + kind)
    module.__file__ = str(wrapper)
    sys.modules[module.__name__] = module
    exec(compile(adapted, str(wrapper) + "::adapted_immutable_protocol", "exec"), module.__dict__)
    context = {
        "schema": "ACTION_GAUGE_TRANSPORT_PROTOCOL_ADAPTATION_V1", "kind": kind,
        "baseline_ref": data["baseline_ref"], "frozen_inputs_sha256": digest(manifest_bytes),
        "source_tree_sha256": data["source_tree_sha256"],
        "immutable_driver": {"path": relative, "sha256": digest(original)},
        "executed_source_sha256": digest(adapted), "substitutions": substitutions,
        "wrapper": {"path": NEW + kind + ".py", "sha256": digest(wrapper.read_bytes())},
        "adapter_sha256": digest(Path(__file__).read_bytes()),
        "claim": "Only listed scope/schema/metadata and export recursion-limit substitutions; actual execution, full census, raw-type comparisons, fixed-edge replay, and source/runtime identity gates remain in the executed predecessor code.",
    }
    archive = {"PROTOCOL_ADAPTATION.json": encoded(context), "FROZEN_INPUTS.json": manifest_bytes,
               "protocol_adapter.py": Path(__file__).read_bytes(), kind + ".py": wrapper.read_bytes(),
               "immutable_" + kind + ".py": original, "executed_" + kind + ".py": adapted}
    if kind == "register_overlay":
        module.ADAPTED_REGISTRATION_INPUTS = archive
    return module, archive


def archive_protocol(output, files):
    output = Path(output)
    if not output.exists():
        return
    for name, content in files.items():
        path = output / name
        if path.exists():
            require(path.read_bytes() == content, "PROTOCOL_ARCHIVE_CONFLICT")
        else:
            with path.open("xb") as stream:
                stream.write(content)


def verify_archived_protocol(kind, repo, manifest_path, base, output):
    _, expected = adapted_driver(kind, repo, manifest_path, base)
    for name, content in expected.items():
        require((Path(output) / name).read_bytes() == content,
                "EXECUTED_PROTOCOL_ARCHIVE_MISMATCH: " + kind + "/" + name)
