#!/usr/bin/env python3
"""Read-only postprocessing of actual Lean output; never run Lean or alter receipts.

This intentionally accepts only the simple universe-parameter/numeral suffixes
needed by the observed standard-axiom output. Unfamiliar level syntax stops the
audit instead of being stripped. Native constants must match complete names.
"""
from __future__ import annotations
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

STANDARD = {"propext": 0, "Classical.choice": 1, "Quot.sound": 1}
TOKEN = re.compile(r"([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)(\.\{([^{}]*)\})?")
LEVEL = re.compile(r"(?:[A-Za-z_][A-Za-z0-9_']*|0|[1-9][0-9]*)")
REPORT = re.compile(r"^'([^'\r\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)[ \t]*(?:\r?\n|$)", re.M)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def split_axioms(raw):
    if not raw.strip():
        return []
    depth, start, pieces = 0, 0, []
    for i, ch in enumerate(raw):
        if ch == "{":
            depth += 1
            require(depth == 1, "Nested universe braces are not accepted")
        elif ch == "}":
            depth -= 1
            require(depth == 0, "Unmatched universe brace")
        elif ch == "," and depth == 0:
            pieces.append(raw[start:i].strip())
            start = i + 1
    require(depth == 0, "Unclosed universe suffix")
    pieces.append(raw[start:].strip())
    require(all(pieces), "Empty or trailing axiom-list item")
    return pieces


def parse_token(raw):
    match = TOKEN.fullmatch(raw)
    require(match is not None, "Unconsumed or invalid axiom token: " + repr(raw))
    name, suffix, levels = match.groups()
    arguments = [] if suffix is None else [s.strip() for s in levels.split(",")]
    require(all(LEVEL.fullmatch(s) for s in arguments), "Unsupported/invalid universe syntax: " + repr(raw))
    return {"raw_token": raw, "constant_name": name, "universe_suffix": suffix or "",
            "universe_arguments": arguments}


def allowed_native(endpoint):
    suffix = endpoint.get("allowed_native_axiom_suffix")
    if suffix is None:
        return None
    complete = endpoint["name"] + "._native.native_decide.ax_1_1"
    require(complete.endswith("." + suffix), "Original native allowlist is not the observed complete constant")
    return complete


def validate_tokens(raw, endpoint):
    result = [parse_token(token) for token in split_axioms(raw)]
    names = [t["constant_name"] for t in result]
    require(len(set(names)) == len(names), "Duplicate axiom constants")
    native = allowed_native(endpoint)
    require(set(endpoint["allowed_axioms"]) <= set(STANDARD), "Unexpected base allowlist")
    for token in result:
        name = token["constant_name"]
        if name in STANDARD and name in endpoint["allowed_axioms"]:
            # Bare constants remain valid. Printed instances must have correct arity.
            if token["universe_suffix"]:
                require(len(token["universe_arguments"]) == STANDARD[name], "Wrong universe arity: " + token["raw_token"])
            token["classification"] = "standard_logic_axiom"
        else:
            require(name == native and not token["universe_suffix"], "Unapproved axiom: " + token["raw_token"])
            token["classification"] = "exact_disclosed_native_axiom"
    if native is not None:
        require(names.count(native) == 1, "Missing exact disclosed native axiom")
    return result


def selfchecks():
    sample = {"name": "Example.theorem", "allowed_axioms": list(STANDARD)}
    require(len(validate_tokens("propext, Classical.choice.{u}, Quot.sound.{u}", sample)) == 3,
            "Observed standard syntax failed")
    invalid = ["propext, sorryAx", "Classical.choice.{u}evil", "Evil.Classical.choice.{u}",
               "Classical.choice.{u},", "Classical.choice.{}", "Classical.choice.{u,v}",
               "propext.{u}", "Classical.choice.{u", "Classical.choice.{u}}, Quot.sound.{u}",
               "Classical.choice.{u}, Classical.choice.{v}", "Classical.choice.{u}; Evil"]
    for raw in invalid:
        try:
            validate_tokens(raw, sample)
        except ValueError:
            continue
        raise ValueError("Invalid input unexpectedly accepted: " + raw)
    native = {**sample, "allowed_native_axiom_suffix": "Example.theorem._native.native_decide.ax_1_1"}
    # A real native entry has a namespace prefix before its registered suffix.
    native["name"] = "UEOT.Example.theorem"
    validate_tokens("propext, UEOT.Example.theorem._native.native_decide.ax_1_1", native)
    for raw in ("propext, Other.UEOT.Example.theorem._native.native_decide.ax_1_1",
                "propext, UEOT.Example.theorem._native.native_decide.ax_1_2",
                "propext, UEOT.Example.theorem._native.native_decide.ax_1_1.{u}"):
        try:
            validate_tokens(raw, native)
        except ValueError:
            continue
        raise ValueError("Invalid native identity accepted: " + raw)
    return {"observed_standard_form_accepted": True, "exact_native_form_accepted": True,
            "negative_cases_rejected": len(invalid) + 3, "kind": "PARSER_ONLY_NOT_LEAN"}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--evidence", type=Path, required=True)
    ap.add_argument("--plan", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    evidence = args.evidence.resolve()
    plan = json.loads(args.plan.read_text())
    source_path = evidence / "run-20261113T0932Z/D3_RECEIPT.json"
    cont_path = evidence / "probe-continuation-20261113T0940Z/CONTINUATION_RECEIPT.json"
    post_path = evidence / "FINAL_SOURCE_ARTIFACT_CHECK.json"
    log_path = evidence / "probe-continuation-20261113T0940Z/D3ProbeFinal.log"
    source, cont, post = [json.loads(p.read_text()) for p in (source_path, cont_path, post_path)]
    require(source["status"] == cont["status"] == "FAILED_OR_BLOCKED", "Preserve original failed wrapper states")
    require(digest(source_path) == cont["source_compilation_receipt_sha256"] == post["source_compilation_receipt_sha256"], "Source receipt binding failed")
    require(digest(cont_path) == post["continuation_receipt_sha256"], "Continuation receipt binding failed")
    require(digest(args.plan) == source["bundle_sha256"]["D3_PLAN.json"] == cont["bound_plan_sha256"], "Original allowlist binding failed")
    require(source["git_head"] == cont["git_head"] == plan["target_head"], "HEAD binding failed")
    modules = [s for s in source["steps"] if "module" in s]
    require(len(modules) == 15 and all(s["exit_code"] == 0 for s in modules), "15 successful source compilations required")
    require([s["module"] for s in modules] == [m["module"] for m in plan["fresh_modules"]], "Source order/scope mismatch")
    mac_root = Path("/Users/murphyhoops/Documents/ueot-core-audit-20261113")
    for receipt in (source, cont):
        for step in receipt["steps"]:
            local_log = evidence / Path(step["log"]).relative_to(mac_root)
            require(digest(local_log) == step["log_sha256"], "Raw log hash mismatch: " + str(local_log))
    require(all(s["exit_code"] == 0 for s in cont["steps"]) and len(cont["steps"]) == 2,
            "Actual final deps and Lean command must both exit 0")
    require(cont["all_15_selected_imports_resolved_to_previous_fresh_artifacts"], "Probe dependency provenance missing")
    require(digest(log_path) == post["final_probe_log_sha256"] and post["final_probe_lean_exit_code"] == 0, "Final log binding failed")
    require(post["source_and_config_files_unchanged"] == 1055 and post["source_module_artifacts_unchanged"] == 30,
            "Final source/artifact readback incomplete")
    expected_artifacts = {a["path"]: (a["sha256"], a["bytes"]) for m in modules for a in m["new_artifacts"]}
    final_artifacts = {a["path"]: (a["sha256"], a["bytes"]) for a in post["source_artifacts"]}
    require(expected_artifacts == final_artifacts, "Final recorded source artifact hashes differ")
    require(post["old_target_cache"]["status"] == "UNCHANGED" and post["old_target_cache"]["before_count"] == post["old_target_cache"]["after_count"] == 63,
            "Old cache preservation not established")
    text = log_path.read_text()
    require(not re.search(r"\berror:|declaration uses.*sorry|sorryAx", text), "Unexpected error or unfinished proof in final log")
    matches = list(REPORT.finditer(text))
    endpoints = plan["endpoints"]
    require(len(endpoints) == len(matches) == 44, "Must parse exactly the 44 original reports")
    require(len(re.findall(r"^'[^'\r\n]+' (?:depends on axioms:|does not depend on any axioms)", text, re.M)) == 44,
            "Malformed or unconsumed axiom report")
    require([m.group(1) for m in matches] == [e["name"] for e in endpoints], "Missing, repeated, out-of-order or unexpected declaration")
    rows = []
    for index, (endpoint, match) in enumerate(zip(endpoints, matches), 1):
        type_pattern = re.compile(r"^@?" + re.escape(endpoint["name"]) + r"(?:\.\{[^{}]*\})?\s*:", re.M)
        type_hits = list(type_pattern.finditer(text, 0, match.start()))
        require(len(type_hits) == 1, "Each endpoint requires one actual printed type: " + endpoint["name"])
        begin = type_hits[0].start()
        token_rows = validate_tokens(match.group(2) or "", endpoint)
        rows.append({"index": index, **endpoint, "actual_type_raw": text[begin:match.start()].rstrip(),
                     "type_line_start": text.count("\n", 0, begin) + 1,
                     "type_line_end": text.count("\n", 0, match.start()),
                     "axiom_line_start": text.count("\n", 0, match.start()) + 1,
                     "axiom_line_end": text.count("\n", 0, match.end()),
                     "axiom_report_raw": match.group(0).rstrip("\n"),
                     "axiom_list_raw": match.group(2) or "", "axioms": token_rows,
                     "exact_allowed_native_constant": allowed_native(endpoint),
                     "axiom_check": "PASS_EXACT_STANDARD_OR_PREVIOUSLY_DISCLOSED_NATIVE"})
    result = {"schema": "UEOT-D3-OBSERVED-AXIOMS-POSTPROCESS-V1", "status": "PASS_STRICT_PARSING_AND_EVIDENCE_BINDING",
              "mathematical_semantic_review": "Recorded separately; this parser does not establish semantic adequacy",
              "new_lean_execution_in_this_postprocess": False, "original_receipts_modified": False,
              "original_wrapper_states": {"source_run": source["status"], "continuation": cont["status"]},
              "target_head": plan["target_head"], "parser_sha256": digest(__file__),
              "input_hashes": {str(p.relative_to(evidence)): digest(p) for p in (source_path, cont_path, post_path, log_path)},
              "original_plan_sha256": digest(args.plan), "endpoint_count": len(rows),
              "mode_counts": dict(Counter(e["evidence_mode"] for e in endpoints)),
              "standard_axiom_constants": list(STANDARD), "disclosed_native_count": sum(allowed_native(e) is not None for e in endpoints),
              "parser_validation": selfchecks(), "rows": rows}
    require(not args.output.exists(), "Use a new derived output; do not overwrite evidence")
    args.output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in ("status", "endpoint_count", "mode_counts", "disclosed_native_count", "parser_validation")}, indent=2))


if __name__ == "__main__":
    main()
