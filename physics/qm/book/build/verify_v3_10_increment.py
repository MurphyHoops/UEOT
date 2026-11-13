#!/usr/bin/env python3
"""Independent book-3.10 preservation, scope, and actual-evidence gate.

This file does not import the metadata generator or mutate scientific files.
Missing publication metadata yields CONTENT_PASS_METADATA_PENDING; use
--require-complete for the release gate. Altered historical bytes, invented
scope, or a false existing hash binding fail even in the development mode.
This is an identity/scope check, not a new physics, Lean or experimental proof.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import io
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import zipfile

BASELINE = "cb17211653fde30aa50e0e9848798a6a5b3b3f12"
BOOK = "physics/qm/book/"
EVIDENCE = BOOK + "evidence/v3.10/"
KERNEL_EVIDENCE = "physics/qm/kernel/evidence/v31.13/"
RUNTIME_DIR = KERNEL_EVIDENCE + "runtime/"
RUNTIME = RUNTIME_DIR + "execution_receipt.json"
DEFAULT_REUSE = KERNEL_EVIDENCE + "proof-reuse.json"
CODE = "physics/qm/simultaneous_cutoff/"
AUDIT = "physics/qm/audits/SIMULTANEOUS_CUTOFF_v31.13/"
NEW_IDS = ["P-OPT-05", "P-MICRO-06", "P-MICRO-07", "C-MICRO-03", "P-ROB-04", "P-ROB-05"]
PRIOR_PINS = {
    "CHAPTER_DOSSIER.json": "10106d93ed533f6eb925beb2da49330ef61140f6fb956255f43c312a7460fb37",
    "CURRENT.json": "2116731b8e35478a4564a9e4c2068326c2567a3359dba72a85aaae55695e2083",
    "README.md": "bddba87b3090f7c685acca5757ecdb30fb05dd12e5c7d9a103dba52a824ddb58",
    "SOURCE_MANIFEST.json": "eb025f0558852ec5f14549c734dcf42c217924ae462102bc71991c9edb95aa02",
    "UEOT_PHYSICS.en.md": "9ba8c0035f171091b753f02c0a452655cc7caf0eb00022a69085ae0e524ea8b1",
    "UEOT_PHYSICS.md": "b52a9b09881adc09432eae2d92ad8ec84cd5d4f23acb6d0340db6e350e33537d",
}
OLD_LEDGER = "physics/qm/status/CLAIM_LEDGER_v31.12.json"
OLD_LEDGER_SHA = "ad1297cdd59bcfa020cdce1ec30f4e3488c7e15ab9db62a54b3ebf7c2f2408f7"
COMMANDS = [
    ("source-integration", "verify_integration.py"),
    ("independent-operational", "check_full_cq_stability.py"),
    ("independent-microscopic", "check_simultaneous_galerkin.py"),
    ("synthetic-generation", "generate_synthetic.py"),
    ("truth-blind-calibration", "certify_from_records.py"),
    ("independent-rational-calibration", "independent_certificate_check.py"),
    ("integer-interval-prediction", "interval_predictor.py"),
    ("independent-interval-output", "verify_interval_output.py"),
    ("end-to-end-binding", "verify_end_to_end.py"),
]
INPUT_NAMES = ["FROZEN_CERTIFICATE_PLAN.json", "README.md", "certified_intervals.py",
    "certify_from_records.py", "check_full_cq_stability.py", "check_simultaneous_galerkin.py",
    "frozen_model.json", "generate_synthetic.py", "independent_certificate_check.py",
    "interval_predictor.py", "model.py", "run_verification.py", "verify_end_to_end.py",
    "verify_integration.py", "verify_interval_output.py"]
REPORT_NAMES = ["integration.json", "operational.json", "micro.json", "calibration.json",
    "independent-calibration.json", "interval-prediction.json", "independent-interval.json", "end-to-end.json"]
RAW_NAMES = ["compiled_holdout_records.txt", "drive_calibration_bits.txt", "drive_holdout_bits.txt",
    "drive_holdout_drift_bits.txt", "q_calibration_flags.txt", "source_holdout_records.txt"]


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def result_rows(dossier):
    return [r for ch in dossier.get("chapters", []) for r in ch.get("numbered_results", [])]


def sections(source):
    matches = list(re.finditer(r'^<a id="(ch-\d+|appendix-[a-z])"></a>\s*$', source, re.M))
    return {m.group(1): source[m.end(): matches[i+1].start() if i+1 < len(matches) else len(source)].strip()
            for i, m in enumerate(matches)}


def displays(source):
    output, active = [], None
    for line in source.splitlines():
        if line.strip() == "$$":
            if active is None:
                active = []
            else:
                output.append("\n".join(active)); active = None
        elif active is not None:
            active.append(line)
    if active is not None:
        raise ValueError("unclosed display-math fence")
    return output


def code_blocks(source):
    output, active, fence = [], None, None
    for line in source.splitlines():
        if active is None:
            m = re.match(r'^(`{3,}|~{3,})(.*)$', line)
            if m:
                fence, active = m.group(1), [line]
        else:
            active.append(line)
            if re.fullmatch(re.escape(fence) + r'\s*', line):
                output.append("\n".join(active)); active, fence = None, None
    if active is not None:
        raise ValueError("unclosed code fence")
    return output


def actual_results(source):
    body = source.split('<a id="appendix-a"></a>', 1)[0]
    pieces = re.split(r'(?m)^(<a id="[a-z0-9-]+"></a>)\s*$', body)
    chapter, rows = None, []
    for i, part in enumerate(pieces):
        if not part.startswith('<a id="'):
            continue
        anchor = re.fullmatch(r'<a id="([a-z0-9-]+)"></a>', part).group(1)
        if anchor.startswith("ch-"):
            chapter = int(anchor[3:]); continue
        title = re.match(r'\s*\*\*(.*?)\*\*', pieces[i+1] if i+1 < len(pieces) else "", re.S)
        if not title or "\n" in title.group(1):
            raise ValueError("result anchor lacks its immediate statement: " + anchor)
        rid = anchor.upper()
        if not re.match(re.escape(rid) + r'(?=$|[^A-Za-z0-9_-])', title.group(1)):
            raise ValueError("result title/anchor mismatch: " + anchor)
        rows.append({"id": rid, "chapter": chapter, "title": title.group(1)})
    return rows


def sha_values(value):
    if isinstance(value, dict):
        return set().union(*(sha_values(v) for v in value.values())) if value else set()
    if isinstance(value, list):
        return set().union(*(sha_values(v) for v in value)) if value else set()
    return {value} if isinstance(value, str) and re.fullmatch(r'[0-9a-f]{64}', value) else set()


def inspect(repo, reuse_rel=DEFAULT_REUSE):
    checks, pending, consumed = [], [], {}

    def check(name, ok, detail=None):
        if not bool(ok):
            raise ValueError(name + (": " + str(detail) if detail is not None else ""))
        checks.append({"name": name, "status": "PASS", "detail": detail})

    def need(name, ok):
        if ok:
            checks.append({"name": name, "status": "PASS"})
        elif name not in pending:
            pending.append(name)

    def read(rel):
        path = Path(rel)
        if path.is_absolute() or ".." in path.parts:
            raise ValueError("outside-repository evidence path: " + str(rel))
        raw = (repo / path).read_bytes()
        consumed[str(path)] = digest(raw)
        return raw

    def text(rel):
        return read(rel).decode("utf-8")

    def load(rel, optional=False):
        if optional and not (repo / rel).is_file():
            need("missing integration artifact: " + str(rel), False)
            return None
        return json.loads(text(rel))

    def identity(item, label, override=None):
        if not isinstance(item, dict) or not item.get("sha256") or not (override or item.get("path")):
            raise ValueError("incomplete file identity: " + label)
        rel = override or item["path"]
        raw = read(rel)
        check(label + " exact identity", digest(raw) == item["sha256"]
              and ("bytes" not in item or len(raw) == item["bytes"]), rel)
        return raw

    def all_passed(rows):
        return bool(rows) and all(r.get("status") == "PASS" or r.get("passed") is True
                                 or r.get("verified") is True for r in rows)

    # Historical source snapshots have independently verified immutable pins.
    for name, sha in PRIOR_PINS.items():
        check("immutable prior " + name, digest(read(EVIDENCE + "prior/" + name)) == sha)
    check("immutable previous 111-claim ledger", digest(read(OLD_LEDGER)) == OLD_LEDGER_SHA)
    old_dossier = load(EVIDENCE + "prior/CHAPTER_DOSSIER.json")
    dossier = load(BOOK + "CHAPTER_DOSSIER.json")
    old_rows, rows = result_rows(old_dossier), result_rows(dossier)
    old_ids, ids = [r["id"] for r in old_rows], [r["id"] for r in rows]
    check("188 unique inherited result objects", len(old_ids) == len(set(old_ids)) == 188)
    check("all 188 result objects and order unchanged", rows[:188] == old_rows)
    check("unique current result IDs", len(ids) == len(set(ids)))
    check("no reordered or unexpected new result", ids[188:] == NEW_IDS[:len(ids)-188] and 188 <= len(ids) <= 194)
    need("dossier edition 3.10 and 194 results", str(dossier.get("edition")) == "3.10" and len(rows) == 194)
    binding = load(AUDIT + "chapter69_formal_bindings.json", optional=True)
    if binding is not None:
        check("six ordered chapter69 bindings", binding.get("chapter") == 69 and binding.get("version") == "v31.13"
              and [r.get("id") for r in binding.get("results", [])] == NEW_IDS)
        check("bindings use actual research entry", binding.get("research_baseline") == BASELINE)
    for row in rows[188:] + (binding.get("results", []) if binding else []):
        rid = row["id"]
        check(rid + " chapter and anchor", row.get("chapter") == 69 and row.get("anchor") == rid.lower())
        check(rid + " no new Lean bindings", not row.get("formal_names") and not row.get("formal_bindings")
              and not any("lean" in str(k).lower() for k in row.get("verification_kind", [])))
        status = str(row.get("machine_status", "")).upper()
        check(rid + " paper-only universal theorem", "PAPER" in status and "ACCEPTED" not in status)
        empirical = row.get("status_axes", {}).get("empirical", row.get("empirical_status"))
        check(rid + " empirical remains untested", empirical in {"NOT_TESTED", "UNTESTED", "UNVERIFIED", "NO_REAL_DATA"})
        if "new_hardware_data" in row:
            check(rid + " no invented hardware data", row["new_hardware_data"] is False)

    old_claims = load(OLD_LEDGER)["claims"]
    check("previous ledger contains exactly 111 claims", len(old_claims) == 111)
    ledger = load("physics/qm/status/CLAIM_LEDGER_v31.13.json", optional=True)
    if ledger is not None:
        claims = ledger["claims"]
        check("all 111 old claim objects and order unchanged", claims[:111] == old_claims)
        check("only six registered claim additions", 111 <= len(claims) <= 117
              and [r.get("book_result") for r in claims[111:]] == NEW_IDS[:len(claims)-111])
        need("117 claims including all six new results", len(claims) == 117)
        for row in claims[111:]:
            check(row["id"] + " paper-only and no hardware", "PAPER" in str(row.get("machine_status", "")).upper()
                  and "ACCEPTED" not in str(row.get("machine_status", "")).upper()
                  and row.get("new_hardware_data") is False)

    texts, parsed, maths = {}, {}, {}
    for lang, suffix in [("zh", ""), ("en", ".en")]:
        name = "UEOT_PHYSICS" + suffix + ".md"
        old_text, now = text(EVIDENCE + "prior/" + name), text(BOOK + name)
        texts[lang] = now
        old, new = sections(old_text), sections(now)
        before, after = actual_results(old_text), actual_results(now)
        parsed[lang] = after
        check(lang + " all inherited statement IDs, titles and chapters unchanged", after[:188] == before and [r["id"] for r in before] == old_ids)
        check(lang + " new body statements match reviewed order", [r["id"] for r in after[188:]] == NEW_IDS)
        check(lang + " exactly 194 numbered body statements", len(after) == 194)
        check(lang + " all new statements belong to chapter69", all(r["chapter"] == 69 for r in after[188:]))
        check(lang + " contiguous 70-chapter sequence", list(map(int, re.findall(r'^# (\d+)\.', now, re.M))) == list(range(70)))
        check(lang + " six appendices", sorted(k for k in new if k.startswith("appendix-")) == ["appendix-" + c for c in "abcdef"])
        check(lang + " source declares edition 3.10", bool(re.search(r'^version:\s*"3\.10"\s*$', now, re.M)))
        anchors = re.findall(r'<a id="([^"]+)"></a>', now)
        check(lang + " unique stable anchors", len(anchors) == len(set(anchors)))
        check(lang + " chapter0 old sections remain an exact prefix", new["ch-0"].startswith(old["ch-0"]))
        for number in range(1, 69):
            key = "ch-" + str(number)
            if number != 48:
                check(lang + " historical chapter body " + str(number), old[key] == new[key])
        # The only permitted chapter48 edits are current-edition metadata.
        expected48 = old["ch-48"]
        replacements = ([("当前正式双语修订版为3.9", "当前正式双语修订版为3.10"), ("第0–68章", "第0–69章")]
                        if lang == "zh" else
                        [("current bilingual revision is 3.9", "current bilingual revision is 3.10"), ("Chapters 0–68", "Chapters 0–69")])
        replacements.append(('edition: "3.9"', 'edition: "3.10"'))
        for a, b in replacements:
            check(lang + " unique metadata replacement " + a, expected48.count(a) == 1)
            expected48 = expected48.replace(a, b, 1)
        check(lang + " chapter48 changes only approved metadata", new["ch-48"] == expected48)
        for key in old:
            check(lang + " all inherited display formulas " + key, displays(old[key]) == displays(new[key]))
        check(lang + " appendixD programs preserved exactly", code_blocks(old["appendix-d"]) == code_blocks(new["appendix-d"]))
        chapter = new["ch-69"]
        check(lang + " nine ordered new subsections", re.findall(r'^## (69\.\d+)\b', chapter, re.M) == ["69." + str(i) for i in range(1, 10)])
        maths[lang] = displays(chapter)
        check(lang + " ten new display groups", len(maths[lang]) == 10)
        if lang == "zh":
            check("Chinese exact-map and one-input numerical scopes", all(s in chapter for s in ["此数值认证只覆盖指定输入", "全输入定理针对精确有限映射", "没有新增 Lean 声明", "经验轴仍未检验", "不能改成仅在获准输出证书后的条件覆盖率"]))
        else:
            check("English exact-map and one-input numerical scopes", all(s in chapter for s in ["This numerical certificate concerns that input only", "all-input theorem above concerns the exact finite map", "no new Lean declarations", "empirical axis remains untested", "not conditional coverage after admission"]))
    check("new bilingual displayed mathematics identical", maths["zh"] == maths["en"])
    if binding:
        check("binding Chinese statement titles match actual body", [r["title"] for r in binding["results"]] == [r["title"] for r in parsed["zh"][188:]])
    for token in ["2969/50000", "0.041930158795", "624", "313"]:
        check("reviewed certificate display token " + token, token in "\n".join(maths["zh"]))
    for lang in ["zh", "en"]:
        for token in ["4095", "4175"]:
            check(lang + " declared cutoff " + token, token in sections(texts[lang])["ch-69"])

    old_manifest = load(EVIDENCE + "prior/SOURCE_MANIFEST.json")
    manifest = load(BOOK + "SOURCE_MANIFEST.json")
    old_entries = old_manifest["entries"]
    check("historical source catalog entries and order unchanged", manifest["entries"][:len(old_entries)] == old_entries)
    need("source manifest edition 3.10", str(manifest.get("edition")) == "3.10")
    for key, lang, filename in [("canonical_identity", "zh", "UEOT_PHYSICS.md"), ("canonical_english_identity", "en", "UEOT_PHYSICS.en.md")]:
        entry = manifest.get(key, {})
        need(lang + " canonical manifest matches final manuscript", entry.get("path") == BOOK + filename
             and entry.get("sha256") == digest(texts[lang].encode()) and entry.get("chapters") == 70
             and entry.get("appendices") == 6 and entry.get("numbered_results") == 194)

    # Inventory the historical evidence tree without modifying or rerunning it.
    try:
        roots = ["physics/qm/kernel/evidence", "physics/qm/book/evidence"]
        historic = set(subprocess.check_output(["git", "ls-tree", "-r", "--name-only", BASELINE, "--", *roots], cwd=repo, text=True, stderr=subprocess.PIPE).splitlines())
        changed = set(subprocess.check_output(["git", "diff", "--name-only", BASELINE, "--", *roots], cwd=repo, text=True, stderr=subprocess.PIPE).splitlines())
        check("historical published evidence unchanged", bool(historic) and not historic.intersection(changed), sorted(historic.intersection(changed)))
    except subprocess.CalledProcessError:
        need("historical Git object required for complete old-evidence inventory", False)

    runtime = load(RUNTIME, optional=True)
    if runtime is not None:
        commands = runtime.get("commands", [])
        check("nine actual runtime commands passed", runtime.get("status") == "PASS" and runtime.get("version") == "v31.13"
              and [c.get("label") for c in commands] == [c[0] for c in COMMANDS]
              and all(c.get("exit_code") == 0 for c in commands))
        check("runtime inputs were stable", runtime.get("inputs_stable_during_execution") is True)
        check("runtime has no new Lean/hardware claim", runtime.get("new_lean_execution") is False and runtime.get("new_hardware_data") is False)
        context = runtime.get("execution_context", {})
        check("observed runtime provider and checkout recorded", context.get("provider") in {"local_python_process", "github_actions"}
              and bool(re.fullmatch(r'[0-9a-f]{40}', str(context.get("observed_git_head", ""))))
              and isinstance(context.get("worktree_has_changes"), bool))
        if context.get("provider") == "github_actions":
            check("actual GitHub workflow identity", all(context.get("github", {}).get(k) for k in ["GITHUB_RUN_ID", "GITHUB_RUN_ATTEMPT", "GITHUB_REPOSITORY", "GITHUB_JOB", "GITHUB_SHA"]))
        wanted_inputs = {CODE + n for n in INPUT_NAMES} | {"physics/qm/conditioning/finite_conditioning.py", AUDIT + "SHARED_MODEL.md"}
        ins = runtime.get("inputs", [])
        check("exact seventeen runtime inputs", len(ins) == 17 and {x.get("path") for x in ins} == wanted_inputs)
        wanted_outputs = {RUNTIME_DIR + n for n in REPORT_NAMES + [label + ".log" for label, _ in COMMANDS] + ["synthetic_raw.zip"]}
        outs = runtime.get("outputs", [])
        check("exact eighteen runtime artifacts", len(outs) == 18 and {x.get("path") for x in outs} == wanted_outputs)
        for item in ins + outs:
            identity(item, "runtime")
        previous_end = None
        for cmd, (label, script) in zip(commands, COMMANDS):
            check(label + " actual invoked script", len(cmd.get("argv", [])) >= 2 and Path(cmd["argv"][1]).name == script)
            start, end = datetime.fromisoformat(cmd["started_at_utc"]), datetime.fromisoformat(cmd["finished_at_utc"])
            check(label + " chronological execution", start <= end and (previous_end is None or previous_end <= start))
            previous_end = end
            log = identity(cmd["log"], label + " actual log")
            check(label + " portable log binding", cmd["log"]["path"] == RUNTIME_DIR + label + ".log")
            printed = json.loads(log.decode().strip().splitlines()[-1])
            check(label + " actual stdout indicates scoped success", printed.get("status") in {"PASS", "CERTIFIED", "CERTIFIED_EXACT_FINITE_MODEL_BOUND"}
                  or printed.get("classification") == "SYNTHETIC_ONLY")
        check("runtime receipt follows command execution", datetime.fromisoformat(runtime["created_at_utc"]) >= previous_end)
        members = runtime.get("raw_archive_members", [])
        wanted_members = set(RAW_NAMES + ["synthetic_provenance.json"])
        check("seven complete raw archive member identities", len(members) == 7 and {m.get("member") for m in members} == wanted_members)
        zipped = read(RUNTIME_DIR + "synthetic_raw.zip")
        with zipfile.ZipFile(io.BytesIO(zipped)) as archive:
            check("actual ZIP has exactly seven unique members", len(archive.namelist()) == 7 and set(archive.namelist()) == wanted_members)
            raw_bytes = {}
            for item in members:
                raw = archive.read(item["member"]); raw_bytes[item["member"]] = raw
                check("actual archived bytes " + item["member"], item.get("archive") == "synthetic_raw.zip" and digest(raw) == item["sha256"] and len(raw) == item["bytes"])
        details = {n: load(RUNTIME_DIR + n) for n in REPORT_NAMES}
        source = lambda name: digest(read(CODE + name))
        for filename, script, field in [("integration.json", "verify_integration.py", "script_sha256"),
            ("operational.json", "check_full_cq_stability.py", "script_sha256"),
            ("micro.json", "check_simultaneous_galerkin.py", "source_sha256")]:
            item = details[filename]
            check(filename + " actual script and passed checks", item.get("status") == "PASS" and item.get(field) == source(script)
                  and item.get("check_count") == len(item.get("checks", [])) and all_passed(item.get("checks", []))
                  and item.get("new_hardware_data") is False)
        check("microscopic source shared-model identity", details["micro.json"]["frozen_model_sha256"] == source("frozen_model.json"))
        cal, independent = details["calibration.json"], details["independent-calibration.json"]
        check("calibration exact source identities", cal["input_identity"] == {"plan_sha256": source("FROZEN_CERTIFICATE_PLAN.json"),
              "analyzer_sha256": source("certify_from_records.py"), "intervals_sha256": source("certified_intervals.py")})
        check("calibration has conditional and untested scope", cal.get("status") == "CERTIFIED" and cal.get("new_hardware_data") is False
              and cal.get("device_membership") == "UNVERIFIED" and cal.get("empirical_full_CQ_status") == "UNTESTED"
              and cal["certificate"]["hidden_truth_consumed"] is False)
        raw_hashes = {n: digest(raw_bytes[n]) for n in RAW_NAMES}
        check("both calibration checks consume actual raw members", cal["raw_sha256"] == independent["raw_sha256"] == raw_hashes)
        expected_independent = {"plan": source("FROZEN_CERTIFICATE_PLAN.json"), "analysis": digest(read(RUNTIME_DIR + "calibration.json")),
                                "checker": source("independent_certificate_check.py"), "shared_model": source("frozen_model.json")}
        check("independent calibration source and actual executor", independent.get("status") == "PASS"
              and independent.get("consumed_sha256") == expected_independent and independent.get("executor") == context["provider"]
              and independent.get("passed_checks") == len(independent.get("checks", [])) and all_passed(independent.get("checks", [])))
        provenance = json.loads(raw_bytes["synthetic_provenance.json"])
        check("raw provenance remains synthetic and independently identified", provenance.get("classification") == "SYNTHETIC_ONLY"
              and provenance.get("new_hardware_data") is False and provenance.get("raw_sha256") == raw_hashes
              and provenance.get("plan_sha256") == source("FROZEN_CERTIFICATE_PLAN.json")
              and provenance.get("generator_sha256") == source("generate_synthetic.py"))
        pred, verified = details["interval-prediction.json"], details["independent-interval.json"]
        check("nominal predictor consumes final observed calibration", pred.get("status") == "PASS"
              and pred.get("script_sha256") == source("interval_predictor.py")
              and pred.get("nominal_x") == cal["nominal_x"] == cal["certificate"]["xhat"]
              and pred.get("calibration_identity", {}).get("sha256") == digest(read(RUNTIME_DIR + "calibration.json")))
        check("numerical predictor has one specified input scope", pred.get("Galerkin_K") == 4175
              and pred.get("initial_G_support") == 1 and pred.get("reference_dimension") == 2
              and "one specified" in pred.get("scope", "") and pred.get("new_hardware_data") is False
              and pred.get("not_an_independent_quantum_hardware_implementation") is True)
        numerical = Fraction(pred["complete_CQ_numerical_error_upper"])
        check("actual arithmetic allowance meets frozen budget", 0 <= numerical < Fraction(1, 10**8) and Fraction(pred["reserved_budget"]) == Fraction(1, 10**8))
        for field, path in [("artifact", RUNTIME_DIR + "interval-prediction.json"), ("predictor_source", CODE + "interval_predictor.py"), ("checker_source", CODE + "verify_interval_output.py")]:
            identity(verified[field], "independent interval " + field, override=path)
        check("interval independent verdict and arithmetic agree", verified.get("status") == "PASS"
              and all_passed(verified.get("checks", [])) and verified.get("check_count") == len(verified.get("checks", []))
              and Fraction(verified["complete_CQ_numerical_error_upper"]) == numerical)
        end = details["end-to-end.json"]
        check("end-to-end binds all seven upstream reports", end.get("inputs") == {n: digest(read(RUNTIME_DIR + n)) for n in REPORT_NAMES if n != "end-to-end.json"})
        exact = Fraction(cal["certificate"]["exact_finite_predictor_bound_interval"][1])
        check("same-output final arithmetic and separate numerical scope", end.get("status") == "PASS"
              and Fraction(end["exact_finite_map_uniform_bound"]) == exact
              and Fraction(end["specified_input_numerical_error"]) == numerical
              and Fraction(end["specified_input_total_bound"]) == exact + numerical
              and Fraction(end["specified_input_bound_with_reserved_error"]) == exact + Fraction(1, 10**8) < Fraction(1, 20)
              and end.get("universal_numerical_certification") is False and end.get("new_lean_execution") is False)
        check("different-setting holdout and mismatch control have actual outcomes", cal["holdout"]["drive"]["status"] == "NOT_REJECTED_BY_FROZEN_DRIVE_TESTER"
              and cal["controls"]["nonshared_pulse_holdout"]["status"] == "REJECTED_BY_FROZEN_DRIVE_TESTER"
              and cal["controls"]["wider_calibration_precision"]["status"] == "INSUFFICIENT_BOUND")

    reuse = load(reuse_rel, optional=True)
    if reuse is not None:
        check("scoped inherited proof reuse actually eligible", reuse.get("status") == "SOURCE_IDENTITY_REUSED"
              and reuse.get("proof_reuse_eligible") is True and reuse.get("proof_input_count") == 158
              and reuse.get("old_runtime_input_count") == 13 and reuse.get("old_runtime_inputs_identical") is True
              and not reuse.get("errors") and not reuse.get("runtime_mismatches"))
        check("historical proof run identity retained", reuse.get("reused_proof_commit") == "06ca0dce8b03cd34e86785e97fdc3c7aa2c582bd"
              and reuse.get("reused_workflow_run") == 43001276385 and reuse.get("reused_axiom_reports") == 1365)
        check("no new Lean run or theorem inferred", reuse.get("new_lean_execution") is False
              and reuse.get("new_lean_theorems") == 0 and reuse.get("new_paper_claims_not_promoted_to_lean") is True)
        previous_proof = load("physics/qm/kernel/evidence/v31.11/source-manifest.json")
        check("158 actual proof inputs with unchanged source-set identity", len(previous_proof["sources"]) == 158
              and previous_proof["source_set_sha256"] == reuse.get("proof_source_set_sha256"))
        for item in previous_proof["sources"]:
            identity(item, "reused proof input")
        previous_runtime = load("physics/qm/kernel/evidence/v31.11/runtime/execution_receipt.json")
        check("13 actual inherited runtime inputs", len(previous_runtime["inputs"]) == 13)
        for item in previous_runtime["inputs"]:
            identity(item, "reused old runtime input")

    source_manifest = load(KERNEL_EVIDENCE + "source-manifest.json", optional=True)
    if source_manifest is not None:
        check("new source manifest actual scope and baseline", source_manifest.get("schema") == "ueot-qm.increment-source-manifest/1"
              and source_manifest.get("version") == "v31.13" and source_manifest.get("research_baseline") == BASELINE
              and source_manifest.get("new_hardware_data") is False)
        identity(source_manifest["inherited_proof"], "science manifest inherited proof")
        identity(source_manifest["new_runtime_receipt"], "science manifest actual runtime")
        check("manifest points to this exact proof and runtime", source_manifest["inherited_proof"]["path"] == DEFAULT_REUSE
              and source_manifest["new_runtime_receipt"]["path"] == RUNTIME)
        sources = source_manifest.get("new_runtime_inputs", [])
        check("source manifest carries the same seventeen executed inputs", runtime is not None
              and source_manifest.get("new_runtime_input_count") == 17 and sources == runtime["inputs"])
        papers = source_manifest.get("paper_and_release_inputs", [])
        check("paper/publication source manifest has distinct actual inputs", bool(papers)
              and len({i.get("path") for i in papers}) == len(papers))
        forbidden = {"physics/qm/status/CURRENT.json", BOOK + "CHAPTER_DOSSIER.json", BOOK + "SOURCE_MANIFEST.json",
                     EVIDENCE + "local-acceptance.json", EVIDENCE + "increment-verification.json"}
        check("science manifest avoids mutable-index and gate cycles", not forbidden.intersection(i.get("path") for i in papers))
        for item in sources + papers:
            identity(item, "current science source manifest")

    current = load("physics/qm/status/CURRENT.json")
    is_current = current.get("version") == "v31.13"
    need("CURRENT advances to actual v31.13", is_current)
    if is_current:
        pointers = {"kernel": "physics/qm/UEOT_QM_KERNEL_v31.13.md", "execution_contract": "physics/qm/UEOT_QM_EXECUTION_v31.13.md",
                    "claim_ledger": "physics/qm/status/CLAIM_LEDGER_v31.13.json", "proof_reuse_receipt": DEFAULT_REUSE,
                    "runtime_receipt": RUNTIME, "increment_source_manifest": KERNEL_EVIDENCE + "source-manifest.json"}
        for key, value in pointers.items():
            check("CURRENT pointer " + key, current.get(key) == value and (repo / value).is_file())
        check("CURRENT no hardware claim", current.get("new_hardware_data") is False)
        check("CURRENT scientific, empirical and computational axes", current.get("kernel_version") == "1.13"
              and current.get("research_baseline") == BASELINE
              and current.get("status_axes", {}).get("empirical") == "UNTESTED_NO_REAL_DEVICE_DATA"
              and current.get("local_verification", {}).get("new_lean") is False
              and "ONE_INPUT" in current.get("status_axes", {}).get("computational", ""))
        book_current = current.get("book", {})
        check("CURRENT book counts and no global formalization", book_current.get("edition") == "3.10"
              and book_current.get("chapters") == 70 and book_current.get("appendices") == 6
              and book_current.get("numbered_results") == 194 and book_current.get("inherited_numbered_results") == 188
              and book_current.get("new_numbered_results") == 6 and book_current.get("whole_book_formalized") is False
              and current.get("completed_in_this_delivery") == NEW_IDS)
        check("CURRENT points to actual book acceptance", book_current.get("local_acceptance") == EVIDENCE + "local-acceptance.json")
        identity(book_current["dossier"], "CURRENT actual dossier")
        identity(dossier["book_source_manifest"], "dossier actual book source manifest")
        for key in ["canonical", "canonical_english"]:
            identity(dossier[key], "dossier " + key)

    for lang, suffix in [("zh", ""), ("en", ".en")]:
        build = load(EVIDENCE + lang + "/pdf-build.json", optional=True)
        if build is None:
            continue
        check(lang + " PDF edition and source structure", str(build.get("edition")) == "3.10" and build.get("chapters") == 70 and build.get("appendices") == 6)
        header = BOOK + "build/header" + (".en" if lang == "en" else "") + ".tex"
        for rel, key in [(BOOK + "build/build_pdf.py", "builder_sha256"), (header, "header_sha256"), (BOOK + "build/tables.lua", "tables_filter_sha256")]:
            check(lang + " PDF build dependency " + key, digest(read(rel)) == build.get(key))
        for extension, field in [("md", "source_sha256"), ("tex", "tex_sha256"), ("pdf", "pdf_sha256")]:
            identity({"path": BOOK + "UEOT_PHYSICS" + suffix + "." + extension, "sha256": build.get(field)}, lang + " delivered " + extension)
        passes = build.get("compile_passes", [])
        check(lang + " three actual successful compile passes", len(passes) == 3 and all(p.get("exit_code") == 0 for p in passes))
        check(lang + " final PDF warning and convergence scope", build.get("layout_warnings") == [] and build.get("rerun_warnings") == []
              and build.get("last_two_auxiliary_files_identical") is True and passes[-1].get("auxiliary_sha256") == passes[-2].get("auxiliary_sha256"))
        for item in passes:
            identity({"path": EVIDENCE + lang + "/" + item["file"], "sha256": item["sha256"]}, lang + " actual TeX log")
        header_text = text(header)
        preamble = text(BOOK + "UEOT_PHYSICS" + suffix + ".tex").split(r"\begin{document}", 1)[0]
        running = (r"\fancyhead[R]{\small 物理学 · 3.10 双语修订版}" if lang == "zh" else r"\fancyhead[R]{\small Bilingual revision 3.10}")
        check(lang + " actual running header has current edition", header_text.count(running) == preamble.count(running) == 1)
        pattern = r'\\begin\{titlepage\}(.*?)\\end\{titlepage\}'
        covers, template = re.findall(pattern, preamble, re.S), re.findall(pattern, header_text, re.S)
        check(lang + " generated cover exactly matches final template", len(covers) == len(template) == 1 and covers == template)
        tokens = (["3.10 双语修订版", "70章", "6个附录", "UEOT-QM Kernel 1.13", "2026年11月12日"] if lang == "zh"
                  else ["Bilingual revision 3.10", "70 chapters", "6 appendices", "UEOT-QM Kernel 1.13", "12 November 2026"])
        check(lang + " generated cover counts and kernel identity", all(s in covers[0] for s in tokens)
              and "3.9" not in covers[0] and "Kernel 1.12" not in covers[0])
        check(lang + " generated publication date", preamble.count(r"\date{2026-11-12}") == 1)

    visual = load(EVIDENCE + "visual-review.json", optional=True)
    if visual is not None:
        check("scoped actual visual inspection recorded", str(visual.get("status", "")).startswith("PASS")
              and visual.get("edition") == "3.10" and bool(visual.get("scope"))
              and visual.get("independent_human_peer_review") is False
              and "not a whole-book or scientific proof" in visual["scope"])
        docs = visual.get("languages", {})
        check("both languages visually reviewed", set(docs) == {"zh", "en"})
        total_images = 0
        for lang in ["zh", "en"]:
            doc = docs[lang]
            identity(doc["pdf"], lang + " visual final PDF")
            bound_build = json.loads(identity(doc["build"], lang + " visual actual build"))
            check(lang + " visual PDF bound through final build", bound_build["pdf_sha256"] == doc["pdf"]["sha256"])
            # MD and TeX are bound by this same build and the local publication
            # receipt; the visual review is specifically of the rendered PDF.
            suffix = "" if lang == "zh" else ".en"
            for extension, field in [("md", "source_sha256"), ("tex", "tex_sha256")]:
                identity({"path": BOOK + "UEOT_PHYSICS" + suffix + "." + extension, "sha256": bound_build[field]}, lang + " visual build source " + extension)
            pages = doc.get("physical_pages", [])
            chapter_pages = list(range(234, 240)) if lang == "zh" else list(range(279, 286))
            check(lang + " actual new chapter and scoped pages recorded", bool(pages) and bool(chapter_pages)
                  and len(pages) == len(set(pages)) == (13 if lang == "zh" else 15)
                  and all(isinstance(n, int) and 0 < n <= doc["page_count"] for n in pages)
                  and set(chapter_pages).issubset(pages)
                  and set(doc.get("root_pages_actually_viewed", [])).issubset(pages))
            reviewed = json.loads(identity(doc["original_review"], lang + " original visual review"))
            check(lang + " original visual review binds final PDF", doc["pdf"]["sha256"] in sha_values(reviewed))
            if lang == "zh":
                check("Chinese actual visual verdict", reviewed.get("status") == "PASS_VISUAL_SCOPED"
                      and reviewed.get("pdf_bytes_unchanged_since_render") is True
                      and reviewed.get("physical_pages_actually_viewed") == pages
                      and reviewed.get("new_lean_execution") is False and reviewed.get("new_hardware_data") is False)
                rows = reviewed.get("inspected_pages", [])
                original_pages = {row["physical_page"]: row for row in rows}
                check("Chinese every listed page was actually viewed", len(rows) == len(pages)
                      and set(original_pages) == set(pages)
                      and all(row.get("visually_viewed") is True and row.get("status") == "PASS" for row in rows))
                image_names = {Path(row["path"]).name: row["sha256"] for row in rows}
            else:
                check("English final scoped visual verdict", reviewed.get("visual_review_status") == "PASS_FOR_LISTED_PAGES"
                      and reviewed.get("issues_remaining") == [] and reviewed.get("external_human_peer_review") is False)
                rows = reviewed.get("pages", [])
                original_pages = {row["pdf_page_1_based"]: row for row in rows}
                check("English actual reviewed pages have precise scope", len(rows) == len(pages) and set(original_pages) == set(pages)
                      and all(row.get("status") == "PASS" for row in rows))
                earlier = json.loads(identity(visual["english_prior_issue_review"], "preserved English prior issue review"))
                check("English prior layout failure not relabelled PASS", earlier.get("visual_review_status") == "COMPLETED_WITH_ONE_TOC_LAYOUT_ISSUE"
                      and bool(earlier.get("issues")) and earlier.get("external_human_peer_review") is False)
                previous_pages = {row["pdf_page_1_based"]: row for row in earlier["pages"]}
                fresh = set(reviewed.get("actually_viewed_final_png_pages", []))
                reused = set(reviewed.get("prior_actual_review_reused_by_exact_png_identity", []))
                check("English fresh and exactly reused visual work partition", fresh == {3, 4}
                      and fresh.isdisjoint(reused) and fresh | reused == set(pages))
                for p in pages:
                    row = original_pages[p]
                    if p in reused:
                        old_page = previous_pages[p]
                        check("English actual PNG reuse page " + str(p), row.get("same_rendered_bytes_as_viewed_v4") is True
                              and row["png_sha256"] == row["v4_png_sha256"] == old_page["png_sha256"]
                              and old_page.get("actually_viewed") is True and old_page.get("status") == "PASS")
                    else:
                        check("English final changed page actually re-viewed " + str(p), row.get("same_rendered_bytes_as_viewed_v4") is False
                              and "Actually opened and visually inspected" in row.get("review_method", "")
                              and row["png_sha256"] != row["v4_png_sha256"])
                image_names = {Path(row["png_path"]).name: row["png_sha256"] for row in rows}
            members = doc.get("image_members", [])
            check(lang + " final archived page inventory matches reviewed images", len(members) == len(pages)
                  and {m["member"]: m["sha256"] for m in members} == image_names)
            archive_raw = identity(doc["image_archive"], lang + " actually viewed image archive")
            with zipfile.ZipFile(io.BytesIO(archive_raw)) as archive:
                check(lang + " actual image ZIP has no omitted or extra members", len(archive.namelist()) == len(members)
                      and set(archive.namelist()) == set(image_names))
                for member in members:
                    raw = archive.read(member["member"])
                    check(lang + " viewed PNG identity " + member["member"], digest(raw) == member["sha256"]
                          and len(raw) == member["bytes"] and raw.startswith(b'\x89PNG\r\n\x1a\n'))
            total_images += len(members)
        check("all twenty-eight actual viewed PNGs accounted for", total_images == 28)

    acceptance = load(EVIDENCE + "local-acceptance.json", optional=True)
    if acceptance is not None:
        check("local acceptance scope is explicit and actual", str(acceptance.get("status", "")).startswith("PASS")
              and acceptance.get("research_baseline") == BASELINE and bool(acceptance.get("scope"))
              and acceptance.get("new_lean_execution") is False and acceptance.get("new_hardware_data") is False)
        artifacts = acceptance.get("current_artifacts", [])
        required = {BOOK + "UEOT_PHYSICS" + suffix + "." + ext for suffix in ["", ".en"] for ext in ["md", "tex", "pdf"]}
        required |= {BOOK + "PHYSICS_RESULT_MAPPING.md", BOOK + "PUBLICATION_RIGHTS.md", RUNTIME, DEFAULT_REUSE,
                     KERNEL_EVIDENCE + "source-manifest.json", EVIDENCE + "zh/pdf-build.json", EVIDENCE + "en/pdf-build.json", EVIDENCE + "visual-review.json"}
        check("local acceptance binds full required publication evidence", required.issubset({i.get("path") for i in artifacts}))
        check("local acceptance has no self/gate hash cycle", not any(i.get("path") in {EVIDENCE + "local-acceptance.json", EVIDENCE + "increment-verification.json"} for i in artifacts))
        for item in artifacts + acceptance.get("review_files", []):
            identity(item, "local acceptance")
        check("exactly the three authorized review roles", set(acceptance.get("native_review_tasks", [])) == {"a_operational_semantics", "b_micro_dynamics", "c_robust_evidence"})
        need("actual independent review files bound", bool(acceptance.get("review_files")))

    changed = [rel for rel, sha in consumed.items() if digest((repo / rel).read_bytes()) != sha]
    check("consumed bytes stable throughout this verification", not changed, changed)
    return {"schema": "ueot_physics.v3.10.increment-independent/1", "status": "PASS" if not pending else "CONTENT_PASS_METADATA_PENDING",
        "executed_at_utc": datetime.now(timezone.utc).isoformat(), "source_baseline": BASELINE,
        "prior_result_count": 188, "new_result_count": 6, "total_result_count": 194,
        "historical_result_object_identity": "EXACTLY_PRESERVED", "historical_claim_count": 111,
        "new_claim_count": 6, "total_claim_count": 117,
        "chapter69_display_math": {"count": len(maths["zh"]), "bilingual_literal_identity": True,
                                   "sha256": [digest(s.encode()) for s in maths["zh"]]},
        "new_result_mapping": [{"id": a["id"], "chapter": 69, "zh_title": a["title"], "en_title": b["title"]}
                               for a, b in zip(parsed["zh"][188:], parsed["en"][188:])],
        "historical_body_policy": "Chapters1-68 exactly unchanged except three specified chapter48 edition/count substitutions; chapter0 old text is an exact prefix; all inherited display groups and appendixD programs unchanged",
        "checks": checks, "pending_integration": pending, "consumed_sha256": consumed,
        "limits": ["Identity and scope checks do not prove universal mathematical truth", "No new Lean compiler or axiom-audit execution",
                   "Actual scoped visual receipts are checked, not generated or substituted by this program",
                   "No actual device verification, measured resource advantage or remote publication inferred",
                   "Exact finite-map full-domain theorem and one-input numerical output remain separate"]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--proof-reuse", default=DEFAULT_REUSE)
    parser.add_argument("--require-complete", action="store_true")
    args = parser.parse_args()
    try:
        report = inspect(args.repo_root.resolve(), args.proof_reuse)
    except (ValueError, KeyError, FileNotFoundError, json.JSONDecodeError, TypeError, zipfile.BadZipFile) as exc:
        report = {"schema": "ueot_physics.v3.10.increment-independent/1", "status": "FAIL", "error": str(exc),
                  "executed_at_utc": datetime.now(timezone.utc).isoformat()}
    context = {"provider": "github_actions" if os.environ.get("GITHUB_ACTIONS") == "true" else "local_python_process",
               "authority": "Observed execution environment; checker authorship is not the executor identity."}
    try:
        context["observed_git_head"] = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=args.repo_root, text=True, stderr=subprocess.PIPE).strip()
        context["worktree_has_changes"] = bool(subprocess.check_output(["git", "status", "--porcelain"], cwd=args.repo_root, text=True, stderr=subprocess.PIPE).strip())
    except (subprocess.CalledProcessError, FileNotFoundError) as exc:
        context["git_observation_error"] = str(exc)
    if context["provider"] == "github_actions":
        context["github"] = {key: os.environ.get(key) for key in ["GITHUB_RUN_ID", "GITHUB_RUN_ATTEMPT", "GITHUB_REPOSITORY", "GITHUB_JOB", "GITHUB_SHA", "GITHUB_REF"]}
    report["execution_context"] = context
    report["checker_author"] = "native research agent C"
    report["checker_sha256"] = digest(Path(__file__).read_bytes())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({k: report[k] for k in ["status", "pending_integration", "error"] if k in report}, ensure_ascii=False))
    return 2 if report["status"] == "FAIL" else 3 if args.require_complete and report.get("pending_integration") else 0


if __name__ == "__main__":
    sys.exit(main())
