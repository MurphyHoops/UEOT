#!/usr/bin/env python3
"""Independent book-3.9 preservation, scope, and publication-evidence checker.

Does not import a production metadata generator or mutate scientific metadata.
Missing integration artifacts are reported as PENDING; --require-complete
makes them a failed release gate. Changed historical objects, altered scientific
body text outside the one reviewed erratum, and false evidence bindings fail in
both modes. This is identity/scope verification, not a new physics or Lean proof.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys


BASELINE = "aea2fceef3c62cc8dc749b6cbb1b40a7d89df80d"
BOOK = "physics/qm/book/"
EVIDENCE = BOOK + "evidence/v3.9/"
RUNTIME = "physics/qm/kernel/evidence/v31.12/runtime/execution_receipt.json"
DEFAULT_REUSE = "physics/qm/kernel/evidence/v31.12/proof-reuse.json"
NEW_IDS = ["P-MICRO-04", "P-OPT-04", "P-MICRO-05", "C-MICRO-02", "P-ROB-03", "C-ROB-02"]
TITLES = {
    "P-MICRO-04": ("P-MICRO-04（分段蓝脉冲的有限激发增长）。", "P-MICRO-04 (Finite excitation growth under segmented blue pulses)."),
    "P-OPT-04": ("P-OPT-04（增长载体上的完整矩形操作桥）。", "P-OPT-04 (Complete rectangular operations on growing carriers)."),
    "P-MICRO-05": ("P-MICRO-05（无蓝参照下的完整记录省略界）。", "P-MICRO-05 (Complete-record omission bound using a no-blue reference)."),
    "C-MICRO-02": ("C-MICRO-02（同时红蓝作用的无限尾反例）。", "C-MICRO-02 (An infinite-tail counterexample for simultaneous red and blue interaction)."),
    "P-ROB-03": ("P-ROB-03（增长源、物理过滤与省略实现的统一证书）。", "P-ROB-03 (A joint certificate for growth, physical filtering, and pulse omission)."),
    "C-ROB-02": ("C-ROB-02（相同旗概率不认证蓝脉冲末态）。", "C-ROB-02 (Identical flag probabilities do not certify the blue-pulse terminal state)."),
}
PRIOR_PINS = {
    EVIDENCE + "prior/CHAPTER_DOSSIER.json": "54e464fb0990a0934b1aa9e7cb0dfb968cf72ae383345578e9c883af67b4e7a9",
    EVIDENCE + "prior/SOURCE_MANIFEST.json": "28fea653d75acd947b60fd1ee7eb00d8beed4a5a361e6319266e67d952b13d5d",
    EVIDENCE + "prior/UEOT_PHYSICS.md": "9a93ce491e9b5001146e17103086f24628a8f7491fda44ae990a97efc485f6b5",
    EVIDENCE + "prior/UEOT_PHYSICS.en.md": "1e88f5d8d624a3a945b24dce5ef057ed5d9c45e8494a7215db1c471947dc94b8",
    "physics/qm/status/CLAIM_LEDGER_v31.11.json": "144c7a77e6107513ea3722b607e63a7aa78d39c99c9cda1272a9d6b641f02dc8",
}
ERRATUM = {
    "zh": (
        "一般能量有界输入在通过后可能增加归一能量预算；未知输入失败后不能凭空重备。",
        "本例低谱过滤的通过态不增加平均激发预算，证明见第68.4节；一般后选择可能增加条件均值，未知输入失败后不能凭空重备。",
    ),
    "en": (
        "A general energy-bounded input can have a larger normalized energy budget after passing.",
        "For the low-spectral filter used here, the passing state does not increase the mean excitation budget, as proved in Section 68.4; general postselection can increase a conditional mean.",
    ),
}
RUNTIME_LABELS = ["source-integration", "independent-operational", "independent-microscopic", "independent-exact-certificate"]


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def results(dossier):
    return [row for ch in dossier.get("chapters", []) for row in ch.get("numbered_results", [])]


def sections(text):
    matches = list(re.finditer(r'^<a id="(ch-\d+|appendix-[a-z])"></a>\s*$', text, re.M))
    return {m.group(1): text[m.end(): matches[i+1].start() if i+1 < len(matches) else len(text)].strip()
            for i, m in enumerate(matches)}


def displays(text):
    output, active = [], None
    for line in text.splitlines():
        if line.strip() == "$$":
            if active is None:
                active = []
            else:
                output.append("\n".join(active))
                active = None
        elif active is not None:
            active.append(line)
    if active is not None:
        raise ValueError("unclosed display math fence")
    return output


def code_blocks(text):
    output, active, fence = [], None, None
    for line in text.splitlines():
        if active is None:
            match = re.match(r'^(`{3,}|~{3,})(.*)$', line)
            if match:
                fence, active = match.group(1), [line]
        else:
            active.append(line)
            if re.fullmatch(re.escape(fence) + r'\s*', line):
                output.append("\n".join(active))
                active, fence = None, None
    if active is not None:
        raise ValueError("unclosed code fence")
    return output


def actual_results(text):
    body = text.split('<a id="appendix-a"></a>', 1)[0]
    pieces = re.split(r'(?m)^(<a id="[a-z0-9-]+"></a>)\s*$', body)
    chapter, output = None, []
    for i, part in enumerate(pieces):
        if not part.startswith('<a id="'):
            continue
        anchor = re.fullmatch(r'<a id="([a-z0-9-]+)"></a>', part).group(1)
        if anchor.startswith("ch-"):
            chapter = int(anchor[3:])
            continue
        title = re.match(r'\s*\*\*(.*?)\*\*', pieces[i+1] if i+1 < len(pieces) else "", re.S)
        if not title or "\n" in title.group(1):
            raise ValueError("result anchor lacks immediate statement: " + anchor)
        rid = anchor.upper()
        if not re.match(re.escape(rid) + r'(?=$|[^A-Za-z0-9_-])', title.group(1)):
            raise ValueError("result title/anchor mismatch: " + anchor)
        output.append({"id": rid, "chapter": chapter, "title": title.group(1)})
    return output


def inspect(repo, reuse_rel=DEFAULT_REUSE):
    checks, pending, consumed = [], [], {}

    def read(rel):
        raw = (repo / rel).read_bytes()
        consumed[str(rel)] = digest(raw)
        return raw

    def text(rel):
        return read(rel).decode("utf-8")

    def load(rel, optional=False):
        if optional and not (repo / rel).is_file():
            pending.append("missing integration artifact: " + str(rel))
            return None
        return json.loads(text(rel))

    def check(name, ok, detail=None):
        if not bool(ok):
            raise ValueError(name + (": " + str(detail) if detail is not None else ""))
        checks.append({"name": name, "status": "PASS", "detail": detail})

    def need(name, ok):
        if not ok:
            pending.append(name)
        else:
            checks.append({"name": name, "status": "PASS"})

    def identity(item, label):
        if not isinstance(item, dict) or not item.get("path") or not item.get("sha256"):
            raise ValueError("incomplete file identity: " + label)
        path = Path(item["path"])
        if path.is_absolute() or ".." in path.parts:
            raise ValueError("nonportable/outside-repository evidence path: " + str(path))
        raw = read(str(path))
        check(label + " exact file identity", digest(raw) == item["sha256"]
              and ("bytes" not in item or len(raw) == item["bytes"]), str(path))

    for rel, expected in PRIOR_PINS.items():
        check("immutable historical input " + rel, digest(read(rel)) == expected)
    prior = load(EVIDENCE + "prior/CHAPTER_DOSSIER.json")
    current = load(BOOK + "CHAPTER_DOSSIER.json")
    old_results, new_results = results(prior), results(current)
    old_ids = [r["id"] for r in old_results]
    ids = [r["id"] for r in new_results]
    check("182 distinct inherited result objects", len(old_ids) == len(set(old_ids)) == 182)
    check("no duplicate current result IDs", len(ids) == len(set(ids)))
    check("all inherited objects and order exactly preserved", new_results[:182] == old_results)
    extra = ids[182:]
    check("no reordered or unregistered new IDs", extra == NEW_IDS[:len(extra)] and len(extra) <= 6, extra)
    need("dossier contains all six ordered chapter-68 results", extra == NEW_IDS)
    need("dossier edition 3.9", str(current.get("edition")) == "3.9")
    for row in new_results[182:]:
        rid = row["id"]
        check(rid + " is in chapter 68", row.get("chapter") == 68 and row.get("anchor") == rid.lower())
        kinds = [str(x).lower() for x in row.get("verification_kind", [])]
        check(rid + " has no new Lean evidence class", "lean" not in kinds)
        check(rid + " has no new formal source bindings", not row.get("formal_bindings") and not row.get("formal_names"))
        status = str(row.get("machine_status", "")).upper()
        need(rid + " explicitly paper-only machine scope", "PAPER" in status and "ACCEPTED" not in status)
        need(rid + " explicit verification scope", bool(row.get("verification_scope")))
        empirical = row.get("status_axes", {}).get("empirical", row.get("empirical_status"))
        need(rid + " empirical axis not tested", empirical in {"NOT_TESTED", "UNVERIFIED", "NO_REAL_DATA"})

    old_ledger = load("physics/qm/status/CLAIM_LEDGER_v31.11.json")
    old_claims = old_ledger["claims"]
    check("105 inherited ledger objects", len(old_claims) == 105)
    ledger = load("physics/qm/status/CLAIM_LEDGER_v31.12.json", optional=True)
    if ledger is not None:
        rows = ledger["claims"]
        check("inherited 105 ledger objects and order unchanged", rows[:105] == old_claims)
        check("no unregistered ledger additions", [r.get("book_result") for r in rows[105:]] == NEW_IDS[:len(rows)-105] and len(rows) <= 111)
        need("ledger has exactly six additions", len(rows) == 111)
        for row in rows[105:]:
            check(row["id"] + " has no fabricated hardware evidence", row.get("new_hardware_data") is False)
            check(row["id"] + " no new machine acceptance", "PAPER" in str(row.get("machine_status", "")).upper()
                  and "ACCEPTED" not in str(row.get("machine_status", "")).upper())

    previous_text, current_text, old_sections, new_sections = {}, {}, {}, {}
    parsed, current_displays = {}, {}
    for lang, suffix in [("zh", ""), ("en", ".en")]:
        filename = "UEOT_PHYSICS" + suffix + ".md"
        previous_text[lang] = text(EVIDENCE + "prior/" + filename)
        current_text[lang] = text(BOOK + filename)
        old_sections[lang], new_sections[lang] = sections(previous_text[lang]), sections(current_text[lang])
        old_actual, now_actual = actual_results(previous_text[lang]), actual_results(current_text[lang])
        parsed[lang] = now_actual
        check(lang + " inherited 182 statements preserve IDs, titles and chapters", now_actual[:182] == old_actual)
        check(lang + " inherited statements agree with dossier IDs", [r["id"] for r in old_actual] == old_ids)
        actual_extra = [r["id"] for r in now_actual[182:]]
        check(lang + " new body IDs have reviewed order", actual_extra == NEW_IDS[:len(actual_extra)] and len(actual_extra) <= 6)
        need(lang + " all six new body statements present", actual_extra == NEW_IDS)
        ch_numbers = list(map(int, re.findall(r'^# (\d+)\.', current_text[lang], re.M)))
        check(lang + " contiguous chapter sequence", ch_numbers == list(range(len(ch_numbers))) and len(ch_numbers) in {68, 69})
        need(lang + " 69 chapters", len(ch_numbers) == 69)
        need(lang + " declares version 3.9", bool(re.search(r'^version:\s*"3\.9"\s*$', current_text[lang], re.M)))
        check(lang + " six appendices", sum(k.startswith("appendix-") for k in new_sections[lang]) == 6)
        anchors = re.findall(r'<a id="([^"]+)"></a>', current_text[lang])
        check(lang + " unique stable anchors", len(anchors) == len(set(anchors)))
        for number in range(1, 67):
            key = "ch-" + str(number)
            if number != 48:
                check(lang + " inherited scientific body " + str(number), old_sections[lang][key] == new_sections[lang][key])
        before67, after67 = old_sections[lang]["ch-67"], new_sections[lang]["ch-67"]
        old_sentence, new_sentence = ERRATUM[lang]
        check(lang + " unique old low-spectral erratum site", before67.count(old_sentence) == 1)
        corrected = before67.replace(old_sentence, new_sentence, 1)
        check(lang + " chapter67 changes only the reviewed low-spectral erratum", after67 in {before67, corrected})
        need(lang + " reviewed low-spectral erratum applied", after67 == corrected)
        for number in range(68):
            key = "ch-" + str(number)
            check(lang + " inherited display math " + str(number), displays(old_sections[lang][key]) == displays(new_sections[lang][key]))
        check(lang + " appendix D programs exactly unchanged", code_blocks(old_sections[lang]["appendix-d"]) == code_blocks(new_sections[lang]["appendix-d"]))
        if "ch-68" not in new_sections[lang]:
            pending.append(lang + " chapter68 not yet integrated")
            continue
        chapter = new_sections[lang]["ch-68"]
        check(lang + " complete ten chapter68 sections", re.findall(r'^## (68\.\d+)\b', chapter, re.M) == ["68." + str(n) for n in range(1, 11)])
        current_displays[lang] = displays(chapter)
        check(lang + " nine reviewed displays", len(current_displays[lang]) == 9)
        for row in now_actual[182:]:
            check(lang + " exact reviewed new title " + row["id"], row["title"] == TITLES[row["id"]][0 if lang == "zh" else 1] and row["chapter"] == 68)
        if lang == "zh":
            check("Chinese paper/machine/empirical separation", "没有新增 Lean 声明" in chapter and "没有取得协议匹配" in chapter)
            check("Chinese reuses rather than recounts sharp filter", "不重新计为新定理" in chapter)
            check("Chinese analytic and numerical cutoff separation", "N=1" in chapter and "N=4095" in chapter and "未数值执行" in chapter)
        else:
            check("English paper/machine/empirical separation", "no new Lean declarations" in chapter and "No protocol-matched raw device data" in chapter)
            check("English reuses rather than recounts sharp filter", "not counted as a new theorem" in chapter)
            check("English analytic and numerical cutoff separation", "N=1" in chapter and "N=4095" in chapter and "not numerical execution" in chapter)
    if len(current_displays) == 2:
        check("all nine new displays literally bilingual-identical", current_displays["zh"] == current_displays["en"])
        joined = "\n".join(current_displays["zh"])
        for literal in ["16381", "8192", "1369/2500", "156/625", "0.049887775359266728"]:
            check("reviewed certificate display value " + literal, literal in joined)

    old_manifest = load(EVIDENCE + "prior/SOURCE_MANIFEST.json")
    manifest = load(BOOK + "SOURCE_MANIFEST.json")
    old_entries, now_entries = old_manifest["entries"], manifest["entries"]
    check("original source catalog entries and order preserved", now_entries[:len(old_entries)] == old_entries)
    need("source manifest edition 3.9", str(manifest.get("edition")) == "3.9")
    for key, lang, filename in [("canonical_identity", "zh", "UEOT_PHYSICS.md"),
                                ("canonical_english_identity", "en", "UEOT_PHYSICS.en.md")]:
        record = manifest.get(key, {})
        need(lang + " current manifest canonical identity", record.get("path") == BOOK + filename
             and record.get("sha256") == digest(current_text[lang].encode())
             and record.get("chapters") == 69 and record.get("appendices") == 6
             and record.get("numbered_results") == 188)

    # Old published evidence is immutable. Newly added v3.9/v31.12 paths are
    # deliberately excluded by intersecting with the historical tree inventory.
    try:
        roots = ["physics/qm/kernel/evidence", "physics/qm/book/evidence"]
        old_paths = set(subprocess.check_output(["git", "ls-tree", "-r", "--name-only", BASELINE, "--", *roots], cwd=repo, text=True).splitlines())
        changed = set(subprocess.check_output(["git", "diff", "--name-only", BASELINE, "--", *roots], cwd=repo, text=True).splitlines())
        check("historical evidence paths are unchanged", bool(old_paths) and not (changed & old_paths), sorted(changed & old_paths))
    except subprocess.CalledProcessError:
        pending.append("historical Git object unavailable for whole evidence inventory check")

    runtime = load(RUNTIME, optional=True)
    if runtime is not None:
        check("four new runtime gates actually passed", runtime.get("status") == "PASS"
              and [c.get("label") for c in runtime.get("commands", [])] == RUNTIME_LABELS
              and all(c.get("exit_code") == 0 for c in runtime["commands"]))
        check("runtime input bytes stable", runtime.get("inputs_stable_during_execution") is True)
        check("runtime is neither Lean nor hardware evidence", runtime.get("new_lean_execution") is False and runtime.get("new_hardware_data") is False)
        context = runtime.get("execution_context", {})
        check("runtime actual execution context recorded", context.get("provider") in {"local_python_process", "github_actions"}
              and bool(re.fullmatch(r'[0-9a-f]{40}', str(context.get("observed_git_head", ""))))
              and isinstance(context.get("worktree_has_changes"), bool))
        if context.get("provider") == "github_actions":
            check("remote run identity explicit", all(context.get("github", {}).get(k) for k in ["GITHUB_RUN_ID", "GITHUB_RUN_ATTEMPT", "GITHUB_REPOSITORY", "GITHUB_JOB", "GITHUB_SHA"]))
        input_paths = [x.get("path") for x in runtime.get("inputs", [])]
        required = {"physics/qm/growing_cutoff/" + f for f in ["run_verification.py", "model.py", "verify_integration.py", "exact_checker.py", "check_operational_growth.py", "check_micro_growth.py", "frozen_model.json"]}
        check("new runtime binds required implementation inputs", len(input_paths) == len(set(input_paths)) and required.issubset(input_paths))
        output_paths = [x.get("path") for x in runtime.get("outputs", [])]
        runtime_dir = str(Path(RUNTIME).parent) + "/"
        report_names = ["integration.json", "operational.json", "micro-growth.json", "exact-certificate.json"]
        check("new runtime binds every actual result artifact", len(output_paths) == len(set(output_paths))
              and {runtime_dir + name for name in report_names}.issubset(output_paths))
        for item in runtime.get("inputs", []) + runtime.get("outputs", []):
            identity(item, "runtime")
        for command in runtime["commands"]:
            identity(command["log"], "runtime log")
        details = {name: load(runtime_dir + name) for name in report_names}
        model_sha = digest(read("physics/qm/growing_cutoff/frozen_model.json"))
        source_sha = lambda name: digest(read("physics/qm/growing_cutoff/" + name))
        integration = details["integration.json"]
        check("actual integration result binds its model and implementation", integration.get("status") == "PASS"
              and integration.get("model_sha256") == model_sha
              and integration.get("script_sha256") == source_sha("verify_integration.py")
              and integration.get("check_count") == len(integration.get("checks", []))
              and all(c.get("status") == "PASS" for c in integration["checks"])
              and len(integration.get("parameter_rows", [])) == 9)
        check("actual numerical filter scope excludes analytic large-cutoff execution",
              integration.get("filter_control", {}).get("numeric_filter_cutoff") == 1
              and integration.get("filter_control", {}).get("analytic_cutoff_4095_was_numerically_executed") is False)
        for filename, script, hash_key in [("operational.json", "check_operational_growth.py", "checker_sha256"),
                                           ("micro-growth.json", "check_micro_growth.py", "source_sha256")]:
            report = details[filename]
            check(filename + " actual checker acceptance and source identity", report.get("status") == "PASS"
                  and report.get(hash_key) == source_sha(script)
                  and report.get("check_count") == len(report.get("checks", []))
                  and report.get("check_count", 0) > 0
                  and all(c.get("pass") is True for c in report["checks"]))
        exact = details["exact-certificate.json"]
        check("exact certificate binds the actual model and independent checker", exact.get("all_verified") is True
              and exact.get("input_sha256", {}).get("model") == model_sha
              and exact.get("input_sha256", {}).get("checker") == source_sha("exact_checker.py")
              and bool(exact.get("checks")) and all(c.get("verified") is True for c in exact["checks"])
              and exact.get("decision", {}).get("empirical_full_CQ_error") == "UNVERIFIED")

    reuse = load(reuse_rel, optional=True)
    if reuse is not None:
        check("proof reuse has exact verified scope", reuse.get("status") == "SOURCE_IDENTITY_REUSED"
              and reuse.get("proof_reuse_eligible") is True and reuse.get("proof_input_count") == 158
              and reuse.get("old_runtime_input_count") == 13 and reuse.get("old_runtime_inputs_identical") is True
              and not reuse.get("errors") and not reuse.get("runtime_mismatches"))
        check("reuse is not new machine acceptance", reuse.get("new_lean_execution") is False
              and reuse.get("new_lean_theorems") == 0 and reuse.get("new_paper_claims_not_promoted_to_lean") is True)
        old_proof = load("physics/qm/kernel/evidence/v31.11/source-manifest.json")
        check("reused proof inventory has 158 actual entries", len(old_proof["sources"]) == 158)
        for item in old_proof["sources"]:
            identity(item, "inherited proof input")

    for lang, suffix in [("zh", ""), ("en", ".en")]:
        rel = EVIDENCE + lang + "/pdf-build.json"
        build = load(rel, optional=True)
        if build is None:
            continue
        check(lang + " actual PDF edition and structure", str(build.get("edition")) == "3.9" and build.get("chapters") == 69 and build.get("appendices") == 6)
        header_rel = BOOK + "build/header" + (".en" if lang == "en" else "") + ".tex"
        for rel, field in [(BOOK + "build/build_pdf.py", "builder_sha256"),
                           (header_rel, "header_sha256"),
                           (BOOK + "build/tables.lua", "tables_filter_sha256")]:
            check(lang + " current PDF build dependency " + field,
                  digest(read(rel)) == build.get(field), rel)
        for extension, field in [("md", "source_sha256"), ("tex", "tex_sha256"), ("pdf", "pdf_sha256")]:
            item = {"path": BOOK + "UEOT_PHYSICS" + suffix + "." + extension, "sha256": build.get(field)}
            identity(item, lang + " PDF-build input/output")
        # This guards an observed publication defect: updating the Markdown
        # version did not automatically update the independently stored cover
        # and running header. Historical 3.8 text in scientific body sections
        # remains legitimate; only the actual current front matter is checked.
        header_text = text(header_rel)
        generated_tex = text(BOOK + "UEOT_PHYSICS" + suffix + ".tex")
        preamble = generated_tex.split(r"\begin{document}", 1)[0]
        right_header = (r"\fancyhead[R]{\small 物理学 · 3.9 双语修订版}" if lang == "zh"
                        else r"\fancyhead[R]{\small Bilingual revision 3.9}")
        check(lang + " generated running header is current 3.9",
              header_text.count(right_header) == preamble.count(right_header) == 1)
        cover_pattern = r'\\begin\{titlepage\}(.*?)\\end\{titlepage\}'
        header_covers = re.findall(cover_pattern, header_text, re.S)
        tex_covers = re.findall(cover_pattern, preamble, re.S)
        check(lang + " actual generated cover matches current header template",
              len(header_covers) == len(tex_covers) == 1 and header_covers[0] == tex_covers[0])
        cover = tex_covers[0]
        cover_values = (["3.9 双语修订版", "69章", "6个附录", "UEOT-QM Kernel 1.12", "2026年11月12日"]
                        if lang == "zh" else
                        ["Bilingual revision 3.9", "69 chapters", "6 appendices", "UEOT-QM Kernel 1.12", "12 November 2026"])
        check(lang + " generated cover edition, counts, kernel and date",
              all(value in cover for value in cover_values)
              and "3.8" not in cover and "Kernel 1.11" not in cover
              and ("68章" if lang == "zh" else "68 chapters") not in cover)
        check(lang + " generated document date is the declared publication date",
              preamble.count(r"\date{2026-11-12}") == 1)
        passes = build.get("compile_passes", [])
        check(lang + " three actual successful PDF passes", len(passes) == 3 and all(p.get("exit_code") == 0 for p in passes))
        check(lang + " PDF layout and references converged", build.get("last_two_auxiliary_files_identical") is True
              and build.get("layout_warnings") == [] and build.get("rerun_warnings") == [])
        for p in passes:
            identity({"path": EVIDENCE + lang + "/" + p["file"], "sha256": p["sha256"]}, lang + " actual PDF log")
    visual = load(EVIDENCE + "visual-review.json", optional=True)
    if visual is not None:
        check("actual scoped visual review recorded", str(visual.get("status", "")).startswith("PASS")
              and bool(visual.get("method") or visual.get("scope")))
        docs = visual.get("languages")
        if docs is None:
            docs = {r["language"]: r for r in visual.get("documents", [])}
        check("visual review covers both languages", all(lang in docs for lang in ["zh", "en"]))
        for lang in ["zh", "en"]:
            doc = docs[lang]
            for kind in ["source", "tex", "pdf"]:
                identity(doc[kind], lang + " visual " + kind)
            pages = doc.get("reviewed_pages_1based", doc.get("new_chapter_pages_1based", []))
            check(lang + " actual reviewed pages listed", bool(pages) and all(isinstance(n, int) and n > 0 for n in pages))

    changed = [rel for rel, sha in consumed.items() if digest((repo / rel).read_bytes()) != sha]
    check("all consumed bytes stable during this verification", not changed, changed)
    return {
        "schema": "ueot_physics.v3.9.increment-independent/1",
        "status": "PASS" if not pending else "CONTENT_PASS_METADATA_PENDING",
        "executed_at_utc": datetime.now(timezone.utc).isoformat(),
        "source_baseline": BASELINE,
        "prior_result_count": 182, "new_result_count": 6, "total_result_count": 188,
        "historical_result_object_identity": "EXACTLY_PRESERVED",
        "historical_claim_count": 105, "new_claim_count": 6,
        "chapter68_display_math": {"count": len(current_displays.get("zh", [])),
                                   "bilingual_literal_identity": len(current_displays) == 2,
                                   "sha256": [digest(s.encode()) for s in current_displays.get("zh", [])]},
        "new_result_mapping": [{"id": r["id"], "chapter": 68, "zh_title": TITLES[r["id"]][0], "en_title": TITLES[r["id"]][1]} for r in new_results[182:]],
        "allowed_historical_body_change": "Only the exact reviewed Chapter 67.5 low-spectral energy erratum; editorial chapters 0 and 48 excluded from body equality, all inherited displays retained",
        "checks": checks, "pending_integration": pending, "consumed_sha256": consumed,
        "limits": ["Identity and scope checks are not proofs of theorem truth",
                   "No new Lean compiler or axiom-audit execution is performed",
                   "Visual review receipts are checked, not generated by this verifier",
                   "No empirical verification, resource advantage or remote publication is inferred"],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--proof-reuse", default=DEFAULT_REUSE, help="Repository-relative reuse receipt path")
    parser.add_argument("--require-complete", action="store_true")
    args = parser.parse_args()
    try:
        report = inspect(args.repo_root.resolve(), args.proof_reuse)
    except (ValueError, KeyError, FileNotFoundError, json.JSONDecodeError, TypeError) as exc:
        report = {"schema": "ueot_physics.v3.9.increment-independent/1", "status": "FAIL", "error": str(exc),
                  "executed_at_utc": datetime.now(timezone.utc).isoformat()}
    report["checker_sha256"] = digest(Path(__file__).read_bytes())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({k: report[k] for k in ["status", "pending_integration", "error"] if k in report}, ensure_ascii=False))
    if report["status"] == "FAIL":
        return 2
    if args.require_complete and report.get("pending_integration"):
        return 3
    return 0


if __name__ == "__main__":
    sys.exit(main())
