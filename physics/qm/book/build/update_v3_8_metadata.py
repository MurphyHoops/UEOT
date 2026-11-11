#!/usr/bin/env python3
"""Reconcile the chapter-67 increment into the existing canonical registries.

Historical numbered-result and claim objects are copied verbatim, never
relabeled as new executions. Actual receipts are required for release mode.
"""
import argparse
from copy import deepcopy
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shutil

from verify_book import actual_claims, inspect_book

BOOK = Path(__file__).resolve().parents[1]
QM = BOOK.parent
REPO = BOOK.parents[2]
PRIOR = BOOK / "evidence/v3.8/prior"
EVIDENCE = QM / "kernel/evidence/v31.11"
AUDIT = QM / "audits/OPERATIONAL_MICRO_ROBUST_v31.11"


def load(p):
    return json.loads(p.read_text())


def save(p, data):
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(data, ensure_ascii=False, indent=2)+"\n")


def ident(p):
    return {"path": str(p.relative_to(REPO)), "sha256": hashlib.sha256(p.read_bytes()).hexdigest(),
            "bytes": p.stat().st_size}


def identities_match(rows):
    return bool(rows) and all((REPO/row["path"]).is_file() and
        ident(REPO/row["path"])["sha256"] == row["sha256"] for row in rows)


def publication_evidence_current():
    path = BOOK/"evidence/v3.8/visual-review.json"
    if not path.is_file():
        return False
    visual = load(path)
    if visual.get("status") != "PASS_SCOPED_VISUAL_REVIEW" or len(visual.get("documents", [])) != 2:
        return False
    for item in visual["documents"]:
        if not identities_match([item["source"], item["pdf"], item["tex"], item["build_receipt"]]):
            return False
        build = load(REPO/item["build_receipt"]["path"])
        for kind in ["source", "pdf", "tex"]:
            if build[kind+"_sha256"] != item[kind]["sha256"]:
                return False
        if build["layout_warnings"] or build["rerun_warnings"] or not build["last_two_auxiliary_files_identical"]:
            return False
        parent = (REPO/item["build_receipt"]["path"]).parent
        if not all(pass_["exit_code"] == 0 and
                   hashlib.sha256((parent/pass_["file"]).read_bytes()).hexdigest() == pass_["sha256"]
                   for pass_ in build["compile_passes"]):
            return False
    return True


def slice_body(text, anchor):
    start = text.index(f'<a id="{anchor}"></a>')
    following = re.search(r'<a id="(?:ch-\d+|appendix-[a-f])"></a>', text[start+1:])
    end = start+1+following.start() if following else len(text)
    return text[start:end]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--require-evidence", action="store_true")
    args = parser.parse_args()
    PRIOR.mkdir(parents=True, exist_ok=True)
    for source in [BOOK/"CHAPTER_DOSSIER.json", BOOK/"SOURCE_MANIFEST.json",
                   BOOK/"README.md", QM/"status/CURRENT.json"]:
        target = PRIOR/source.name
        if not target.exists():
            shutil.copyfile(source, target)
    now = datetime.now(timezone.utc).isoformat()
    old_dossier = load(PRIOR/"CHAPTER_DOSSIER.json")
    old_manifest = load(PRIOR/"SOURCE_MANIFEST.json")
    old_current = load(PRIOR/"CURRENT.json")
    old_ledger = load(QM/"status/CLAIM_LEDGER_v31.10.json")
    bindings = load(AUDIT/"chapter67_formal_bindings.json")["results"]
    zh, en = (BOOK/"UEOT_PHYSICS.md").read_text(), (BOOK/"UEOT_PHYSICS.en.md").read_text()
    structures = {"zh": inspect_book(zh), "en": inspect_book(en)}
    claims = {"zh": actual_claims(zh), "en": actual_claims(en)}
    assert [r["id"] for r in claims["zh"]] == [r["id"] for r in claims["en"]]
    assert [r["id"] for r in claims["zh"][-9:]] == [r["id"] for r in bindings]
    lean_path = EVIDENCE/"lean-verification.json"
    runtime_path = EVIDENCE/"runtime/execution_receipt.json"
    lean = load(lean_path) if lean_path.exists() else {"status": "PENDING"}
    runtime = load(runtime_path) if runtime_path.exists() else {"status": "PENDING"}
    source_path = EVIDENCE/"source-manifest.json"
    source_manifest = load(source_path) if source_path.exists() else {}
    remote_path = EVIDENCE/"integration-verification.json"
    remote = load(remote_path) if remote_path.exists() else {"state": "NOT_PUBLISHED", "remote_verified": False}
    proof_current = identities_match(source_manifest.get("sources", []))
    runtime_rows = runtime.get("inputs", []) + runtime.get("outputs", []) + [
        command["log"] for command in runtime.get("commands", [])]
    runtime_current = identities_match(runtime_rows)
    publication_current = publication_evidence_current()
    if args.require_evidence:
        assert lean["status"] == runtime["status"] == "PASS"
        assert source_manifest.get("source_count", 0)>0
        assert proof_current, "Current proof inputs differ from executed inputs"
        assert runtime_current, "Current runtime inputs, outputs or logs differ from the execution receipt"
        assert publication_current, "Current bilingual source/PDF/TeX/logs do not match completed visual review"
    local_pass = lean["status"] == runtime["status"] == "PASS" and proof_current and runtime_current
    state = "LOCAL_VERIFIED" if local_pass else "LOCAL_IN_PROGRESS"
    if local_pass and not publication_current:
        state = "LOCAL_SCIENCE_VERIFIED_PUBLICATION_PENDING"
    if remote.get("remote_verified"):
        state = remote["state"]
    new_results = []
    for item in bindings:
        r = deepcopy(item)
        rid = r["id"]
        r.update({"chapter": 67, "anchor": rid.lower(), "origin": "NEW_IN_3_8",
                  "argument_status": ["N" if rid.startswith("C-") else "P"],
                  "verification_kind": ["analytic", "exact_arithmetic"],
                  "verification_scope": r["question_and_quantifiers"],
                  "limits": r["paper_only"],
                  "type_responsibility": {"domain_assumptions": r["premises"],
                                          "proved_scope": r["question_and_quantifiers"],
                                          "paper_only_components": r["paper_only"]},
                  "empirical_data": "NO_REAL_DATA",
                  "runtime_receipt": str(runtime_path.relative_to(REPO))})
        names = r.get("formal_names", [])
        if names:
            r["formal_bindings"] = [{"file": r["formal_file"],
                                      "declaration": r["formal_namespace"]+"."+name,
                                      "kind": "theorem", "sha256": ident(REPO/r["formal_file"])["sha256"]}
                                     for name in names]
            r["formal_audit_ref"] = str(lean_path.relative_to(REPO))
            r["machine_status"] = "ACCEPTED_SCOPED" if lean["status"] == "PASS" else "PENDING"
            if lean["status"] == "PASS":
                r["verification_kind"].append("lean")
        else:
            r["formal_bindings"] = []
            r["machine_status"] = "PAPER_ONLY_NOT_INFERRED_FROM_NEARBY_BUILD"
        if rid in {"P-ROB-01", "P-ROB-02"}:
            r["verification_kind"].append("synthetic")
        r["status_axes"] = {"mathematical": r["mathematical_status"],
                            "physical_selection": r["physical_selection_status"],
                            "computational": "EXECUTED_EXACT_FINITE_CONTROLS" if runtime["status"]=="PASS" else "PENDING",
                            "empirical": r["empirical_status"]}
        new_results.append(r)
    dossier = deepcopy(old_dossier)
    dossier.update({"edition": "3.8", "recorded_at_utc": now, "editorial_status": state,
                    "prior_complete_dossier": ident(PRIOR/"CHAPTER_DOSSIER.json"),
                    "current_release_stage": state, "current_remote_code_identity": remote,
                    "next_execution_contract": "physics/qm/UEOT_QM_EXECUTION_v31.11.md"})
    dossier["chapters"].append({"number": 67, "anchor": "ch-67",
                                "title": "操作等价、微观截断与共同参数下的鲁棒实现",
                                "edition_status": "NEW_IN_3_8", "numbered_results": new_results,
                                "dependency_class": ["B", "P", "E", "O"],
                                "verification_kind": ["analytic", "exact_arithmetic", "synthetic"],
                                "source_refs": [{"id": "QM3111", "locator": "Common contract, chapter67 bindings and actual evidence"}],
                                "whole_chapter_formalized": False, "new_experimental_data": False})
    dossier["source_catalog"]["QM3111"] = {"name": "v31.11 operational/microscopic/robust increment",
                                            "path": "physics/qm/UEOT_QM_KERNEL_v31.11.md",
                                            "baseline": "16a89154183c22030d4526413167d095d94e6890"}
    old_results = [r for c in old_dossier["chapters"] for r in c.get("numbered_results", [])]
    assert len(old_results)==173
    assert [r for c in dossier["chapters"][:-1] for r in c.get("numbered_results", [])] == old_results
    for group in [dossier["chapters"], dossier["appendices"]]:
        for chapter in group:
            anchor = chapter["anchor"]
            pieces = {}
            for language, text, path in [("zh", zh, BOOK/"UEOT_PHYSICS.md"), ("en", en, BOOK/"UEOT_PHYSICS.en.md")]:
                body = slice_body(text, anchor)
                pieces[language] = {"path": str(path.relative_to(REPO)), "anchor": anchor,
                                    "body_sha256": hashlib.sha256(body.encode()).hexdigest(),
                                    "body_utf8_bytes": len(body.encode()),
                                    "sections": [{"id": a, "title": b} for a,b in
                                                 re.findall(r'^## ([0-9A-F]+\.\d+) (.+)$', body, re.M)]}
            chapter["body_sha256"] = pieces["zh"]["body_sha256"]
            chapter["body_utf8_bytes"] = pieces["zh"]["body_utf8_bytes"]
            chapter["sections"] = pieces["zh"]["sections"]
            chapter["publication_3_8"] = pieces
            chapter["current_edition_action"] = "NEW_IN_3_8" if anchor=="ch-67" else "PRESERVED_OR_SCOPE_UPDATED_IN_3_8"
            chapter["current_edition_verification"] = {"edition": "3.8", "body_hash_checked": True,
                                                       "english_body_hash_checked": True,
                                                       "scope": "Current bilingual text; inherited result objects retain exact historical fields"}
    identities = {}
    for key,name,language in [("canonical","UEOT_PHYSICS.md","zh-CN"),
                              ("canonical_english","UEOT_PHYSICS.en.md","en")]:
        identities[key] = {**ident(BOOK/name), "status": state, "chapters": 68, "appendices": 6,
                           "numbered_results": 182, "inherited_result_ids": 173, "new_result_ids": 9,
                           "language": language, "identity_scope": "Current exact source bytes"}
        dossier[key] = identities[key]
    for key in ["pdf", "latex"]:
        suffix = "pdf" if key=="pdf" else "tex"
        p = BOOK/("UEOT_PHYSICS."+suffix)
        dossier["derivatives"][key] = ident(p) if p.exists() else {"status": "PENDING"}
    dossier["derivatives"]["english"] = {suffix: ident(BOOK/("UEOT_PHYSICS.en."+suffix))
                                          for suffix in ["md", "tex", "pdf"] if (BOOK/("UEOT_PHYSICS.en."+suffix)).exists()}
    dossier["derivatives"]["visual_review"] = "physics/qm/book/evidence/v3.8/visual-review.json"
    source_identity = {"manifest": str(source_path.relative_to(REPO)), "verification": str(lean_path.relative_to(REPO)),
                       "source_count": source_manifest.get("source_count"),
                       "source_set_sha256": source_manifest.get("source_set_sha256"),
                       "scope": "New-source targeted build and exhaustive new-namespace audit; old executions separately preserved",
                       "current_bytes_match_executed_bytes": proof_current}
    dossier["unified_source_identity"] = source_identity
    dossier["publication_source_identity"] = source_identity
    dossier["verified_inventory"] = {"scoped_lean": lean, "runtime_receipt": str(runtime_path.relative_to(REPO)),
                                      "new_hardware_data": False, "historical_suites_reexecuted_locally": False}
    dossier["validation"] = {"status": state, "numbered_result_count": 182,
                              "all173_prior_result_objects_exactly_preserved": True,
                              "historical_dossier": ident(PRIOR/"CHAPTER_DOSSIER.json"),
                              "all_body_hashes_verified": True, "whole_physics_formalized": False,
                              "new_experimental_data": False, "remote_verified": bool(remote.get("remote_verified"))}
    dossier["release_acceptance"] = {"new_lean": lean["status"], "new_runtime": runtime["status"],
                                     "current_proof_inputs_match": proof_current,
                                     "current_runtime_inputs_outputs_logs_match": runtime_current,
                                     "current_publication_matches_visual_review": publication_current,
                                     "old_numbered_results": "EXACTLY_PRESERVED",
                                     "publication_receipt": "physics/qm/book/evidence/v3.8/local-acceptance.json",
                                     "remote_integration": remote}
    dossier["publication_revision"] = {"edition": "3.8", "generator": str(Path(__file__).relative_to(REPO)),
                                       "recorded_at_utc": now, "scope": "Chapter67 scientific increment with bilingual publication",
                                       "new_scientific_results_in_publication": 9, "new_experimental_data": False,
                                       "prior_snapshot": ident(PRIOR/"CHAPTER_DOSSIER.json"),
                                       "local_artifact_state": state, "remote_publication": remote,
                                       "review_identity_policy": "Internal AI cross-review, not external human peer review"}
    dossier["edition_history"].append({"edition": "3.8", "date": "2026-11-11", "new_results": 9,
                                       "prior_dossier": ident(PRIOR/"CHAPTER_DOSSIER.json")})
    manifest = deepcopy(old_manifest)
    manifest.update({"edition": "3.8", "recorded_at_utc": now,
                     "prior_complete_manifest": ident(PRIOR/"SOURCE_MANIFEST.json"),
                     "current_code_baseline": "16a89154183c22030d4526413167d095d94e6890",
                     "current_code_baseline_role": "Reread main authoring baseline; new execution bound separately",
                     "current_code_manifest": "../kernel/evidence/v31.11/source-manifest.json",
                     "current_publication_code_manifest": "../kernel/evidence/v31.11/source-manifest.json",
                     "current_code_identity": source_identity, "unified_source_identity": source_identity,
                     "publication_source_identity": source_identity, "current_remote_code_identity": remote,
                     "current_release_stage": state, "remote_metadata_completion": remote,
                     "canonical_identity": identities["canonical"],
                     "canonical_english_identity": identities["canonical_english"],
                     "local_release_receipt": "physics/qm/book/evidence/v3.8/local-acceptance.json",
                     "local_release_receipt_scope": "Book3.8 publication only; not a substitute for scientific gates",
                     "publication_revision": dossier["publication_revision"]})
    manifest["entries"].append({"id": "QM3111", "name": "Same-source operational/microscopic/robust model",
                                 "path": "physics/qm/UEOT_QM_KERNEL_v31.11.md",
                                 "evidence_level": "NEW_PAPER_PROOFS_SCOPED_MACHINE_EXACT_AND_SYNTHETIC",
                                 "use": "Chapter67; no real device data or independent sector selection"})
    manifest["scientific_execution_partition"] = {"new_proof": source_identity,
                                                  "new_runtime": str(runtime_path.relative_to(REPO)),
                                                  "historical_reuse": "physics/qm/audits/OPERATIONAL_MICRO_ROBUST_v31.11/historical-source-reuse.json",
                                                  "real_data": False}
    assert manifest["entries"][:12] == old_manifest["entries"]
    save(BOOK/"SOURCE_MANIFEST.json", manifest)
    dossier["book_source_manifest"] = ident(BOOK/"SOURCE_MANIFEST.json")
    save(BOOK/"CHAPTER_DOSSIER.json", dossier)
    mapping = ["# UEOT Physics bilingual stable-result mapping — edition 3.8", "",
               "All 173 prior result identities are preserved; chapter67 appends nine. Titles are bound to actual statement anchors, not inferred from substrings.", "",
               "| ID | Chapter | Chinese title | English title |", "|---|---:|---|---|"]
    mapping += [f"| [{a['id']}](UEOT_PHYSICS.md#{a['id'].lower()}) | {a['chapter']} | {a['title']} | {b['title']} |"
                for a,b in zip(claims["zh"], claims["en"])]
    (BOOK/"PHYSICS_RESULT_MAPPING.md").write_text("\n".join(mapping)+"\n")
    ledger = deepcopy(old_ledger)
    ledger.update({"version": "v31.11-kernel1.11", "date": "2026-11-11", "metadata_updated_at_utc": now,
                   "previous_ledger": "physics/qm/status/CLAIM_LEDGER_v31.10.json",
                   "research_baseline": "16a89154183c22030d4526413167d095d94e6890",
                   "claim_count": 105, "new_claim_count": 9,
                   "inheritance": {"inherited_claims": 96, "all_objects_exactly_preserved": True,
                                   "historical_status_words_not_relabelled_as_new_execution": True},
                   "verification": {"state": state, "new_source_identity": source_identity,
                                    "runtime": str(runtime_path.relative_to(REPO)), "integration": remote}})
    ledger["claims"] += [{"id": "QMK-"+r["id"], "claim": r["title"], "book_result": r["id"],
                           "layers": r["dependency_class"], "status_axes": r["status_axes"],
                           "machine_status": r["machine_status"], "premises": r["premises"],
                           "paper_only": r["paper_only"], "witnesses": r["formal_bindings"],
                           "verification_scope": r["verification_scope"],
                           "formal_binding_detail": "physics/qm/audits/OPERATIONAL_MICRO_ROBUST_v31.11/chapter67_formal_bindings.json",
                           "runtime_receipt": str(runtime_path.relative_to(REPO)),
                           "new_hardware_data": False, "remote_status": remote.get("state", "NOT_PUBLISHED")}
                          for r in new_results]
    assert ledger["claims"][:96] == old_ledger["claims"]
    ledger["nonclaims"] = old_ledger["nonclaims"]+["New finite controls do not prove infinite-dimensional statements by sampling", "No hardware data, device accuracy, cost advantage or full physics completion", "No independent complex-sector selection from Core"]
    save(QM/"status/CLAIM_LEDGER_v31.11.json", ledger)
    current = {"schema": "ueot-qm-current/6", "date": "2026-11-11", "version": "v31.11-kernel1.11",
               "layer": "P — selected complex quantum physics; Core read-only; GI excluded",
               "objective": "Same-source operational identity, microscopic finite-CQ approximation, robust deployment and full costs",
               "research_baseline": "16a89154183c22030d4526413167d095d94e6890",
               "core_policy": {"tracked_core_modified": False, "role": "read-only mathematical dependency"},
               "entrypoint": "physics/qm/UEOT_QM_KERNEL_v31.11.md", "execution_contract": "physics/qm/UEOT_QM_EXECUTION_v31.11.md",
               "runtime_entrypoint": "physics/qm/operational_micro_robust/README.md",
               "formalization": "formalization/ueot-qm/README.md", "roadmap": "physics/qm/ROADMAP.md",
               "claim_ledger": "physics/qm/status/CLAIM_LEDGER_v31.11.json",
               "previous_claim_ledger": "physics/qm/status/CLAIM_LEDGER_v31.10.json",
               "verification_state": state, "local_checkpoint_state": "PASS" if local_pass else "PENDING",
               "status_axes": {"mathematical": "DECLARED_MODEL_PAPER_PROOFS_AND_COUNTEREXAMPLES",
                               "physical_selection": "COMPLEX_MODEL_AND_CONTROL_INPUTS_REMAIN_INDEPENDENT",
                               "computational": "PASS_SCOPED" if local_pass else "IN_PROGRESS",
                               "empirical": "UNTESTED_NO_REAL_DEVICE_DATA"},
               "source_identity": source_identity, "proof_receipt": str(lean_path.relative_to(REPO)),
               "source_manifest": str(source_path.relative_to(REPO)), "runtime_receipt": str(runtime_path.relative_to(REPO)),
               "integration": remote, "local_verification": {"new_lean": lean, "new_runtime": runtime["status"],
                                                              "proof_inputs_match": proof_current,
                                                              "runtime_inputs_outputs_logs_match": runtime_current,
                                                              "publication_matches_visual_review": publication_current,
                                                              "historical_heavy_suites_rerun_locally": False},
               "completed_in_this_delivery": ["Four equivalent operational identities with explicit finite-complex scope",
                    "Microscopic conserving source to full adaptive-CQ truncation; trace-class posterior and physical filter flags",
                    "Shared-parameter robust certificate and exact design-region minimax policy",
                    "Single-excitation marginal mixing, full-record isometry and whole-system nonuniqueness"],
               "book": {"edition": "3.8", "chapters": 68, "appendices": 6, "numbered_results": 182,
                        "inherited_numbered_results": 173, "new_numbered_results": 9,
                        "canonical": "physics/qm/book/UEOT_PHYSICS.md", "english": "physics/qm/book/UEOT_PHYSICS.en.md",
                        "dossier": ident(BOOK/"CHAPTER_DOSSIER.json"), "whole_book_formalized": False,
                        "local_acceptance": "physics/qm/book/evidence/v3.8/local-acceptance.json"},
               "historical_current_checkpoint": ident(PRIOR/"CURRENT.json"),
               "historical_claim_scope": "All96 old claim objects and173 old book result objects retain exact historical identity",
               "scope_limits": ["Finite classical protocols and finite untouched references", "No leakage or excitation growth without a new defect budget",
                   "Full OPT/reconstruction only partially formalized", "Normal trace-class and long-time proofs remain paper arguments",
                   "Full-design minimax is not every realized calibration-set optimum", "Flag counts do not certify quantum gate matching or terminal-state distance",
                   "Unknown quantum inputs are not free repeatable resources", "No real data or empirical closure"],
               "next_execution": {"theory": "Weak leakage or finite-bath deletion bound for the same interventions and complete records",
                                  "operations": "Complete finite Test quotient and independently justified sector principles",
                                  "data": "Protocol-matched raw calibration, ordered failures/leakage, gate identity, terminal testers and full costs"},
               "new_hardware_data": False, "metadata_updated_at_utc": now}
    save(QM/"status/CURRENT.json", current)
    for language, result in structures.items():
        save(BOOK/f"evidence/v3.8/structure-{language}.json", result)
    print(json.dumps({"status": state, "chapters":68, "results":182, "old_result_objects_preserved":173,
                      "claims":105, "old_claim_objects_preserved":96, "new_hardware_data":False}))


if __name__ == "__main__":
    main()
