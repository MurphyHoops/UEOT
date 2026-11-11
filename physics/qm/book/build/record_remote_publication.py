#!/usr/bin/env python3
"""Record the observed 3.7 source-PR acceptance; never infer main/follow-up CI.

Read-only unless --write or --output-dir is supplied. Only stdlib and local Git
objects are used. The remote observation is supplied by the responsible caller.
"""
from __future__ import annotations

import argparse
import copy
from datetime import datetime
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import subprocess
import sys
import tempfile

BOOK = "physics/qm/book/"
EV = BOOK + "evidence/v3.7/"
REPOSITORY = "MurphyHoops/UEOT"
SOURCE = "17b8959154d0459efd44cb9d7d30233e847d4e8f"
SOURCE_TREE = "c8464ea2cd3f4f1aaca52aba97f7085ab626be53"
RUN = 42974391710
PR = 454
STATE = "PR_SOURCE_VERIFIED_UNMERGED"
STAGE = "PUBLICATION_PR_VERIFIED_UNMERGED"
REPORT = EV + "publication-remote-metadata-update.json"
RECEIPT = EV + "remote-delivery.json"
OLD_REPORT = EV + "publication-metadata-update.json"
MANIFEST = BOOK + "SOURCE_MANIFEST.json"
DOSSIER = BOOK + "CHAPTER_DOSSIER.json"
SIX = {BOOK + "UEOT_PHYSICS" + suffix for suffix in
       (".md", ".tex", ".pdf", ".en.md", ".en.tex", ".en.pdf")}
FOLLOWUP_FILES = (
    BOOK + "README.md", BOOK + "review/README.md",
    BOOK + "build/record_remote_publication.py",
    BOOK + "review/REMOTE_PUBLICATION_METADATA_README.md",
    EV + "remote-publication-guard-check.json",
)
HASH_DIRECTION = (
    "Immutable source-commit files and remote-delivery/payload/preflight evidence "
    "-> SOURCE_MANIFEST -> CHAPTER_DOSSIER -> publication-remote-metadata-update; "
    "the final report is referenced by path only. Source CI does not cover the "
    "later metadata commit; its CI is recorded in the PR body, without recursive receipt commits."
)


class GuardError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise GuardError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def encoded(obj):
    return (json.dumps(obj, ensure_ascii=False, indent=2) + "\n").encode()


def digest(obj):
    return sha(json.dumps(obj, ensure_ascii=False, sort_keys=True,
                          separators=(",", ":")).encode())


def stamp(value):
    require(isinstance(value, str), "Missing timestamp")
    result = datetime.fromisoformat(value.replace("Z", "+00:00"))
    require(result.utcoffset() is not None and result.utcoffset().total_seconds() == 0,
            "Timestamp must explicitly use UTC")
    return result


def identity(path, raw):
    return {"path": path, "sha256": sha(raw), "bytes": len(raw)}


def check_identity(record, raw, label):
    require(record["sha256"] == sha(raw) and record["bytes"] == len(raw),
            f"Identity mismatch: {label}")


def validate_receipt(receipt):
    """Validate the supplied observation, not a new independent GitHub query."""
    require(receipt["schema"] == "ueot_physics.remote_delivery.v1", "Wrong receipt schema")
    require(receipt["edition"] == "3.7" and receipt["repository"] == REPOSITORY,
            "Wrong edition/repository")
    require(receipt["status"] == STATE, "Receipt is not completed source acceptance")
    require(receipt["source"]["commit"] == SOURCE and
            receipt["source"]["tree"] == SOURCE_TREE, "Wrong source commit/tree")
    observed = stamp(receipt["observed_at_utc"])
    pr = receipt["pull_request"]
    require(pr["number"] == PR and pr["state"] == "open" and pr["merged"] is False,
            "Expected the open, unmerged publication PR")
    require(pr["head_sha"] == SOURCE and pr["base_ref"] == "main", "Wrong observed PR head/base")
    require(pr["url"] == f"https://github.com/{REPOSITORY}/pull/{PR}", "Wrong PR URL")
    ci = receipt["source_ci"]
    require(ci["run_id"] == RUN and type(ci["run_attempt"]) is int and ci["run_attempt"] > 0,
            "Wrong CI run/attempt")
    require(ci["name"] == "UEOT QM Kernel" and
            ci["workflow_path"] == ".github/workflows/ueot-qm.yml" and
            ci["event"] == "pull_request", "Wrong workflow/event")
    require(ci["head_sha"] == SOURCE and ci["status"] == "completed" and
            ci["conclusion"] == "success", "Source CI is not completed success on the source head")
    require(ci["url"] == f"https://github.com/{REPOSITORY}/actions/runs/{RUN}", "Wrong CI URL")
    jobs = ci["jobs"]
    require(len(jobs) == 2 and {j["name"] for j in jobs} == {"runtime", "lean"},
            "Both runtime and lean jobs are required exactly once")
    require(len({j["id"] for j in jobs}) == 2, "Duplicate job IDs")
    critical = {
        "runtime": {"Checkout", "Verify finite conditioning source, records, implementations and costs",
                    "Verify canonical physics book structure", "Verify exact kernel and independent negative controls"},
        "lean": {"Checkout", "Record source identity", "Reject proof escapes", "Build all QM proofs",
                 "Audit theorem axioms", "Verify generated exact certificates and false witnesses",
                 "Verify retained finite and quantum Lean witnesses"},
    }
    for job in jobs:
        require(type(job["id"]) is int and job["id"] > 0 and job["run_id"] == RUN and
                job["head_sha"] == SOURCE, "Job belongs to another run/head")
        require(job["status"] == "completed" and job["conclusion"] == "success",
                f"Job not completed success: {job['name']}")
        require(stamp(job["completed_at"]) <= observed, "Observation precedes job completion")
        if "steps" in job:
            steps = job["steps"]
            require(all(s["status"] == "completed" and s["conclusion"] in {"success", "skipped"}
                        for s in steps), "Incomplete or unsuccessful reported step")
            passed = {s["name"] for s in steps if s["conclusion"] == "success"}
            require(critical[job["name"]] <= passed, "A required source verification step was not successful")
    if "updated_at" in ci:
        require(stamp(ci["updated_at"]) <= observed, "Observation precedes CI update")
    require(isinstance(receipt.get("scope"), str) and receipt["scope"].strip(), "Missing receipt scope")


class Inputs:
    def __init__(self, book):
        self.book = book.resolve()
        self.repo = self.book.parents[2]
        require(self.book == self.repo / BOOK.rstrip("/"), "Expected repository physics/qm/book")
        self.reads = {}

    def read(self, relative):
        p = PurePosixPath(relative)
        require(not p.is_absolute() and ".." not in p.parts and relative.startswith(BOOK),
                f"Out-of-scope input: {relative}")
        path = (self.repo / relative).resolve()
        require(path.is_relative_to(self.book), f"Input escapes book directory: {relative}")
        raw = path.read_bytes()
        self.reads[relative] = raw
        return raw

    def git(self, *args):
        return subprocess.run(["git", "-C", str(self.repo), *args], check=True,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE).stdout

    def source(self, relative):
        return self.git("show", f"{SOURCE}:{relative}")

    def unchanged(self):
        for relative, raw in self.reads.items():
            require((self.repo / relative).read_bytes() == raw, f"Input changed while preparing: {relative}")


def changed_paths(before, after, prefix=""):
    if type(before) is not type(after):
        return [prefix]
    if isinstance(before, dict):
        result = []
        for key in sorted(set(before) | set(after)):
            p = prefix + "/" + key
            result.extend([p] if key not in before or key not in after else changed_paths(before[key], after[key], p))
        return result
    if isinstance(before, list) and len(before) == len(after):
        return [p for i, (a, b) in enumerate(zip(before, after))
                for p in changed_paths(a, b, prefix + "/" + str(i))]
    return [] if before == after else [prefix]


def prepare(ctx):
    receipt_raw = ctx.read(RECEIPT)
    receipt = json.loads(receipt_raw)
    validate_receipt(receipt)
    require(ctx.git("rev-parse", SOURCE + "^{tree}").decode().strip() == SOURCE_TREE,
            "Local Git source tree disagrees with observation")
    originals = {p: ctx.source(p) for p in (MANIFEST, DOSSIER)}
    old_m, old_d = (json.loads(originals[p]) for p in (MANIFEST, DOSSIER))
    require(old_m["edition"] == old_d["edition"] == "3.7", "Source metadata edition mismatch")
    require({k: v for k, v in old_m["publication_revision"].items() if k != "prior_current_fields"} ==
            {k: v for k, v in old_d["publication_revision"].items() if k != "prior_current_fields"},
            "Source publication revision objects differ beyond their own historical fields")
    require(old_m["current_release_stage"] == old_d["current_release_stage"] == "PUBLICATION_PR_PENDING",
            "Source commit must identify the pre-PR publication checkpoint")
    require(old_m["publication_revision"]["remote_publication"]["status"] == "PENDING",
            "Source metadata already has another remote state")
    check_identity(old_d["book_source_manifest"], originals[MANIFEST], "pre-PR manifest binding")

    bound_evidence = {}
    for key, name in (("git_payload_readback", "git-payload-readback.json"),
                      ("publication_preflight", "publication-preflight.json")):
        record = receipt["evidence"][key]
        require(record["path"] == EV + name, "Unexpected remote evidence path")
        raw = ctx.read(record["path"])
        check_identity(record, raw, key)
        bound_evidence[key] = json.loads(raw)
    payload = bound_evidence["git_payload_readback"]
    require(payload["schema"] == "ueot_physics.git_payload_readback.v1" and payload["status"] == "PASS" and
            payload["repository"] == REPOSITORY and payload["pull_request"] == PR and
            payload["source_commit"] == SOURCE and payload["remote_commit_tree"] == SOURCE_TREE and
            payload["local_staged_tree"] == SOURCE_TREE and payload["all_uploaded_blobs_match_staged_objects"] is True and
            payload["all_110_pr_file_blob_shas_read_back_and_equal"] is True, "Payload readback does not match source acceptance")
    files = payload["changed_files"]
    require(len(files) == 110 and len({x["path"] for x in files}) == 110, "Expected 110 unique source payload files")
    for entry in files:
        require(entry["path"].startswith(BOOK) and ".." not in PurePosixPath(entry["path"]).parts,
                "Payload path outside publication scope")
        raw = ctx.source(entry["path"])
        check_identity(entry, raw, entry["path"] + " at source commit")
        blob = hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()
        require(blob == entry["git_blob_sha"] == entry["pr_file_readback_sha"], "Payload Git blob identity mismatch")
    preflight = bound_evidence["publication_preflight"]
    require(preflight["schema"] == "ueot_physics.publication_preflight.v1" and
            preflight["status"] in {"PASS", "PASS_WITH_DOCUMENTED_WHITESPACE_NOTICES"} and
            preflight["source_commit"] == SOURCE and preflight["tree"] == SOURCE_TREE and
            preflight["missing_relative_file_targets"] == [] and preflight["changed_paths_outside_book"] == [] and
            preflight["staged_and_worktree_bytes_equal"] is True, "Preflight is not successful for the source tree")

    revision = copy.deepcopy(old_m["publication_revision"])
    artifacts = [record for edition in revision["artifacts"].values() for record in edition.values()]
    require(len(artifacts) == 6 and {x["path"] for x in artifacts} == SIX, "Expected exactly the six frozen artifacts")
    for record in artifacts:
        raw = ctx.read(record["path"])
        check_identity(record, raw, record["path"])
        require(raw == ctx.source(record["path"]), "Frozen artifact differs from CI source: " + record["path"])
    require(len(old_m["entries"]) == 12 and len(old_d["chapters"]) == 67 and len(old_d["appendices"]) == 6,
            "Unexpected publication inventory")
    results = [r for row in old_d["chapters"] + old_d["appendices"] for r in row.get("numbered_results", [])]
    require(len(results) == 173, "Expected 173 scientific result objects")
    workflow = ctx.source(".github/workflows/ueot-qm.yml")
    require(workflow.count(b"ref: ${{ github.event.pull_request.head.sha || github.sha }}") == 2,
            "Expected both workflow jobs to check out the exact PR head")

    # Only the two delivery READMEs may have changed after the tested source.
    for record in revision["review_materials"]:
        raw = ctx.read(record["path"])
        if record["path"] == BOOK + "review/README.md":
            record.update(identity(record["path"], raw))
        else:
            check_identity(record, raw, "unchanged scientific review: " + record["path"])
    historical = {}
    for label, path in (("source_manifest", MANIFEST), ("chapter_dossier", DOSSIER),
                        ("metadata_update_receipt", OLD_REPORT), ("local_acceptance_receipt", EV + "local-acceptance.json")):
        raw = ctx.source(path)
        if path not in originals:
            require(ctx.read(path) == raw, "Historical pre-PR receipt changed: " + path)
        historical[label] = {**identity(path, raw), "source_commit": SOURCE,
                             "immutable_url": f"https://github.com/{REPOSITORY}/blob/{SOURCE}/{path}"}
    followup = [identity(p, ctx.read(p)) for p in FOLLOWUP_FILES if (ctx.repo / p).is_file()]
    remote = {
        "status": STATE, "observed_at_utc": receipt["observed_at_utc"], "pr": PR,
        "pr_url": receipt["pull_request"]["url"], "source_commit": SOURCE, "source_tree": SOURCE_TREE,
        "pr_ci": copy.deepcopy(receipt["source_ci"]),
        "merged_main_commit": None, "main_ci": None, "merged_main_status": "PENDING_PUBLICATION_MAIN",
        "receipt": identity(RECEIPT, receipt_raw), "evidence": copy.deepcopy(receipt["evidence"]),
        "scope": receipt["scope"],
        "observation_responsibility": "Root-supplied GitHub observation; this helper validates local identities and receipt consistency, without a new network query",
        "metadata_followup": {
            "status": "SEPARATE_FOLLOWUP_COMMIT_NOT_COVERED_BY_SOURCE_CI",
            "final_ci_record": "PR_BODY", "recursive_receipt_commits_required": False,
            "frozen_six_artifacts_changed": False,
        },
    }
    revision["remote_publication"] = remote
    revision["prior_publication_metadata_checkpoint"] = {
        "stage": "PUBLICATION_PR_PENDING", "files": historical,
        "scope": "Old receipts are preserved at the immutable tested source commit. The original pre-PR metadata report stays unchanged; the current terminal local-acceptance receipt is regenerated downstream after this transition",
    }
    revision["metadata_update_receipt"] = {"path": REPORT, "direction": "Downstream; path only"}
    revision["local_acceptance_receipt"]["scope"] = (
        "Downstream terminal local acceptance: regenerate after this metadata update; path only. "
        "The old pre-PR receipt is separately preserved by its immutable source-commit identity")
    revision["followup_documents"] = {
        "files": followup,
        "scope": "Actual current delivery documentation/helper identities; subsequent metadata commit, not source-CI acceptance",
    }
    revision["hash_direction"] = HASH_DIRECTION
    revision["not_inferred"] = [
        "external peer review or new hardware experiments",
        "new local heavy scientific execution by this helper",
        "publication main merge or main CI acceptance",
        "CI acceptance of the subsequent delivery-metadata commit from the source run",
        "independent download/hash/content verification of remote CI artifact ZIPs",
    ]
    new_m, new_d = copy.deepcopy(old_m), copy.deepcopy(old_d)
    for obj, prior in ((new_m, old_m), (new_d, old_d)):
        obj["current_release_stage"] = STAGE
        obj["publication_revision"] = copy.deepcopy(revision)
        obj["publication_revision"]["prior_current_fields"] = copy.deepcopy(prior["publication_revision"]["prior_current_fields"])
    for obj, keys in ((new_m, ("canonical_identity", "canonical_english_identity")),
                      (new_d, ("canonical", "canonical_english"))):
        for key in keys:
            obj[key]["installation_status"] = STATE
    new_d["editorial_status"] = "PUBLICATION_REVIEWED_PR_SOURCE_VERIFIED_UNMERGED"
    for row in new_d["chapters"] + new_d["appendices"]:
        row["current_edition_verification"]["publication_remote_status"] = STATE
    for group in (new_d["derivatives"], new_d["derivatives"]["english"]):
        for key in ("pdf", "latex"):
            group[key]["remote_publication_status"] = STATE
    new_d["validation"].update({
        "remote_verified": True, "remote_status": STATE,
        "remote_status_scope": "Exact publication source commit and completed source PR CI only; main and later metadata CI are separate",
        "current_dossier_hash_receipt": REPORT, "hash_direction": HASH_DIRECTION,
    })
    new_d["release_acceptance"]["source_pr_ci"] = "PASS_SOURCE_COMMIT_" + SOURCE
    new_d["release_acceptance"]["new_runtime"] = (
        "NO_NEW_RUNTIME_SUITE; NO_MANUAL_LOCAL_HEAVY_RERUN; "
        "EXISTING_REMOTE_RUNTIME_PASSED_ON_SOURCE_" + SOURCE +
        "; SOURCE_BOUND_V31_10_RESEARCH_RECEIPTS_RETAINED")
    new_d["release_acceptance"]["source_pr_ci_scope"] = (
        f"Run {RUN}, both jobs completed success on {SOURCE}; later metadata-commit CI is recorded in PR body")
    # merged_main_ci remains PENDING_PUBLICATION_MAIN; all research objects remain literal.
    require(new_d["release_acceptance"]["merged_main_ci"] == "PENDING_PUBLICATION_MAIN", "Unexpected source main status")
    require(new_m["entries"] == old_m["entries"] and new_d["source_catalog"] == old_d["source_catalog"],
            "Scientific source object mutation")
    require([r for row in new_d["chapters"] + new_d["appendices"] for r in row.get("numbered_results", [])] == results,
            "Scientific result object mutation")
    require(new_m["publication_revision"]["scientific_reuse"] == old_m["publication_revision"]["scientific_reuse"],
            "Research acceptance mutation")
    manifest_raw = encoded(new_m)
    new_d["book_source_manifest"] = identity(MANIFEST, manifest_raw)
    dossier_raw = encoded(new_d)
    candidates = {MANIFEST: manifest_raw, DOSSIER: dossier_raw}
    diffs = {p: changed_paths(json.loads(originals[p]), json.loads(candidates[p])) for p in candidates}
    # A complete candidate is derived from immutable source objects. Any other
    # in-place metadata edit is refused, including changes to historical states.
    for path, candidate in candidates.items():
        current = ctx.read(path)
        require(current in (originals[path], candidate), "Current metadata is neither exact pre-PR source nor this exact update: " + path)
    report = {
        "schema": "ueot_physics.publication_remote_metadata_update.v1", "edition": "3.7",
        "status": "READY", "recorded_at_utc": receipt["observed_at_utc"],
        "publication_state": STATE, "source_commit": SOURCE, "source_tree": SOURCE_TREE,
        "source_ci_run": RUN, "remote_receipt": identity(RECEIPT, receipt_raw),
        "prior_checkpoint": historical,
        "resulting_metadata": {p: identity(p, raw) for p, raw in candidates.items()},
        "preservation": {
            "numbered_results": {"count": 173, "exact": True, "canonical_json_sha256": digest(results)},
            "manifest_entries": {"count": 12, "exact": True, "canonical_json_sha256": digest(old_m["entries"])},
            "source_catalog": {"exact": True, "canonical_json_sha256": digest(old_d["source_catalog"])},
            "scientific_reuse": {"exact": True, "canonical_json_sha256": digest(revision["scientific_reuse"])},
            "frozen_artifacts": artifacts, "source_payload_git_objects_checked": len(files),
        },
        "changed_json_pointers": diffs, "followup_documents": revision["followup_documents"],
        "workflow_source": identity(".github/workflows/ueot-qm.yml", workflow),
        "main_acceptance": "PENDING_PUBLICATION_MAIN",
        "metadata_followup_ci": "Separate commit; actual final run to be recorded in PR body",
        "terminal_acceptance_action": "Run accept_publication.py after this update to regenerate local-acceptance.json against the new metadata; do not feed its hash back into either metadata file",
        "hash_direction": HASH_DIRECTION,
        "scope": "Source receipt and metadata identity validation; no new network observation, local scientific execution, book edit, PDF build or visual review",
        "generator": {"path": str(Path(__file__).resolve()), "sha256": sha(Path(__file__).read_bytes())},
    }
    return candidates, report


def atomic_write(path, raw):
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix=path.name + ".", dir=path.parent)
    try:
        with os.fdopen(fd, "wb") as handle:
            handle.write(raw)
            handle.flush()
            os.fsync(handle.fileno())
        os.chmod(temporary, 0o644)
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--book-dir", type=Path, required=True)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true", help="Install only the two metadata files and new external report")
    mode.add_argument("--output-dir", type=Path, help="Write three preview files outside the official book")
    args = parser.parse_args()
    try:
        ctx = Inputs(args.book_dir)
        candidates, report = prepare(ctx)
        ctx.unchanged()
        if args.write:
            report["status"] = "PASS_INSTALLED_REMOTE_PUBLICATION_METADATA"
            for path, raw in candidates.items():
                atomic_write(ctx.repo / path, raw)  # manifest first, dossier second
            atomic_write(ctx.repo / REPORT, encoded(report))
        elif args.output_dir:
            output = args.output_dir.resolve()
            require(not output.is_relative_to(ctx.book), "Preview output must be outside the official book")
            report["status"] = "PREVIEW_READY"
            for path, raw in candidates.items():
                atomic_write(output / Path(path).name, raw)
            atomic_write(output / Path(REPORT).name, encoded(report))
        print(json.dumps({"status": report["status"], "publication_state": STATE,
                          "source_commit": SOURCE, "source_ci_run": RUN,
                          "resulting_metadata": report["resulting_metadata"]}, ensure_ascii=False, indent=2))
        return 0
    except (GuardError, KeyError, TypeError, ValueError, OSError, subprocess.CalledProcessError) as error:
        print("REFUSED: " + str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
