#!/usr/bin/env python3
"""Inspect actual v31.12 CI artifacts against an exact hydrated Git commit.

Read-only; does not extract ZIPs, execute source code, rerun proofs, or infer
paper/hardware claims from CI. Job metadata is required to certify skipped
build steps and is normally read beside the ZIPs as github-jobs.json.
"""
from pathlib import Path, PurePosixPath
import argparse
import datetime
import hashlib
import json
import subprocess
import sys
import zipfile

REPOSITORY = "MurphyHoops/UEOT"
PROOF_BASE = "06ca0dce8b03cd34e86785e97fdc3c7aa2c582bd"
PROOF_RUN = 43001276385
PINNED = {
    "source-manifest.json": "ec214db86cebe2e0bae2f02e5fe2028fc63d99c585ad655170bc2c9f4881bb2a",
    "lean-verification.json": "45afc9ee3bc2d02fd0c687c60910b5775831844a68416373e05f32fcdf21af8c",
    "remote/main/github-run.json": "d9d60b2f3859f7acf4730cd774c7b67ebc4ab556f118fa35e98aba61342b5cbf",
    "remote/main/lean-inspection.json": "f32d0a4e5b1320e87cb3cf63f6fa22d005aaf225e4c3c29409b569f8feb77575",
    "runtime/execution_receipt.json": "44c4d1a1e06144c1b8f7932fc576cba5e17e0fdf669a0198f480e390c5547523",
}


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def require(ok, label):
    if not ok:
        raise AssertionError(label)


class Archive:
    def __init__(self, path, expected):
        self.path = path
        self.sha256 = digest(path.read_bytes())
        require(self.sha256 == expected, f"archive digest: {path}")
        self.zip = zipfile.ZipFile(path)
        self.names = self.zip.namelist()
        require(len(set(self.names)) == len(self.names), "duplicate ZIP entry")
        require(all(not p.startswith("/") and ".." not in PurePosixPath(p).parts
                    for p in self.names), "unsafe ZIP name")

    def raw(self, suffix):
        suffix = suffix.removeprefix("/tmp/")
        matches = [n for n in self.names if n == suffix or n.endswith("/"+suffix)]
        require(len(matches) == 1, f"unique archived member: {suffix}")
        return self.zip.read(matches[0])

    def json(self, suffix):
        return json.loads(self.raw(suffix))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--repo", type=Path, required=True)
    p.add_argument("--runtime-zip", type=Path, required=True)
    p.add_argument("--proof-zip", type=Path, required=True)
    p.add_argument("--runtime-sha256", required=True)
    p.add_argument("--proof-sha256", required=True)
    p.add_argument("--head", required=True)
    p.add_argument("--run", required=True, type=int)
    p.add_argument("--output", required=True, type=Path)
    p.add_argument("--jobs-json", type=Path)
    p.add_argument("--run-json", type=Path)
    a = p.parse_args()
    repo = a.repo.resolve()
    source_cache = {}

    def at_commit(path):
        require(not path.startswith("/") and ".." not in PurePosixPath(path).parts,
                f"repository-relative path: {path}")
        if path not in source_cache:
            source_cache[path] = subprocess.check_output(
                ["git", "show", a.head+":"+path], cwd=repo)
        return source_cache[path]

    require(len(a.head) == 40, "full scientific commit required")
    subprocess.check_output(["git", "cat-file", "-e", a.head+"^{commit}"], cwd=repo)
    rt = Archive(a.runtime_zip, a.runtime_sha256)
    pf = Archive(a.proof_zip, a.proof_sha256)

    def source_id(item, prefix=""):
        raw = at_commit(prefix+item["path"])
        require(digest(raw) == item["sha256"], "commit source hash: "+prefix+item["path"])
        if "bytes" in item:
            require(len(raw) == item["bytes"], "commit source size: "+prefix+item["path"])

    def archived_id(item):
        raw = rt.raw(item["path"])
        require(digest(raw) == item["sha256"], "archive output hash: "+item["path"])
        if "bytes" in item:
            require(len(raw) == item["bytes"], "archive output size: "+item["path"])

    def runtime_context(ctx, workflow_key):
        require(ctx["provider"] == "github_actions", "actual GitHub provider")
        require(ctx["observed_git_head"] == a.head, "actual checked-out head")
        g = ctx[workflow_key]
        require(g["GITHUB_REPOSITORY"] == REPOSITORY, "runtime repository")
        require(g["GITHUB_RUN_ID"] == str(a.run), "runtime run id")
        require(g["GITHUB_JOB"] == "runtime", "runtime job id")
        require(int(g["GITHUB_RUN_ATTEMPT"]) >= 1, "runtime run attempt")
        require(g["GITHUB_EVENT_NAME"] in {"pull_request", "push", "workflow_dispatch"}, "event identity")
        # In pull_request events GITHUB_SHA may be GitHub's synthetic merge SHA.
        # observed_git_head, captured after the explicit head checkout, binds code.
        return g

    fresh_name = "ueot-qm-growing-cutoff/execution_receipt.json"
    fresh = rt.json(fresh_name)
    require(fresh["schema"] == "ueot-qm.growing-cutoff-runtime/1", "new receipt schema")
    require(fresh["version"] == "v31.12" and fresh["status"] == "PASS", "new runtime PASS")
    require(len(fresh["inputs"]) == 12 and len(fresh["outputs"]) == 8, "new inventory dimensions")
    require(len(fresh["commands"]) == 4 and all(c["exit_code"] == 0 for c in fresh["commands"]), "four commands passed")
    require([c["label"] for c in fresh["commands"]] == [
        "source-integration", "independent-operational", "independent-microscopic",
        "independent-exact-certificate"], "four actual gate identities")
    require(fresh["inputs_stable_during_execution"] is True, "stable new inputs")
    require(fresh["new_lean_execution"] is False and fresh["new_hardware_data"] is False,
            "no promoted Lean or hardware evidence")
    fresh_github = runtime_context(fresh["execution_context"], "github")
    for item in fresh["inputs"]:
        source_id(item)
    for item in fresh["outputs"]+[c["log"] for c in fresh["commands"]]:
        archived_id(item)

    # The older runtime is retained as a distinct actual CI execution.
    older = rt.json("ueot-qm-operational-micro-robust/execution_receipt.json")
    require(older["schema"] == "ueot-qm.runtime-increment/2" and older["status"] == "PASS", "older runtime PASS")
    require(older["execution_actor"] == "GitHub Actions runner", "older actual actor")
    require(len(older["inputs"]) == 13 and len(older["commands"]) == 7, "older runtime scope")
    require(older["inputs_stable_during_execution"] is True, "older stable inputs")
    require(all(c["exit_code"] == 0 for c in older["commands"]), "older seven commands")
    runtime_context(older["execution_context"], "workflow")
    for item in older["inputs"]:
        source_id(item)
    for item in older["outputs"]+[c["log"] for c in older["commands"]]:
        archived_id(item)

    book = rt.json("ueot-qm-book3.9-increment.json")
    require(book["status"] == "PASS", "bilingual incremental verification")
    require(book["total_result_count"] == 188 and book["new_result_count"] == 6,
            "bilingual result counts")
    for path, expected in book["consumed_sha256"].items():
        require(digest(at_commit(path)) == expected, "book consumed exact head: "+path)
    require(digest(at_commit("physics/qm/book/build/verify_v3_9_increment.py")) == book["checker_sha256"],
            "actual bilingual checker identity")

    finite = rt.json("ueot-qm-finite-conditioning/execution_receipt.json")
    require(finite["status"] == "PASS" and finite["source_unchanged_during_execution"] is True,
            "finite conditioning PASS")
    for name, expected in finite["source_sha256"].items():
        require(digest(at_commit("physics/qm/conditioning/"+name)) == expected, "finite source: "+name)
    for gate in finite["gates"]:
        require(gate["status"] == "PASS" and gate["returncode"] == 0, "finite gate: "+gate["name"])
        require(digest(rt.raw("ueot-qm-finite-conditioning/"+gate["log"])) == gate["log_sha256"],
                "finite actual log: "+gate["name"])
    kernel = rt.json("ueot-qm-runtime-verification.json")
    require(kernel["status"] == "PASS" and not kernel["failures"] and not kernel["errors"], "kernel PASS")
    for item in kernel["sources"]:
        source_id(item, "physics/qm/kernel/")

    reused = pf.json("ueot-qm-proof-reuse.json")
    require(reused["status"] == "SOURCE_IDENTITY_REUSED" and reused["proof_reuse_eligible"] is True,
            "proof reuse actual decision")
    require(not reused["errors"] and not reused["runtime_mismatches"], "no source reuse mismatch")
    require(reused["proof_input_count"] == 158 and reused["old_runtime_input_count"] == 13,
            "proof reuse exact inventories")
    require(reused["old_runtime_inputs_identical"] is True, "old runtime source identity")
    require(reused["reused_proof_commit"] == PROOF_BASE and reused["reused_workflow_run"] == PROOF_RUN,
            "original proof execution identity")
    require(reused["reused_axiom_reports"] == 1365 and reused["new_lean_execution"] is False
            and reused["new_lean_theorems"] == 0 and reused["new_paper_claims_not_promoted_to_lean"] is True,
            "machine scope is reuse only")
    prefix = "physics/qm/kernel/evidence/v31.11/"
    for path, expected in PINNED.items():
        require(digest(at_commit(prefix+path)) == expected, "pinned old evidence: "+path)
    old_manifest = json.loads(at_commit(prefix+"source-manifest.json"))
    require(len(old_manifest["sources"]) == 158 and old_manifest["source_set_sha256"] == reused["proof_source_set_sha256"],
            "proof manifest scope")
    for item in old_manifest["sources"]:
        source_id(item)
    old_receipt = json.loads(at_commit(prefix+"runtime/execution_receipt.json"))
    require(len(old_receipt["inputs"]) == 13, "original runtime inventory")
    for item in old_receipt["inputs"]:
        source_id(item)
    changed = subprocess.check_output([
        "git", "diff", "--name-only", PROOF_BASE, a.head, "--",
        "formalization/ueot-qm", "formalization/ueot-core", "physics/qm/kernel",
        ":(exclude)physics/qm/kernel/evidence/**"], cwd=repo, text=True).splitlines()
    require(not changed, "entire proof/tool inventory unchanged: "+repr(changed))

    jobs_path = a.jobs_json or a.runtime_zip.parent/"github-jobs.json"
    require(jobs_path.is_file(), "actual jobs metadata required for skipped-step verification")
    jobs_doc = json.loads(jobs_path.read_text())
    jobs = jobs_doc if isinstance(jobs_doc, list) else jobs_doc["jobs"]
    selected = {j["name"]:j for j in jobs if j["name"] in {"runtime", "lean"}}
    require(set(selected) == {"runtime", "lean"}, "runtime and lean actual jobs")
    for name,j in selected.items():
        require(j["run_id"] == a.run, "job run identity: "+name)
        if "head_sha" in j:
            require(j["head_sha"] == a.head, "job head identity: "+name)
        require(j["status"] == "completed" and j["conclusion"] == "success", "job completion: "+name)
    steps = {s["name"]:s for s in selected["lean"]["steps"]}
    for name in ["Check exact inherited proof identity or require a full build", "Archive proof evidence"]:
        require(steps[name]["conclusion"] == "success", "actual lean reuse step: "+name)
    skipped = [
        "Record source identity", "Check inherited dependency lock",
        "Install and verify official pinned Lean", "Restore pinned dependencies",
        "Restore Mathlib proof cache", "Save pinned dependency cache", "Reject proof escapes",
        "Build all QM proofs", "Audit theorem axioms",
        "Verify generated exact certificates and false witnesses",
        "Verify retained finite and quantum Lean witnesses",
    ]
    for name in skipped:
        require(steps[name]["conclusion"] == "skipped", "actual skipped build step: "+name)

    run_path = a.run_json or a.runtime_zip.parent/"github-run.json"
    # The connector's normalized jobs response may omit head_sha. Bind every
    # job's run_id to the separate actual run metadata rather than inventing it.
    require(run_path.is_file(), "actual workflow metadata required for job/head binding")
    run_meta = json.loads(run_path.read_text())
    require(run_meta["id"] == a.run and run_meta["head_sha"] == a.head, "workflow run identity")
    require(run_meta["status"] == "completed" and run_meta["conclusion"] == "success", "workflow success")

    result = {
        "schema": "ueot-qm.growing-cutoff-remote-artifacts/1",
        "status": "PASS", "observed_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "checker_sha256": digest(Path(__file__).read_bytes()), "command": sys.argv,
        "run_id": a.run, "scientific_head": a.head,
        "workflow_url": f"https://github.com/{REPOSITORY}/actions/runs/{a.run}",
        "artifacts": {"runtime_sha256":rt.sha256, "proof_sha256":pf.sha256},
        "new_runtime": {"inputs":12, "outputs":8, "logs":4, "commands":4,
                        "receipt_sha256":digest(rt.raw(fresh_name)), "execution_context":fresh["execution_context"]},
        "older_runtime": {"inputs":13, "outputs":len(older["outputs"]), "commands":7,
                          "execution_context":older["execution_context"]},
        "book": {"status":"PASS", "consumed_identities":len(book["consumed_sha256"]),
                 "result_count":188, "new_results":6},
        "finite_conditioning": {"status":"PASS", "inputs":len(finite["source_sha256"]), "gates":len(finite["gates"])},
        "kernel": {"status":"PASS", "source_count":len(kernel["sources"]), "test_methods_run":kernel["test_methods_run"]},
        "proof_reuse": {"status":"SOURCE_IDENTITY_REUSED", "inputs":158, "old_runtime_inputs":13,
                        "original_commit":PROOF_BASE, "original_run":PROOF_RUN,
                        "public_axiom_reports":1365, "new_lean_execution":False},
        "jobs_metadata_sha256":digest(jobs_path.read_bytes()),
        "jobs": {name:{"id":j["id"],"conclusion":j["conclusion"],"run_id":j["run_id"],
                       "head_bound_via_run_metadata":run_meta["head_sha"]} for name,j in selected.items()},
        "actually_skipped_lean_build_steps":skipped,
        "run_metadata_sha256":digest(run_path.read_bytes()) if run_meta else None,
        "unique_exact_commit_sources_read":len(source_cache),
        "new_hardware_data":False,
        "scope":"Archive hashes, actual CI identities, exact commit bytes and skipped-step evidence. No new proof-assistant coverage for paper theorems and no device evidence inferred.",
    }
    a.output.parent.mkdir(parents=True, exist_ok=True)
    a.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({"status":"PASS", "run":a.run, "head":a.head,
                     "new_inputs":12,"new_outputs":8,"new_logs":4,
                     "proof_inputs":158,"book_inputs":len(book["consumed_sha256"]),
                     "lean_build":"SKIPPED_WITH_EXACT_SOURCE_REUSE"}))


if __name__ == "__main__":
    main()
