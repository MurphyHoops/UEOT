#!/usr/bin/env python3
"""Read-only positive and in-memory negative controls for the remote transition."""
import argparse
import copy
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--book-dir", type=Path, required=True)
parser.add_argument("--helper", type=Path, default=Path(__file__).with_name("record_remote_publication.py"))
parser.add_argument("--output", type=Path, required=True)
args = parser.parse_args()
spec = importlib.util.spec_from_file_location("remote_publication", args.helper)
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
ctx = m.Inputs(args.book_dir)
candidates, positive = m.prepare(ctx)
receipt = json.loads(ctx.read(m.RECEIPT))
controls = []


def reject(name, operation):
    try:
        operation()
    except m.GuardError as error:
        controls.append({"name": name, "status": "PASS_REJECTED", "reason": str(error)})
    else:
        raise AssertionError("Negative control was accepted: " + name)


def changed_receipt(name, mutate):
    altered = copy.deepcopy(receipt)
    mutate(altered)
    reject(name, lambda: m.validate_receipt(altered))


changed_receipt("source_run_in_progress", lambda r: r["source_ci"].update(status="in_progress", conclusion=None))
changed_receipt("source_run_failed", lambda r: r["source_ci"].update(conclusion="failure"))
changed_receipt("wrong_source_run_head", lambda r: r["source_ci"].update(head_sha="0" * 40))
changed_receipt("lean_job_in_progress", lambda r: r["source_ci"]["jobs"][1].update(status="in_progress", conclusion=None))
changed_receipt("wrong_job_source_head", lambda r: r["source_ci"]["jobs"][1].update(head_sha="0" * 40))
changed_receipt("missing_lean_job", lambda r: r["source_ci"].update(jobs=r["source_ci"]["jobs"][:1]))
changed_receipt("merged_pr_cannot_be_recorded_as_unmerged", lambda r: r["pull_request"].update(merged=True))
changed_receipt("observation_before_completion", lambda r: r.update(observed_at_utc="2026-01-01T00:00:00Z"))


def skip_certificate(r):
    for job in r["source_ci"]["jobs"]:
        for step in job.get("steps", []):
            if step["name"] == "Verify generated exact certificates and false witnesses":
                step["conclusion"] = "skipped"


changed_receipt("skipped_certificate_check", skip_certificate)


class Modified(m.Inputs):
    def __init__(self, overrides):
        super().__init__(args.book_dir)
        self.overrides = overrides

    def read(self, relative):
        original = super().read(relative)
        return self.overrides.get(relative, original)


artifact_path = m.BOOK + "UEOT_PHYSICS.en.md"
reject("modified_frozen_english_manuscript", lambda: m.prepare(Modified({artifact_path: ctx.read(artifact_path) + b"\n"})))
for name, path, mutate in (
    ("modified_numbered_result", m.DOSSIER,
     lambda d: next(row for row in d["chapters"] if row["numbered_results"])["numbered_results"][0].update(_synthetic_mutation=True)),
    ("modified_source_catalog", m.DOSSIER, lambda d: d.update(source_catalog={})),
    ("modified_manifest_entry", m.MANIFEST, lambda d: d["entries"][0].update(_synthetic_mutation=True)),
    ("modified_research_acceptance", m.MANIFEST,
     lambda d: d["publication_revision"]["scientific_reuse"].update(status="SYNTHETIC_UNAUTHORIZED_CHANGE")),
):
    altered = json.loads(ctx.read(path))
    mutate(altered)
    reject(name, lambda p=path, a=altered: m.prepare(Modified({p: m.encoded(a)})))
report_path = m.BOOK + "review/PHYSICAL_DERIVATION_AUDIT.md"
reject("modified_scientific_audit_report", lambda: m.prepare(Modified({report_path: ctx.read(report_path) + b"\n"})))
bad = copy.deepcopy(receipt)
bad["evidence"]["git_payload_readback"]["sha256"] = "0" * 64
reject("incorrect_payload_receipt_hash", lambda: m.prepare(Modified({m.RECEIPT: m.encoded(bad)})))

same, _ = m.prepare(Modified(candidates))
assert same == candidates
partial, _ = m.prepare(Modified({m.MANIFEST: candidates[m.MANIFEST]}))
assert partial == candidates
ctx.unchanged()
result = {
    "schema": "ueot_physics.remote_publication_guard_check.v1",
    "status": "PASS", "source_commit": m.SOURCE, "source_ci_run": m.RUN,
    "helper": {"name": args.helper.name, "sha256": m.sha(args.helper.read_bytes())},
    "guard_driver": {"name": Path(__file__).name, "sha256": m.sha(Path(__file__).read_bytes())},
    "actual_remote_receipt": m.identity(m.RECEIPT, ctx.read(m.RECEIPT)),
    "actual_receipt_positive_check": "PASS_READ_ONLY",
    "already_generated_candidate_before_terminal_regeneration": "PASS_REPRODUCIBLE",
    "partial_manifest_first_install_recovery": "PASS_REPRODUCIBLE",
    "negative_controls": controls, "negative_controls_count": len(controls),
    "formal_worktree_modified_by_this_check": False,
    "scope": "Actual root-supplied receipt positive validation and synthetic in-memory negative controls only; no remote observation or science rerun. No candidate metadata hash is included, so this report can be an upstream input without a cycle.",
}
args.output.parent.mkdir(parents=True, exist_ok=True)
args.output.write_bytes(m.encoded(result))
print(json.dumps({"status": result["status"], "negative_controls_count": len(controls),
                  "output": str(args.output), "helper_sha256": result["helper"]["sha256"]}, indent=2))
