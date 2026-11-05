#!/usr/bin/env python3
"""One concrete rejection probe for the complete-alternative certificate gate.

The successful actual graph is never modified on disk. One positive receipt
edge of an unchosen root action is removed only from an in-memory JSON copy.
"""
from pathlib import Path
import hashlib
import json

from verify_representation_dag import validate_graph


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def main():
    base = Path(__file__).resolve().parent
    source = base / "representation_actual_runs/long-01/stdout.json"
    reference = base / "representation_reference_runs/long-01/REFERENCE_RESULT.json"
    successful = base / "representation_dag_checks/long-01/THIS_DAG_CHECK.json"
    output = base / "representation_dag_checks/OMITTED_ALTERNATIVE_REJECTION_01.json"
    if output.exists():
        raise SystemExit("preserve the previous probe output")
    original = source.read_bytes()
    checked = json.loads(successful.read_bytes())
    assert checked["status"] == "PASS" and checked["dag_output_sha256"] == sha(original)
    data = json.loads(original)
    root = data["nodes"][data["root_id"]]
    alternative = next(a for a in root["alternatives"]
        if a["action"] != root["chosen_action"] and a["edges"])
    removed = alternative["edges"].pop(0)
    mutant = json.dumps(data, separators=(",", ":")).encode()
    result = {
        "schema": "UEOT/DECISION_REPRESENTATION_ALTERNATIVE_REJECTION/V1",
        "probe_sha256": sha(Path(__file__).read_bytes()),
        "checker_sha256": sha((base / "verify_representation_dag.py").read_bytes()),
        "original_dag_sha256": sha(original),
        "original_success_check_sha256": sha(successful.read_bytes()),
        "in_memory_mutant_sha256": sha(mutant),
        "root_node": root["id"], "unchanged_chosen_action": root["chosen_action"],
        "unchosen_alternative": alternative["action"], "removed_positive_edge": removed,
        "scope": "One deliberately incomplete unchosen-action certificate; no optimizer or original artifact mutation",
    }
    try:
        validate_graph(mutant, json.loads(reference.read_bytes()), 1000000)
    except AssertionError as exc:
        result["observed_rejection"] = str(exc)
        assert str(exc) == "certificate omits a positive successor of a legal alternative"
        result["status"] = "PASS_EXPECTED_REJECTION"
    else:
        result["status"] = "FAIL_MUTANT_ACCEPTED"
    assert source.read_bytes() == original
    result["original_artifact_unchanged"] = True
    output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps(result, ensure_ascii=False, indent=2))
    return 0 if result["status"] == "PASS_EXPECTED_REJECTION" else 1


if __name__ == "__main__":
    raise SystemExit(main())
