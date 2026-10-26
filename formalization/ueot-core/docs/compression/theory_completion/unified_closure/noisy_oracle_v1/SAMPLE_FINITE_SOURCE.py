#!/usr/bin/env python3
"""Draw once from the declared finite model; preserve every registered row.

The probability theorem uses ideal independent uniform draws. Correctness of
the OS CSPRNG backend is an explicit source-matching assumption, not a theorem
proved by inspecting this dataset. Raw draws support exact deterministic replay.
"""
import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import secrets

N = 4096

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    rows = [[0] * N, [2 if secrets.randbelow(4) == 0 else 1 for _ in range(N)], [2] * N]
    assert len(rows) == 3 and all(len(row) == N for row in rows)
    assert set(rows[0]) == {0} and set(rows[1]) <= {1, 2} and set(rows[2]) == {2}
    dataset = {
        "schema": "R2_FINITE_MODEL_SAMPLES_V1",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "sample_count": N,
        "state_order": ["cemetery", "start", "goal"],
        "source": "p=1/4 progress from start; goal and cemetery absorbing; action Unit",
        "sampler": "Python secrets.randbelow(4), queried once per start-row response",
        "seed": None,
        "replay": "Use these complete raw rows; no resampling to obtain a desired certificate",
        "source_matching": "Ideal uniform independent OS draws assumed; backend not verified in Lean",
        "external_scientific_evidence": "UNVERIFIED",
        "oracle_inputs": ["sample_count", "rows"],
        "rows": rows,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("x") as stream:
        json.dump(dataset, stream, indent=2)
        stream.write("\n")
    print(json.dumps({"state": "DRAWN_ONCE", "samples_per_row": N,
                      "start_goal_count": rows[1].count(2), "output": str(args.output)}))
