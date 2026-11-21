"""Replay the research and the four peer reviews using the current physics interpreter."""
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
CHECKS = (
    ("field/match.py --check", None),
    ("heat/verify_heat.py --check", None),  # includes the independent field check
    ("matter/verify.py --predict-only", "matter/prediction_before_comparison.json"),
    ("matter/verify.py", "matter/observed.json"),
    ("gravity/verify_gravity.py", "gravity/observed.json"),
    ("cosmology/replay.py --check", None),
    ("matter/review_gravity.py", "matter/gravity_review_run.json"),
    ("gravity/check_cosmology.py", "gravity/cosmology-check.json"),
    ("cosmology/replay.py --review-matter", "cosmology/matter_review_run.json"),
    ("background_limit.py", None),
)


if __name__ == "__main__":
    for command, receipt in CHECKS:
        run = subprocess.run([sys.executable, "-B", *command.split()], cwd=ROOT,
                             check=True, stdout=subprocess.PIPE, text=True)
        if receipt and json.loads(run.stdout) != json.loads((ROOT / receipt).read_text()):
            raise ValueError(f"{command} differs from {receipt}")
        print("PASS", command, flush=True)
    print(f"{len(CHECKS)} replays passed")
