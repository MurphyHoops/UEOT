"""Replay the physics claims and independently check the archived readouts."""
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
CHECKS = (
    ("weak_lens.py --check", None),
    ("aperture.py", None),
    ("herald.py", None),
    ("geometry/verify_geometry.py --check", None),
    ("geometry/review_weak.py", None),
    ("geometry/sphere.py", None),
    ("central_jet.py", None),
    ("finite_window.py", "finite_window_result.json"),
    ("probe/replay.py", "probe/observed.json"),
    ("probe/sign_pair.py", "probe/pair_observed.json"),
    ("probe/reset_selection.py", None),
    ("inference/replay.py --check", None),
    ("inference/cross_review.py --check", None),
    ("matter/replay.py --check", None),
    ("matter/review_inference.py", None),
    ("timelike/geometry/verify.py --check", None),
    ("timelike/quantum/check.py", "timelike/quantum/observed.json"),
    ("timelike/instrument/instrument.py --check", None),
    ("timelike/identification/replay.py --check", None),
    ("timelike/joint.py", "timelike/result.json"),
    ("timelike/experiment/replay.py", "timelike/experiment/result.json"),
)

if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Enable scientific assertions")
    for command, receipt in CHECKS:
        output = subprocess.check_output([sys.executable, "-B", *command.split()], cwd=HERE, text=True)
        if receipt and json.loads(output) != json.loads((HERE / receipt).read_text()):
            raise ValueError(f"Archived result changed: {receipt}")
        print(f"PASS {command}", flush=True)
