"""Replay the joint scientific review offline in its physics environment."""
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
CHECKS = (
    ("source_bridge.py --check", None),
    ("selection/verify.py", "selection/observed.json"),
    ("selection/audit_source.py", "selection/source_review.json"),
    ("network_review/replay.py --check", None),
    ("local/verify_local.py --check", None),
    ("local/energy_witness.py", None),
    ("accounting/replay.py", None),
    ("accounting/next_gate.py", None),
)


def compare_full_tables():
    import numpy as np
    from source_bridge import direct_network, field_noise
    sys.path[:0] = [str(HERE / "selection"), str(HERE / "network_review")]
    from audit_source import mixture, probabilities
    from kg_review import distribution, gaussian_preparation

    noise = np.array([float(x.mid) for x in field_noise(320)])
    worst = 0.
    for ratio in (1., .0001):
        args = noise * ratio
        _, _, table = direct_network(*args)
        gibbs = probabilities(mixture(*args, 13)[0])
        popper = distribution(gaussian_preparation(*args, 16))
        assert table.shape == gibbs.shape == popper.shape == (3,6,2,4,2)
        for peer in (gibbs, popper):
            np.testing.assert_allclose(table, peer, rtol=0, atol=2e-14)
            worst = max(worst, float(np.max(abs(table-peer))))
    print(f"PASS two doses, 288 record probabilities each, three implementations, max difference {worst:.3g}")


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Enable scientific assertions")
    for command, receipt in CHECKS:
        output = subprocess.check_output([sys.executable, "-B", *command.split()], cwd=HERE, text=True)
        if receipt and json.loads(output) != json.loads((HERE / receipt).read_text()):
            raise ValueError(f"Archived result changed: {receipt}")
        print(f"PASS {command}", flush=True)
    compare_full_tables()
