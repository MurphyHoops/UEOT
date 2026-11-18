"""Regenerate field/sector outputs and compare with the published observations."""
import json
import math
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def compare(a, b):
    if isinstance(a, dict) and isinstance(b, dict):
        return a.keys() == b.keys() and all(compare(a[k], b[k]) for k in a)
    if isinstance(a, list) and isinstance(b, list):
        return len(a) == len(b) and all(compare(i, j) for i, j in zip(a,b))
    if isinstance(a, float) and isinstance(b, float):
        return math.isclose(a,b,rel_tol=1e-9,abs_tol=5e-12)
    return a == b


def main():
    rows=[]
    for source, output in (("field/probe.py","field/observed.json"),("sectors/matter.py","sectors/matter-result.json"),
                           ("sectors/heat.py","sectors/heat-result.json"),("sectors/geometry.py","sectors/geometry-result.json")):
        actual = json.loads(subprocess.check_output([sys.executable, "-B", str(ROOT/source)]))
        expected = json.loads((ROOT/output).read_text())
        if not compare(actual,expected):
            raise ValueError("published checks differ for "+source)
        rows.append(source)
    print(json.dumps({"status":"PASS","compared":rows}))


if __name__=="__main__":
    main()
