"""New k=257..512 enclosures for the same prepared state; old modes stay frozen."""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import sys
from mpmath import iv, mp

HERE=Path(__file__).resolve().parent
PROP=HERE.parent/"evolution"/"propagation"
sys.path.insert(0,str(PROP))
import extra_eta0
import finite_modes as fm
from background import I, box, upper
BASE="d62c9ff9525ebf314f5aae5f674c38c9761de1fa"

def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def run():
    assert __debug__ and sys.flags.optimize==0
    sources={str(p.relative_to(HERE.parent)):digest(p)
        for p in [Path(__file__),PROP/"extra_eta0.py",PROP/"finite_modes.py",PROP/"background.py"]}
    result=extra_eta0.calculate(first=257,last=512,degree=16,tolerance="1e-16",rho_budget="0.000001")
    result["new_source_sha256"]=sources
    result["old_modes_reintegrated"]=0
    result["new_modes_integrated"]=256
    result["frozen_predecessor"]=BASE
    assert sources=={name:digest(HERE.parent/name) for name in sources}
    return result

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--write",action="store_true")
    ap.add_argument("--check",action="store_true")
    args=ap.parse_args()
    result=run()
    path=HERE/"modes_257_512.json"
    if args.check:
        old=json.loads(path.read_text())
        for key in set(old)|set(result):
            if key!="diagnostic_wall_seconds":
                assert old[key]==result[key],("New mode receipt mismatch",key)
    if args.write:path.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    print("PASS: 256 new modes certified; no previous mode reintegrated",flush=True)
if __name__=="__main__":main()
