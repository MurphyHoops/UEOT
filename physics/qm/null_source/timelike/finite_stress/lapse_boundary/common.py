"""Independent new-cohort utilities; predecessor files are JSON/text inputs only."""
from __future__ import annotations
import argparse, hashlib, json, math, sys
from pathlib import Path
from mpmath import iv
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[5]
TIMELIKE = HERE.parents[1]
BASE = "eae6769b97393b310054c21b804d7ed03a1371dc"
iv.dps = 120

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def load(rel):
    path = TIMELIKE / rel
    value = json.loads(path.read_text())
    require(value.get("status") == "PASS", "Unaccepted frozen input: " + rel)
    return value

def exact(value):
    if isinstance(value, float):
        n, d = value.as_integer_ratio()
        return iv.mpf(n) / d
    return iv.mpf(value)

def box(value):
    return iv.mpf([exact(value[0]).a, exact(value[1]).b])

def interval(lo, hi):
    return iv.mpf([exact(lo).a, exact(hi).b])

def above(x, y=0):
    return bool(x.a > exact(y))

def below(x, y):
    return bool(x.b < exact(y))

def outward(x):
    return [math.nextafter(float(x.a), -math.inf),
            math.nextafter(float(x.b), math.inf)]

def finish(script, payload, inputs=(), proof=None):
    require(__debug__ and sys.flags.optimize == 0, "Assertions must stay enabled")
    ap = argparse.ArgumentParser()
    ag = ap.add_mutually_exclusive_group(required=True)
    ag.add_argument("--write", action="store_true")
    ag.add_argument("--check", action="store_true")
    args = ap.parse_args()
    name = Path(script).stem
    paths = [HERE / script, HERE / "common.py",
             HERE / (proof or (name.upper() + ".md"))]
    paths += [TIMELIKE / p for p in inputs]
    for p in paths:
        require(p.is_file() and not p.is_symlink(), "Missing regular source: " + str(p))
    payload.update(
        schema="ueot-lapse-boundary-" + name + "/1",
        status="PASS",
        source_sha256={str(p.relative_to(REPO)): sha(p.read_bytes()) for p in sorted(set(paths))},
        verification_kind="new symbolic/exact or outward interval checks; analytic proofs separately stated",
        old_scientific_modules_imported_or_executed=0,
        mode_ODE_integrations=0,
        geometry_ODE_integrations=0,
        full_joint_Einstein_CTP_device_solution=False,
        whole_physical_unification="OPEN")
    target = HERE / (name + ".json")
    if args.write:
        target.write_text(json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True) + "\n")
    else:
        require(json.loads(target.read_text()) == payload, "Saved result differs: " + name)
    print("PASS: " + name)
