"""I/O and read-only access to immutable upstream Git blobs."""
from functools import lru_cache
from pathlib import Path
import hashlib
import json
import subprocess
import sys
import types

ROOT = Path(__file__).resolve().parent
COMMIT = "44b6cd200cd01eccf15d4dc817311388d317a1af"
REPO = "/Users/murphyhoops/Documents/ueotlean"
NAMES = ("common_c", "interval_source", "dynamics")

@lru_cache(None)
def blob(name):
    if name not in NAMES:
        raise ValueError(name)
    return subprocess.check_output(["git","-C",REPO,"show",f"{COMMIT}:physics/qm/persistent_bath/{name}.py"])

@lru_cache(None)
def historic(name):
    if name == "interval_source":
        historic("common_c")
    m = types.ModuleType(name)
    m.__file__ = str(ROOT / (name + ".py"))
    sys.modules[name] = m
    exec(compile(blob(name), m.__file__, "exec"), m.__dict__)
    return m

def read(name):
    return json.loads((ROOT/name).read_text())

def write(name,obj):
    (ROOT/name).write_text(json.dumps(obj,indent=2,allow_nan=False)+"\n")

def sha(name):
    return hashlib.sha256((ROOT/name).read_bytes()).hexdigest()

def verify_freeze():
    for name,digest in read("freeze.json")["files"].items():
        if name == "truth.json":
            continue  # Truth is verified by the producer, opaque to inference.
        if sha(name) != digest:
            raise ValueError(f"changed after freeze: {name}")

def settings(phase):
    cfg=read("protocol.json")
    if phase=="calibration":
        return cfg["calibration"]
    return cfg["holdout_phase"] | {f"{f}_{o}":cfg["shots_per_bell_setting"]
             for f in cfg["holdout_families"] for o in cfg["bell_tests"]}

def unpack(phase):
    import numpy as np
    cfg=read("protocol.json")
    n=cfg["block"]
    plan=settings(phase)
    with np.load(ROOT/(phase+".npz"),allow_pickle=False) as f:
        order,rows=f["block_setting"],f["ordered_codes"]
    if rows.shape!=(len(order),n) or rows.dtype!=np.uint8 or np.any(order>=len(plan)):
        raise ValueError("invalid archive")
    result={}
    for i,(key,total) in enumerate(plan.items()):
        data=rows[order==i].reshape(-1)
        cells=8 if "_" in key else 2
        if len(data)!=total or np.any(data>=cells):
            raise ValueError(f"invalid data: {key}")
        result[key]=np.bincount(data,minlength=cells).tolist()
    return result
