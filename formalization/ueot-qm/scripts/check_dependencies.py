"""Verify the QM package inherits the exact Core dependency lock."""
import json
from pathlib import Path

root = Path(__file__).resolve().parents[1]
core = root.parent / "ueot-core"
assert (root / "lean-toolchain").read_bytes() == (core / "lean-toolchain").read_bytes()
qm_lock = json.loads((root / "lake-manifest.json").read_text())
core_lock = json.loads((core / "lake-manifest.json").read_text())
key = lambda p: (p["name"], p.get("url"), p.get("rev"), p.get("subDir"))
assert {key(p) for p in qm_lock["packages"] if p["type"] == "git"} == {
    key(p) for p in core_lock["packages"] if p["type"] == "git"
}, "QM dependency lock diverges from the Core lock"
local = [p for p in qm_lock["packages"] if p["type"] == "path"]
assert len(local) == 1 and local[0]["name"] == "ueot_core"
assert (root / local[0]["dir"]).resolve() == core.resolve()
print("PASS: exact Core toolchain and dependency revisions inherited")

