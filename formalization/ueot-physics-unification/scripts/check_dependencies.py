"""Verify ueot-physics-unification inherits exact Core and QM toolchain & dependency locks."""
import json
from pathlib import Path

root = Path(__file__).resolve().parents[1]
qm = root.parent / "ueot-qm"
core = root.parent / "ueot-core"

assert (root / "lean-toolchain").read_bytes() == (core / "lean-toolchain").read_bytes()
assert (root / "lean-toolchain").read_bytes() == (qm / "lean-toolchain").read_bytes()

u_lock = json.loads((root / "lake-manifest.json").read_text())
qm_lock = json.loads((qm / "lake-manifest.json").read_text())
core_lock = json.loads((core / "lake-manifest.json").read_text())

key = lambda p: (p["name"], p.get("url"), p.get("rev"), p.get("subDir"))
u_git = {key(p) for p in u_lock["packages"] if p["type"] == "git"}
assert u_git == {key(p) for p in core_lock["packages"] if p["type"] == "git"}
assert u_git == {key(p) for p in qm_lock["packages"] if p["type"] == "git"}

local = {p["name"]: p["dir"] for p in u_lock["packages"] if p["type"] == "path"}
assert local == {"ueot_qm": "../ueot-qm", "ueot_core": "../ueot-core"}
print("PASS: exact Core + QM toolchain and dependency revisions inherited")
