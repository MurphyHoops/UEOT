#!/usr/bin/env python3
"""Deterministically package the audited pure-kernel Lean 4 proof code from
formalization/ueot-core/ into an Apache-2.0 Zenodo-ready software archive,
excluding .lake/, build caches, and non-code CC BY 4.0 documentation under docs/.
"""
from pathlib import Path
import datetime
import gzip
import hashlib
import io
import json
import subprocess
import tarfile

HERE = Path(__file__).resolve().parent
REPO_ROOT = HERE.parents[2]
CORE_DIR = REPO_ROOT / "formalization" / "ueot-core"
APACHE_TXT = REPO_ROOT / "LICENSES" / "Apache-2.0.txt"
DIST_DIR = HERE / "dist"
DIST_DIR.mkdir(exist_ok=True)

ARCHIVE_PREFIX = "lean4-pure-kernel-formalization-v1.0.0"
TARBALL_PATH = DIST_DIR / f"{ARCHIVE_PREFIX}.tar.gz"


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


EXPORT_README = """# Pure-Kernel Lean 4 Formalization Archive (v1.0.0)

**License:** Apache License, Version 2.0 (`Apache-2.0` — see `LICENSE` and `NOTICE`)  
**Toolchain:** `leanprover/lean4:v4.33.1`  
**Mathlib Pin:** `0df444a360eaa60ab8c11dca51a86af692955474` (`lake-manifest.json`)

## Contents

- `UEOT.lean` & `UEOT/` — 1,051 Lean 4 library modules (`0` `sorryAx`, `0` `Lean.ofReduceBool` / `native_decide`)
- `scripts/ExhaustiveAxiomAudit.lean` — environment-wide kernel axiom verifier confirming transitive dependencies lie strictly inside `{propext, Classical.choice, Quot.sound}`
- `lakefile.lean`, `lake-manifest.json`, `lean-toolchain` — pinned reproducible Lake configuration
- `LICENSE`, `NOTICE`, `CITATION.cff`, `.zenodo.json` — Apache-2.0 license, Section 4(d) upstream attributions, and citation metadata

## Reproducible Build & Kernel Axiom Audit

```bash
lake exe cache get
lake build UEOT
lake env lean --run scripts/ExhaustiveAxiomAudit.lean
```
"""


def collect_files():
    entries = []

    # 1. License & attribution metadata at archive root
    entries.append(("LICENSE", APACHE_TXT.read_bytes()))
    entries.append(("NOTICE", (HERE / "NOTICE").read_bytes()))
    entries.append(("CITATION.cff", (HERE / "CITATION.cff").read_bytes()))
    entries.append((".zenodo.json", (HERE / ".zenodo.json").read_bytes()))
    entries.append(("README.md", EXPORT_README.encode("utf-8")))

    # 2. Pinned Lake build configuration & root library entry
    for cfg in ["lean-toolchain", "lakefile.lean", "lake-manifest.json", "UEOT.lean"]:
        p = CORE_DIR / cfg
        entries.append((cfg, p.read_bytes()))

    # 3. All Lean 4 modules + preserved ThirdParty upstream notices under UEOT/
    for p in sorted((CORE_DIR / "UEOT").rglob("*")):
        if p.is_file() and "__pycache__" not in p.parts and p.name != ".DS_Store":
            rel = str(p.relative_to(CORE_DIR))
            entries.append((rel, p.read_bytes()))

    # 4. Pure-kernel verification scripts under scripts/
    for p in sorted((CORE_DIR / "scripts").rglob("*")):
        if p.is_file() and "__pycache__" not in p.parts and p.name != ".DS_Store":
            rel = str(p.relative_to(CORE_DIR))
            entries.append((rel, p.read_bytes()))

    return sorted(entries, key=lambda kv: kv[0])


def main():
    entries = collect_files()
    lean_lib_modules = [
        rel for rel, _ in entries
        if (rel == "UEOT.lean" or rel.startswith("UEOT/")) and rel.endswith(".lean")
    ]
    script_files = [rel for rel, _ in entries if rel.startswith("scripts/")]

    # Deterministic reproducible tar.gz (mtime=0, uid=0, gid=0)
    raw_tar = io.BytesIO()
    with tarfile.open(fileobj=raw_tar, mode="w") as tf:
        for rel, data in entries:
            ti = tarfile.TarInfo(name=f"{ARCHIVE_PREFIX}/{rel}")
            ti.size = len(data)
            ti.mtime = 0
            ti.uid = 0
            ti.gid = 0
            ti.uname = "root"
            ti.gname = "root"
            ti.mode = 0o644
            tf.addfile(ti, io.BytesIO(data))

    gz_buf = io.BytesIO()
    with gzip.GzipFile(filename=f"{ARCHIVE_PREFIX}.tar", mode="wb", fileobj=gz_buf, mtime=0) as gz:
        gz.write(raw_tar.getvalue())
    tar_bytes = gz_buf.getvalue()
    TARBALL_PATH.write_bytes(tar_bytes)

    git_probe = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=REPO_ROOT, capture_output=True, text=True
    )
    head_sha = git_probe.stdout.strip() if git_probe.returncode == 0 else "standalone"

    receipt = {
        "schema": "lean4-apache2-export-receipt/1",
        "version": "1.0.0",
        "exported_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "git_base_commit": head_sha,
        "spdx_license": "Apache-2.0",
        "lean_toolchain": (CORE_DIR / "lean-toolchain").read_text(encoding="utf-8").strip(),
        "mathlib_rev": "0df444a360eaa60ab8c11dca51a86af692955474",
        "lean_library_modules": len(lean_lib_modules),
        "verification_scripts": script_files,
        "total_archived_files": len(entries),
        "docs_prose_excluded": True,
        "archive_filename": TARBALL_PATH.name,
        "archive_size_bytes": len(tar_bytes),
        "archive_sha256": sha256_bytes(tar_bytes),
        "license_sha256": sha256_bytes(APACHE_TXT.read_bytes()),
        "notice_sha256": sha256_bytes((HERE / "NOTICE").read_bytes()),
    }
    (HERE / "EXPORT_RECEIPT.json").write_text(
        json.dumps(receipt, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps({
        k: receipt[k]
        for k in [
            "spdx_license", "lean_library_modules", "total_archived_files",
            "archive_size_bytes", "archive_sha256",
        ]
    }, indent=2))


if __name__ == "__main__":
    main()
