#!/usr/bin/env python3
"""Deterministically package the audited pure-kernel Lean 4 proof code from
formalization/ueot-core/ into an Apache-2.0 Zenodo-ready software archive,
excluding .lake/, build caches, and non-code CC BY 4.0 documentation under docs/.
"""
from __future__ import annotations

from pathlib import Path
import argparse
import datetime
import gzip
import hashlib
import io
import json
import re
import subprocess
import tarfile

HERE = Path(__file__).resolve().parent
REPO_ROOT = HERE.parents[2]
CORE_DIR = REPO_ROOT / "formalization" / "ueot-core"
APACHE_TXT = REPO_ROOT / "LICENSES" / "Apache-2.0.txt"
DIST_DIR = HERE / "dist"

CONCEPT_DOI = "10.5281/zenodo.24433584"
V1_DOI = "10.5281/zenodo.24433585"
SEMVER_RE = re.compile(r"^\d+\.\d+\.\d+(?:[-+][0-9A-Za-z.-]+)?$")
DATE_RE = re.compile(r"^\d{4}-\d{2}-\d{2}$")


def digest_bytes(data: bytes, alg: str) -> str:
    """Return hexadecimal digest for `data` under hashlib algorithm `alg`."""
    return hashlib.new(alg, data).hexdigest()


def normalize_version(raw: str) -> str:
    """Strip common tag prefixes (`lean4-export-v`, `v`) and validate SemVer."""
    version = raw.strip()
    if version.startswith("lean4-export-v"):
        version = version[len("lean4-export-v"):]
    elif version.startswith("v"):
        version = version[1:]
    if not SEMVER_RE.match(version):
        raise ValueError(f"Invalid semantic version {raw!r}; expected X.Y.Z")
    return version


def render_export_readme(version: str, toolchain: str) -> str:
    """Render top-level README.md embedded inside the exported archive."""
    return f"""# Pure-Kernel Lean 4 Formalization Archive (v{version})

**License:** Apache License, Version 2.0 (`Apache-2.0` — see `LICENSE` and `NOTICE`)  
**Toolchain:** `{toolchain}`  
**Mathlib Pin:** `0df444a360eaa60ab8c11dca51a86af692955474` (`lake-manifest.json`)  
**Zenodo Concept DOI (all versions):** `{CONCEPT_DOI}`

## Contents

- `UEOT.lean` & `UEOT/` — 1,051 Lean 4 library modules (`0` `sorryAx`, `0` `Lean.ofReduceBool` / `native_decide`)
- `scripts/ExhaustiveAxiomAudit.lean` — environment-wide kernel axiom verifier confirming transitive dependencies lie strictly inside `{{propext, Classical.choice, Quot.sound}}`
- `lakefile.lean`, `lake-manifest.json`, `lean-toolchain` — pinned reproducible Lake configuration
- `LICENSE`, `NOTICE`, `CITATION.cff`, `.zenodo.json` — Apache-2.0 license, Section 4(d) upstream attributions, and citation metadata

## Reproducible Build & Kernel Axiom Audit

```bash
lake exe cache get
lake build UEOT
lake env lean --run scripts/ExhaustiveAxiomAudit.lean
```
"""


def render_zenodo_json_bytes(version: str, pub_date: str) -> bytes:
    """Return `.zenodo.json` payload with parameterized version and date."""
    meta = json.loads((HERE / ".zenodo.json").read_text(encoding="utf-8"))
    meta["version"] = version
    meta["publication_date"] = pub_date
    return (json.dumps(meta, ensure_ascii=False, indent=2) + "\n").encode("utf-8")


def render_citation_cff_bytes(version: str, pub_date: str) -> bytes:
    """Return `CITATION.cff` payload synchronized to `version` and `pub_date`."""
    cff = (HERE / "CITATION.cff").read_text(encoding="utf-8")
    cff = re.sub(r'^version:\s*"[^"]*"', f'version: "{version}"', cff, flags=re.M)
    cff = re.sub(r'^date-released:\s*"[^"]*"', f'date-released: "{pub_date}"', cff, flags=re.M)
    if version != "1.0.0":
        # Future versions not yet minted cite the permanent lineage concept DOI.
        cff = cff.replace(V1_DOI, CONCEPT_DOI)
    return cff.encode("utf-8")


def collect_files(version: str, pub_date: str, toolchain: str):
    """Collect sorted `(relative_path, data_bytes)` entries for the tarball."""
    entries = []

    # 1. License & attribution metadata at archive root
    entries.append(("LICENSE", APACHE_TXT.read_bytes()))
    entries.append(("NOTICE", (HERE / "NOTICE").read_bytes()))
    entries.append(("CITATION.cff", render_citation_cff_bytes(version, pub_date)))
    entries.append((".zenodo.json", render_zenodo_json_bytes(version, pub_date)))
    entries.append(("README.md", render_export_readme(version, toolchain).encode("utf-8")))

    # 2. Pinned Lake build configuration & root library entry
    for cfg in ["lean-toolchain", "lakefile.lean", "lake-manifest.json", "UEOT.lean"]:
        entries.append((cfg, (CORE_DIR / cfg).read_bytes()))

    # 3. All Lean 4 modules + preserved ThirdParty upstream notices under UEOT/
    for p in sorted((CORE_DIR / "UEOT").rglob("*")):
        if p.is_file() and "__pycache__" not in p.parts and p.name != ".DS_Store":
            entries.append((str(p.relative_to(CORE_DIR)), p.read_bytes()))

    # 4. Pure-kernel verification scripts under scripts/
    for p in sorted((CORE_DIR / "scripts").rglob("*")):
        if p.is_file() and "__pycache__" not in p.parts and p.name != ".DS_Store":
            entries.append((str(p.relative_to(CORE_DIR)), p.read_bytes()))

    return sorted(entries, key=lambda kv: kv[0])


def build_archive(
    version: str | None = None,
    publication_date: str | None = None,
    output_receipt: Path | str | None = None,
    write_tracked_receipt: bool = False,
) -> dict:
    """Build deterministic Apache-2.0 archive for `version` and return provenance dict."""
    DIST_DIR.mkdir(exist_ok=True)
    default_meta = json.loads((HERE / ".zenodo.json").read_text(encoding="utf-8"))
    target_version = normalize_version(version if version is not None else default_meta["version"])

    if publication_date is not None:
        pub_date = publication_date.strip()
        if not DATE_RE.match(pub_date):
            raise ValueError(f"Invalid --publication-date {publication_date!r}; expected YYYY-MM-DD")
    elif target_version == default_meta["version"]:
        pub_date = default_meta["publication_date"]
    else:
        pub_date = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%d")

    toolchain = (CORE_DIR / "lean-toolchain").read_text(encoding="utf-8").strip()
    entries = collect_files(target_version, pub_date, toolchain)
    lean_lib_modules = [
        rel for rel, _ in entries
        if (rel == "UEOT.lean" or rel.startswith("UEOT/")) and rel.endswith(".lean")
    ]
    script_files = [rel for rel, _ in entries if rel.startswith("scripts/")]

    archive_prefix = f"lean4-pure-kernel-formalization-v{target_version}"
    tarball_path = DIST_DIR / f"{archive_prefix}.tar.gz"

    # Deterministic reproducible tar.gz (mtime=0, uid=0, gid=0)
    raw_tar = io.BytesIO()
    with tarfile.open(fileobj=raw_tar, mode="w") as tf:
        for rel, data in entries:
            ti = tarfile.TarInfo(name=f"{archive_prefix}/{rel}")
            ti.size = len(data)
            ti.mtime = 0
            ti.uid = 0
            ti.gid = 0
            ti.uname = "root"
            ti.gname = "root"
            ti.mode = 0o644
            tf.addfile(ti, io.BytesIO(data))

    gz_buf = io.BytesIO()
    with gzip.GzipFile(filename=f"{archive_prefix}.tar", mode="wb", fileobj=gz_buf, mtime=0) as gz:
        gz.write(raw_tar.getvalue())
    tar_bytes = gz_buf.getvalue()
    tarball_path.write_bytes(tar_bytes)

    git_probe = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=REPO_ROOT, capture_output=True, text=True
    )
    head_sha = git_probe.stdout.strip() if git_probe.returncode == 0 else "standalone"

    receipt = {
        "schema": "lean4-apache2-export-receipt/1",
        "version": target_version,
        "publication_date": pub_date,
        "exported_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "git_base_commit": head_sha,
        "spdx_license": "Apache-2.0",
        "lean_toolchain": toolchain,
        "mathlib_rev": "0df444a360eaa60ab8c11dca51a86af692955474",
        "lean_library_modules": len(lean_lib_modules),
        "verification_scripts": script_files,
        "total_archived_files": len(entries),
        "docs_prose_excluded": True,
        "archive_filename": tarball_path.name,
        "archive_size_bytes": len(tar_bytes),
        "archive_sha256": digest_bytes(tar_bytes, "sha256"),
        "archive_md5": digest_bytes(tar_bytes, "md5"),
        "license_sha256": digest_bytes(APACHE_TXT.read_bytes(), "sha256"),
        "notice_sha256": digest_bytes((HERE / "NOTICE").read_bytes(), "sha256"),
    }

    if output_receipt is not None:
        receipt_path = Path(output_receipt)
    elif write_tracked_receipt:
        receipt_path = HERE / "EXPORT_RECEIPT.json"
    else:
        receipt_path = DIST_DIR / f"EXPORT_RECEIPT-v{target_version}.json"
    receipt_path.parent.mkdir(parents=True, exist_ok=True)
    receipt_path.write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    return {
        **receipt,
        "tarball_path": str(tarball_path),
        "receipt_path": str(receipt_path),
    }


def parse_args(argv=None):
    parser = argparse.ArgumentParser(description="Build deterministic Apache-2.0 Lean 4 export tarball.")
    parser.add_argument(
        "--version",
        default=None,
        help="Target semantic version (accepts v1.1.0 or lean4-export-v1.1.0; defaults to .zenodo.json version).",
    )
    parser.add_argument(
        "--publication-date",
        default=None,
        help="Publication date YYYY-MM-DD (defaults to .zenodo.json date for v1.0.0, else UTC today).",
    )
    parser.add_argument(
        "--output-receipt",
        default=None,
        help="Explicit JSON path for the export receipt (defaults to dist/EXPORT_RECEIPT-v<version>.json).",
    )
    parser.add_argument(
        "--write-tracked-receipt",
        action="store_true",
        help="Also overwrite tracked EXPORT_RECEIPT.json in the export package directory.",
    )
    return parser.parse_args(argv)


def main(argv=None):
    args = parse_args(argv)
    result = build_archive(
        version=args.version,
        publication_date=args.publication_date,
        output_receipt=args.output_receipt,
        write_tracked_receipt=args.write_tracked_receipt,
    )
    print(json.dumps({
        k: result[k]
        for k in [
            "version", "publication_date", "spdx_license",
            "lean_library_modules", "total_archived_files",
            "archive_filename", "archive_size_bytes",
            "archive_sha256", "archive_md5", "receipt_path",
        ]
    }, indent=2))


if __name__ == "__main__":
    main()
