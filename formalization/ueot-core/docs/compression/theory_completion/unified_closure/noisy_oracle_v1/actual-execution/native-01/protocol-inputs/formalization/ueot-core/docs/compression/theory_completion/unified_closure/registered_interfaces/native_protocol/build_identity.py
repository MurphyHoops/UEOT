#!/usr/bin/env python3
"""Read-only, deterministic UEOT Core build-input identity.

Use actual toolchain executables, not elan proxies. This module runs only
``lean --version``, ``lake --version`` and read-only Git commands. It never
invokes Lake configuration, environment setup, update, build or cache commands.
The returned object has no timestamp or repository HEAD, so documentation-only
commits do not invalidate identical proof inputs. A caller must save the first
identity with its actual build receipt and compare it before/after execution.
"""
from __future__ import annotations

import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

CORE_PREFIX = "formalization/ueot-core/"
TOOLCHAIN = "leanprover/lean4:v4.33.1"
LEAN_VERSION = "4.33.1"
ENVIRONMENT_SHA256 = {
    "lean-toolchain": "3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71",
    "lakefile.lean": "7f083f896c58e521092721637c067a9bd892c4b2d5185bdd1b99fd5391f25986",
    "lake-manifest.json": "84542dad0540d0595b67e5b83d6b2d7bf96b4ca4aee9051f557ed73b0cb012d1",
}
DEPENDENCY_REVISIONS = {
    "mathlib": "0df444a360eaa60ab8c11dca51a86af692955474",
    "plausible": "b7eb3304aeae834b12dda98993a37f6a41f6f0bb",
    "LeanSearchClient": "5f4d51b81cbd3f6b32b156bfad9056621a040404",
    "importGraph": "16f02aa7642864af59f1ff0e384a015994db9118",
    "proofwidgets": "4be2e3d5087eeb272cf5a8853b8f9dd025ef5957",
    "aesop": "3448c0bcc5ce01b2d1546e483ec3620e32df3d0e",
    "Qq": "92c15be17b7caf78c2ad767ec40f89052d908d81",
    "batteries": "4488d40d070b9700d4d5a6aa342f0d40c31b2a2d",
    "Cli": "6130a47896ce867c6a4a55373441e59e565bad0f",
}


def _sha(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def _run(command: list[str], cwd: Path, timeout: float) -> str:
    env = os.environ.copy()
    env["GIT_OPTIONAL_LOCKS"] = "0"
    env["LC_ALL"] = "C"
    process = subprocess.run(command, cwd=cwd, env=env, capture_output=True,
                             text=True, timeout=timeout, check=False)
    if process.returncode:
        raise RuntimeError("READ_ONLY_IDENTITY_COMMAND_FAILED: " +
                           json.dumps(command) + "\n" + process.stderr[-3000:])
    return process.stdout.strip()


def _executable(value: str | Path) -> Path:
    name = str(value)
    found = shutil.which(name)
    if not found:
        raise RuntimeError("IDENTITY_EXECUTABLE_UNAVAILABLE: " + name)
    path = Path(found).resolve(strict=True)
    if path.name == "elan":
        raise RuntimeError("USE_ACTUAL_TOOLCHAIN_BINARY_NOT_ELAN_PROXY: " + name)
    return path


def _source_identity(repo: Path, core: Path) -> dict:
    root = core / "UEOT.lean"
    if not root.is_file() or not (core / "UEOT").is_dir():
        raise RuntimeError("INCOMPLETE_UEOT_SOURCE_ROOT")
    paths = [root, *(core / "UEOT").rglob("*.lean")]
    mapping = {p.relative_to(core).with_suffix("").as_posix().replace("/", "."): p
               for p in paths if p.is_file()}
    if len(mapping) != len([p for p in paths if p.is_file()]):
        raise RuntimeError("DUPLICATE_UEOT_MODULE_NAME")
    digest = sha256()
    records = []
    # Exactly knowledge/fkrg.py:fingerprint: module, NUL, bytes, NUL.
    for module, path in sorted(mapping.items()):
        data = path.read_bytes()
        digest.update(module.encode())
        digest.update(b"\0")
        digest.update(data)
        digest.update(b"\0")
        records.append({"module": module, "path": path.relative_to(repo).as_posix(),
                        "bytes": len(data), "sha256": sha256(data).hexdigest()})
    return {"module_count": len(records), "source_tree_sha256": digest.hexdigest(),
            "source_files": records}


def capture(repo: str | Path, *, lake: str | Path, lean: str | Path,
            expected: dict | None = None, expected_module_count: int | None = None,
            timeout: float = 30) -> dict:
    """Verify pinned inputs; optionally reject any difference from a saved identity."""
    repo = Path(repo).resolve(strict=True)
    core = repo / CORE_PREFIX
    source = _source_identity(repo, core)
    if expected_module_count is not None and source["module_count"] != expected_module_count:
        raise RuntimeError("UNEXPECTED_UEOT_MODULE_COUNT: " + str(source["module_count"]))
    environment_files = []
    for name, pinned in sorted(ENVIRONMENT_SHA256.items()):
        path = core / name
        actual = _sha(path)
        if actual != pinned:
            raise RuntimeError("PINNED_BUILD_ENVIRONMENT_DRIFT: " + name)
        environment_files.append({"path": CORE_PREFIX + name, "sha256": actual})
    if (core / "lean-toolchain").read_text().strip() != TOOLCHAIN:
        raise RuntimeError("PINNED_TOOLCHAIN_TEXT_DRIFT")
    manifest = json.loads((core / "lake-manifest.json").read_text())
    packages = manifest.get("packages", [])
    names = [p.get("name") for p in packages]
    if len(names) != len(set(names)) or set(names) != set(DEPENDENCY_REVISIONS):
        raise RuntimeError("EXPECTED_EXACT_NINE_DEPENDENCIES")
    dependencies = []
    for package in sorted(packages, key=lambda p: p["name"]):
        name = package["name"]
        pinned = DEPENDENCY_REVISIONS[name]
        if package.get("type") != "git" or package.get("rev") != pinned:
            raise RuntimeError("MANIFEST_DEPENDENCY_PIN_DRIFT: " + name)
        location = (core / manifest["packagesDir"] / name).resolve(strict=True)
        git = ["git", "--no-optional-locks", "-c", "core.fsmonitor=false", "-C", str(location)]
        toplevel = Path(_run(git + ["rev-parse", "--show-toplevel"], core, timeout)).resolve()
        if toplevel != location:
            raise RuntimeError("DEPENDENCY_IS_NOT_ITS_OWN_CHECKOUT: " + name)
        head = _run(git + ["rev-parse", "--verify", "HEAD^{commit}"], core, timeout)
        if head != pinned:
            raise RuntimeError("ACTUAL_DEPENDENCY_HEAD_DRIFT: " + name)
        dirty = _run(git + ["status", "--porcelain=v1", "--untracked-files=normal",
                            "--ignore-submodules=none"], core, timeout)
        if dirty:
            raise RuntimeError("ACTUAL_DEPENDENCY_NOT_CLEAN: " + name + "\n" + dirty[:3000])
        dependencies.append({"name": name, "manifest_rev": pinned, "actual_head": head,
                             "clean": True, "status_porcelain": ""})
    lean_binary, lake_binary = _executable(lean), _executable(lake)
    if lean_binary.parent != lake_binary.parent:
        raise RuntimeError("LEAN_AND_LAKE_ARE_NOT_FROM_THE_SAME_BIN_DIRECTORY")
    tools = {}
    for name, path in (("lean", lean_binary), ("lake", lake_binary)):
        before = _sha(path)
        version = _run([str(path), "--version"], core, timeout)
        pattern = (r"\bversion\s+4\.33\.1(?=[,\s)]|$)" if name == "lean" else
                   r"\bLean(?:\s+version)?\s+4\.33\.1(?=[,\s)]|$)")
        if not re.search(pattern, version):
            raise RuntimeError("ACTUAL_" + name.upper() + "_VERSION_MISMATCH: " + version)
        if _sha(path) != before:
            raise RuntimeError("EXECUTABLE_CHANGED_DURING_IDENTITY_CAPTURE: " + name)
        tools[name] = {"executable": str(path), "sha256": before, "version": version}
    result = {
        "schema": "UEOT_BUILD_IDENTITY_V1", "source_scope": "UEOT.lean plus UEOT/**/*.lean",
        **source, "toolchain": TOOLCHAIN, "environment_files": environment_files,
        "runtime_tools": tools, "dependencies": dependencies,
        "import_environment": {key: os.environ.get(key, "") for key in
            ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT", "ELAN_TOOLCHAIN")},
    }
    # Detect edits while the multi-part identity was being collected.
    if _source_identity(repo, core) != source:
        raise RuntimeError("UEOT_SOURCE_CHANGED_DURING_IDENTITY_CAPTURE")
    for name, pinned in ENVIRONMENT_SHA256.items():
        if _sha(core / name) != pinned:
            raise RuntimeError("BUILD_ENVIRONMENT_CHANGED_DURING_IDENTITY_CAPTURE: " + name)
    if expected is not None and result != expected:
        changed = sorted(key for key in set(result) | set(expected)
                         if result.get(key) != expected.get(key))
        raise RuntimeError("BUILD_IDENTITY_DIFFERS_FROM_SAVED_RECEIPT: " + ", ".join(changed))
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--lake", required=True)
    parser.add_argument("--lean", required=True)
    parser.add_argument("--expected", type=Path, help="Saved identity JSON to compare exactly")
    parser.add_argument("--expected-module-count", type=int)
    args = parser.parse_args()
    expected = json.loads(args.expected.read_text()) if args.expected else None
    print(json.dumps(capture(args.repo, lake=args.lake, lean=args.lean, expected=expected,
                             expected_module_count=args.expected_module_count),
                     ensure_ascii=False, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
