#!/usr/bin/env python3
"""Read-only external source audit; no Lean, GI adapter, Runtime, or native request."""
import datetime
import hashlib
import json
import pathlib
import re
import sys

EXPECTED_FILES = 1048
PREFIX = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure."
TARGETS = {PREFIX + s for s in (
    "CoreRegenerativeSource", "CoreRegenerativeRepair", "CoreRegenerativeOneStep",
    "FiniteSourceGrowthControl", "SourceCohortFeedback", "CoreRegenerativeFeedback",
    "CoreRegenerativeFeedbackBoundary", "CoreRegenerativePopulation", "CoreRegenerativeQuotient",
    "CoreRegenerativeFormation", "CoreRegenerativeLineage", "CoreRegenerativeControlPopulation",
    "CoreTheoryClosure")}
ROOTS = ["UEOT", "UEOT.V3", "UEOT.V3.Compression", "UEOT.V3.Compression.TheoryCompletion"]
MODULE = r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*"
FLAGS = ("sorry", "admit", "axiom", "unsafe", "opaque", "implemented_by", "sorryAx", "native_decide")
TOKEN = re.compile(r"(?<![\w'])" + "(" + "|".join(FLAGS) + r")(?![\w'])")


def mask(text):
    """Preserve offsets/newlines while masking nested comments and string/char literals."""
    out, i, n = [], 0, len(text)
    def blank(a, b):
        return "".join("\n" if c == "\n" else " " for c in text[a:b])
    while i < n:
        j = i
        if text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
        elif text.startswith("/-", i):
            j, depth = i + 2, 1
            while j < n and depth:
                if text.startswith("/-", j): depth, j = depth + 1, j + 2
                elif text.startswith("-/", j): depth, j = depth - 1, j + 2
                else: j += 1
            if depth: raise ValueError("unterminated nested comment")
        elif text[i] == "«":
            j = text.find("»", i + 1)
            if j < 0: raise ValueError("unterminated quoted identifier")
            out.append(text[i:j + 1]); i = j + 1; continue
        else:
            raw = re.match(r'r(#[#]*)?"', text[i:]) if text[i] == "r" and (i == 0 or not (text[i-1].isalnum() or text[i-1] in "_'")) else None
            char = re.match(r"'(?:\\.|[^\\'\n])'", text[i:]) if text[i] == "'" and (i == 0 or not (text[i-1].isalnum() or text[i-1] in "_'")) else None
            if raw:
                if i and text[i-1] == "!": raise ValueError("interpolated raw strings require explicit parser support")
                close = '"' + (raw.group(1) or "")
                end = text.find(close, i + raw.end())
                if end < 0: raise ValueError("unterminated raw string")
                j = end + len(close)
            elif char: j = i + char.end()
            elif text[i] == '"':
                if i and text[i-1] == "!": raise ValueError("interpolated strings require explicit parser support")
                j = i + 1
                while j < n:
                    if text[j] == "\\": j += 2
                    elif text[j] == '"': j += 1; break
                    else: j += 1
                else: raise ValueError("unterminated string")
            else:
                out.append(text[i]); i += 1; continue
        out.append(blank(i, j)); i = j
    return "".join(out)


def imports(code):
    found, header = [], True
    for line, text in enumerate(code.splitlines(), 1):
        text = text.strip()
        if not text: continue
        if text == "prelude" and header and not found: continue
        if text.startswith("import ") or text.startswith("import\t"):
            if not header: raise ValueError(f"import outside header at line {line}")
            names = text.split()[1:]
            if len(names) != 1 or not re.fullmatch(MODULE, names[0]):
                raise ValueError(f"unsupported import syntax at line {line}: {text}")
            found.extend(names)
        elif re.search(r"\b(import|prelude)\b", text) or (
                header and re.match(r"(?:(?:public|private|meta)\s+)?module\b", text)):
            raise ValueError(f"unsupported module/import syntax at line {line}: {text}")
        else: header = False
    return found


def inspect(root):
    sample = 'import UEOT.Foo /- outer /- sorry -/ axiom -/\n-- admit\ndef x := "opaque -- \\""\nby native_decide\n'
    assert imports(mask(sample)) == ["UEOT.Foo"]
    assert [m.group() for m in TOKEN.finditer(mask(sample))] == ["native_decide"]
    actual_tactic = "import UEOT.Foo\ntheorem source_test :\n  (Real.exp (-a*s) * -a) • f s = 0 := by module\n"
    assert imports(mask(actual_tactic)) == ["UEOT.Foo"]
    assert imports(mask("import UEOT.Foo\nexample : x = x := by module\n")) == ["UEOT.Foo"]
    for bad in ("module", "public module", "public import UEOT.Foo", "import UEOT.«Foo»", "import\nUEOT.Foo", "import all UEOT.Foo"):
        try: imports(mask(bad))
        except ValueError: pass
        else: raise AssertionError("unsupported-import guard failed")
    if not (root / "UEOT").is_dir(): raise ValueError("missing UEOT production directory")
    if any(p.is_symlink() for p in (root / "UEOT").rglob("*")): raise ValueError("symlink in production tree")
    paths = [root / "UEOT.lean", *sorted((root / "UEOT").rglob("*.lean"))]
    graph, files, findings = {}, [], {word: [] for word in FLAGS}
    for path in paths:
        if path.is_symlink() or not path.is_file(): raise ValueError(f"not a regular source: {path}")
        rel = path.relative_to(root).as_posix(); name = rel[:-5].replace("/", ".")
        if not re.fullmatch(MODULE, name): raise ValueError(f"unsupported module path: {rel}")
        before = path.stat(); data = path.read_bytes(); after = path.stat()
        if (before.st_ino, before.st_size, before.st_mtime_ns) != (after.st_ino, after.st_size, after.st_mtime_ns):
            raise ValueError(f"source changed while reading: {rel}")
        try: code = mask(data.decode("utf-8-sig")); graph[name] = imports(code)
        except ValueError as exc: raise ValueError(f"{rel}: {exc}") from exc
        files.append({"module": name, "path": rel, "bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()})
        for match in TOKEN.finditer(code):
            findings[match.group()].append({"module": name, "path": rel, "line": code.count("\n", 0, match.start()) + 1})
    internal = lambda name: name == "UEOT" or name.startswith("UEOT.")
    missing = [{"importer": m, "missing": dep} for m, deps in graph.items() for dep in deps if internal(dep) and dep not in graph]
    def reachable(start):
        seen, todo = set(), [start]
        while todo:
            m = todo.pop()
            if m in seen or m not in graph: continue
            seen.add(m); todo.extend(dep for dep in graph[m] if internal(dep))
        return seen
    colors, stack, cycles = {}, [], []
    def visit(m):
        colors[m] = 1; stack.append(m)
        for dep in graph[m]:
            if dep not in graph: continue
            if colors.get(dep) == 1: cycles.append(stack[stack.index(dep):] + [dep])
            elif not colors.get(dep): visit(dep)
        stack.pop(); colors[m] = 2
    for m in graph:
        if not colors.get(m): visit(m)
    coverage = {r: {"reachable_count": len(reachable(r)), "target_count": len(TARGETS & reachable(r)), "missing_targets": sorted(TARGETS - reachable(r))} for r in ROOTS}
    forbidden = sum(len(findings[t]) for t in FLAGS if t != "native_decide")
    checks = {"expected_file_count": len(files) == EXPECTED_FILES, "all_roots_present": all(r in graph for r in ROOTS), "all_targets_present": TARGETS <= graph.keys(), "UEOT_reaches_every_production_module": len(reachable("UEOT")) == len(graph), "required_public_target_coverage": all(not coverage[r]["missing_targets"] for r in (ROOTS[0], *ROOTS[2:])), "no_missing_internal_imports": not missing, "no_cycles": not cycles, "no_forbidden_tokens": forbidden == 0, "recorded_native_decide_count_unchanged": len(findings["native_decide"]) == 2}
    digest = hashlib.sha256(json.dumps(files, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    return {"schema": "UEOT/CORE_PUBLIC_STATIC_AUDIT/V1", "status": "PASS" if all(checks.values()) else "FAIL", "scope": "STATIC_SOURCE_ONLY_NOT_COMPILATION", "root": str(root), "expected_production_files": EXPECTED_FILES, "production_files": len(files), "production_bytes": sum(f["bytes"] for f in files), "source_manifest_sha256": digest, "checks": checks, "public_root_coverage": coverage, "unreachable_from_UEOT": sorted(graph.keys() - reachable("UEOT")), "missing_internal_imports": missing, "cycles": cycles, "findings": findings, "files": files, "interpretation": "UEOT.V3 is a parallel public subset. Source tokens exclude nested comments and strings; no old native request or long enumeration was executed."}


if __name__ == "__main__":
    try:
        if len(sys.argv) != 2: raise ValueError("usage: inspect_public_source.py FORMALIZATION_ROOT")
        result = inspect(pathlib.Path(sys.argv[1]).resolve(strict=True))
    except Exception as exc:
        result = {"schema": "UEOT/CORE_PUBLIC_STATIC_AUDIT/V1", "status": "FAIL", "error": type(exc).__name__ + ": " + str(exc)}
    result["observed_at"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    print(json.dumps(result, ensure_ascii=False, indent=2))
    sys.exit(0 if result["status"] == "PASS" else 1)
