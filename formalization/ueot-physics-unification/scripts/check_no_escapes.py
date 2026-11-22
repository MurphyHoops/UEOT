"""Comment-aware syntactic proof-escape scanner for UEOTPhysicsUnification."""
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1] / "UEOTPhysicsUnification"
FORBIDDEN = re.compile(r"(?m)^[ \t]*(?:axiom|opaque)\b|\b(?:sorry|admit|native_decide)\b")


def strip_lean_comments(src: str) -> str:
    out = []
    i, n, depth = 0, len(src), 0
    while i < n:
        if src.startswith("/-", i):
            depth += 1
            i += 2
        elif depth > 0 and src.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth > 0:
            if src[i] == "\n":
                out.append("\n")
            i += 1
        elif src.startswith("--", i):
            while i < n and src[i] != "\n":
                i += 1
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


def main() -> int:
    bad = []
    for path in sorted(ROOT.rglob("*.lean")):
        cleaned = strip_lean_comments(path.read_text(encoding="utf-8"))
        for m in FORBIDDEN.finditer(cleaned):
            line = cleaned.count("\n", 0, m.start()) + 1
            bad.append(f"{path.name}:{line}: forbidden token '{m.group(0).strip()}'")
    if bad:
        sys.stderr.write("\n".join(bad) + "\n")
        return 1
    print("PASS: zero syntactic proof escapes in UEOTPhysicsUnification")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
