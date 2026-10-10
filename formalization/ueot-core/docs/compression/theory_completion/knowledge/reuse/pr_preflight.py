#!/usr/bin/env python3
"""Mandatory-execution, non-authoritative FKRG Lean-PR reuse discovery gate.

Compare the exact base and candidate Git trees, NOT the immutable 633-file
snapshot (which must become stale when legitimate new proofs are added).
Reject structurally invalid inputs or clashing fully qualified declarations.
Suggest existing named proof candidates; never infer Lean type equality from
lexical matching and never prohibit independent generator derivations.
"""
import argparse
from collections import defaultdict
from difflib import SequenceMatcher
from hashlib import sha256
import io
import json
from pathlib import Path
import re
import subprocess
import sys
import tarfile

HERE = Path(__file__).resolve().parent
REPO_DEFAULT = HERE.parents[6]
sys.path.insert(0, str(HERE.parent))
from fkrg import no_lean_comments

LEAN_PREFIX = "formalization/ueot-core/UEOT/"
LEAN_ROOT = "formalization/ueot-core/UEOT.lean"
PUBLIC_KINDS = {"theorem", "lemma"}
SCHEMA = "FKRG_PR_DIFF_PREFLIGHT_V1"
# FKRG v1 lexical discovery is ASCII-oriented. Keep the historical
# extractor frozen, but use the PR-specific complete Unicode-qualified
# theorem name recognizer here, rather than accepting an ASCII prefix
# then silently dropping a Unicode name component.
# Modifiers apply independently to declarations and scope openers.
# In particular both public section and @[expose] public section create
# nested scope frames that must match their later end command.
PR_MODIFIER = (
    r"(?:@\[[^\]\n]*\]|public|nonrec|private|protected|"
    r"noncomputable|unsafe|irreducible|partial|scoped|local|meta)"
)
PR_SCOPE = re.compile(
    r"^\s*(?:" + PR_MODIFIER + r"\s+)*"
    r"(namespace|section|end)\b(?:\s+(\S+))?"
)
PUBLIC_DECL_START = re.compile(
    r"^\s*(?:" + PR_MODIFIER + r"\s+)*"
    r"(theorem|lemma)\b"
)
PR_UNICODE_SEGMENT = r"(?:«[^»\n]+»|[^\W\d][\w'!?]*)"
PR_UNICODE_NAME = re.compile(
    PR_UNICODE_SEGMENT + r"(?:\." + PR_UNICODE_SEGMENT + r")*"
)
# Lean scoped command syntax can locally alter declaration context:
# open Foo in theorem, include h in theorem, omit h in lemma, and similar
# wrappers. Consume the command prefix before the terminal public command
# but do not mutate the enclosing namespace stack.
SCOPED_IN_PUBLIC = re.compile(
    r"^\s*[^\n]+?\bin\s+"
    r"(?=(?:" + PR_MODIFIER + r"\s+)*(?:theorem|lemma)\b)"
)



def git(repo, *args):
    done = subprocess.run(["git", *args], cwd=repo, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, check=False)
    if done.returncode:
        raise RuntimeError("GIT_COMMAND_FAILED: " + " ".join(args[:3]) +
                           " " + done.stderr.decode("utf-8", "replace")[-500:])
    return done.stdout


def commit(repo, ref):
    if not ref or ref.startswith("-"):
        raise RuntimeError("INVALID_REVISION")
    sha = git(repo, "rev-parse", "--verify", f"{ref}^{{commit}}").decode().strip()
    if not re.fullmatch(r"[0-9a-f]{40}", sha):
        raise RuntimeError("UNRESOLVED_COMMIT")
    return sha


def corpus(repo, sha):
    # A candidate may delete the final directory member; do not pass a
    # nonexistent directory pathspec to git archive (which would abort).
    exists = git(repo, "ls-tree", "-r", "--name-only", sha, "--", LEAN_PREFIX[:-1])
    paths = [LEAN_ROOT]
    if any(line.startswith(LEAN_PREFIX) and line.endswith(".lean")
           for line in exists.decode().splitlines()):
        paths.append(LEAN_PREFIX[:-1])
    archive = git(repo, "archive", "--format=tar", sha, *paths)
    entries = {}
    with tarfile.open(fileobj=io.BytesIO(archive), mode="r:") as stream:
        for member in stream:
            if not member.isfile() or not member.name.endswith(".lean"):
                continue
            if member.name != LEAN_ROOT and not member.name.startswith(LEAN_PREFIX):
                raise RuntimeError("OUT_OF_SCOPE_ARCHIVE_PATH")
            content = stream.extractfile(member)
            if content is None:
                raise RuntimeError("CORRUPT_LEAN_ARCHIVE_MEMBER")
            entries[member.name] = content.read().decode("utf-8")
    if LEAN_ROOT not in entries or len(entries) < 1:
        raise RuntimeError("MISSING_UEOT_ROOT")
    return entries


def declarations(path, source):
    """Use the existing FKRG lexical declaration parser on exact Git bytes."""
    code = no_lean_comments(source).splitlines()
    ns, stack, found = "", [], []
    for line_number, line in enumerate(code, 1):
        scope = PR_SCOPE.match(line)
        if scope:
            op, arg = scope.groups()
            if op == "namespace":
                previous = ns
                target = arg or ""
                if target.startswith("_root_."):
                    ns = target[len("_root_."):]
                else:
                    ns = (ns + "." if ns else "") + target
                stack.append(("namespace", previous, target))
            elif op == "section":
                stack.append(("section", ns, arg or ""))
            elif op == "end":
                if not stack:
                    raise RuntimeError(f"UNBALANCED_SCOPE_END: {path}:{line_number}")
                if not arg:
                    _, ns, _ = stack.pop()
                else:
                    # Qualified section endings can collapse multiple nested
                    # named section frames: section A; section B; end A.B.
                    # Prefer the nearest matching section segment or full
                    # suffix, retaining the surrounding namespace.
                    match_depth = 0
                    names = []
                    for frame in reversed(stack):
                        if frame[0] != "section":
                            break
                        names.insert(0, frame[2])
                        if arg == frame[2] or arg == ".".join(names):
                            match_depth = len(names)
                            break
                    if match_depth:
                        for _ in range(match_depth):
                            _, ns, _ = stack.pop()
                        # No namespace suffix removal for a section-only end.
                        # Do not bypass the multi-command fail-closed check.
                        if re.search(r"\b(?:theorem|lemma)\b", line[scope.end():]):
                            raise RuntimeError(
                                f"UNSUPPORTED_MULTICOMMAND_LEAN_LINE: {path}:{line_number}"
                            )
                        continue
                    # A qualified Lean namespace end can consume multiple
                    # components (and parts of namespace A.B opened at once).
                    # Preserve any remaining outer component as a synthetic
                    # frame, so a later 'end A' still closes it correctly.
                    current = ns.split(".") if ns else []
                    closed = arg.removeprefix("_root_.").split(".")
                    if not closed or current[-len(closed):] != closed:
                        raise RuntimeError(
                            f"UNSUPPORTED_QUALIFIED_END: {path}:{line_number}: {arg}"
                        )
                    remain = ".".join(current[:-len(closed)])
                    while stack:
                        kind, before, _ = stack[-1]
                        # End section frames nested inside this namespace too.
                        if kind == "section":
                            stack.pop()
                            continue
                        if before == remain:
                            stack.pop()
                            break
                        if before.startswith(remain + ".") or remain == "":
                            stack.pop()
                            continue
                        if before == "" or remain.startswith(before + "."):
                            stack.pop()
                            stack.append(("namespace", before, remain))
                            break
                        raise RuntimeError(
                            f"INCONSISTENT_QUALIFIED_END: {path}:{line_number}"
                        )
                    ns = remain
            # Multiple commands can share a physical line in Lean. The
            # lexical scanner deliberately rejects rather than silently
            # pretending that any theorem after a scope header is absent.
            if re.search(r"\b(?:theorem|lemma)\b", line[scope.end():]):
                raise RuntimeError(
                    f"UNSUPPORTED_MULTICOMMAND_LEAN_LINE: {path}:{line_number}"
                )
        wrapper = SCOPED_IN_PUBLIC.match(line)
        scan_line = line[wrapper.end():] if wrapper else line
        start = PUBLIC_DECL_START.match(scan_line)
        if start is None:
            continue
        kind = start.group(1)
        tail = scan_line[start.end():].lstrip()
        detected = PR_UNICODE_NAME.match(tail)
        if not detected or (len(tail) > detected.end() and
                            not (tail[detected.end()].isspace() or
                                 tail[detected.end()] in "({[:")):
            raise RuntimeError(
                f"UNSUPPORTED_PUBLIC_LEAN_DECLARATION: {path}:{line_number}"
            )
        local_name = detected.group(0)
        # Reject adjacent commands on a single physical line even after
        # recognizing the first public declaration. A second lemma/theorem
        # could otherwise silently disappear from the incremental census.
        if re.search(r"\b(?:theorem|lemma)\b", tail[detected.end():]):
            raise RuntimeError(
                f"UNSUPPORTED_MULTICOMMAND_LEAN_LINE: {path}:{line_number}"
            )
        is_private = re.search(r"\bprivate\b", scan_line[:start.start(1)]) is not None
        if is_private:
            continue
        # Explicit root qualification bypasses ambient namespace context.
        name = (local_name[len("_root_."):] if local_name.startswith("_root_.")
                else (ns + "." if ns else "") + local_name)
        if not name or name.startswith("."):
            raise RuntimeError("INVALID_PARSED_DECLARATION")
        found.append({
            "symbol": name,
            "short_name": local_name.rsplit(".", 1)[-1],
            "kind": kind,
            "path": path,
            "line": line_number,
            "header_preview": " ".join(code[line_number - 1:line_number + 5])[:600],
            "origin": "VENDORED_ADAPTED_UPSTREAM" if "/ThirdParty/" in path else "UEOT_MAINTAINED",
        })
    return found


def name_score(a, b):
    if a == b:
        return 1.0
    aa = re.sub(r"(?<!^)(?=[A-Z])", "_", a).replace("-", "_").lower()
    bb = re.sub(r"(?<!^)(?=[A-Z])", "_", b).replace("-", "_").lower()
    tokens_a = set(filter(None, re.split(r"[^a-z0-9]+", aa)))
    tokens_b = set(filter(None, re.split(r"[^a-z0-9]+", bb)))
    jaccard = len(tokens_a & tokens_b) / len(tokens_a | tokens_b) if tokens_a | tokens_b else 0.0
    return max(jaccard, 0.65 * SequenceMatcher(None, aa, bb).ratio())


def candidate_hints(entry, baseline, limit=5):
    hints = []
    for old in baseline:
        if old["symbol"] == entry["symbol"]:
            continue
        score = name_score(entry["short_name"], old["short_name"])
        if score >= 0.48:
            hints.append({
                "symbol": old["symbol"],
                "path": old["path"],
                "similarity": round(score, 3),
                "epistemic_status": "NAME_SIMILARITY_ONLY_KERNEL_TYPE_NOT_CHECKED",
            })
    hints.sort(key=lambda row: (-row["similarity"], row["symbol"]))
    return hints[:limit]


def validate_unique(decls, where):
    seen = {}
    for row in decls:
        name = row["symbol"]
        if name in seen:
            raise RuntimeError(f"DUPLICATE_PUBLIC_LEXICAL_FQN_{where}: {name} in " +
                               f"{seen[name]} and {row['path']}")
        seen[name] = row["path"]
    return seen


def preflight(repo, base_ref, candidate_ref):
    repo = repo.resolve()
    base_sha = commit(repo, base_ref)
    head_sha = commit(repo, candidate_ref)
    base_sources = corpus(repo, base_sha)
    head_sources = corpus(repo, head_sha)
    baseline = [decl for path, source in base_sources.items()
                for decl in declarations(path, source)]
    current = [decl for path, source in head_sources.items()
               for decl in declarations(path, source)]
    prior_names = validate_unique(baseline, "BASE")
    current_names = validate_unique(current, "HEAD")
    changed = [path for path in sorted(set(base_sources) | set(head_sources))
               if base_sources.get(path) != head_sources.get(path)]
    added = [row for row in current if row["symbol"] not in prior_names]
    # All changes in Git objects are compared, not the working tree.
    result = {
        "schema": SCHEMA,
        "base_sha": base_sha, "candidate_sha": head_sha,
        "source_scope": "formalization/ueot-core/UEOT.lean plus UEOT/**/*.lean",
        "base_lean_module_count": len(base_sources),
        "candidate_lean_module_count": len(head_sources),
        "changed_lean_paths": changed,
        "base_public_lexical_theorem_count": len(baseline),
        "candidate_public_lexical_theorem_count": len(current),
        "new_public_source_theorem_count": len(added),
        "new_public_source_theorems": [{
            **row, "reuse_candidates": candidate_hints(row, baseline),
            "review_outcome": "TYPED_REUSE_REVIEW_REQUIRED",
        } for row in added],
        "counted_ledger_promotion": "NONE",
        "fuzzy_similarity_is_a_proof": False,
        "source_graph": "GIT_COMMIT_DIFF_LEXICAL_NOT_ELABORATED",
        "status": "PASS_NO_NEW_PUBLIC_THEOREMS" if not added else
                  "PASS_WITH_TYPED_REUSE_REVIEW_REQUIRED",
        "reason": "This gate is mandatory discovery and audit, not an "
                  "automatic proof equivalence or scientific promotion detector",
    }
    if not current_names or not prior_names:
        raise RuntimeError("EMPTY_BASE_OR_HEAD_THEOREM_CORPUS")
    return result


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo-root", type=Path, default=REPO_DEFAULT)
    ap.add_argument("--baseline-ref", required=True)
    ap.add_argument("--candidate-ref", required=True)
    ap.add_argument("--report", type=Path)
    ap.add_argument("--summary", type=Path)
    args = ap.parse_args()
    report = preflight(args.repo_root, args.baseline_ref, args.candidate_ref)
    raw = json.dumps(report, ensure_ascii=False, indent=2) + "\n"
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(raw)
    print(raw)
    if args.summary:
        lines = [
            "## FKRG new Lean proof preflight (non-promotional)",
            "",
            f"- Base commit: {report['base_sha']}",
            f"- Candidate commit: {report['candidate_sha']}",
            f"- Changed Lean modules: {len(report['changed_lean_paths'])}",
            f"- Newly discovered public theorem/lemma names: {report['new_public_source_theorem_count']}",
            f"- Status: {report['status']}",
            "- Suggested reuse hits are lexical hints only; no "
            "type or independent-generator claim is made.",
        ]
        for item in report["new_public_source_theorems"][:40]:
            hint = ", ".join(x["symbol"] for x in item["reuse_candidates"][:3]) or "none"
            lines.append(f"- {item['symbol']} ({item['path']}): inspect {hint}")
        args.summary.parent.mkdir(parents=True, exist_ok=True)
        with args.summary.open("a") as f:
            f.write("\n".join(lines) + "\n")


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, OSError, UnicodeError, tarfile.TarError,
            ValueError, KeyError) as error:
        print("FKRG_PR_PREFLIGHT_ERROR", str(error), file=sys.stderr)
        sys.exit(2)
