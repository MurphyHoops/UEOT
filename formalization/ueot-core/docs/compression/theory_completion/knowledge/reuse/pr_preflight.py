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
# Attribute terminators are NOT raw closing brackets inside Lean escaped
# identifiers or quoted attribute arguments. Keep a single shared token
# grammar for modifier, privacy and standalone-attribute recognition.
PR_ATTRIBUTE_TOKEN = (
    r'@\[(?:«[^»]*»|"(?:\\.|[^"\\\n])*"|[^\]\n])*\]'
)
PR_MODIFIER = (
    r"(?:" + PR_ATTRIBUTE_TOKEN + r"|public|nonrec|private|protected|"
    r"noncomputable|unsafe|irreducible|partial|scoped|local|meta)"
)
PR_SCOPE = re.compile(
    r"^\s*(?:" + PR_MODIFIER + r"\s+)*"
    r"(namespace|section|end)\b"
)
PUBLIC_DECL_START = re.compile(
    r"^\s*(?:" + PR_MODIFIER + r"\s+)*"
    r"(theorem|lemma)\b"
)
PR_UNICODE_SEGMENT = r"(?:«[^»]+»|[^\W\d][\w'!?]*)"
PR_UNICODE_NAME = re.compile(
    PR_UNICODE_SEGMENT + r"(?:\." + PR_UNICODE_SEGMENT + r")*"
)
PR_LEVEL_PARAMS = re.compile(
    r"^\.\{\s*" + PR_UNICODE_NAME.pattern +
    r"(?:\s*,\s*" + PR_UNICODE_NAME.pattern + r")*\s*\}"
)
# Lean scoped command syntax can locally alter declaration context:
# open Foo in theorem, include h in theorem, omit h in lemma, and similar
# wrappers. Consume the command prefix before the terminal public command
# but do not mutate the enclosing namespace stack.
SCOPED_IN_PUBLIC = re.compile(
    r"^\s*[^\n]+?\bin\s+"
    r"(?=(?:" + PR_MODIFIER + r"\s+)*(?:theorem|lemma)\b)"
)

# Escaped Lean identifiers can be reserved words (e.g., def «theorem»).
# The fallback is a command-token guard, not an identifier substring search.
ESCAPED_LEAN_NAME = re.compile(r"«[^»]*»")
MUTUAL_START = re.compile(r"^\s*mutual\b")


def contains_command_token(line):
    return bool(re.search(r"\b(?:theorem|lemma|namespace|section|end|mutual)\b",
                          ESCAPED_LEAN_NAME.sub("ESCAPED_NAME", line)))


def has_private_modifier(prefix):
    # An attribute payload is NOT a modifier token. In particular,
    # @[deprecated «private» (...)] does not create a private theorem.
    without_attributes = re.sub(PR_ATTRIBUTE_TOKEN, " ", prefix)
    return "private" in without_attributes.split()


# Char literals inside a syntax quotation must not alter parentheses depth.
# Recognize single Unicode chars and Lean-style escaped character forms;
# a bare apostrophe in an identifier is not a char literal.
LEAN_CHAR_LITERAL = re.compile(
    r"'(?:[^'\\\n]|\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|u\{[0-9a-fA-F]+\}|.))'"
)


def mask_syntax_quotations(lines, path):
    # Lean command quotations are syntax DATA, never executable commands.
    # Scan across physical lines, masking all quotation contents while
    # retaining the full line count and external command prefixes.
    output = []
    depth = 0
    quoted_string = False
    escape = False
    for number, line in enumerate(lines, 1):
        result = list(line)
        i = 0
        while i < len(line):
            if depth == 0 and line[i:i+2] == chr(96) + "(":
                result[i] = result[i+1] = " "
                i += 2
                depth = 1
                continue
            if depth > 0:
                ch = line[i]
                result[i] = " "
                if quoted_string:
                    if escape:
                        escape = False
                    elif ch == "\\":
                        escape = True
                    elif ch == '"':
                        quoted_string = False
                elif ch == '"':
                    quoted_string = True
                elif ch == "'":
                    char_match = LEAN_CHAR_LITERAL.match(line, i)
                    if char_match:
                        for j in range(i, char_match.end()):
                            result[j] = " "
                        i = char_match.end()
                        continue
                elif ch == "(":
                    depth += 1
                elif ch == ")":
                    depth -= 1
            i += 1
        output.append("".join(result))
    if depth:
        raise RuntimeError(f"UNTERMINATED_SYNTAX_QUOTATION: {path}")
    return output


def qualified_parts(name):
    tokens = list(re.finditer(PR_UNICODE_SEGMENT, name))
    if not tokens or ".".join(x.group(0) for x in tokens) != name:
        raise RuntimeError("UNSUPPORTED_QUALIFIED_SCOPE_NAME: " + name)
    return [x.group(0) for x in tokens]



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
            # A Git symlink is not a regular tar file, but checkout may
            # resolve it into compilable Lean code. Never omit such a module
            # from the public-declaration census without telling the caller.
            if member.issym() or member.islnk():
                raise RuntimeError(
                    f"UNSUPPORTED_LEAN_SOURCE_SYMLINK: {member.name}"
                )
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



def comment_safe_escaped_names(source):
    """Mask escaped identifier interiors before handling comments or quotations.

    Lean permits comment syntax, quotation markers and quotes as literal
    identifier contents. Preserve all codepoint positions and newlines;
    restore only if the name delimiters survive the two masking passes.
    """
    masked = list(source)
    spans = []
    i = 0
    depth = 0
    line_comment = False
    string = False
    escape = False
    while i < len(source):
        ch = source[i]
        pair = source[i:i + 2]
        if line_comment:
            if ch == "\n":
                line_comment = False
            i += 1
            continue
        if depth:
            if pair == "/-":
                depth += 1
                i += 2
            elif pair == "-/":
                depth -= 1
                i += 2
            else:
                i += 1
            continue
        if string:
            if escape:
                escape = False
            elif ch == "\\":
                escape = True
            elif ch == '"':
                string = False
            i += 1
            continue
        character = LEAN_CHAR_LITERAL.match(source, i)
        if character is not None:
            i = character.end()
            continue
        if pair == "/-":
            depth = 1
            i += 2
            continue
        if pair == "--":
            line_comment = True
            i += 2
            continue
        if ch == '"':
            string = True
            i += 1
            continue
        if ch == "«":
            finish = source.find("»", i + 1)
            if finish < 0:
                i += 1
                continue
            spans.append((i, finish, source[i + 1:finish]))
            for pos in range(i + 1, finish):
                if source[pos] != "\n":
                    masked[pos] = "x"
            i = finish + 1
            continue
        i += 1
    return "".join(masked), spans


def lexical_code_preserving_escaped_names(source, path):
    masked, spans = comment_safe_escaped_names(source)
    text = "\n".join(mask_syntax_quotations(
        no_lean_comments(masked).split("\n"), path
    ))
    if len(text) != len(source):
        raise RuntimeError(f"ESCAPED_NAME_MASK_POSITION_DRIFT: {path}")
    code = list(text)
    for begin, finish, original in spans:
        if code[begin] == "«" and code[finish] == "»":
            for offset, ch in enumerate(original, begin + 1):
                code[offset] = ch
    return "".join(code).splitlines()


def logical_escaped_identifier_lines(lines, path):
    """Join physical lines only while inside a Lean «...» name component.

    Retain the original start line for error locations and source previews.
    Splitting physical lines before parsing must not reject valid newlines
    INSIDE an escaped declaration identifier or silently lose that theorem.
    """
    buffered = []
    active = False
    first = 1
    for number, line in enumerate(lines, 1):
        if not buffered:
            first = number
        buffered.append(line)
        i = 0
        while i < len(line):
            # Character literals such as '«' and '»' are values, not
            # escaped identifier delimiters. Skip the complete literal.
            char_literal = LEAN_CHAR_LITERAL.match(line, i)
            if char_literal:
                i = char_literal.end()
                continue
            char = line[i]
            if char == "«":
                # Additional « within «...» is literal identifier content.
                if not active:
                    active = True
            elif char == "»" and active:
                active = False
            i += 1
        if not active:
            yield first, "\n".join(buffered)
            buffered = []
    if buffered:
        raise RuntimeError(f"UNTERMINATED_ESCAPED_IDENTIFIER: {path}:{first}")


def logical_multiline_command_headers(lines, path):
    """Join valid indented command-header continuations without losing lines.

    Lean requires an indented continuation for a command name on the next
    physical line (unindented `namespace\nFoo` is rejected by Lean).
    `section`/`end` names are optional and joined only when the next
    indented line is solely an identifier, not an executable command.
    """
    rows = list(logical_escaped_identifier_lines(lines, path))
    commands = {"theorem", "lemma", "namespace", "section", "end", "mutual"}
    i = 0
    while i < len(rows):
        first_line, text = rows[i]
        raw = text
        scoped = PR_SCOPE.match(text)
        wrapper = SCOPED_IN_PUBLIC.match(text)
        bare = text[wrapper.end():] if wrapper else text
        declared = PUBLIC_DECL_START.match(bare)
        directive = scoped.group(1) if scoped else (declared.group(1) if declared else None)
        header_end = scoped.end() if scoped else (
            (wrapper.end() if wrapper else 0) + declared.end() if declared else 0
        )
        if directive in {"namespace", "section", "end", "theorem", "lemma"} and not text[header_end:].strip():
            j = i + 1
            while j < len(rows) and not rows[j][1].strip():
                j += 1
            if j < len(rows):
                continuation = rows[j][1]
                tail = continuation.lstrip()
                name = PR_UNICODE_NAME.match(tail)
                indented = bool(continuation[:len(continuation)-len(tail)])
                head_is_keyword = (name is not None and name.group(0) in commands)
                is_sole_name = name is not None and not tail[name.end():].strip()
                if directive in {"namespace", "theorem", "lemma"}:
                    if not indented or not name or head_is_keyword:
                        raise RuntimeError(
                            f"UNSUPPORTED_REQUIRED_MULTILINE_NAME: {path}:{first_line}"
                        )
                    text += " " + tail
                    i = j
                elif indented and is_sole_name and not head_is_keyword:
                    text += " " + tail
                    i = j
            elif directive in {"namespace", "theorem", "lemma"}:
                raise RuntimeError(
                    f"UNTERMINATED_REQUIRED_DECLARATION_NAME: {path}:{first_line}"
                )
        yield first_line, text
        i += 1



def attribute_bracket_delta(line):
    """Count actual attribute brackets, ignoring escaped-name/string content."""
    line = re.sub(r"«[^»]*»", "", line)
    line = re.sub(r'"(?:\\.|[^"\\])*"', "", line)
    return line.count("[") - line.count("]")



def normalize_inline_attribute_brackets(line):
    """Replace complete @[...nested...] modifiers with @[] before regex parsing.

    Preserve everything outside the attribute, including standalone privacy
    modifiers and the actual public command. Only complete same-line tokens
    are rewritten; incomplete multiline tokens retain existing fail-closed
    multiline attribute handling. Strings and Lean escaped names may contain
    any bracket characters without changing nesting depth.
    """
    out = []
    i = 0
    string = False
    escape = False
    escaped_name = False
    while i < len(line):
        ch = line[i]
        if string:
            out.append(ch)
            if escape:
                escape = False
            elif ch == "\\":
                escape = True
            elif ch == '"':
                string = False
            i += 1
            continue
        if escaped_name:
            out.append(ch)
            if ch == "»":
                escaped_name = False
            i += 1
            continue
        if ch == '"':
            string = True
            out.append(ch)
            i += 1
            continue
        if ch == "«":
            escaped_name = True
            out.append(ch)
            i += 1
            continue
        if line.startswith("@[", i):
            j = i + 2
            depth = 1
            in_str = False
            esc = False
            name = False
            while j < len(line) and depth:
                x = line[j]
                if in_str:
                    if esc:
                        esc = False
                    elif x == "\\":
                        esc = True
                    elif x == '"':
                        in_str = False
                elif name:
                    if x == "»":
                        name = False
                elif x == '"':
                    in_str = True
                elif x == "«":
                    name = True
                elif x == "[":
                    depth += 1
                elif x == "]":
                    depth -= 1
                j += 1
            if depth == 0:
                out.append("@[]")
                i = j
                continue
            # This is a multiline attribute. Retain the original prefix so
            # the pre-existing depth tracking can join or reject correctly.
            out.append(line[i:])
            break
        out.append(ch)
        i += 1
    return "".join(out)


def logical_universe_parameter_lines(rows, path):
    """Join line-wrapped .{universe identifiers} immediately after declId."""
    items = list(rows)
    i = 0
    while i < len(items):
        first_line, text = items[i]
        wrapper = SCOPED_IN_PUBLIC.match(text)
        candidate = text[wrapper.end():] if wrapper else text
        decl = PUBLIC_DECL_START.match(candidate)
        if decl:
            tail = candidate[decl.end():].lstrip()
            name = PR_UNICODE_NAME.match(tail)
            if name and tail[name.end():].startswith(".{"):
                suffix = tail[name.end():]
                if PR_LEVEL_PARAMS.match(suffix) is None:
                    j = i + 1
                    while j < len(items):
                        text += "\n" + items[j][1]
                        suffix += "\n" + items[j][1]
                        if PR_LEVEL_PARAMS.match(suffix):
                            i = j
                            break
                        j += 1
                    else:
                        raise RuntimeError(
                            f"UNSUPPORTED_UNIVERSE_PARAMETER_LIST: {path}:{first_line}: unterminated or invalid"
                        )
        yield first_line, text
        i += 1

def declarations(path, source):
    """Use the existing FKRG lexical declaration parser on exact Git bytes."""
    code = lexical_code_preserving_escaped_names(source, path)
    ns, stack, found = "", [], []
    pending_modifiers = []
    multiline_attribute_depth = 0
    # Lean permits a declaration modifier on its own physical line:
    # "private\ntheorem foo" must not create a publicly searchable foo.
    standalone_modifier = re.compile(
        r"^\s*(private|public|protected|noncomputable|nonrec|"
        r"unsafe|meta|scoped|local)\s*$"
    )
    standalone_attribute = re.compile(r"^\s*(" + PR_ATTRIBUTE_TOKEN + r")\s*$")
    rows = logical_multiline_command_headers(code, path)
    for line_number, line in logical_universe_parameter_lines(rows, path):
        if not line.strip():
            continue
        if multiline_attribute_depth:
            multiline_attribute_depth += attribute_bracket_delta(line)
            if multiline_attribute_depth < 0:
                raise RuntimeError(
                    f"MALFORMED_MULTILINE_ATTRIBUTE: {path}:{line_number}"
                )
            if multiline_attribute_depth == 0 and not line.rstrip().endswith("]"):
                # A command after a closing attribute on its last physical
                # line is not supported by this lexical scanner.
                raise RuntimeError(
                    f"UNSUPPORTED_MULTILINE_ATTRIBUTE_TAIL: {path}:{line_number}"
                )
            continue
        # A multiline attribute can appear between a standalone private
        # modifier and its actual public-command syntax. Keep privacy until
        # the complete attribute is consumed, not just its first line.
        if line.lstrip().startswith("@[") and attribute_bracket_delta(line) > 0:
            multiline_attribute_depth = attribute_bracket_delta(line)
            pending_modifiers.append("@[]")
            continue
        line = normalize_inline_attribute_brackets(line)
        attribute = standalone_attribute.match(line)
        if attribute:
            # Attributes may occupy their own line between a privacy
            # modifier and the declaration; preserve the modifier chain.
            pending_modifiers.append(attribute.group(1))
            continue
        modifier = standalone_modifier.match(line)
        if modifier:
            pending_modifiers.append(modifier.group(1))
            continue
        if pending_modifiers:
            line = " ".join(pending_modifiers) + " " + line.lstrip()
            pending_modifiers.clear()
        if MUTUAL_START.match(line):
            stack.append(("mutual", ns, ""))
            if contains_command_token(line[MUTUAL_START.match(line).end():]):
                raise RuntimeError(
                    f"UNSUPPORTED_MULTICOMMAND_LEAN_LINE: {path}:{line_number}"
                )
            continue
        scope = PR_SCOPE.match(line)
        if scope:
            op = scope.group(1)
            rest = line[scope.end():]
            stripped = rest.lstrip()
            parsed_arg = PR_UNICODE_NAME.match(stripped)
            arg = parsed_arg.group(0) if parsed_arg else None
            after_header = stripped[parsed_arg.end():] if parsed_arg else stripped
            if contains_command_token(after_header):
                raise RuntimeError(
                    f"UNSUPPORTED_MULTICOMMAND_LEAN_LINE: {path}:{line_number}"
                )
            if after_header.strip():
                raise RuntimeError(
                    f"UNSUPPORTED_SCOPE_COMMAND_TAIL: {path}:{line_number}"
                )
            if op == "namespace":
                previous = ns
                target = arg or ""
                # Namespace scope headers treat _root_ as a literal
                # component (validated in pinned Lean), unlike root-qualified
                # declaration identifiers.
                ns = (ns + "." if ns else "") + target
                is_private_ns = has_private_modifier(line[:scope.start(1)])
                stack.append(("private_namespace" if is_private_ns else "namespace",
                              previous, target))
            elif op == "section":
                is_private_section = has_private_modifier(line[:scope.start(1)])
                stack.append(("private_section" if is_private_section else "section",
                              ns, arg or ""))
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
                        if frame[0] not in ("section", "private_section"):
                            break
                        # An anonymous section prevents combining named
                        # frames across it (validated by actual Lean).
                        names.insert(0, frame[2])
                        if arg == frame[2] or arg == ".".join(names):
                            match_depth = len(names)
                            break
                    if match_depth:
                        for _ in range(match_depth):
                            _, ns, _ = stack.pop()
                        # No namespace suffix removal for a section-only end.
                        # Do not bypass the multi-command fail-closed check.
                        if contains_command_token(line[scope.end():]):
                            raise RuntimeError(
                                f"UNSUPPORTED_MULTICOMMAND_LEAN_LINE: {path}:{line_number}"
                            )
                        continue
                    # A qualified Lean namespace end can consume multiple
                    # components (and parts of namespace A.B opened at once).
                    # Preserve any remaining outer component as a synthetic
                    # frame, so a later 'end A' still closes it correctly.
                    current = qualified_parts(ns) if ns else []
                    closed = qualified_parts(arg.removeprefix("_root_."))
                    if not closed or current[-len(closed):] != closed:
                        raise RuntimeError(
                            f"UNSUPPORTED_QUALIFIED_END: {path}:{line_number}: {arg}"
                        )
                    remain = ".".join(current[:-len(closed)])
                    while stack:
                        kind, before, _ = stack[-1]
                        # End section frames nested inside this namespace too.
                        if kind in ("section", "private_section"):
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
            if contains_command_token(line[scope.end():]):
                raise RuntimeError(
                    f"UNSUPPORTED_MULTICOMMAND_LEAN_LINE: {path}:{line_number}"
                )
        if scope:
            continue
        wrapper = SCOPED_IN_PUBLIC.match(line)
        scan_line = line[wrapper.end():] if wrapper else line
        start = PUBLIC_DECL_START.match(scan_line)
        if start is None:
            # Lean command delimiters are not guaranteed to coincide with
            # physical newline boundaries. Any otherwise-unparsed theorem
            # token is a potential nested/adjacent public command: reject
            # instead of claiming that no new theorem was introduced.
            if contains_command_token(line):
                raise RuntimeError(
                    f"UNSUPPORTED_MULTICOMMAND_LEAN_LINE: {path}:{line_number}"
                )
            continue
        kind = start.group(1)
        tail = scan_line[start.end():].lstrip()
        detected = PR_UNICODE_NAME.match(tail)
        if detected is None:
            raise RuntimeError(
                f"UNSUPPORTED_PUBLIC_LEAN_DECLARATION: {path}:{line_number}"
            )
        local_name = detected.group(0)
        # Lean declId permits an explicit universe-parameter suffix after
        # the name: theorem fresh.{u} and theorem fresh.{u,v}. These
        # parameters are NOT part of the fully qualified theorem symbol.
        suffix = tail[detected.end():]
        if suffix.startswith(".{"):
            level_params = PR_LEVEL_PARAMS.match(suffix)
            if level_params is None:
                raise RuntimeError(
                    f"UNSUPPORTED_UNIVERSE_PARAMETER_LIST: {path}:{line_number}"
                )
            suffix = suffix[level_params.end():]
        if suffix and not (suffix[0].isspace() or suffix[0] in "({[:"):
            raise RuntimeError(
                f"UNSUPPORTED_PUBLIC_LEAN_DECLARATION: {path}:{line_number}"
            )
        # Reject adjacent commands on a single physical line even after
        # recognizing the first public declaration. A second lemma/theorem
        # could otherwise silently disappear from the incremental census.
        if contains_command_token(suffix):
            raise RuntimeError(
                f"UNSUPPORTED_MULTICOMMAND_LEAN_LINE: {path}:{line_number}"
            )
        is_private = has_private_modifier(scan_line[:start.start(1)])
        if is_private or any(
            kind in ("private_section", "private_namespace") for kind, _, _ in stack
        ):
            continue
        # Explicit root qualification bypasses ambient namespace context.
        name = (local_name[len("_root_."):] if local_name.startswith("_root_.")
                else (ns + "." if ns else "") + local_name)
        if not name or name.startswith("."):
            raise RuntimeError("INVALID_PARSED_DECLARATION")
        found.append({
            "symbol": name,
            # Dots enclosed by «...» are part of ONE Lean identifier,
            # not separators of its qualified name.
            "short_name": qualified_parts(local_name)[-1],
            "kind": kind,
            "path": path,
            "line": line_number,
            "header_preview": " ".join(code[line_number - 1:line_number + 5])[:600],
            "origin": "VENDORED_ADAPTED_UPSTREAM" if "/ThirdParty/" in path else "UEOT_MAINTAINED",
        })
    if multiline_attribute_depth:
        raise RuntimeError(f"UNTERMINATED_MULTILINE_ATTRIBUTE: {path}")
    if pending_modifiers:
        raise RuntimeError(f"UNTERMINATED_STANDALONE_MODIFIER: {path}")
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
