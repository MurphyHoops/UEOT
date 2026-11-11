#!/usr/bin/env python3
"""Audit explicitly selected UEOT bilingual InlineMath with Pandoc and a narrow exception ledger.

This is translation-fidelity checking, not a theorem prover.  No display-math,
PDF, or remote-publication acceptance is implied.  All math payloads are kept
literal: no global whitespace removal, command stripping, comma splitting,
variable deletion, equation rearrangement, or algebraic simplification occurs.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import difflib
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

READER = "markdown+tex_math_dollars"
EXPECTED_CHAPTERS = [f"ch-{i}" for i in range(67)] + [f"appendix-{c}" for c in "abcdef"]
ANCHOR = re.compile(r'<a id="(ch-\d+|appendix-[a-f])">(?:</a>)?')
SECTION = re.compile(r"^([0-9]+\.[0-9]+|[A-F]\.[0-9]+)(?:\s|[.：:])")

# Each occurrence is constrained by chapter, subsection, exact expression group,
# a specific paragraph marker, and an expected unique match.  The original
# inventory and consumed occurrence IDs remain in the JSON audit output.
RULES = [
    {
        "id": "IM-01", "kind": "enumeration_split", "chapter": "ch-2", "section": "2.2",
        "zh": ["A,B"], "en": ["A", "B"], "canonical": ["A", "B"],
        "marker_zh": "H-QSEL-1", "marker_en": "H-QSEL-1",
        "reason": "The same two channel carriers are separated by English prose; no generic comma normalization is allowed.",
    },
    {
        "id": "IM-02", "kind": "enumeration_split", "chapter": "ch-7", "section": "7.2",
        "zh": ["L_{ab},K_{ab}"], "en": ["L_{ab}", "K_{ab}"], "canonical": ["L_{ab}", "K_{ab}"],
        "marker_zh": "先后乘以", "marker_en": "multiplied successively",
        "reason": "The two successive block multipliers retain their order and indices; only the prose separator changes.",
    },
    {
        "id": "IM-03", "kind": "prose_identity_made_explicit", "chapter": "ch-8", "section": "8.1",
        "zh": ["X", r"\sum_{a,b}P_aXP_b"], "en": [r"X=\sum_{a,b}P_aXP_b"],
        "canonical": [r"X=\sum_{a,b}P_aXP_b"],
        "marker_zh": "展成", "marker_en": "Expand",
        "reason": "Chinese says to expand X into the displayed sum; English places that already asserted equality inside one math node. This is an explicit reviewed exception, not a general rule for inserting equals signs.",
    },
    {
        "id": "IM-04", "kind": "enumeration_split", "chapter": "ch-11", "section": "11.4",
        "zh": [r"(A-\langle A\rangle)\psi,(B-\langle B\rangle)\psi"],
        "en": [r"(A-\langle A\rangle)\psi", r"(B-\langle B\rangle)\psi"],
        "canonical": [r"(A-\langle A\rangle)\psi", r"(B-\langle B\rangle)\psi"],
        "marker_zh": "内积", "marker_en": "inner product",
        "reason": "The same two vectors in the Cauchy–Schwarz inner product are separated by English prose; operators and ordering are unchanged.",
    },
    {
        "id": "IM-05", "kind": "enumeration_split", "chapter": "ch-18", "section": "18.2",
        "zh": [r"|0\rangle,|1\rangle"], "en": [r"|0\rangle", r"|1\rangle"],
        "canonical": [r"|0\rangle", r"|1\rangle"],
        "marker_zh": "未来却分别为", "marker_en": "but futures",
        "reason": "The adjacent two future-state nodes are the two outcomes of the memory counterexample. The earlier re-preparation of |0> is not consumed.",
    },
    {
        "id": "IM-06", "kind": "enumeration_split", "chapter": "ch-22", "section": "22.2",
        "zh": [r"m>0,r=|\mathbf x|"], "en": ["m>0", r"r=|\mathbf x|"],
        "canonical": ["m>0", r"r=|\mathbf x|"],
        "marker_zh": "Wightman", "marker_en": "Wightman",
        "reason": "The positive-mass assumption and radial-coordinate definition are unchanged and separated by prose.",
    },
    {
        "id": "IM-07", "kind": "explicit_existing_variable_reference", "chapter": "ch-22", "section": "22.2",
        "zh": [], "en": ["x"], "canonical": [],
        "marker_zh": "P-QKG-02", "marker_en": "P-QKG-02",
        "support_context_zh": ["x^2<0", "x^0=0"],
        "support_context_en": ["x^2<0", "x^0=0"],
        "reason": "English explicitly names x as the argument carried by the Lorentz transformation. Chinese refers to the same spacelike argument implicitly; both retain x^2<0 and x^0=0. Only this one located mention is attributed as extra prose notation.",
    },
    {
        "id": "IM-08", "kind": "prose_identity_made_explicit", "chapter": "ch-26", "section": "26.1",
        "zh": [r"\phi_<+\phi_>"], "en": [r"\phi=\phi_<+\phi_>"],
        "canonical": [r"\phi=\phi_<+\phi_>"],
        "marker_zh": "将场分成", "marker_en": "split",
        "reason": "Chinese says to split the field into low and high modes. English names the existing field on the left of that same decomposition. No new operator or condition is asserted.",
    },
    {
        "id": "IM-09", "kind": "explicit_existing_variable_reference", "chapter": "ch-28", "section": "28.3",
        "zh": [], "en": ["y"], "canonical": [],
        "marker_zh": "K-QQED-01", "marker_en": "K-QQED-01",
        "support_context_zh": [r"\int_0^{1-z}dy"],
        "support_context_en": [r"\int_0^{1-z}dy"],
        "reason": "English names y when explaining the inner integral already present in the identical displayed integral. This does not add an integration, a bound, or a physical variable.",
    },
    {
        "id": "IM-10", "kind": "enumeration_split", "chapter": "ch-31", "section": "31.5",
        "zh": [r"3X_L^3,3N_cX_{Q\pm}^3"], "en": [r"3X_L^3", r"3N_cX_{Q\pm}^3"],
        "canonical": [r"3X_L^3", r"3N_cX_{Q\pm}^3"],
        "marker_zh": "P-QG3-04", "marker_en": "P-QG3-04",
        "reason": "The same two triplet anomaly contributions are listed separately; coefficients, powers, and signs remain literal.",
    },
]


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def json_hash(value) -> str:
    return sha256(json.dumps(value, ensure_ascii=False, separators=(",", ":")).encode("utf-8"))


def walk(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def ast_text(value) -> str:
    """Readable context only; never used as formula normalization."""
    if isinstance(value, dict):
        typ = value.get("t")
        if typ == "Str":
            return value["c"]
        if typ in ("Code", "Math"):
            return value["c"][1]
        if typ in ("Space", "SoftBreak", "LineBreak"):
            return " "
        if typ in ("RawInline", "RawBlock"):
            return ""
        return ast_text(value.get("c", []))
    if isinstance(value, list):
        return "".join(ast_text(child) for child in value)
    return ""


def extract(document, language):
    records, blocks, anchors = [], [], []
    chapter = section = "frontmatter"
    section_title = "frontmatter"
    chapter_counts = Counter()
    section_counts = Counter()
    header_one_count = 0

    def add_math(node, block_index, context, current_chapter, current_section, title):
        if node.get("t") != "Math" or node["c"][0].get("t") != "InlineMath":
            return
        chapter_counts[current_chapter] += 1
        section_counts[(current_chapter, current_section)] += 1
        records.append({
            "occurrence_id": f"{language}-inline-{len(records) + 1:04d}",
            "chapter": current_chapter, "section": current_section,
            "section_title": title, "block_index": block_index,
            "chapter_ordinal": chapter_counts[current_chapter],
            "section_ordinal": section_counts[(current_chapter, current_section)],
            "text": node["c"][1], "context_sha256": sha256(context.encode("utf-8")),
        })

    metadata_context = ast_text(document.get("meta", {}))
    for node in walk(document.get("meta", {})):
        add_math(node, "metadata", metadata_context, "metadata", "metadata", "metadata")
    for index, block in enumerate(document["blocks"]):
        for node in walk(block):
            if node.get("t") in ("RawInline", "RawBlock"):
                match = ANCHOR.fullmatch(node["c"][1])
                if match:
                    chapter = section = match.group(1)
                    section_title = chapter
                    anchors.append(chapter)
        if block["t"] == "Header":
            title = ast_text(block["c"][2])
            if block["c"][0] == 1:
                header_one_count += 1
                section = chapter
                section_title = title
            else:
                match = SECTION.match(title)
                if match:
                    section, section_title = match.group(1), title
        context = ast_text(block)
        blocks.append({"block_index": index, "chapter": chapter, "section": section, "context": context})
        for node in walk(block):
            add_math(node, index, context, chapter, section, section_title)
    return {"records": records, "blocks": blocks, "anchors": anchors,
            "header_one_count": header_one_count, "api_version": document["pandoc-api-version"]}


def locate_rule(data, rule, language):
    """Locate exactly one paragraph and contiguous InlineMath group, or fail."""
    marker = rule[f"marker_{language}"]
    candidate_blocks = [b for b in data["blocks"]
                        if b["chapter"] == rule["chapter"] and b["section"] == rule["section"]
                        and marker in b["context"]]
    pattern = rule[language]
    matches = []
    for block in candidate_blocks:
        if any(part not in block["context"] for part in rule.get(f"support_context_{language}", [])):
            continue
        occurrences = [r for r in data["records"] if r["block_index"] == block["block_index"]]
        if not pattern:
            matches.append((block, []))
            continue
        for start in range(len(occurrences) - len(pattern) + 1):
            group = occurrences[start:start + len(pattern)]
            if [r["text"] for r in group] == pattern:
                matches.append((block, group))
    if len(matches) != 1:
        raise ValueError(f"{rule['id']} {language}: expected exactly one located group, found {len(matches)}")
    block, group = matches[0]
    return {"block_index": block["block_index"], "context": block["context"],
            "context_sha256": sha256(block["context"].encode("utf-8")),
            "occurrence_ids": [r["occurrence_id"] for r in group], "original_texts": pattern}


def counter_difference(left, right):
    return [{"text": text, "count": count} for text, count in sorted((left - right).items())]


def comparison(left, right):
    lseq, rseq = [r["text"] for r in left], [r["text"] for r in right]
    lc, rc = Counter(lseq), Counter(rseq)
    return {"zh_count": len(lseq), "en_count": len(rseq),
            "sequence_equal": lseq == rseq, "counter_equal": lc == rc,
            "zh_only": counter_difference(lc, rc), "en_only": counter_difference(rc, lc)}


def apply_rules(data, located, language):
    starts, consumed = {}, set()
    for entry in located:
        ids = entry[language]["occurrence_ids"]
        if not ids:
            continue
        if consumed.intersection(ids):
            raise ValueError(f"Overlapping exception occurrences in {entry['id']} {language}")
        consumed.update(ids)
        starts[ids[0]] = entry
    normalized = []
    for row in data["records"]:
        oid = row["occurrence_id"]
        if oid in starts:
            entry = starts[oid]
            for text in entry["canonical"]:
                normalized.append({"text": text, "chapter": row["chapter"], "section": row["section"],
                                   "origin_occurrence_ids": entry[language]["occurrence_ids"],
                                   "exception_id": entry["id"]})
        elif oid not in consumed:
            normalized.append({"text": row["text"], "chapter": row["chapter"], "section": row["section"],
                               "origin_occurrence_ids": [oid], "exception_id": None})
    return normalized


def ordered_keys(rows):
    return list(dict.fromkeys((r["chapter"], r["section"]) for r in rows))


def audit(args):
    result = {
        "schema": "UEOT-PHYSICS-INLINE-MATH-FIDELITY-2",
        "checkpoint": "Bilingual 3.7, Chapters 0–66 and Appendices A–F; exact input identity is recorded below and optionally checked against caller-supplied freeze hashes",
        "scope": "Pandoc InlineMath translation fidelity for the explicitly selected bilingual manuscripts; not formula truth or display/PDF/CI verification",
        "reader": READER, "status": "FAIL", "errors": [], "unexplained_differences": [],
        "normalization_policy": {
            "baseline": "Exact literal Pandoc InlineMath payload; even internal whitespace is retained.",
            "counter_unit": "Every chapter/appendix, with an additional subsection-level Counter check.",
            "permitted_changes": "Only the ten exact located groups listed in the exception ledger; every original occurrence is retained in the inventory.",
            "prohibited": ["generic whitespace or TeX-command stripping", "generic comma splitting", "generic deletion of variables", "algebraic simplification", "cross-chapter or cross-section cancellation"],
        },
    }
    checker = Path(__file__).resolve()
    result["checker"] = {"path": str(checker), "sha256": sha256(checker.read_bytes())}
    book_dir = Path(args.book_dir).resolve()
    source_paths = {"zh": book_dir / "UEOT_PHYSICS.md", "en": book_dir / "UEOT_PHYSICS.en.md"}
    expected_hashes = {"zh": args.expected_zh_sha256, "en": args.expected_en_sha256}
    result["identity_policy"] = "Always record the exact input hashes. If caller-supplied freeze hashes are present, require both exact matches before comparing any math. No manuscript revision inherits a prior PASS."
    result["sources"] = {}
    for lang, path in source_paths.items():
        content = path.read_bytes()
        actual_hash = sha256(content)
        expected_hash = expected_hashes[lang]
        result["sources"][lang] = {"path": str(path), "bytes": len(content), "sha256": actual_hash,
                                    "expected_sha256": expected_hash, "hash_matches": None if expected_hash is None else actual_hash == expected_hash}
        if expected_hash is not None and actual_hash != expected_hash:
            result["errors"].append(f"Caller-specified frozen {lang} manuscript hash mismatch; refusing to attach this run to that identity.")
    if result["errors"]:
        return result
    result["pandoc_version"] = subprocess.run([args.pandoc, "--version"], check=True, capture_output=True, text=True).stdout.splitlines()[0]
    parsed = {}
    for lang, path in source_paths.items():
        process = subprocess.run([args.pandoc, str(path), "-f", READER, "-t", "json"],
                                 check=True, capture_output=True, text=True, encoding="utf-8")
        parsed[lang] = extract(json.loads(process.stdout), lang)
        if parsed[lang]["anchors"] != EXPECTED_CHAPTERS:
            result["errors"].append(f"{lang}: chapter/appendix anchor sequence is incomplete, duplicated, or reordered")
        if parsed[lang]["header_one_count"] != len(EXPECTED_CHAPTERS):
            result["errors"].append(f"{lang}: expected {len(EXPECTED_CHAPTERS)} first-level chapter/appendix headings")
    result["coverage"] = {lang: {"chapter_anchors": data["anchors"], "level_one_headers": data["header_one_count"],
                                       "pandoc_api_version": data["api_version"],
                                       "frontmatter_inline_math": sum(r["chapter"] == "frontmatter" for r in data["records"]),
                                       "metadata_inline_math": sum(r["chapter"] == "metadata" for r in data["records"])}
                          for lang, data in parsed.items()}
    located = []
    for rule in RULES:
        entry = {key: value for key, value in rule.items() if key not in ("zh", "en")}
        try:
            entry["zh"] = locate_rule(parsed["zh"], rule, "zh")
            entry["en"] = locate_rule(parsed["en"], rule, "en")
        except ValueError as error:
            result["errors"].append(str(error))
            continue
        entry["status"] = "EXACT_LOCATED_EXCEPTION"
        located.append(entry)
    result["exceptions"] = located
    result["inventory"] = {lang: data["records"] for lang, data in parsed.items()}
    if len(located) != len(RULES):
        return result
    normalized = {lang: apply_rules(data, located, lang) for lang, data in parsed.items()}
    chapters, order_variations, sections = [], [], []
    unit_order = ["metadata", "frontmatter"] + EXPECTED_CHAPTERS
    for chapter in unit_order:
        raw = {lang: [r for r in data["records"] if r["chapter"] == chapter] for lang, data in parsed.items()}
        norm = {lang: [r for r in rows if r["chapter"] == chapter] for lang, rows in normalized.items()}
        rc, nc = comparison(raw["zh"], raw["en"]), comparison(norm["zh"], norm["en"])
        row = {"chapter": chapter, "raw": rc, "after_explicit_attribution": nc,
               "exception_ids": [r["id"] for r in located if r["chapter"] == chapter]}
        chapters.append(row)
        if not nc["counter_equal"]:
            result["unexplained_differences"].append({"level": "chapter", "chapter": chapter, "difference": nc})
    for chapter, section in ordered_keys(normalized["zh"] + normalized["en"]):
        rows = {lang: [r for r in values if r["chapter"] == chapter and r["section"] == section]
                for lang, values in normalized.items()}
        comp = comparison(rows["zh"], rows["en"])
        sections.append({"chapter": chapter, "section": section, **comp})
        if not comp["counter_equal"]:
            result["unexplained_differences"].append({"level": "section", "chapter": chapter, "section": section, "difference": comp})
        elif not comp["sequence_equal"]:
            zseq, eseq = [r["text"] for r in rows["zh"]], [r["text"] for r in rows["en"]]
            edits = [{"tag": tag, "zh": zseq[a:b], "en": eseq[c:d]}
                     for tag, a, b, c, d in difflib.SequenceMatcher(a=zseq, b=eseq, autojunk=False).get_opcodes()
                     if tag != "equal"]
            order_variations.append({"chapter": chapter, "section": section,
                                     "counter_equal": True, "zh_sequence_sha256": json_hash(zseq),
                                     "en_sequence_sha256": json_hash(eseq), "edit_script": edits})
    result["chapters"] = chapters
    result["sections"] = sections
    result["order_variations"] = order_variations
    result["summary"] = {
        "raw_inline_math_zh": len(parsed["zh"]["records"]), "raw_inline_math_en": len(parsed["en"]["records"]),
        "attributed_inline_tokens_zh": len(normalized["zh"]), "attributed_inline_tokens_en": len(normalized["en"]),
        "chapters_and_appendices": len(EXPECTED_CHAPTERS),
        "chapters_raw_counter_equal": sum(r["raw"]["counter_equal"] for r in chapters if r["chapter"] in EXPECTED_CHAPTERS),
        "chapters_raw_sequence_equal": sum(r["raw"]["sequence_equal"] for r in chapters if r["chapter"] in EXPECTED_CHAPTERS),
        "chapters_attributed_counter_equal": sum(r["after_explicit_attribution"]["counter_equal"] for r in chapters if r["chapter"] in EXPECTED_CHAPTERS),
        "exception_groups": len(located), "enumeration_splits": sum(r["kind"] == "enumeration_split" for r in located),
        "prose_identities_made_explicit": sum(r["kind"] == "prose_identity_made_explicit" for r in located),
        "existing_variable_references": sum(r["kind"] == "explicit_existing_variable_reference" for r in located),
        "sections_with_inline_math": len(sections), "sections_with_order_variation": len(order_variations),
        "unexplained_differences": len(result["unexplained_differences"]),
    }
    if not result["errors"] and not result["unexplained_differences"]:
        result["status"] = "PASS"
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--book-dir", required=True, help="Directory containing the explicitly selected UEOT_PHYSICS.md and UEOT_PHYSICS.en.md")
    parser.add_argument("--expected-zh-sha256", help="Optional frozen Chinese identity; supply together with --expected-en-sha256")
    parser.add_argument("--expected-en-sha256", help="Optional frozen English identity; supply together with --expected-zh-sha256")
    parser.add_argument("--pandoc", default="pandoc")
    parser.add_argument("--output", required=True, help="Destination JSON audit receipt")
    args = parser.parse_args()
    if bool(args.expected_zh_sha256) != bool(args.expected_en_sha256):
        parser.error("Supply both expected manuscript hashes, or neither; exact observed hashes are always recorded.")
    for expected in (args.expected_zh_sha256, args.expected_en_sha256):
        if expected is not None and re.fullmatch(r"[0-9a-f]{64}", expected) is None:
            parser.error("Expected SHA256 values must be 64 lowercase hexadecimal characters.")
    try:
        result = audit(args)
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        result = {"schema": "UEOT-PHYSICS-INLINE-MATH-FIDELITY-2", "status": "ERROR",
                  "scope": "InlineMath translation fidelity only", "errors": [str(error)]}
    output = Path(args.output).resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": result["status"], "output": str(output),
                      "summary": result.get("summary", {}), "errors": result.get("errors", []),
                      "unexplained_differences": result.get("unexplained_differences", [])}, ensure_ascii=False))
    return 0 if result["status"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
