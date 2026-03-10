#!/usr/bin/env python3
"""Build a deterministic shared-memory registry for UEOT agents.

This registry is the file-first fallback when OpenClaw memory indexing is
unavailable or remote embedding quota is exhausted. It gives every agent the
same canonical map of constitutional files, accepted memos, resolutions, and
book dossiers without requiring any local model installation.
"""

from __future__ import annotations

from datetime import datetime, timezone
from pathlib import Path
import re


REPO_ROOT = Path(__file__).resolve().parents[3]
OUTPUT_PATH = REPO_ROOT / "memory" / "shared" / "UEOT_MEMORY_REGISTRY.yaml"


def parse_frontmatter(text: str) -> tuple[dict[str, object], str]:
    if not text.startswith("---\n"):
        return {}, text
    lines = text.splitlines()
    end = None
    for idx in range(1, len(lines)):
        if lines[idx].strip() == "---":
            end = idx
            break
    if end is None:
        return {}, text

    meta: dict[str, object] = {}
    list_key: str | None = None

    for raw in lines[1:end]:
        if not raw.strip():
            continue
        if raw.startswith("  - ") and list_key:
            value = raw[4:].strip()
            current = meta.setdefault(list_key, [])
            if isinstance(current, list):
                current.append(value)
            continue
        if raw.startswith("  "):
            continue
        if ":" not in raw:
            continue
        key, value = raw.split(":", 1)
        key = key.strip()
        value = value.strip()
        list_key = None
        if value:
            meta[key] = value
        else:
            meta[key] = []
            list_key = key

    body = "\n".join(lines[end + 1 :]).lstrip()
    return meta, body


def find_title(body: str, fallback: str) -> str:
    for line in body.splitlines():
        stripped = line.strip()
        if stripped.startswith("# "):
            return stripped[2:].strip()
    return fallback


def rel(path: Path) -> str:
    return path.relative_to(REPO_ROOT).as_posix()


def chapter_sort_key(path: Path) -> tuple[int, str]:
    match = re.match(r"(\d+)-", path.name)
    if match:
        return int(match.group(1)), path.name
    return 999, path.name


def doc_entry(path: Path, extra_keys: list[str] | None = None) -> dict[str, object]:
    text = path.read_text(encoding="utf-8")
    frontmatter, body = parse_frontmatter(text)
    entry: dict[str, object] = {
        "path": rel(path),
        "title": find_title(body, path.stem.replace("-", " ")),
    }
    for key in extra_keys or []:
        value = frontmatter.get(key)
        if value not in (None, "", []):
            entry[key] = value
    return entry


def build_domain_index(domain_dir: Path) -> dict[str, object]:
    memos_dir = domain_dir / "memos"
    memo_entries = []
    accepted_entries = []
    if memos_dir.exists():
        for memo_path in sorted(memos_dir.glob("*.md")):
            entry = doc_entry(
                memo_path,
                ["id", "agent", "status", "question", "book_targets", "dependencies"],
            )
            memo_entries.append(entry)
            if entry.get("status") == "accepted":
                accepted_entries.append(entry)

    return {
        "state": doc_entry(domain_dir / "STATE.md"),
        "memo_count": len(memo_entries),
        "accepted_memo_count": len(accepted_entries),
        "accepted_memos": accepted_entries,
        "all_memos": memo_entries,
    }


def build_registry() -> dict[str, object]:
    constitution_dir = REPO_ROOT / "constitution"
    extracted_dir = REPO_ROOT / "source" / "extracted"
    domains_dir = REPO_ROOT / "domains"
    council_dir = REPO_ROOT / "council"
    book_dir = REPO_ROOT / "book" / "chapters"

    registry = {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "shared_memory_mode": "file-registry-first",
        "openclaw_memory_search": "optional-remote-enhancement",
        "local_embedding_models": "disabled-in-this-environment",
        "agent_load_order": [
            "constitution/UEOT_CONSTITUTION.md",
            "constitution/UEOT_METHOD.md",
            "constitution/UEOT_GLOSSARY.md",
            "memory/shared/UEOT_MEMORY_REGISTRY.yaml",
            "source/extracted/CLAIM_INVENTORY.md",
            "source/extracted/UNRESOLVED_QUESTIONS.md",
        ],
        "constitution": [
            doc_entry(path)
            for path in sorted(constitution_dir.glob("*.md"))
        ],
        "source_extracted": [
            doc_entry(path)
            for path in sorted(extracted_dir.glob("*.md"))
        ],
        "domains": {},
        "council": {
            "resolutions": [
                doc_entry(path, ["decision_id", "scope", "ruling", "followups"])
                for path in sorted((council_dir / "resolutions").glob("*.md"))
            ],
            "reviews": [
                doc_entry(path, ["from", "to", "relation", "claim", "required_action"])
                for path in sorted((council_dir / "reviews").glob("*.md"))
            ],
        },
        "book": {
            "chapters": [
                doc_entry(
                    path,
                    ["thesis", "depends_on_memos", "open_gaps", "citations_needed", "architect_status"],
                )
                for path in sorted(book_dir.glob("*.md"), key=chapter_sort_key)
            ]
        },
    }

    for domain_dir in sorted(path for path in domains_dir.iterdir() if path.is_dir()):
        registry["domains"][domain_dir.name] = build_domain_index(domain_dir)

    return registry


def dump_yaml(value: object, indent: int = 0) -> list[str]:
    prefix = " " * indent
    if isinstance(value, dict):
        lines: list[str] = []
        for key, item in value.items():
            if isinstance(item, (dict, list)):
                lines.append(f"{prefix}{key}:")
                lines.extend(dump_yaml(item, indent + 2))
            else:
                lines.append(f"{prefix}{key}: {format_scalar(item)}")
        return lines
    if isinstance(value, list):
        lines = []
        for item in value:
            if isinstance(item, (dict, list)):
                lines.append(f"{prefix}-")
                lines.extend(dump_yaml(item, indent + 2))
            else:
                lines.append(f"{prefix}- {format_scalar(item)}")
        return lines
    return [f"{prefix}{format_scalar(value)}"]


def format_scalar(value: object) -> str:
    if value is None:
        return '""'
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, (int, float)):
        return str(value)
    text = str(value)
    escaped = text.replace("\\", "\\\\").replace('"', '\\"')
    return f'"{escaped}"'


def main() -> None:
    registry = build_registry()
    OUTPUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT_PATH.write_text("\n".join(dump_yaml(registry)) + "\n", encoding="utf-8")
    domain_count = len(registry["domains"])
    memo_count = sum(
        item["accepted_memo_count"] for item in registry["domains"].values()
    )
    print(
        f"wrote {rel(OUTPUT_PATH)} with {domain_count} domains and {memo_count} accepted memos"
    )


if __name__ == "__main__":
    main()
