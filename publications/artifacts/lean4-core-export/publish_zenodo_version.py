#!/usr/bin/env python3
"""Publish or stage a new semantic version of the pure-kernel Lean 4 archive
into the existing Zenodo concept lineage (Concept DOI: 10.5281/zenodo.24433584).

Supports:
  --mode dry-run  Build deterministic archive & query latest Zenodo version (no token required)
  --mode draft    Create new version draft, replace archive, verify MD5, update metadata & pre-reserve DOI
  --mode publish  Perform full draft flow and publish the new version (mints permanent version DOI)
"""
from __future__ import annotations

from pathlib import Path
import argparse
import html
import json
import os
import sys
import urllib.error
import urllib.parse
import urllib.request

from export_lean4_archive import build_archive, normalize_version

HERE = Path(__file__).resolve().parent
USER_AGENT = "ueot-zenodo-release/1.0 (https://doi.org/10.5281/zenodo.24433584)"
SPDX_TO_ZENODO_LICENSE = {
    "Apache-2.0": "apache2.0",
}
CODE_TOKENS = (
    "ExhaustiveAxiomAudit.lean",
    "{propext, Classical.choice, Quot.sound}",
    "sorryAx",
    "Lean.ofReduceBool",
    "native_decide",
    "NOTICE",
)


def api_request(
    method: str,
    url: str,
    token: str | None = None,
    json_body: dict | None = None,
    raw_bytes: bytes | None = None,
    content_type: str | None = None,
    timeout: int = 120,
) -> tuple[int, dict]:
    """Send HTTP request with descriptive User-Agent and return `(status, parsed_json)`."""
    headers = {
        "User-Agent": USER_AGENT,
        "Accept": "application/json",
    }
    if token:
        headers["Authorization"] = f"Bearer {token}"

    data = None
    if json_body is not None:
        data = json.dumps(json_body, ensure_ascii=False).encode("utf-8")
        headers["Content-Type"] = "application/json"
    elif raw_bytes is not None:
        data = raw_bytes
        headers["Content-Type"] = content_type or "application/octet-stream"
        headers["Content-Length"] = str(len(raw_bytes))

    req = urllib.request.Request(url, data=data, headers=headers, method=method)
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            raw = resp.read().decode("utf-8", errors="replace")
            parsed = json.loads(raw) if raw.strip() else {}
            return resp.status, parsed
    except urllib.error.HTTPError as exc:
        body = exc.read().decode("utf-8", errors="replace")
        raise SystemExit(f"Zenodo API {method} {url} failed ({exc.code}): {body}") from exc


def format_description_html(plain_description: str) -> str:
    """Wrap `.zenodo.json` plain description in `<p>` with `<code>` highlights."""
    escaped = html.escape(plain_description.strip())
    for tok in CODE_TOKENS:
        escaped_tok = html.escape(tok)
        escaped = escaped.replace(escaped_tok, f"<code>{escaped_tok}</code>")
    return f"<p>{escaped}</p>"


def build_deposit_metadata(version: str, publication_date: str) -> dict:
    """Build exact Zenodo deposit `metadata` payload synchronized to `24433585`."""
    raw = json.loads((HERE / ".zenodo.json").read_text(encoding="utf-8"))
    spdx = raw["license"]
    zenodo_license = SPDX_TO_ZENODO_LICENSE.get(spdx)
    if not zenodo_license:
        raise ValueError(f"Unsupported SPDX license mapping for Zenodo API: {spdx!r}")

    return {
        "title": raw["title"],
        "upload_type": raw.get("upload_type", "software"),
        "publication_date": publication_date,
        "description": format_description_html(raw["description"]),
        "access_right": raw.get("access_right", "open"),
        "license": zenodo_license,
        "creators": raw["creators"],
        "keywords": raw.get("keywords", []),
        "version": version,
        "language": "eng",
        "prereserve_doi": True,
    }


def resolve_web_base(zenodo_api_url: str) -> str:
    """Derive Zenodo web origin from API base URL (e.g. https://zenodo.org/api -> https://zenodo.org)."""
    base = zenodo_api_url.rstrip("/")
    if base.endswith("/api"):
        return base[:-4]
    return base


def write_step_summary(summary_path: Path | str | None, result: dict) -> None:
    """Append a concise Markdown release table to GitHub Actions Step Summary when set."""
    if not summary_path:
        return
    p = Path(summary_path)
    lines = [
        f"### Zenodo Lean 4 Release (`v{result['version']}` — `{result['mode']}`)",
        "",
        "| Field | Value |",
        "|:---|:---|",
        f"| **Status** | `{result['status']}` |",
        f"| **Target Version** | `{result['version']}` ({result['publication_date']}) |",
        f"| **Concept DOI** | `{result['concept_doi']}` |",
        f"| **Lineage Base Record** | `{result['latest_published_record_id']}` (v{result['latest_published_version']}) |",
        f"| **Archive** | `{result['archive_filename']}` ({result['archive_size_bytes']} bytes) |",
        f"| **SHA-256** | `{result['archive_sha256']}` |",
        f"| **MD5** | `{result['archive_md5']}` |",
    ]
    if result.get("reserved_doi"):
        lines.append(f"| **Reserved DOI** | `{result['reserved_doi']}` |")
    if result.get("draft_url"):
        lines.append(f"| **Draft URL** | {result['draft_url']} |")
    if result.get("doi"):
        lines.append(f"| **Published DOI** | `https://doi.org/{result['doi']}` |")
    if result.get("record_url"):
        lines.append(f"| **Record URL** | {result['record_url']} |")
    lines.append("")
    p.parent.mkdir(parents=True, exist_ok=True)
    with p.open("a", encoding="utf-8") as fh:
        fh.write("\n".join(lines) + "\n")


def run_release(
    version: str,
    mode: str = "draft",
    publication_date: str | None = None,
    zenodo_api_url: str = "https://zenodo.org/api",
    seed_record_id: str = "24433585",
    concept_doi: str = "10.5281/zenodo.24433584",
    token: str | None = None,
    summary_file: Path | str | None = None,
) -> dict:
    """Execute dry-run, draft creation, or full version publish against Zenodo."""
    target_version = normalize_version(version)
    api_base = zenodo_api_url.rstrip("/")
    web_base = resolve_web_base(api_base)

    build = build_archive(version=target_version, publication_date=publication_date)
    pub_date = build["publication_date"]
    tarball_path = Path(build["tarball_path"])
    tar_bytes = tarball_path.read_bytes()

    latest_url = f"{api_base}/records/{urllib.parse.quote(seed_record_id)}/versions/latest"
    _, latest_rec = api_request("GET", latest_url, token=token)
    latest_id = str(latest_rec["id"])
    latest_version = str(latest_rec.get("metadata", {}).get("version", ""))

    if latest_version == target_version:
        raise SystemExit(
            f"Refusing release: version {target_version!r} is already the latest published "
            f"Zenodo record (ID {latest_id}) under concept DOI {concept_doi}."
        )

    deposit_metadata = build_deposit_metadata(target_version, pub_date)
    base_result = {
        "mode": mode,
        "version": target_version,
        "publication_date": pub_date,
        "concept_doi": concept_doi,
        "latest_published_record_id": latest_id,
        "latest_published_version": latest_version,
        "archive_filename": build["archive_filename"],
        "archive_size_bytes": build["archive_size_bytes"],
        "archive_sha256": build["archive_sha256"],
        "archive_md5": build["archive_md5"],
        "tarball_path": build["tarball_path"],
        "receipt_path": build["receipt_path"],
    }

    if mode == "dry-run":
        result = {
            **base_result,
            "status": "dry_run_ok",
            "validated_deposit_metadata": deposit_metadata,
        }
        write_step_summary(summary_file, result)
        return result

    if not token:
        raise SystemExit(
            "Missing ZENODO_TOKEN environment variable. Create a personal access token at "
            "https://zenodo.org/account/settings/applications/tokens/new/ (scopes: deposit:write, "
            "deposit:actions) and run `gh secret set ZENODO_TOKEN`."
        )

    # 1. Mint editable new-version draft from the latest published version in the lineage
    newver_url = f"{api_base}/deposit/depositions/{urllib.parse.quote(latest_id)}/actions/newversion"
    _, newver_resp = api_request("POST", newver_url, token=token)
    latest_draft_url = newver_resp.get("links", {}).get("latest_draft")
    if not latest_draft_url:
        raise SystemExit(f"Zenodo newversion response missing links.latest_draft: {newver_resp}")

    _, draft = api_request("GET", latest_draft_url, token=token)
    draft_id = str(draft["id"])
    bucket_url = draft["links"]["bucket"].rstrip("/")

    # 2. Remove inherited files from prior version before streaming the new tarball
    for old_file in draft.get("files", []):
        del_url = f"{api_base}/deposit/depositions/{draft_id}/files/{urllib.parse.quote(str(old_file['id']))}"
        api_request("DELETE", del_url, token=token)

    # 3. Upload tarball via Bucket PUT and assert byte count + MD5 checksum parity
    put_url = f"{bucket_url}/{urllib.parse.quote(tarball_path.name)}"
    _, uploaded = api_request(
        "PUT",
        put_url,
        token=token,
        raw_bytes=tar_bytes,
        content_type="application/octet-stream",
        timeout=300,
    )
    expected_md5 = f"md5:{build['archive_md5']}"
    if uploaded.get("checksum") != expected_md5 or uploaded.get("size") != build["archive_size_bytes"]:
        raise SystemExit(
            f"Zenodo uploaded file checksum/size mismatch: got {uploaded}, "
            f"expected size={build['archive_size_bytes']} checksum={expected_md5}"
        )

    # 4. Update deposit metadata for the new version & capture pre-reserved DOI
    dep_url = f"{api_base}/deposit/depositions/{draft_id}"
    _, updated = api_request("PUT", dep_url, token=token, json_body={"metadata": deposit_metadata})
    reserved_doi = updated.get("metadata", {}).get("prereserve_doi", {}).get("doi") or f"10.5281/zenodo.{draft_id}"

    if mode == "draft":
        result = {
            **base_result,
            "status": "draft_saved",
            "draft_id": draft_id,
            "draft_url": f"{web_base}/uploads/{draft_id}",
            "reserved_doi": reserved_doi,
        }
        write_step_summary(summary_file, result)
        return result

    # 5. Publish the verified new-version draft (only in --mode publish)
    pub_url = f"{api_base}/deposit/depositions/{draft_id}/actions/publish"
    _, published = api_request("POST", pub_url, token=token)
    record_id = str(published.get("id", draft_id))
    minted_doi = published.get("doi") or reserved_doi
    result = {
        **base_result,
        "status": "published",
        "record_id": record_id,
        "record_url": f"{web_base}/records/{record_id}",
        "doi": minted_doi,
        "concept_doi": published.get("conceptdoi") or concept_doi,
    }
    write_step_summary(summary_file, result)
    return result


def parse_args(argv=None):
    parser = argparse.ArgumentParser(
        description="Automate versioned Zenodo upload under Concept DOI 10.5281/zenodo.24433584."
    )
    parser.add_argument("--version", required=True, help="Release version (e.g. 1.1.0 or lean4-export-v1.1.0).")
    parser.add_argument("--mode", choices=["dry-run", "draft", "publish"], default="draft")
    parser.add_argument("--publication-date", default=None, help="Publication date YYYY-MM-DD (default: UTC today).")
    parser.add_argument(
        "--zenodo-api-url",
        default=os.environ.get("ZENODO_API_URL", "https://zenodo.org/api"),
        help="Zenodo API root URL (default: https://zenodo.org/api).",
    )
    parser.add_argument("--seed-record-id", default="24433585", help="Seed record ID for lineage lookup.")
    parser.add_argument("--concept-doi", default="10.5281/zenodo.24433584", help="Concept DOI for lineage.")
    parser.add_argument(
        "--summary-file",
        default=os.environ.get("GITHUB_STEP_SUMMARY"),
        help="Optional Markdown summary file path (defaults to GITHUB_STEP_SUMMARY).",
    )
    return parser.parse_args(argv)


def main(argv=None):
    args = parse_args(argv)
    result = run_release(
        version=args.version,
        mode=args.mode,
        publication_date=args.publication_date,
        zenodo_api_url=args.zenodo_api_url,
        seed_record_id=args.seed_record_id,
        concept_doi=args.concept_doi,
        token=os.environ.get("ZENODO_TOKEN"),
        summary_file=args.summary_file,
    )
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
