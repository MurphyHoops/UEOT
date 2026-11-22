#!/usr/bin/env python3
"""Unit and mock-API tests for parameterized Apache-2.0 Zenodo archive export
and concept-lineage version synchronization.
"""
from __future__ import annotations

from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
import hashlib
import json
import sys
import tarfile
import tempfile
import threading
import unittest

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

from export_lean4_archive import build_archive, normalize_version  # noqa: E402
from publish_zenodo_version import run_release  # noqa: E402


class MockZenodoState:
    """In-memory Zenodo API recorder for deterministic draft/publish tests."""

    def __init__(self, base_url: str = ""):
        self.base_url = base_url
        self.requests: list[tuple[str, str]] = []
        self.uploaded_bytes: bytes | None = None
        self.updated_payload: dict | None = None
        self.published: bool = False


def make_handler(state: MockZenodoState):
    class MockZenodoHandler(BaseHTTPRequestHandler):
        def log_message(self, format, *args):  # noqa: A002
            return

        def _send_json(self, code: int, payload: dict):
            raw = json.dumps(payload).encode("utf-8")
            self.send_response(code)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(raw)))
            self.end_headers()
            self.wfile.write(raw)

        def do_GET(self):  # noqa: N802
            state.requests.append(("GET", self.path))
            if self.path == "/api/records/24433585/versions/latest":
                self._send_json(200, {
                    "id": 24433585,
                    "metadata": {"version": "1.0.0"},
                })
                return
            if self.path == "/api/deposit/depositions/24499999":
                self._send_json(200, {
                    "id": 24499999,
                    "links": {"bucket": f"{state.base_url}/api/files/mock-bucket"},
                    "files": [{"id": "old-file-1", "filename": "lean4-pure-kernel-formalization-v1.0.0.tar.gz"}],
                })
                return
            self._send_json(404, {"error": f"Unexpected GET {self.path}"})

        def do_POST(self):  # noqa: N802
            state.requests.append(("POST", self.path))
            if self.path == "/api/deposit/depositions/24433585/actions/newversion":
                self._send_json(201, {
                    "id": 24433585,
                    "links": {
                        "latest_draft": f"{state.base_url}/api/deposit/depositions/24499999",
                    },
                })
                return
            if self.path == "/api/deposit/depositions/24499999/actions/publish":
                state.published = True
                self._send_json(202, {
                    "id": 24499999,
                    "doi": "10.5281/zenodo.24499999",
                    "conceptdoi": "10.5281/zenodo.24433584",
                })
                return
            self._send_json(404, {"error": f"Unexpected POST {self.path}"})

        def do_DELETE(self):  # noqa: N802
            state.requests.append(("DELETE", self.path))
            if self.path == "/api/deposit/depositions/24499999/files/old-file-1":
                self.send_response(204)
                self.end_headers()
                return
            self._send_json(404, {"error": f"Unexpected DELETE {self.path}"})

        def do_PUT(self):  # noqa: N802
            state.requests.append(("PUT", self.path))
            length = int(self.headers.get("Content-Length", "0"))
            body = self.rfile.read(length)
            if self.path == "/api/files/mock-bucket/lean4-pure-kernel-formalization-v1.1.0.tar.gz":
                state.uploaded_bytes = body
                md5_hex = hashlib.md5(body).hexdigest()
                self._send_json(200, {
                    "key": "lean4-pure-kernel-formalization-v1.1.0.tar.gz",
                    "size": len(body),
                    "checksum": f"md5:{md5_hex}",
                })
                return
            if self.path == "/api/deposit/depositions/24499999":
                state.updated_payload = json.loads(body.decode("utf-8"))
                self._send_json(200, {
                    "id": 24499999,
                    "metadata": {
                        **state.updated_payload["metadata"],
                        "prereserve_doi": {"doi": "10.5281/zenodo.24499999", "recid": 24499999},
                    },
                })
                return
            self._send_json(404, {"error": f"Unexpected PUT {self.path}"})

    return MockZenodoHandler


class TestZenodoReleaseAutomation(unittest.TestCase):
    @classmethod
    def tearDownClass(cls):
        dist = HERE / "dist"
        for fname in ("lean4-pure-kernel-formalization-v1.1.0.tar.gz", "EXPORT_RECEIPT-v1.1.0.json"):
            p = dist / fname
            if p.exists():
                p.unlink()

    def test_version_normalization(self):
        self.assertEqual(normalize_version("1.2.3"), "1.2.3")
        self.assertEqual(normalize_version("v1.2.3"), "1.2.3")
        self.assertEqual(normalize_version("lean4-export-v1.2.3"), "1.2.3")
        with self.assertRaises(ValueError):
            normalize_version("not-a-semver")

    def test_deterministic_parameterized_archive(self):
        tracked_receipt = (HERE / "EXPORT_RECEIPT.json").read_bytes()
        r1 = build_archive(version="1.1.0", publication_date="2026-12-01")
        r2 = build_archive(version="1.1.0", publication_date="2026-12-01")

        self.assertEqual(r1["archive_sha256"], r2["archive_sha256"])
        self.assertEqual(r1["archive_md5"], r2["archive_md5"])
        self.assertEqual(r1["lean_library_modules"], 1051)
        self.assertTrue(r1["docs_prose_excluded"])
        self.assertEqual((HERE / "EXPORT_RECEIPT.json").read_bytes(), tracked_receipt)

        tarball = Path(r1["tarball_path"])
        with tarfile.open(tarball, "r:gz") as tf:
            names = tf.getnames()
            prefix = "lean4-pure-kernel-formalization-v1.1.0/"
            self.assertIn(prefix + "LICENSE", names)
            self.assertIn(prefix + "NOTICE", names)
            self.assertFalse(any("/docs/" in n for n in names))
            lean_count = sum(
                1 for n in names
                if n.endswith(".lean") and (n == prefix + "UEOT.lean" or n.startswith(prefix + "UEOT/"))
            )
            self.assertEqual(lean_count, 1051)

            zen_meta = json.loads(tf.extractfile(prefix + ".zenodo.json").read().decode("utf-8"))
            self.assertEqual(zen_meta["version"], "1.1.0")
            self.assertEqual(zen_meta["publication_date"], "2026-12-01")

            cff_text = tf.extractfile(prefix + "CITATION.cff").read().decode("utf-8")
            self.assertIn('version: "1.1.0"', cff_text)
            self.assertIn('date-released: "2026-12-01"', cff_text)
            self.assertIn("10.5281/zenodo.24433584", cff_text)
            self.assertNotIn("24433585", cff_text)

    def _start_server(self):
        state = MockZenodoState()
        server = ThreadingHTTPServer(("127.0.0.1", 0), make_handler(state))
        host, port = server.server_address
        state.base_url = f"http://{host}:{port}"
        thread = threading.Thread(target=server.serve_forever, daemon=True)
        thread.start()
        return server, state

    def test_duplicate_guard_and_draft_and_publish(self):
        server, state = self._start_server()
        try:
            api_url = f"{state.base_url}/api"

            # 1. Duplicate version guard
            with self.assertRaises(SystemExit):
                run_release(
                    version="1.0.0",
                    mode="dry-run",
                    publication_date="2026-11-22",
                    zenodo_api_url=api_url,
                )

            # 2. Draft flow (must NOT publish)
            draft_res = run_release(
                version="1.1.0",
                mode="draft",
                publication_date="2026-12-01",
                zenodo_api_url=api_url,
                token="fake-token",
            )
            self.assertEqual(draft_res["status"], "draft_saved")
            self.assertEqual(draft_res["reserved_doi"], "10.5281/zenodo.24499999")
            self.assertEqual(draft_res["draft_url"], f"{state.base_url}/uploads/24499999")
            self.assertFalse(state.published)
            self.assertEqual(state.requests, [
                ("GET", "/api/records/24433585/versions/latest"),
                ("GET", "/api/records/24433585/versions/latest"),
                ("POST", "/api/deposit/depositions/24433585/actions/newversion"),
                ("GET", "/api/deposit/depositions/24499999"),
                ("DELETE", "/api/deposit/depositions/24499999/files/old-file-1"),
                ("PUT", "/api/files/mock-bucket/lean4-pure-kernel-formalization-v1.1.0.tar.gz"),
                ("PUT", "/api/deposit/depositions/24499999"),
            ])
            meta = state.updated_payload["metadata"]
            self.assertEqual(meta["license"], "apache2.0")
            self.assertEqual(meta["language"], "eng")
            self.assertEqual(meta["version"], "1.1.0")
            self.assertTrue(meta["prereserve_doi"])
            self.assertNotIn("doi", meta)
            self.assertEqual(
                hashlib.md5(state.uploaded_bytes).hexdigest(),
                draft_res["archive_md5"],
            )

            # 3. Publish flow + step summary
            state.requests.clear()
            with tempfile.TemporaryDirectory() as tmp:
                summary = Path(tmp) / "summary.md"
                pub_res = run_release(
                    version="1.1.0",
                    mode="publish",
                    publication_date="2026-12-01",
                    zenodo_api_url=api_url,
                    token="fake-token",
                    summary_file=summary,
                )
                self.assertTrue(state.published)
                self.assertEqual(pub_res["status"], "published")
                self.assertEqual(pub_res["record_url"], f"{state.base_url}/records/24499999")
                self.assertEqual(pub_res["doi"], "10.5281/zenodo.24499999")
                self.assertEqual(pub_res["concept_doi"], "10.5281/zenodo.24433584")
                self.assertIn("POST", [m for m, p in state.requests if p.endswith("/actions/publish")])
                summary_txt = summary.read_text(encoding="utf-8")
                self.assertIn("10.5281/zenodo.24499999", summary_txt)
        finally:
            server.shutdown()
            server.server_close()


if __name__ == "__main__":
    unittest.main()
