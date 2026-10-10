#!/usr/bin/env python3
"""Fast read-only regression for FKRG pinned proof reuse and clone evidence."""
import sys
from pathlib import Path
import unittest
from unittest import mock

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import fkrg_reuse as reuse
import VERIFY_PMF_TV_BRIDGE as bridge
import REBUILD_CLONE_CANDIDATES as clone_scanner


class ProofReuseTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = reuse.load()

    def test_evidence_and_sources_exact_baseline(self):
        res = reuse.status(self.data)
        self.assertEqual(res["module_source_hashes_verified"], 633)
        self.assertEqual(res["ueot_maintained_modules"], 622)
        self.assertEqual(res["vendor_modules"], 11)
        self.assertEqual(res["public_source_theorems_with_direct_proof_graph"], 3793)
        self.assertEqual(res["verified_equal_type_groups"], 37)
        self.assertEqual(res["equal_type_statement_names"], 77)
        self.assertEqual(res["near_type_not_defeq_candidate_pairs"], 15)
        self.assertEqual(res["crossfile_exact_code_clone_candidates"], 68)

    def test_known_type_equal_and_direct_generator(self):
        item = reuse.explain(
            self.data,
            "UEOT.V3.Compression.TransportCertificate.processInterface_approx_via_twoStage")
        self.assertEqual(item["role"], "COUNTED_GENERATOR_FAMILY_REDERIVATION")
        self.assertEqual(item["type_relation"], "LEANTYPE_DEF_EQ_VERIFIED_SNAPSHOT_40_PAIRS")
        self.assertIn("UEOT.V3.Compression.TransportCertificate.twoStage_bound",
                      item["direct_existing_source_theorem_uses"])
        self.assertTrue(any(p["name"] == "UEOT.V3.ProcessInterface.p_api_01_approx"
                            for p in item["definitionally_equal_type_peers"]))

    def test_counts_from_canonical_ledger_tiers(self):
        names = [member["name"]
                 for group in self.data["groups"] if not group["verified_direct_proof_dep_edges"]
                 for member in group["group_member_declarations"]]
        selected = [n for n in names if reuse.role(n) not in ("NO_TRIAGE_CLASSIFICATION", "PREFERRED_TV_HELPER_IMPLEMENTATION")]
        self.assertEqual(len(selected), 14)
        counts = {}
        for name in selected:
            key = reuse.role(name)
            counts[key] = counts.get(key, 0) + 1
        self.assertEqual(
            counts,
            {"COUNTED_GENERATOR_FAMILY_REDERIVATION": 7,
             "COUNTED_GENERATOR_FAMILY_SUPPORT_LEMMA": 1,
             "UNCOUNTED_RETAINED_ADAPTER_EXPERIMENT": 4,
             "LOW_RISK_DUPLICATE_HELPER_IMPLEMENTATION": 1,
             "SAME_NO_GO_INTERFACE_ALIAS": 1}
        )

    def test_tv_helper_equal_type_but_public_clients(self):
        item = reuse.explain(self.data, reuse.DUPLICATED_TV_HELPER)
        self.assertEqual(item["role"], "LOW_RISK_DUPLICATE_HELPER_IMPLEMENTATION")
        self.assertTrue(item["direct_source_theorem_users"])
        self.assertIn(reuse.CANONICAL_TV_HELPER,
                      {p["name"] for p in item["definitionally_equal_type_peers"]})

    def test_vendor_is_not_first_party(self):
        rows = [r for r in self.data["graph"].values()
                if r["source_origin"] == "VENDORED_ADAPTED_UPSTREAM"]
        self.assertEqual(len(rows), 156)

    def test_search_recall_and_no_equivalence_overclaim(self):
        rows = reuse.search(self.data, "tvDist_symm", 20)
        self.assertIn(reuse.CANONICAL_TV_HELPER, [x["symbol"] for x in rows])
        rows = reuse.search(self.data, "program reconstruction", 15)
        self.assertTrue(rows)
        self.assertTrue(all(x["has_equal_type_peers"] in (True, False) for x in rows))
        with self.assertRaisesRegex(RuntimeError, "UNKNOWN_PUBLIC_SOURCE_THEOREM"):
            reuse.explain(self.data, "not.a.real.theorem")

    def test_code_clones_are_not_type_identity(self):
        entries = reuse.clone_candidates(self.data, threshold=15)
        self.assertEqual(entries["count"], 12)
        self.assertEqual(max(int(x["equal_nonblank_code_lines"])
                             for x in entries["entries"]), 31)
        pair = entries["entries"][0]
        self.assertIn("SymmetricKilledSpectralStability", pair["file_b"])
        self.assertEqual(reuse.role("UEOT.V3.Nonexistent"), "NO_TRIAGE_CLASSIFICATION")

    def test_regenerate_all_crossfile_exact_source_clones(self):
        fresh = clone_scanner.scan()
        self.assertEqual(fresh, self.data["clones"])
        self.assertEqual(len(fresh), 68)

    def test_mutating_pinned_audit_hash_fails_closed(self):
        key = next(iter(reuse.EVIDENCE_SHA))
        with mock.patch.dict(reuse.EVIDENCE_SHA, {key: "0" * 64}):
            with self.assertRaisesRegex(RuntimeError, "AUDIT_EVIDENCE_DRIFT"):
                reuse.verify_evidence_files()
        with mock.patch.object(reuse, "CLONE_SHA256", "f" * 64):
            with self.assertRaisesRegex(RuntimeError, "AUDIT_CLONE_EVIDENCE_DRIFT"):
                reuse.verify_evidence_files()
        with mock.patch.object(reuse, "LEDGER_SHA256", "f" * 64):
            with self.assertRaisesRegex(RuntimeError, "CANONICAL_COMPRESSION_LEDGER_CHANGED"):
                reuse.verify_evidence_files()

    def test_any_modified_source_rejected(self):
        row = dict(self.data["modules"][-1])
        row["content_sha256"] = "0" * 64
        with self.assertRaisesRegex(RuntimeError, "STALE_AUDIT_SOURCE"):
            reuse.verify_sources([row])

    def test_bridge_last_source_negative_control_before_compilation(self):
        with mock.patch.dict(bridge.PINNED_SHA, {bridge.SECOND: "0" * 64}):
            def fail_compiler(*args, **kwargs):
                self.fail("compiler ran before source preflight")
            with self.assertRaisesRegex(RuntimeError, "STALE_ORIGINAL_SOURCE"):
                bridge.run(compilation=fail_compiler)


if __name__ == "__main__":
    unittest.main(verbosity=2)
