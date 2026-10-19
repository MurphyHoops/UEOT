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
        self.assertEqual(res["module_source_hashes_verified"], 636)
        self.assertEqual(res["ueot_maintained_modules"], 625)
        self.assertEqual(res["vendor_modules"], 11)
        self.assertEqual(res["public_source_theorems_with_direct_proof_graph"], 3817)
        self.assertEqual(res["verified_equal_type_groups"], 37)
        self.assertEqual(res["equal_type_statement_names"], 77)
        self.assertEqual(res["near_type_not_defeq_candidate_pairs"], 15)
        self.assertEqual(res["crossfile_exact_code_clone_candidates"], 68)
        self.assertEqual(res["overlay_public_theorems"], 24)
        self.assertEqual(res["overlay_cross_snapshot_defeq_matches"], 0)
        self.assertEqual(res["overlay_lexical_reuse_candidates"], 1)
        self.assertEqual(res["overlay_count"], 3)
        self.assertEqual(res["overlay_registered_direct_edges"], 9)

    def test_calibrated_defect_overlay_chain_and_kernel_graph(self):
        self.assertEqual(len(self.data["overlays"]), 3)
        prior, current = self.data["overlays"][:2]
        self.assertEqual(prior["base_snapshot_modules"], 633)
        self.assertEqual(current["base_snapshot_modules"], 634)
        self.assertEqual(
            current["prior_overlay"]["sha256"],
            reuse.OVERLAY_SHA256S[0],
        )
        self.assertEqual(
            current["type_distinctness"]["registered_prior_theorems"],
            3803,
        )
        self.assertEqual(
            current["proof_dependency_certification"]["registered_direct_edges"],
            3,
        )
        weighted = (
            "UEOT.V3.Compression.TheoryCompletion.MinCore."
            "calibrated_weighted_chain_bound"
        )
        weighted_item = reuse.explain(self.data, weighted)
        self.assertEqual(weighted_item["role"], "UNCOUNTED_MINCORE_BOUNDARY")
        self.assertEqual(
            weighted_item["direct_existing_source_theorem_uses"],
            ["UEOT.V3.Compression.TransportCertificate.weighted_chain_bound"],
        )
        rel = (
            "UEOT.V3.Compression.TheoryCompletion.MinCore."
            "DefectCalibration.rel_iff"
        )
        self.assertEqual(
            reuse.explain(self.data, rel)["direct_existing_source_theorem_uses"],
            [
                "UEOT.V3.Compression.TheoryCompletion.MinCore."
                "DefectCalibration.zero_defect_iff"
            ],
        )

    def test_defect_gauge_overlay_chain_and_kernel_graph(self):
        current = self.data["overlays"][2]
        self.assertEqual(current["base_snapshot_modules"], 635)
        self.assertEqual(current["prior_overlay"]["sha256"], reuse.OVERLAY_SHA256S[1])
        self.assertEqual(current["type_distinctness"]["registered_prior_theorems"], 3811)
        self.assertEqual(current["type_distinctness"]["cross_isDefEq_comparisons"], 22866)
        self.assertEqual(current["type_distinctness"]["internal_isDefEq_comparisons"], 15)
        self.assertEqual(current["proof_dependency_certification"]["registered_direct_edges"], 6)
        prefix = "UEOT.V3.Compression.TheoryCompletion.MinCore."
        for name in ("DefectCalibration.triangle_quasi", "calibrated_cross_stage_contraction"):
            with self.subTest(symbol=name):
                self.assertEqual(
                    reuse.explain(self.data, prefix + name)["direct_existing_source_theorem_uses"],
                    [prefix + "DefectCalibration.reverse_budget"],
                )
        weighted = reuse.explain(self.data, prefix + "rescaled_weighted_chain_bound")
        self.assertEqual(weighted["role"], "UNCOUNTED_MINCORE_BOUNDARY")
        self.assertEqual(
            set(weighted["direct_existing_source_theorem_uses"]),
            {
                "UEOT.V3.Compression.TransportCertificate.weighted_chain_bound",
                prefix + "rescale_triangle_preserved",
                prefix + "rescale_contraction_transformed",
                prefix + "rescale_local_budget_transformed",
            },
        )
        for name in ("rescale_triangle_preserved", "rescale_contraction_transformed",
                     "rescale_local_budget_transformed"):
            with self.subTest(symbol=name):
                self.assertEqual(
                    reuse.explain(self.data, prefix + name)["direct_existing_source_theorem_uses"],
                    [],
                )
        self.assertEqual(
            current["lexical_pr_preflight"]["new_theorems_with_lexical_reuse_candidates"], 1
        )

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

    def test_mincore_overlay_is_searchable_and_uncounted(self):
        symbol = (
            "UEOT.V3.Compression.TheoryCompletion.MinCore."
            "no_relation_only_quantitative_recovery"
        )
        item = reuse.explain(self.data, symbol)
        self.assertEqual(item["role"], "UNCOUNTED_MINCORE_BOUNDARY")
        self.assertEqual(item["direct_existing_source_theorem_uses"], [])
        self.assertEqual(item["type_relation"], "NO_TYPE_EQUIVALENCE_CERTIFICATE")
        self.assertEqual(self.data["overlays"][0]["type_distinctness"]["definitionally_equal_matches"], 0)

    def test_mincore_overlay_kernel_proof_graph(self):
        source = (
            "UEOT.V3.Compression.TheoryCompletion.MinCore."
            "RelationDefectPresentation.rescale_changes_nonzero_defect"
        )
        target = (
            "UEOT.V3.Compression.TheoryCompletion.MinCore."
            "RelationDefectPresentation.rescale_defect"
        )
        item = reuse.explain(self.data, source)
        self.assertEqual(item["direct_existing_source_theorem_uses"], [])
        target_item = reuse.explain(self.data, target)
        self.assertNotIn(source, target_item["direct_source_theorem_users"])
        self.assertEqual(
            self.data["overlays"][0]["proof_dependency_certification"]["registered_direct_edges"],
            0,
        )

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
        for index in range(len(reuse.OVERLAY_PATHS)):
            with self.subTest(overlay=index):
                hashes = list(reuse.OVERLAY_SHA256S)
                hashes[index] = "0" * 64
                with mock.patch.object(reuse, "OVERLAY_SHA256S", hashes):
                    with self.assertRaisesRegex(RuntimeError, "REUSE_OVERLAY_EVIDENCE_DRIFT"):
                        reuse.verify_evidence_files()
                type_hashes = list(reuse.OVERLAY_TYPE_CHECK_SHA256S)
                type_hashes[index] = "0" * 64
                with mock.patch.object(reuse, "OVERLAY_TYPE_CHECK_SHA256S", type_hashes):
                    with self.assertRaisesRegex(RuntimeError, "REUSE_OVERLAY_TYPE_CHECK_DRIFT"):
                        reuse.verify_evidence_files()
        with mock.patch.object(reuse, "LEDGER_SHA256", "f" * 64):
            with self.assertRaisesRegex(RuntimeError, "CANONICAL_COMPRESSION_LEDGER_CHANGED"):
                reuse.verify_evidence_files()
        for name in reuse.BUILD_ENVIRONMENT_SHA256:
            with self.subTest(build_input=name):
                with mock.patch.dict(reuse.BUILD_ENVIRONMENT_SHA256, {name: "0" * 64}):
                    with self.assertRaisesRegex(RuntimeError, "STALE_LEAN_BUILD_ENVIRONMENT"):
                        reuse.verify_evidence_files()

    def test_any_modified_source_rejected(self):
        modules = [dict(row) for row in self.data["modules"]]
        modules[-1]["content_sha256"] = "0" * 64
        with self.assertRaisesRegex(RuntimeError, "STALE_AUDIT_SOURCE"):
            reuse.verify_sources(modules)

    def test_new_lean_module_cannot_be_omitted_from_index(self):
        live = reuse.live_source_paths()
        self.assertEqual(len(live), 636)
        new = "formalization/ueot-core/UEOT/V3/FutureNovelLemma.lean"
        with mock.patch.object(reuse, "live_source_paths", return_value=live | {new}):
            with self.assertRaisesRegex(RuntimeError, "STALE_AUDIT_SOURCE_SET"):
                reuse.verify_sources(self.data["modules"])

    def test_deleted_lean_module_cannot_be_omitted_from_index(self):
        live = reuse.live_source_paths()
        old = self.data["modules"][-1]["path"]
        self.assertIn(old, live)
        with mock.patch.object(reuse, "live_source_paths", return_value=live - {old}):
            with self.assertRaisesRegex(RuntimeError, "STALE_AUDIT_SOURCE_SET"):
                reuse.verify_sources(self.data["modules"])

    def test_bridge_last_source_negative_control_before_compilation(self):
        with mock.patch.dict(bridge.PINNED_SHA, {bridge.SECOND: "0" * 64}):
            def fail_compiler(*args, **kwargs):
                self.fail("compiler ran before source preflight")
            with self.assertRaisesRegex(RuntimeError, "STALE_ORIGINAL_SOURCE"):
                bridge.run(compilation=fail_compiler)


if __name__ == "__main__":
    unittest.main(verbosity=2)
