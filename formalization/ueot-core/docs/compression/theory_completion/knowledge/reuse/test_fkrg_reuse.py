#!/usr/bin/env python3
"""Fast read-only regression for FKRG pinned proof reuse and clone evidence."""
import sys
import json
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
        self.assertEqual(res["module_source_hashes_verified"], 650)
        self.assertEqual(res["ueot_maintained_modules"], 639)
        self.assertEqual(res["vendor_modules"], 11)
        self.assertEqual(res["public_source_theorems_with_direct_proof_graph"], 3992)
        self.assertEqual(res["verified_equal_type_groups"], 37)
        self.assertEqual(res["equal_type_statement_names"], 77)
        self.assertEqual(res["near_type_not_defeq_candidate_pairs"], 15)
        self.assertEqual(res["crossfile_exact_code_clone_candidates"], 68)
        self.assertEqual(res["overlay_public_theorems"], 199)
        self.assertEqual(res["overlay_cross_snapshot_defeq_matches"], 0)
        self.assertEqual(res["overlay_lexical_reuse_candidates"], 40)
        self.assertEqual(res["overlay_count"], 6)
        self.assertEqual(res["overlay_registered_direct_edges"], 271)
        self.assertEqual(sum(len(json.loads(row["source_theorem_deps_json"]))
                             for row in self.data["graph"].values()), 5157)

    def test_calibrated_defect_overlay_chain_and_kernel_graph(self):
        self.assertEqual(len(self.data["overlays"]), 6)
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

    def test_finite_risk_overlay_reuses_real_source_endpoints(self):
        current = self.data["overlays"][3]
        self.assertEqual(current["base_snapshot_modules"], 636)
        self.assertEqual(current["prior_overlay"]["sha256"], reuse.OVERLAY_SHA256S[2])
        self.assertEqual(len(current["added_modules"]), 5)
        self.assertEqual(len(current["public_theorems"]), 48)
        distinct = current["type_distinctness"]
        self.assertEqual(distinct["registered_prior_theorems"], 3817)
        self.assertEqual(distinct["cross_isDefEq_comparisons"], 183216)
        self.assertEqual(distinct["internal_isDefEq_comparisons"], 1128)
        self.assertEqual(current["proof_dependency_certification"]["registered_direct_edges"], 73)
        prefix = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure."
        coordinate = reuse.explain(self.data, prefix + "pmf_tv_le_clipped_coordinate_budget")
        self.assertEqual(set(coordinate["direct_existing_source_theorem_uses"]), {
            "UEOT.V3.TotalVariation.tvDist_le_one",
            "UEOT.V3.FiniteRecurrentDecompositionStability.pmf_tv_eq_half_sum_abs",
        })
        finite_path = reuse.explain(self.data, prefix + "finite_horizon_path_error")
        self.assertIn("UEOT.V3.PathError.p_dyn_03_finite_path_error",
                      finite_path["direct_existing_source_theorem_uses"])
        calibrated = reuse.explain(self.data, prefix + "calibrated_representative_path_error")
        self.assertEqual(set(calibrated["direct_existing_source_theorem_uses"]), {
            prefix + "same_policy_projected_path_error",
            prefix + "calibrated_observable_partition_tv_budget",
        })
        self.assertEqual(calibrated["role"], "UNCOUNTED_FINITE_HORIZON_RISK_AND_CALIBRATION_BRIDGES")
        self.assertEqual(current["counted_core_impact"], "NONE")

    def test_statistical_risk_overlay_chain_and_source_endpoints(self):
        current = self.data["overlays"][4]
        self.assertEqual(current["base_snapshot_modules"], 641)
        self.assertEqual(current["prior_overlay"]["sha256"], reuse.OVERLAY_SHA256S[3])
        self.assertEqual(len(current["added_modules"]), 5)
        self.assertEqual(len(current["public_theorems"]), 73)
        distinct = current["type_distinctness"]
        self.assertEqual(distinct["registered_prior_theorems"], 3865)
        self.assertEqual(distinct["cross_isDefEq_comparisons"], 282145)
        self.assertEqual(distinct["internal_isDefEq_comparisons"], 2628)
        self.assertEqual(current["proof_dependency_certification"]["registered_direct_edges"],
                         91)
        lexical = current["lexical_pr_preflight"]
        self.assertEqual(lexical["new_theorems_with_lexical_reuse_candidates"], 11)
        self.assertEqual(lexical["base_public_lexical_theorem_count"], 3866)
        self.assertEqual(lexical["candidate_public_lexical_theorem_count"], 3939)
        self.assertEqual(lexical["candidate_registered_public_source_theorem_count"], 3938)
        self.assertEqual(current["counted_core_impact"], "NONE")
        self.assertEqual(current["scientific_closure"], "NOT_ESTABLISHED")
        prefix = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure."
        # Exact sets observed in the separately executed fixed native verifier.
        # Source tactic tokens are not evidence of compiled direct dependencies.
        expected_edges = {
            "measure_finite_row_calibration_bad_le": [
                'UEOT.V3.BoundedLossTwoSided.measure_exists_candidate_bad_le',
            ],
            "statistical_representative_risk_certificate": [
                prefix + 'empirical_representative_risk_of_calibrated',
                prefix + 'measurableSet_empirical_transition_calibrated',
                prefix + 'measure_empirical_transition_uncalibrated_le',
            ],
            "statistical_empirical_reference_certificate": [
                prefix + 'empirical_reference_risk_of_calibrated',
                prefix + 'measurableSet_empirical_transition_calibrated',
                prefix + 'measure_empirical_transition_uncalibrated_le',
            ],
            "same_policy_microscopic_failure_risk": [
                prefix + 'risk_microscopic_event_le_envelope',
                prefix + 'same_policy_projected_failure_risk',
            ],
        }
        for short_name, expected in expected_edges.items():
            with self.subTest(symbol=short_name):
                item = reuse.explain(self.data, prefix + short_name)
                self.assertEqual(set(item["direct_existing_source_theorem_uses"]), set(expected))
                self.assertEqual(item["role"],
                                 "UNCOUNTED_STATISTICAL_RISK_CALIBRATION_AND_FAILURE_BRIDGES")
                self.assertEqual(item["area"], "V3/Compression/TheoryCompletion/UnifiedClosure")

    def test_native_statistical_scope_and_evidence_binding(self):
        current = self.data["overlays"][4]
        evidence = current["native_export_evidence"]
        artifact = reuse.REPO / evidence["path"]
        native = json.loads(artifact.read_text())
        public = native["public_source_theorems"]
        scope = native["all_native_theorem_constants"]
        self.assertEqual(evidence["sha256"],
                         "9a87e5f99d48cfc7fa95df595d7884837f0dd24253205858f5c27ae22545a63d")
        self.assertEqual(len(public), 73)
        self.assertEqual(len(scope), 126)
        self.assertEqual(sum(row["is_private"] for row in scope), 11)
        native_by_name = {row["name"]: row for row in scope}
        self.assertEqual(len(native_by_name), 126)
        expected_fields = {"name", "source_module", "is_private", "level_parameters",
                           "type", "direct_constants", "direct_theorem_constants", "axioms"}
        for row in scope:
            with self.subTest(native_symbol=row["name"]):
                self.assertEqual(set(row), expected_fields)
                self.assertTrue(set(row["direct_theorem_constants"]) <= set(row["direct_constants"]))
        for row in public:
            with self.subTest(public_symbol=row["name"]):
                native_row = native_by_name[row["name"]]
                for field in ("source_module", "level_parameters", "type", "direct_constants"):
                    self.assertEqual(row[field], native_row[field])
                self.assertTrue(set(row["source_theorem_deps"]) <=
                                set(native_row["direct_theorem_constants"]))
        names = {row["name"] for row in public}
        self.assertEqual(len(names), len(public))
        self.assertEqual(names, {row["name"] for row in current["public_theorems"]})
        self.assertTrue(names <= {row["name"] for row in scope if not row["is_private"]})
        others = [row for row in scope if not row["is_private"] and row["name"] not in names]
        self.assertEqual(len(others), 42)
        owners = {row["module"] for row in current["added_modules"]}
        self.assertEqual({row["source_module"] for row in scope}, owners)
        self.assertTrue(all(row["source_module"] in owners for row in public))
        self.assertTrue(all(set(row["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"}
                            for row in scope))
        original = Path.read_bytes
        def drift(path):
            return b"deliberate statistical native evidence drift" if path == artifact else original(path)
        with mock.patch.object(Path, "read_bytes", drift):
            with self.assertRaisesRegex(RuntimeError, "NATIVE_OVERLAY_EVIDENCE_DRIFT"):
                reuse.verify_evidence_files()

    def test_deployment_joint_overlay_chain_and_source_endpoints(self):
        current = self.data["overlays"][5]
        self.assertEqual(current["base_snapshot_modules"], 646)
        self.assertEqual(current["prior_overlay"]["sha256"], reuse.OVERLAY_SHA256S[4])
        self.assertEqual(len(current["added_modules"]), 4)
        self.assertEqual(len(current["public_theorems"]), 54)
        distinct = current["type_distinctness"]
        self.assertEqual(distinct["registered_prior_theorems"], 3938)
        self.assertEqual(distinct["cross_isDefEq_comparisons"], 212652)
        self.assertEqual(distinct["internal_isDefEq_comparisons"], 1431)
        self.assertEqual(current["proof_dependency_certification"]["registered_direct_edges"], 98)
        lexical = current["lexical_pr_preflight"]
        self.assertEqual(lexical["new_theorems_with_lexical_reuse_candidates"], 13)
        self.assertEqual(lexical["base_public_lexical_theorem_count"], 3939)
        self.assertEqual(lexical["candidate_public_lexical_theorem_count"], 3993)
        self.assertEqual(lexical["candidate_registered_public_source_theorem_count"], 3992)
        self.assertEqual(current["counted_core_impact"], "NONE")
        self.assertEqual(current["scientific_closure"], "NOT_ESTABLISHED")
        prefix = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure."
        expected_edges = {
            "coverage_statistical_selected_joint_failure_risk": [
                "coverage_empirical_registered_microscopic_failure_risk",
                "coverage_registered_source_calibration",
                "selectedTrainingDeployment_failure_le",
            ],
            "statistical_selected_empirical_deployment_risk": [
                "selectedTrainingDeployment_failure_le",
                "statistical_empirical_reference_certificate",
            ],
            "statistical_fixed_policy_training_deployment_witness": [
                "StatisticalRiskWitness.good_sample_exists",
                "StatisticalRiskWitness.microscopic_two_step_risk_on_good",
                "selectedTrainingDeployment_failure_le",
            ],
        }
        for short_name, expected in expected_edges.items():
            with self.subTest(symbol=short_name):
                item = reuse.explain(self.data, prefix + short_name)
                self.assertEqual(set(item["direct_existing_source_theorem_uses"]),
                                 {prefix + name for name in expected})
                self.assertEqual(item["role"],
                                 "UNCOUNTED_REGISTERED_COVERAGE_AND_TRAINING_DEPLOYMENT_BRIDGES")
                self.assertEqual(item["area"], "V3/Compression/TheoryCompletion/UnifiedClosure")

    def test_deployment_joint_registered_calibration_path_and_joint_routes(self):
        prefix = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure."
        terminal = prefix + "coverage_statistical_selected_joint_failure_risk"
        # These are actual proof-constant paths, not module imports. The typed
        # source contracts separately establish the shared P, experiment and E.
        routes = [
            [terminal] + [prefix + name for name in (
                "coverage_registered_source_calibration",
                "coverage_registered_row_calibration",
                "measure_finite_row_calibration_bad_le",
            )] + ["UEOT.V3.BoundedLossTwoSided.measure_exists_candidate_bad_le"],
            [terminal] + [prefix + name for name in (
                "coverage_empirical_registered_microscopic_failure_risk",
                "coverage_same_policy_microscopic_failure_risk",
                "coverage_same_policy_certified_path_error",
                "coverage_same_policy_path_error",
                "coverage_projected_causalLaw_error",
                "coverage_tv_extend_same_kernel",
            )] + ["UEOT.V3.PathError.pmfCommonMass_extend_lower_bound"],
            [terminal] + [prefix + name for name in (
                "selectedTrainingDeployment_failure_le",
                "selectedTrainingDeployment_good_bad_bound",
                "selectedTrainingDeployment_data_dependent_bound",
                "selectedTrainingDeployment_failure_tower",
                "selectedTrainingDeployment_mass",
            )] + ["UEOT.V3.PathError.pmfExtend_apply"],
        ]
        for route in routes:
            for source, target in zip(route, route[1:]):
                with self.subTest(source=source, target=target):
                    self.assertIn(target, reuse.explain(self.data, source)[
                        "direct_existing_source_theorem_uses"])

    def test_native_deployment_joint_scope_law_identity_and_evidence_binding(self):
        current = self.data["overlays"][5]
        evidence = current["native_export_evidence"]
        artifact = reuse.REPO / evidence["path"]
        native = json.loads(artifact.read_text())
        public = native["public_source_theorems"]
        scope = native["all_native_theorem_constants"]
        self.assertEqual(evidence["sha256"],
                         "04058c199ae439fbafb0a659ed78228b3c5e5ab2a4e2444efa6e60d1df588725")
        self.assertEqual(len(public), 54)
        self.assertEqual(len(scope), 93)
        self.assertEqual(sum(row["is_private"] for row in scope), 12)
        native_by_name = {row["name"]: row for row in scope}
        self.assertEqual(len(native_by_name), 93)
        expected_fields = {"name", "source_module", "is_private", "level_parameters",
                           "type", "direct_constants", "direct_theorem_constants", "axioms"}
        for row in scope:
            with self.subTest(native_symbol=row["name"]):
                self.assertEqual(set(row), expected_fields)
                self.assertTrue(set(row["direct_theorem_constants"]) <= set(row["direct_constants"]))
                self.assertTrue(set(row["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"})
        for row in public:
            with self.subTest(public_symbol=row["name"]):
                native_row = native_by_name[row["name"]]
                for field in ("source_module", "level_parameters", "type", "direct_constants"):
                    self.assertEqual(row[field], native_row[field])
                self.assertTrue(set(row["source_theorem_deps"]) <=
                                set(native_row["direct_theorem_constants"]))
        names = {row["name"] for row in public}
        self.assertEqual(len(names), 54)
        self.assertEqual(names, {row["name"] for row in current["public_theorems"]})
        self.assertTrue(names <= {row["name"] for row in scope if not row["is_private"]})
        others = [row for row in scope if not row["is_private"] and row["name"] not in names]
        self.assertEqual(len(others), 27)
        owners = {row["module"] for row in current["added_modules"]}
        self.assertEqual({row["source_module"] for row in scope}, owners)

        prefix = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure."
        empirical = native_by_name[prefix + "statistical_selected_empirical_deployment_risk"]
        self.assertIn("MeasureTheory.Measure.toPMF_toMeasure", empirical["direct_theorem_constants"])
        self.assertIn(prefix + "candidateSourceDeployment", empirical["direct_constants"])
        self.assertIn(prefix + "finiteKernelRowPMF", empirical["direct_constants"])
        self.assertIn(prefix + "selectedTrainingDeployment", empirical["direct_constants"])
        # This public node has no registered edges; its real private helper
        # still reaches the actual pmfExtend theorem in the full native graph.
        reference = native_by_name[prefix + "DeploymentCoverageWitness.reference_one_step_failure"]
        helpers = [native_by_name[name] for name in reference["direct_theorem_constants"]
                   if name in native_by_name and native_by_name[name]["is_private"]
                   and name.endswith(".DeploymentCoverageWitness.referenceLaw_one_apply")]
        self.assertEqual(len(helpers), 1)
        self.assertIn("UEOT.V3.PathError.pmfExtend_apply", helpers[0]["direct_theorem_constants"])
        original = Path.read_bytes
        def drift(path):
            return b"deliberate deployment joint native evidence drift" if path == artifact else original(path)
        with mock.patch.object(Path, "read_bytes", drift):
            with self.assertRaisesRegex(RuntimeError, "NATIVE_OVERLAY_EVIDENCE_DRIFT"):
                reuse.verify_evidence_files()

    def test_overlay_areas_follow_physical_sources(self):
        prefix = "formalization/ueot-core/UEOT/"
        self.assertEqual(reuse.source_area(prefix + "V3/Compression/TheoryCompletion/MinCore/X.lean"),
                         "V3/Compression/TheoryCompletion/MinCore")
        symbol = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.AbsorbingLeakage.row_tv_le"
        item = reuse.explain(self.data, symbol)
        self.assertEqual(item["area"], "V3/Compression/TheoryCompletion/UnifiedClosure")
        for bad in ("/tmp/X.lean", prefix + "../../Outside.lean", "UEOT/V3/Fake.lean", prefix + "X.json"):
            with self.subTest(path=bad):
                with self.assertRaisesRegex(RuntimeError, "INVALID_OVERLAY_SOURCE_PATH"):
                    reuse.source_area(bad)

    def test_native_risk_scope_is_larger_than_public_source_graph(self):
        current = self.data["overlays"][3]
        evidence = current["native_export_evidence"]
        native = json.loads((reuse.REPO / evidence["path"]).read_text())
        self.assertEqual(len(native["public_source_theorems"]), 48)
        scope = native["all_native_theorem_constants"]
        self.assertEqual(len(scope), 75)
        self.assertEqual(sum(row["is_private"] for row in scope), 8)
        names = {row["name"] for row in native["public_source_theorems"]}
        others = [row for row in scope if not row["is_private"] and row["name"] not in names]
        self.assertEqual(len(others), 19)
        owners = {row["module"] for row in current["added_modules"]}
        self.assertTrue(all(row["source_module"] in owners for row in scope))
        self.assertTrue(all(set(row["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"}
                            for row in scope))
        artifact = reuse.REPO / evidence["path"]
        original = Path.read_bytes
        def drift(path):
            return b"deliberate native evidence drift" if path == artifact else original(path)
        with mock.patch.object(Path, "read_bytes", drift):
            with self.assertRaisesRegex(RuntimeError, "NATIVE_OVERLAY_EVIDENCE_DRIFT"):
                reuse.verify_evidence_files()

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
        self.assertEqual(len(live), 650)
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
