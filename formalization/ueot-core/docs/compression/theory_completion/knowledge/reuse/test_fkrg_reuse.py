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
        self.assertEqual(res["module_source_hashes_verified"], 666)
        self.assertEqual(res["ueot_maintained_modules"], 655)
        self.assertEqual(res["vendor_modules"], 11)
        self.assertEqual(res["public_source_theorems_with_direct_proof_graph"], 4147)
        self.assertEqual(res["verified_equal_type_groups"], 37)
        self.assertEqual(res["equal_type_statement_names"], 77)
        self.assertEqual(res["near_type_not_defeq_candidate_pairs"], 15)
        self.assertEqual(res["crossfile_exact_code_clone_candidates"], 68)
        self.assertEqual(res["overlay_public_theorems"], 354)
        self.assertEqual(res["overlay_cross_snapshot_defeq_matches"], 0)
        self.assertEqual(res["overlay_lexical_reuse_candidates"], 75)
        self.assertEqual(res["overlay_count"], 8)
        self.assertEqual(res["overlay_registered_direct_edges"], 531)
        self.assertEqual(res["overlay_historical_public_repairs"], 1)
        self.assertEqual(res["overlay_existing_registered_direct_edge_repairs"], 1)
        self.assertEqual(sum(len(json.loads(row["source_theorem_deps_json"]))
                             for row in self.data["graph"].values()), 5418)

    def test_calibrated_defect_overlay_chain_and_kernel_graph(self):
        self.assertEqual(len(self.data["overlays"]), 8)
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

    def test_support_viability_overlay_scope_and_source_endpoints(self):
        current = self.data["overlays"][6]
        self.assertEqual(current["base_snapshot_modules"], 650)
        self.assertEqual(current["prior_overlay"]["sha256"], reuse.OVERLAY_SHA256S[5])
        self.assertEqual(len(current["added_modules"]), 9)
        self.assertEqual(len(current["public_theorems"]), 102)
        distinct = current["type_distinctness"]
        self.assertEqual(distinct["registered_prior_theorems"], 3992)
        self.assertEqual(distinct["cross_isDefEq_comparisons"], 407184)
        self.assertEqual(distinct["internal_isDefEq_comparisons"], 5151)
        self.assertEqual(distinct["definitionally_equal_matches"], 0)
        self.assertEqual(current["proof_dependency_certification"]["registered_direct_edges"], 163)
        lexical = current["lexical_pr_preflight"]
        self.assertEqual(lexical["new_theorems_with_lexical_reuse_candidates"], 17)
        self.assertEqual(lexical["base_public_lexical_theorem_count"], 3993)
        self.assertEqual(lexical["candidate_public_lexical_theorem_count"], 4095)
        self.assertEqual(lexical["candidate_registered_public_source_theorem_count"], 4094)
        self.assertEqual(current["source_checkpoint_kind"], "FROZEN_SOURCE_CONTENT_BEFORE_GIT_COMMIT")
        self.assertIsNone(lexical["candidate_ref"])
        self.assertEqual(current["counted_core_impact"], "NONE")
        self.assertEqual(current["scientific_closure"], "NOT_ESTABLISHED")
        prefix = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure."
        expected = {
            "PolicyPrefixCongruenceCheck.actual_causalLaw_congr_before": [
                "causalLaw_congr_before"],
            "SupportViabilityClosure.initial_viability_iff_exists_zero_uncovered_policy": [
                "SupportViabilityClosure.viablePolicy_zero_uncovered",
                "SupportViabilityClosure.mem_coarseLaw_zero_support_iff",
                "SupportViabilityClosure.supported_viable_of_zero_uncovered"],
            "ViableRegisteredJointCheck.viable_registered_selected_joint_failure_on_good": [
                "RegisteredGoodJointCheck.registered_selected_joint_failure_of_cap_on_good",
                "SupportViabilityClosure.viablePolicy_zero_uncovered"],
        }
        for short, uses in expected.items():
            with self.subTest(symbol=short):
                item = reuse.explain(self.data, prefix + short)
                self.assertEqual(set(item["direct_existing_source_theorem_uses"]),
                                 {prefix + name for name in uses})
                self.assertEqual(item["role"],
                                 "UNCOUNTED_SUPPORT_VIABILITY_AND_REGISTERED_JOINT_BRIDGES")
                self.assertEqual(item["area"], "V3/Compression/TheoryCompletion/UnifiedClosure")

    def test_support_viability_actual_support_checker_and_joint_routes(self):
        prefix = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure."
        viability = prefix + "SupportViabilityClosure."
        joint = prefix + "RegisteredGoodJointCheck."
        # These are registered compiled proof edges. Their shared source and
        # policy parameters are reviewed separately in the typed contracts.
        routes = [
            [viability + "initial_viability_iff_exists_zero_uncovered_policy",
             viability + "viablePolicy_zero_uncovered",
             viability + "zero_uncovered_iff_support_certified",
             viability + "zero_uncertified_mass_iff_support",
             prefix + "coverage_uncovered_indicator_expectation"],
            [viability + "initial_viability_iff_exists_zero_uncovered_policy",
             viability + "supported_viable_of_zero_uncovered",
             viability + "mem_coarseLaw_succ_support_iff",
             viability + "mem_traceSupport_iff_realized"],
            [viability + "finiteRelationViabilityCheck_correct",
             viability + "finiteRelationViabilityCheck_eq"],
            [viability + "finiteRelationViabilityCheck_correct",
             viability + "finiteViabilityCheck_correct"],
            [joint + "registered_selected_joint_failure_of_cap_on_good",
             joint + "registered_calibration_good_bad_le",
             prefix + "coverage_registered_source_calibration",
             prefix + "coverage_registered_row_calibration",
             prefix + "measure_finite_row_calibration_bad_le"],
            [joint + "registered_selected_joint_failure_of_cap_on_good",
             prefix + "selectedTrainingDeployment_failure_le",
             prefix + "selectedTrainingDeployment_good_bad_bound"],
            [prefix + "RegisteredSelectionWitness.actual_joint_failure_exact",
             prefix + "selectedTrainingDeployment_failure_tower",
             prefix + "selectedTrainingDeployment_mass",
             "UEOT.V3.PathError.pmfExtend_apply"],
        ]
        for route in routes:
            for source, target in zip(route, route[1:]):
                with self.subTest(source=source, target=target):
                    self.assertIn(target, reuse.explain(self.data, source)[
                        "direct_existing_source_theorem_uses"])

    def test_support_viability_full_native_and_retained_private_computations(self):
        current = self.data["overlays"][6]
        evidence = current["native_export_evidence"]
        self.assertEqual(evidence["sha256"],
                         "34376e2c8564d148e5dcd4452ab0dddeb9aa20bbb1b9d0f7c88c194b9b82baca")
        native = json.loads((reuse.REPO / evidence["path"]).read_text())
        scope = native["all_native_theorem_constants"]
        public = native["public_source_theorems"]
        self.assertEqual(len(scope), 219)
        self.assertEqual(len(public), 102)
        self.assertEqual(sum(row["is_private"] for row in scope), 22)
        by_name = {row["name"]: row for row in scope}
        public_names = {row["name"] for row in public}
        self.assertEqual(len(by_name), 219)
        self.assertEqual(len(public_names), 102)
        self.assertEqual(public_names, {row["name"] for row in current["public_theorems"]})
        self.assertEqual(sum(not row["is_private"] and row["name"] not in public_names
                             for row in scope), 95)
        self.assertEqual({row["source_module"] for row in scope},
                         {row["module"] for row in current["added_modules"]})
        expected_fields = {"name", "source_module", "is_private", "level_parameters",
                           "type", "direct_constants", "direct_theorem_constants", "axioms"}
        for row in scope:
            with self.subTest(native_symbol=row["name"]):
                self.assertEqual(set(row), expected_fields)
                self.assertTrue(set(row["direct_theorem_constants"]) <= set(row["direct_constants"]))
                self.assertTrue(set(row["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"})
        for row in public:
            with self.subTest(public_symbol=row["name"]):
                native_row = by_name[row["name"]]
                self.assertFalse(native_row["is_private"])
                for field in ("source_module", "level_parameters", "type", "direct_constants"):
                    self.assertEqual(row[field], native_row[field])
                self.assertTrue(set(row["source_theorem_deps"]) <=
                                set(native_row["direct_theorem_constants"]))
        prefix = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure."
        helpers = {
            "SupportViabilityClosure.SafePrefixDeadend.initial_checker_pass": (
                "ControlCoverageWitness",
                ["SupportViabilityClosure.SafePrefixDeadend.a_complete_zero_uncovered_policy_exists"]),
            "SupportViabilityClosure.SafePrefixDeadend.good_successor_checker_pass": (
                "ControlCoverageWitness", []),
            "RegisteredSelectionWitness.allTrue_selects_true": (
                "RegisteredDeploymentRiskWitness", ["RegisteredSelectionWitness.allTrue_checkedBudget"]),
        }
        # Three actual closed-computation collisions were fixed by a private
        # API boundary. Their native theorem records must never disappear.
        for short, (owner, users) in helpers.items():
            with self.subTest(private_helper=short):
                old_public_name = prefix + short
                self.assertNotIn(old_public_name, public_names)
                records = [row for row in scope
                           if row["name"].endswith("." + old_public_name)]
                self.assertEqual(len(records), 1)
                helper = records[0]
                self.assertTrue(helper["is_private"])
                self.assertEqual(helper["source_module"], prefix + owner)
                actual_users = {row["name"] for row in scope
                                if helper["name"] in row["direct_theorem_constants"]}
                self.assertEqual(actual_users, {prefix + name for name in users})

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

    def test_registered_interfaces_scope_and_same_source_proof_routes(self):
        current = self.data["overlays"][7]
        self.assertEqual(current["base_snapshot_modules"], 659)
        self.assertEqual(current["prior_overlay"]["sha256"], reuse.OVERLAY_SHA256S[6])
        self.assertEqual(len(current["added_modules"]), 7)
        self.assertEqual(len(current["public_theorems"]), 53)
        distinct = current["type_distinctness"]
        self.assertEqual(distinct["new_source_public_theorem_count"], 52)
        self.assertEqual(distinct["historical_public_repair_count"], 1)
        self.assertEqual(distinct["registered_prior_theorems"], 4094)
        self.assertEqual(distinct["cross_isDefEq_comparisons"], 216982)
        self.assertEqual(distinct["internal_isDefEq_comparisons"], 1378)
        self.assertEqual(distinct["new_source_to_historical_repair_isDefEq_comparisons"], 52)
        self.assertEqual(current["proof_dependency_certification"]["registered_direct_edges"], 97)
        self.assertEqual(current["lexical_pr_preflight"]["new_theorems_with_lexical_reuse_candidates"], 18)
        prefix = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure."
        viable = reuse.explain(self.data, prefix +
                              "ViableVariableRegisteredJointCheck.viable_registered_selected_joint_failure_on_good")
        self.assertEqual(set(viable["direct_existing_source_theorem_uses"]), {
            prefix + "SupportViabilityClosure.viablePolicy_zero_uncovered",
            prefix + "VariableRegisteredJointCheck.registered_selected_joint_failure_of_cap_on_good",
        })
        joint = reuse.explain(self.data, prefix +
                             "VariableRegisteredJointCheck.registered_selected_joint_failure_of_cap_on_good")
        self.assertIn(prefix + "ArbitraryObservationRiskCheck.coverage_arbitrary_observation_microscopic_failure_risk",
                      joint["direct_existing_source_theorem_uses"])
        self.assertIn(prefix + "selectedTrainingDeployment_failure_le",
                      joint["direct_existing_source_theorem_uses"])
        path = reuse.explain(self.data, prefix +
                            "ArbitraryObservationRiskCheck.factorized_same_policy_path_error")
        self.assertIn(prefix + "coverage_same_policy_path_error",
                      path["direct_existing_source_theorem_uses"])
        self.assertIn(prefix + "PathObservationEscapeCheck.escape_path_tv",
                      path["direct_existing_source_theorem_uses"])

    def test_registered_interfaces_full_native_owner_axiom_and_edge_binding(self):
        current = self.data["overlays"][7]
        evidence = current["native_export_evidence"]
        artifact = reuse.REPO / evidence["path"]
        self.assertEqual(reuse.sha256(artifact.read_bytes()).hexdigest(),
                         "75945bbff2e0212a406f27859c68a777bc3deba75b0b8aece66c84236b5e39c1")
        self.assertEqual(evidence["sha256"], reuse.sha256(artifact.read_bytes()).hexdigest())
        native = json.loads(artifact.read_text())
        scope = native["all_native_theorem_constants"]
        public = native["public_source_theorems"]
        self.assertEqual(native["collisions"], [])
        self.assertEqual(len(scope), 92)
        self.assertEqual(sum(row["is_private"] for row in scope), 17)
        self.assertEqual(len({row["source_module"] for row in scope}), 8)
        self.assertEqual(len(public), 53)
        fields = {"name", "source_module", "is_private", "level_parameters", "type",
                  "direct_constants", "direct_theorem_constants", "axioms"}
        by_name = {row["name"]: row for row in scope}
        self.assertEqual(len(by_name), len(scope))
        registered_names = set(self.data["graph"])
        for row in scope:
            with self.subTest(symbol=row["name"]):
                self.assertTrue(fields <= row.keys())
                self.assertTrue(set(row["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"})
        overlay_public = {row["name"]: row for row in current["public_theorems"]}
        self.assertEqual(set(overlay_public), {row["name"] for row in public})
        for row in public:
            with self.subTest(public_symbol=row["name"]):
                full = by_name[row["name"]]
                self.assertFalse(full["is_private"])
                self.assertEqual(row["source_module"], full["source_module"])
                actual = (set(full["direct_constants"]) & registered_names) - {row["name"]}
                self.assertEqual(set(overlay_public[row["name"]]["source_theorem_deps"]), actual)
        self.assertEqual(sum(len(row["source_theorem_deps"]) for row in overlay_public.values()), 97)

    def test_historical_apostrophe_registration_and_existing_incoming_edge(self):
        current = self.data["overlays"][7]
        helper = "UEOT.V3.FreeInformationValue.integrable_finset_sup'"
        caller = "UEOT.V3.FreeInformationValue.p_ref_03"
        self.assertEqual({row["name"] for row in current["historical_public_repairs"]}, {helper})
        self.assertEqual(reuse.explain(self.data, helper)["role"],
                         "HISTORICAL_PUBLIC_DECLARATION_REPAIR_UNCOUNTED")
        self.assertEqual(reuse.explain(self.data, caller)["direct_existing_source_theorem_uses"], [helper])
        self.assertIn(caller, self.data["incoming"][helper])
        repairs = current["existing_proof_dependency_repairs"]
        self.assertEqual(len(repairs), 1)
        self.assertEqual(repairs[0]["name"], caller)
        self.assertEqual(repairs[0]["prior_source_theorem_deps"], [])
        self.assertEqual(repairs[0]["added_source_theorem_deps"], [helper])
        self.assertEqual(repairs[0]["actual_source_theorem_deps"], [helper])
        cert = current["existing_proof_dependency_repair_certification"]
        self.assertEqual(cert["registered_theorems_scanned"], 4094)
        self.assertEqual(cert["added_registered_direct_edges"], 1)
        historical = reuse.read_csv(reuse.AUDIT / "all_3793_theorem_direct_reuse_graph.csv")
        historical_caller = next(row for row in historical if row["name"] == caller)
        self.assertEqual(json.loads(historical_caller["source_theorem_deps_json"]), [])
        self.assertFalse(any(row["name"] == helper for row in historical))

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
        self.assertEqual(len(live), 666)
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


class AdditiveHistoricalRepairTests(unittest.TestCase):
    """Synthetic structure checks; these fixtures are not Lean/native evidence."""

    def setUp(self):
        from hashlib import sha256
        from tempfile import TemporaryDirectory
        self.temporary = TemporaryDirectory(prefix="synthetic-repair-", dir=HERE)
        self.addCleanup(self.temporary.cleanup)
        self.repo = Path(self.temporary.name)
        self.owner = "UEOT.V3.SyntheticRepairFixture"
        self.path = "formalization/ueot-core/UEOT/V3/SyntheticRepairFixture.lean"
        source = self.repo / self.path
        source.parent.mkdir(parents=True)
        source.write_text("-- SYNTHETIC UNIT FIXTURE ONLY: no Lean theorem is asserted.\n")
        self.source_sha = sha256(source.read_bytes()).hexdigest()
        self.old = self.owner + ".old"
        self.prior = self.owner + ".priorDependency"
        self.helper = self.owner + ".historicalHelper'"
        self.fresh = "UEOT.V3.SyntheticNewFixture.fresh"
        self.prior_names = {self.old, self.prior}
        self.prior_modules = {self.path:{"path":self.path, "module":self.owner,
                                        "content_sha256":self.source_sha}}
        def graph_row(name, deps, line):
            return {"name":name,"path":self.path,"line":str(line),
                    "source_theorem_deps_json":json.dumps(deps),
                    "direct_existing_source_theorem_deps":str(len(deps)),
                    "all_direct_project_scoped_constants":"2"}
        self.rows = [graph_row(self.old,[self.prior],2),graph_row(self.prior,[],3),
                     graph_row(self.helper,[],4),graph_row(self.fresh,[self.old],5)]
        self.overlay = {
            "overlay_id":"SYNTHETIC_STRUCTURE_ONLY",
            "source_checkpoint":"SYNTHETIC_STRUCTURE_ONLY",
            "public_theorems":[
                {"name":self.helper,"path":self.path,"line":4,
                 "registration_kind":"historical_public_repair","source_theorem_deps":[]},
                {"name":self.fresh,"path":self.path,"line":5,
                 "registration_kind":"new_source_public","source_theorem_deps":[self.old]}],
            "historical_public_repairs":[
                {"name":self.helper,"path":self.path,"module":self.owner,
                 "content_sha256":self.source_sha}],
            "existing_proof_dependency_repairs":[
                {"name":self.old,"path":self.path,"line":2,"source_module":self.owner,
                 "content_sha256":self.source_sha,"prior_source_theorem_deps":[self.prior],
                 "added_source_theorem_deps":[self.helper],
                 "actual_source_theorem_deps":[self.prior,self.helper]}],
            "type_distinctness":{"status":"PASS","definitionally_equal_matches":0},
            "native_axiom_census":{"status":"PASS"},
            "proof_dependency_certification":{"status":"PASS","registered_direct_edges":1},
            "historical_public_repair_certification":{
                "status":"PASS","historical_registered_base":2,
                "historical_public_repairs":1,"new_source_public_theorems":1},
            "existing_proof_dependency_repair_certification":{
                "status":"PASS","registered_theorems_scanned":2,
                "historical_public_repair_targets":[self.helper],
                "repaired_existing_nodes":1,"added_registered_direct_edges":1},
            "lexical_pr_preflight":{"new_theorems_with_lexical_reuse_candidates":0},
        }
        self.native = {
            "schema":"REGISTERED_INTERFACES_NATIVE_EXPORT_V1","collisions":[],
            "registered_prior_theorems":2,
            "public_source_theorems":[
                {"name":self.helper,"registration_kind":"historical_public_repair","source_module":self.owner},
                {"name":self.fresh,"registration_kind":"new_source_public","source_module":self.owner}],
            "all_native_theorem_constants":[
                {"name":self.helper,"source_module":self.owner,"is_private":False},
                {"name":self.old,"source_module":self.owner,"direct_constants":[self.prior,self.helper]}],
            "historical_repair_incoming_scan":{
                "registered_theorems_scanned":2,"historical_public_repair_targets":[self.helper],
                "incoming_rows":[{"name":self.old,"source_module":self.owner,
                    "direct_constants":[self.prior,self.helper],"historical_repair_deps":[self.helper],
                    "actual_source_theorem_deps":[self.prior,self.helper]}]},
        }
        self.native_path = "formalization/ueot-core/docs/compression/theory_completion/knowledge/reuse/SYNTHETIC_STRUCTURE_ONLY.json"
        (self.repo / self.native_path).parent.mkdir(parents=True)
        self.bind_native()

    def bind_native(self):
        from hashlib import sha256
        artifact = self.repo / self.native_path
        artifact.write_text(json.dumps(self.native))
        self.overlay["native_export_evidence"] = {
            "path":self.native_path,"sha256":sha256(artifact.read_bytes()).hexdigest()}

    def apply(self):
        reuse.apply_existing_proof_dependency_repairs(
            self.rows,self.overlay,self.prior_names,self.prior_modules,repo=self.repo)

    def test_additive_repair_preserves_prior_edges_and_separate_counts(self):
        self.apply()
        self.assertEqual(set(json.loads(self.rows[0]["source_theorem_deps_json"])),
                         {self.prior,self.helper})
        self.assertEqual(self.rows[0]["direct_existing_source_theorem_deps"],"2")
        self.assertEqual(self.rows[0]["all_direct_project_scoped_constants"],"2")
        self.assertEqual(self.rows[0]["additive_dependency_repair_provenance"][0][
            "prior_source_theorem_deps"],[self.prior])
        data = {"overlays":[self.overlay],"modules":[],
                "graph":{r["name"]:r for r in self.rows},"groups":[],"duplicates":{},
                "near":[],"clones":[]}
        summary = reuse.status(data)
        self.assertEqual(summary["overlay_registered_direct_edges"],1)
        self.assertEqual(summary["overlay_existing_registered_direct_edge_repairs"],1)
        self.assertEqual(summary["overlay_historical_public_repairs"],1)

    def test_repair_rejects_prior_edge_deletion(self):
        self.overlay["existing_proof_dependency_repairs"][0]["prior_source_theorem_deps"] = []
        with self.assertRaisesRegex(RuntimeError,"PRIOR_EDGE_MISMATCH"):
            self.apply()
        self.assertEqual(json.loads(self.rows[0]["source_theorem_deps_json"]),[self.prior])

    def test_repair_rejects_missing_prior_edge_in_actual_proof(self):
        self.native["historical_repair_incoming_scan"]["incoming_rows"][0]["actual_source_theorem_deps"] = [self.helper]
        self.bind_native()
        with self.assertRaisesRegex(RuntimeError,"ACTUAL_PROOF_EDGE_MISMATCH"):
            self.apply()

    def test_repair_rejects_fake_delta_absent_from_native_constants(self):
        self.native["historical_repair_incoming_scan"]["incoming_rows"][0]["direct_constants"] = [self.prior]
        self.bind_native()
        with self.assertRaisesRegex(RuntimeError,"FALSE_OR_NONADDITIVE_DELTA"):
            self.apply()

    def test_repair_rejects_delta_outside_historical_targets(self):
        self.overlay["existing_proof_dependency_repairs"][0]["added_source_theorem_deps"] = [self.fresh]
        with self.assertRaisesRegex(RuntimeError,"FALSE_OR_NONADDITIVE_DELTA"):
            self.apply()

    def test_repair_rejects_nonprevious_caller(self):
        self.overlay["existing_proof_dependency_repairs"][0]["name"] = self.fresh
        self.native["historical_repair_incoming_scan"]["incoming_rows"][0]["name"] = self.fresh
        self.bind_native()
        with self.assertRaisesRegex(RuntimeError,"CALLER_NOT_PREVIOUSLY_REGISTERED"):
            self.apply()

    def test_repair_rejects_source_hash_mismatch(self):
        self.overlay["existing_proof_dependency_repairs"][0]["content_sha256"] = "0" * 64
        with self.assertRaisesRegex(RuntimeError,"SOURCE_HASH_MISMATCH"):
            self.apply()

    def test_repair_rejects_actual_source_byte_drift(self):
        (self.repo / self.path).write_text("-- changed synthetic source bytes\n")
        with self.assertRaisesRegex(RuntimeError,"SOURCE_HASH_MISMATCH"):
            self.apply()

    def test_repair_rejects_unregistered_target(self):
        self.rows = [row for row in self.rows if row["name"] != self.helper]
        with self.assertRaisesRegex(RuntimeError,"UNREGISTERED_TARGET"):
            self.apply()

    def test_repair_rejects_pending_proof_status(self):
        keys = ("type_distinctness","proof_dependency_certification","native_axiom_census",
                "historical_public_repair_certification","existing_proof_dependency_repair_certification")
        for key in keys:
            with self.subTest(key=key):
                self.overlay[key]["status"] = "PENDING"
                with self.assertRaisesRegex(RuntimeError,"REPAIR_NOT_CERTIFIED"):
                    self.apply()
                self.overlay[key]["status"] = "PASS"

    def test_repair_rejects_changed_native_artifact_hash(self):
        self.overlay["native_export_evidence"]["sha256"] = "0" * 64
        with self.assertRaisesRegex(RuntimeError,"NATIVE_EVIDENCE_DRIFT"):
            self.apply()

    def test_repair_rejects_unapplied_actual_incoming_caller(self):
        extra = dict(self.native["historical_repair_incoming_scan"]["incoming_rows"][0])
        extra["name"] = self.prior
        self.native["historical_repair_incoming_scan"]["incoming_rows"].append(extra)
        self.bind_native()
        with self.assertRaisesRegex(RuntimeError,"INCOMING_CALLER_SET_MISMATCH"):
            self.apply()

    def test_repair_rejects_wrong_owner_and_duplicate_caller(self):
        self.overlay["existing_proof_dependency_repairs"][0]["source_module"] = "Wrong.Owner"
        with self.assertRaisesRegex(RuntimeError,"CALLER_OWNER_MISMATCH"):
            self.apply()
        self.overlay["existing_proof_dependency_repairs"][0]["source_module"] = self.owner
        self.overlay["existing_proof_dependency_repairs"].append(
            dict(self.overlay["existing_proof_dependency_repairs"][0]))
        with self.assertRaisesRegex(RuntimeError,"INVALID_NAME_LIST"):
            self.apply()

    def test_legacy_overlay_without_repairs_is_unchanged(self):
        before = json.dumps(self.rows,sort_keys=True)
        reuse.apply_existing_proof_dependency_repairs(
            self.rows,{},self.prior_names,self.prior_modules,repo=self.repo)
        self.assertEqual(json.dumps(self.rows,sort_keys=True),before)


if __name__ == "__main__":
    unittest.main(verbosity=2)
