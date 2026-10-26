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
        self.assertEqual(res["module_source_hashes_verified"], 701)
        self.assertEqual(res["ueot_maintained_modules"], 690)
        self.assertEqual(res["vendor_modules"], 11)
        self.assertEqual(res["public_source_theorems_with_direct_proof_graph"], 4463)
        self.assertEqual(res["verified_equal_type_groups"], 37)
        self.assertEqual(res["equal_type_statement_names"], 77)
        self.assertEqual(res["near_type_not_defeq_candidate_pairs"], 15)
        self.assertEqual(res["crossfile_exact_code_clone_candidates"], 68)
        self.assertEqual(res["overlay_public_theorems"], 670)
        self.assertEqual(res["overlay_cross_snapshot_defeq_matches"], 0)
        self.assertEqual(res["overlay_lexical_reuse_candidates"], 177)
        self.assertEqual(res["overlay_count"], 15)
        self.assertEqual(res["overlay_registered_direct_edges"], 1020)
        self.assertEqual(res["overlay_historical_public_repairs"], 1)
        self.assertEqual(res["overlay_existing_registered_direct_edge_repairs"], 1)
        self.assertEqual(sum(len(json.loads(row["source_theorem_deps_json"]))
                             for row in self.data["graph"].values()), 5907)

    def test_calibrated_defect_overlay_chain_and_kernel_graph(self):
        self.assertEqual(len(self.data["overlays"]), 15)
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

    def test_longterm_overlay_native_owner_types_and_edge_binding(self):
        current = self.data["overlays"][8]
        self.assertEqual(current["base_snapshot_modules"], 666)
        self.assertEqual(current["prior_overlay"]["sha256"], reuse.OVERLAY_SHA256S[7])
        self.assertEqual(len(current["added_modules"]), 12)
        self.assertEqual(len(current["public_theorems"]), 90)
        self.assertNotIn("historical_public_repairs", current)
        self.assertNotIn("existing_proof_dependency_repairs", current)
        self.assertEqual(current["counted_core_impact"], "NONE")
        self.assertEqual(current["scientific_closure"], "NOT_ESTABLISHED")
        self.assertEqual(current["lexical_pr_preflight"]["new_theorems_with_lexical_reuse_candidates"], 27)
        distinct = current["type_distinctness"]
        self.assertEqual(distinct["registered_prior_theorems"], 4147)
        self.assertEqual(distinct["cross_isDefEq_comparisons"], 373230)
        self.assertEqual(distinct["internal_isDefEq_comparisons"], 4005)
        evidence = current["native_export_evidence"]
        artifact = reuse.REPO / evidence["path"]
        self.assertEqual(reuse.sha256(artifact.read_bytes()).hexdigest(),
                         "0b6b77967ad43da71cec3a569b361501f591a7a8b384d072dda31af1b897d02c")
        native = json.loads(artifact.read_text())
        self.assertEqual(native["collisions"], [])
        scope = native["all_native_theorem_constants"]
        self.assertEqual(len(scope), 199)
        self.assertEqual(sum(row["is_private"] for row in scope), 30)
        self.assertEqual({row["source_module"] for row in scope},
                         {row["module"] for row in current["added_modules"]})
        by_name = {row["name"]: row for row in scope}
        self.assertEqual(len(by_name), len(scope))
        for row in scope:
            self.assertTrue(set(row["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"})
        public = {row["name"]: row for row in current["public_theorems"]}
        self.assertEqual(set(public), {row["name"] for row in native["public_source_theorems"]})
        for name, row in public.items():
            self.assertFalse(by_name[name]["is_private"])
            self.assertEqual(row["source_module"], by_name[name]["source_module"])
            actual = (set(by_name[name]["direct_constants"]) & set(self.data["graph"])) - {name}
            self.assertEqual(set(row["source_theorem_deps"]), actual)
        self.assertEqual(sum(len(row["source_theorem_deps"]) for row in public.values()), 149)

    def test_longterm_same_source_reuse_and_sisc_physical_owner(self):
        prefix = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure."
        def uses(name):
            return set(reuse.explain(self.data, name)["direct_existing_source_theorem_uses"])
        self.assertNotIn(prefix + "SameSourceKilledExitFluxCheck.actual_survival_zero", self.data["graph"])
        self.assertIn(prefix + "SameSourceConditionedTerminalCheck.actual_survival_mass_at_zero",
                      uses(prefix + "SameSourceKilledExitFluxCheck.actual_failure_mass_telescope"))
        self.assertIn(prefix + "SameSourceSafePrefixCheck.homogeneous_survival_real_eq_killed_pow_sum",
                      uses(prefix + "SameSourceSurvivalTailCheck.killed_survival_mass_tendsto_homogeneous_neverHit_real"))
        policy = prefix + "SupportViabilityClosure."
        self.assertEqual(uses(policy + "arbitrarily_long_zero_uncovered_iff_single_all_times_policy"), {
            policy + "initial_infiniteViability_iff_exists_all_times_zero_uncovered_policy",
            policy + "initial_viability_iff_exists_zero_uncovered_policy",
        })
        sisc = "UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC."
        calibrated = sisc + "rowwise_protocol_calibrated_on_good"
        self.assertIn(sisc + "rowwise_population_risk_eq_registered", uses(calibrated))
        self.assertEqual(reuse.explain(self.data, calibrated)["area"],
                         "V3/Compression/TheoryCompletion/UnifiedClosure")
        self.assertIn(prefix + "RowwiseProbeSampling.measure_coordinateGood_compl_le",
                      uses(sisc + "measure_rowwise_failure_to_identify_le"))
        self.assertIn(sisc + "measure_rowwise_failure_to_identify_le",
                      uses(prefix + "SISCRowwiseProbeWitness.actual_product_candidate_power"))
        self.assertIn(prefix + "SISCRowwiseProbeWitness.exact_data_good_does_not_calibrate_wrong_kernel",
                      self.data["graph"])

    def test_finite_memory_native_ownership_types_and_registered_edges(self):
        current = self.data["overlays"][9]
        self.assertEqual(current["base_snapshot_modules"], 678)
        self.assertEqual(current["prior_overlay"]["sha256"], reuse.OVERLAY_SHA256S[8])
        self.assertEqual(current["baseline_ref"], "299a4e3a71914af064ccd7916bb285bac201f62a")
        self.assertEqual(current["source_checkpoint"], "worktree-sha256:179783b20a817affae721d2f1ad36c4fcb25763cbb91701c120b68351b103ae6")
        self.assertEqual(current["source_checkpoint_kind"], "FROZEN_SOURCE_CONTENT_BEFORE_GIT_COMMIT")
        self.assertEqual(current["scientific_role"], "UNCOUNTED_FINITE_SUPPORT_MEMORY_CONTROL")
        self.assertEqual(current["counted_core_impact"], "NONE")
        self.assertEqual(current["scientific_closure"], "NOT_ESTABLISHED")
        self.assertNotIn("historical_public_repairs", current)
        self.assertNotIn("existing_proof_dependency_repairs", current)
        prefix = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure."
        modules = {prefix + name for name in (
            "FiniteMemoryPolicy", "FiniteSupportFixedPoint", "SupportMemoryController",
            "SupportMemoryCheck", "FiniteMemorySeparation", "FiniteMemoryCheckWitness")}
        self.assertEqual({row["module"] for row in current["added_modules"]}, modules)
        self.assertEqual(len(current["added_modules"]), 6)
        self.assertEqual(len(current["public_theorems"]), 35)
        self.assertEqual(current["lexical_pr_preflight"]["new_theorems_with_lexical_reuse_candidates"], 6)
        distinct = current["type_distinctness"]
        self.assertEqual(distinct["registered_prior_theorems"], 4237)
        self.assertEqual(distinct["cross_isDefEq_comparisons"], 148295)
        self.assertEqual(distinct["internal_isDefEq_comparisons"], 595)
        self.assertEqual(distinct["definitionally_equal_matches"], 0)
        evidence = current["native_export_evidence"]
        artifact = reuse.REPO / evidence["path"]
        self.assertEqual(reuse.sha256(artifact.read_bytes()).hexdigest(), "5a06a9df4a662327e48e34f2743f485fb7471f86f99e18fd71d6feceb7eaa471")
        self.assertEqual(evidence["sha256"], "5a06a9df4a662327e48e34f2743f485fb7471f86f99e18fd71d6feceb7eaa471")
        native = json.loads(artifact.read_text())
        self.assertEqual(native["schema"], "FINITE_MEMORY_NATIVE_EXPORT_V1")
        self.assertEqual(native["collisions"], [])
        scope = native["all_native_theorem_constants"]
        self.assertEqual(len(scope), 82)
        self.assertEqual(sum(row["is_private"] for row in scope), 22)
        self.assertEqual({row["source_module"] for row in scope}, modules)
        by_name = {row["name"]: row for row in scope}
        self.assertEqual(len(by_name), len(scope))
        fields = {"name", "source_module", "is_private", "level_parameters", "type",
                  "direct_constants", "direct_theorem_constants", "axioms"}
        for row in scope:
            with self.subTest(native_symbol=row["name"]):
                self.assertTrue(fields <= row.keys())
                self.assertTrue(set(row["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"})
                self.assertTrue(set(row["direct_theorem_constants"]) <= set(row["direct_constants"]))
        public = {row["name"]: row for row in current["public_theorems"]}
        native_public = {row["name"]: row for row in native["public_source_theorems"]}
        self.assertEqual(len(native_public), 35)
        self.assertEqual(set(public), set(native_public))
        # This generic controller module has generated native theorem constants
        # even though it contributes no explicit public theorem candidate.
        policy_owner = prefix + "FiniteMemoryPolicy"
        self.assertTrue(any(row["source_module"] == policy_owner for row in scope))
        self.assertFalse(any(row["source_module"] == policy_owner for row in public.values()))
        for name, row in public.items():
            with self.subTest(public_symbol=name):
                full = by_name[name]
                self.assertFalse(full["is_private"])
                self.assertEqual(row["source_module"], full["source_module"])
                for field in ("source_module", "level_parameters", "type", "direct_constants"):
                    self.assertEqual(native_public[name][field], full[field])
                self.assertEqual(set(row["source_theorem_deps"]),
                                 set(native_public[name]["source_theorem_deps"]))
                actual = (set(full["direct_constants"]) & set(self.data["graph"])) - {name}
                self.assertEqual(set(row["source_theorem_deps"]), actual)
        self.assertEqual(sum(len(row["source_theorem_deps"]) for row in public.values()), 47)
        original = Path.read_bytes

        def drift(path):
            return b"deliberate finite memory native drift" if path == artifact else original(path)

        with mock.patch.object(Path, "read_bytes", drift):
            with self.assertRaisesRegex(RuntimeError, "NATIVE_OVERLAY_EVIDENCE_DRIFT"):
                reuse.load(verify_source=False)

    def test_finite_memory_same_source_checker_and_controller_reuse(self):
        prefix = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure."
        support = prefix + "SupportViabilityClosure."

        def uses(name):
            return set(reuse.explain(self.data, name)["direct_existing_source_theorem_uses"])

        self.assertIn(support + "initial_viability_iff_exists_zero_uncovered_policy",
                      uses(support + "bounded_horizon_iff_all_times_zero_uncovered"))
        self.assertIn(support + "supportMemoryController_zero_uncovered",
                      uses(support + "bounded_horizon_iff_all_times_zero_uncovered"))
        self.assertIn(support + "zero_uncovered_iff_support_certified",
                      uses(support + "supportMemoryController_zero_uncovered"))
        self.assertIn(support + "finiteRelationViabilityCheck_correct",
                      uses(support + "finiteMemoryCheck_iff_initial_winning"))
        self.assertIn(support + "supportIterate_eq_winning_of_card_le",
                      uses(support + "finiteMemoryCheck_iff_initial_winning"))
        self.assertIn(support + "bounded_horizon_iff_all_times_zero_uncovered",
                      uses(support + "finiteMemoryCheck_iff_exists_all_times_policy"))
        self.assertIn(support + "finiteMemoryCheck_iff_controller_zero_uncovered",
                      uses(prefix + "FiniteMemoryCheckWitness.checked_support_controller_zero_uncovered"))
        self.assertIn(support + "finiteMemoryCheck_iff_exists_all_times_policy",
                      uses(prefix + "FiniteMemoryCheckWitness.mixed_initial_has_no_all_times_policy"))
        self.assertIn(prefix + "FiniteMemorySeparation.stationary_uncovered_zero_add_one",
                      uses(prefix + "FiniteMemorySeparation.stationary_feedback_cannot_certify_two_rows"))
        checked = reuse.explain(self.data, support + "finiteMemoryCheck_iff_controller_zero_uncovered")
        self.assertTrue(checked["file"].endswith("/UnifiedClosure/SupportMemoryCheck.lean"))
        self.assertEqual(checked["area"], "V3/Compression/TheoryCompletion/UnifiedClosure")
        for definition in (prefix + "FiniteMemoryController.policy",
                           support + "supportMemoryController", support + "finiteMemoryCheck"):
            self.assertNotIn(definition, self.data["graph"])

    def test_finite_memory_registration_preserves_raw_execution_and_metadata_scope(self):
        current = self.data["overlays"][9]
        provenance = current["registration_provenance"]
        additions = {"lexical_pr_preflight", "registration_provenance"}
        self.assertEqual(provenance["schema"], "FINITE_MEMORY_REGISTRATION_PROVENANCE_V1")
        self.assertEqual(set(provenance["metadata_additions_only"]), additions)
        self.assertTrue(provenance["raw_evidence_bytes_preserved"])
        self.assertFalse(provenance["consumer_registry_modified"])
        self.assertEqual(provenance["git_object_pr_preflight"], "NOT_PERFORMED_SEPARATE_GATE")
        self.assertEqual(provenance["source_tree_sha256"], "179783b20a817affae721d2f1ad36c4fcb25763cbb91701c120b68351b103ae6")
        self.assertEqual(provenance["baseline_ref"], "299a4e3a71914af064ccd7916bb285bac201f62a")
        inputs = provenance["inputs"]
        self.assertEqual(len({(row["role"], row["path"]) for row in inputs}), len(inputs))
        for row in inputs:
            with self.subTest(archived_input=row["path"]):
                path = reuse.REPO / row["path"]
                self.assertTrue(path.resolve().is_relative_to(reuse.REPO.resolve()))
                self.assertEqual(reuse.sha256(path.read_bytes()).hexdigest(), row["sha256"])
        raw_rows = [row for row in inputs if row["role"] == "actual_native_output"
                    and row["path"].endswith("/FINITE_MEMORY_REUSE_OVERLAY_V1.json")]
        self.assertEqual(len(raw_rows), 1)
        raw_path = reuse.REPO / raw_rows[0]["path"]
        raw = json.loads(raw_path.read_text())
        self.assertEqual(set(current) - set(raw), additions)
        self.assertEqual({k: v for k, v in current.items() if k not in additions}, raw)
        archive = raw_path.parent
        self.assertEqual((archive / "REGISTERED_OVERLAY.json").read_bytes(),
                         reuse.OVERLAY_PATHS[9].read_bytes())
        receipt = json.loads((archive / "REGISTRATION_RECEIPT.json").read_text())
        self.assertEqual(receipt["schema"], "FINITE_MEMORY_REGISTRATION_RECEIPT_V1")
        self.assertEqual(receipt["state"], "PASS_METADATA_ONLY_CONSUMER_UNCHANGED")
        self.assertEqual(receipt["raw_overlay_sha256"], raw_rows[0]["sha256"])
        self.assertEqual(receipt["registered_overlay"]["sha256"], reuse.OVERLAY_SHA256S[9])
        self.assertEqual(set(receipt["added_top_level_keys"]), additions)
        self.assertTrue(receipt["stripped_registered_json_equals_raw"])
        self.assertIsNone(receipt["candidate_ref"])
        self.assertEqual(receipt["input_files"], inputs)
        preflight = json.loads((archive / "SOURCE_PREFLIGHT.json").read_text())
        self.assertEqual(preflight["status"], "PENDING_ACTUAL_NATIVE_EXECUTION")
        self.assertEqual(preflight["source_tree_sha256"], "179783b20a817affae721d2f1ad36c4fcb25763cbb91701c120b68351b103ae6")
        self.assertEqual(preflight["complete_source_modules"], 684)
        self.assertEqual(preflight["added_modules"], current["added_modules"])
        execution = json.loads((archive / "STATUS.json").read_text())
        self.assertEqual(execution["state"], "PASS_PENDING_INDEPENDENT_REVIEW_AND_REGISTRATION")
        self.assertTrue(current["native_execution"]["fixed_export_equals_initial_native_export"])
        self.assertEqual(json.loads((archive / "observed_first_native.json").read_text()),
                         json.loads((reuse.REPO / current["native_export_evidence"]["path"]).read_text()))
        lexical = current["lexical_pr_preflight"]
        self.assertIsNone(lexical["candidate_ref"])
        self.assertEqual(lexical["new_public_source_theorem_count"], 35)
        self.assertEqual(lexical["candidate_registered_public_source_theorem_count"], 4272)


    def test_path_realization_native_ownership_types_and_registered_edges(self):
        current = self.data["overlays"][10]
        self.assertEqual(current["base_snapshot_modules"], 684)
        self.assertEqual(current["prior_overlay"]["sha256"], reuse.OVERLAY_SHA256S[9])
        self.assertEqual(current["baseline_ref"], "d503586107974c56e0773b4ea106b41a7d144b43")
        self.assertEqual(current["source_checkpoint"], "worktree-sha256:de7c7e287bd1b351ed3f790de58bfd71edf18df4013f7e5aaf2af55a6b3f6379")
        self.assertEqual(current["source_checkpoint_kind"], "FROZEN_SOURCE_CONTENT_BEFORE_GIT_COMMIT")
        self.assertEqual(current["scientific_role"], "UNCOUNTED_SAME_SOURCE_PATH_REALIZATION")
        self.assertEqual(current["counted_core_impact"], "NONE")
        self.assertEqual(current["scientific_closure"], "NOT_ESTABLISHED")
        self.assertNotIn("historical_public_repairs", current)
        self.assertNotIn("existing_proof_dependency_repairs", current)
        prefix = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure."
        modules = {prefix + name for name in (
            "SameSourceFiniteWindow", "FiniteWindowDoob", "FiniteWindowDoobWitness",
            "FiniteMemoryRealization", "FiniteMemoryPhysicalSafety",
            "FiniteMemorySafetyWitness", "C3ExecutableSearch")}
        self.assertEqual({row["module"] for row in current["added_modules"]}, modules)
        self.assertEqual(len(current["added_modules"]), 7)
        self.assertEqual(len(current["public_theorems"]), 73)
        self.assertEqual(current["lexical_pr_preflight"]["new_theorems_with_lexical_reuse_candidates"], 25)
        distinct = current["type_distinctness"]
        self.assertEqual(distinct["registered_prior_theorems"], 4272)
        self.assertEqual(distinct["cross_isDefEq_comparisons"], 311856)
        self.assertEqual(distinct["internal_isDefEq_comparisons"], 2628)
        self.assertEqual(distinct["definitionally_equal_matches"], 0)
        evidence = current["native_export_evidence"]
        artifact = reuse.REPO / evidence["path"]
        native_sha = "61dabee5113b7fd2e640971c55ef6d2dba91e257744f587b57235f94a73b3308"
        self.assertEqual(evidence["sha256"], native_sha)
        self.assertEqual(reuse.sha256(artifact.read_bytes()).hexdigest(), native_sha)
        native = json.loads(artifact.read_text())
        self.assertEqual(native["schema"], "PATH_REALIZATION_NATIVE_EXPORT_V1")
        self.assertEqual(native["collisions"], [])
        scope = native["all_native_theorem_constants"]
        self.assertEqual(len(scope), 249)
        self.assertEqual(sum(row["is_private"] for row in scope), 51)
        self.assertEqual({row["source_module"] for row in scope}, modules)
        by_name = {row["name"]: row for row in scope}
        self.assertEqual(len(by_name), len(scope))
        fields = {"name", "source_module", "is_private", "level_parameters", "type",
                  "direct_constants", "direct_theorem_constants", "axioms"}
        for row in scope:
            with self.subTest(native_symbol=row["name"]):
                self.assertEqual(set(row), fields)
                self.assertTrue(set(row["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"})
                self.assertTrue(set(row["direct_theorem_constants"]) <= set(row["direct_constants"]))
        public = {row["name"]: row for row in current["public_theorems"]}
        native_public = {row["name"]: row for row in native["public_source_theorems"]}
        self.assertEqual(len(native_public), 73)
        self.assertEqual(set(public), set(native_public))
        self.assertEqual(sum(not row["is_private"] and row["name"] not in public
                             for row in scope), 125)
        for name, row in public.items():
            with self.subTest(public_symbol=name):
                full = by_name[name]
                self.assertFalse(full["is_private"])
                self.assertEqual(row["source_module"], full["source_module"])
                for field in ("source_module", "level_parameters", "type", "direct_constants"):
                    self.assertEqual(native_public[name][field], full[field])
                self.assertEqual(set(row["source_theorem_deps"]),
                                 set(native_public[name]["source_theorem_deps"]))
                actual = (set(full["direct_constants"]) & set(self.data["graph"])) - {name}
                self.assertEqual(set(row["source_theorem_deps"]), actual)
        self.assertEqual(sum(len(row["source_theorem_deps"]) for row in public.values()), 114)
        original = Path.read_bytes

        def drift(path):
            return b"deliberate path realization native drift" if path == artifact else original(path)

        with mock.patch.object(Path, "read_bytes", drift):
            with self.assertRaisesRegex(RuntimeError, "NATIVE_OVERLAY_EVIDENCE_DRIFT"):
                reuse.load(verify_source=False)

    def test_path_realization_same_source_and_canonical_reuse(self):
        prefix = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure."
        expected = {
            "C3ExecutableSearch.search_eq_firstGoodIndex": {
                prefix + "C3ExecutableSearch.search_found_iff",
                "UEOT.V3.Compression.TheoryCompletion.ScientificClosure.NestedCandidateFamily.firstGoodIndex_chainMinimal",
            },
            "FiniteMemoryRealization.actual_augmented_prefix_eq": {
                prefix + "FiniteMemoryRealization.actual_augmented_history_law",
                prefix + "FiniteMemoryRealization.state_history_eq_sequence_prefix",
            },
            "FiniteMemoryPhysicalSafety.controller_all_times_physical_safe": {
                "UEOT.V3.ViabilityPath.all_times_safe_eq_one",
                prefix + "FiniteMemoryPhysicalSafety.stateTrajMeasure_coordinate_mass",
                prefix + "FiniteMemoryPhysicalSafety.supported_micro_history_safe",
            },
            "SameSourceFiniteWindowCheck.actual_conditioned_prefix_mass": {
                prefix + "SameSourceFiniteWindowCheck.actual_prefix_survival_mass",
            },
            "FiniteWindowDoobCheck.actual_survival_mass_eq_initial_remaining_sum": {
                prefix + "SameSourceKilledPathCheck.actual_survival_mass_eq_killed_pow_sum",
            },
            "FiniteWindowDoobCheck.actual_doob_path_comparison": {
                prefix + "SameSourceKilledPathCheck.killedMatrix_nonneg",
                prefix + "FiniteWindowDoobCheck.safeInitialRow_nonneg",
                prefix + "FiniteWindowDoobCheck.doob_path_atom",
                prefix + "SameSourceFiniteWindowCheck.actual_conditioned_safe_path_mass",
            },
        }
        for name, deps in expected.items():
            with self.subTest(symbol=name):
                item = reuse.explain(self.data, prefix + name)
                self.assertEqual(set(item["direct_existing_source_theorem_uses"]), deps)
                self.assertEqual(item["role"], "UNCOUNTED_SAME_SOURCE_PATH_REALIZATION")
                self.assertEqual(item["area"], "V3/Compression/TheoryCompletion/UnifiedClosure")
        tv = reuse.explain(self.data, prefix + "FiniteWindowDoobWitnessCheck.actual_conditioned_doob_tv")
        self.assertIn("UEOT.V3.PathError.tvDist_eq_one_sub_pmfCommonMass",
                      tv["direct_existing_source_theorem_uses"])

    def test_path_realization_public_witness_really_uses_all_private_mass_facts(self):
        current = self.data["overlays"][10]
        native = json.loads((reuse.REPO / current["native_export_evidence"]["path"]).read_text())
        owner = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteMemorySafetyWitness"
        scope = native["all_native_theorem_constants"]
        by_name = {row["name"]: row for row in scope}
        endpoint = owner + ".physical_safety_premises_independent"
        public = next(row for row in native["public_source_theorems"] if row["name"] == endpoint)
        helpers = {}
        for short_name in (
                "safe_source_all_times_mass_one", "unsafe_transition_time_one_mass_zero",
                "unsafe_transition_all_times_mass_zero", "unsafe_initial_time_zero_mass_zero",
                "unsafe_initial_all_times_mass_zero"):
            matches = [row for row in scope if row["source_module"] == owner
                       and row["name"].endswith("." + short_name)]
            self.assertEqual(len(matches), 1)
            row = matches[0]
            helpers[short_name] = row
            self.assertTrue(row["is_private"])
            self.assertTrue(row["name"].startswith("_private."))
            self.assertEqual(set(row["axioms"]), {"propext", "Classical.choice", "Quot.sound"})
            self.assertNotIn(row["name"], self.data["graph"])
            self.assertIn(row["name"], public["direct_constants"])
            self.assertIn(row["name"], by_name[endpoint]["direct_theorem_constants"])
        self.assertEqual(set(public["source_theorem_deps"]), {owner + "." + name for name in (
            "safe_is_proper_nonempty", "all_rows_zero_uncovered",
            "initial_false_safe", "source_false_preserves_safe")})
        # Preserve the actual private proof path, without inventing public direct edges.
        self.assertIn("UEOT.V3.Compression.TheoryCompletion.UnifiedClosure."
                      "FiniteMemoryPhysicalSafety.controller_all_times_physical_safe",
                      helpers["safe_source_all_times_mass_one"]["direct_theorem_constants"])
        for case, coordinate in (("transition", "one"), ("initial", "zero")):
            self.assertIn(helpers[f"unsafe_{case}_time_{coordinate}_mass_zero"]["name"],
                          helpers[f"unsafe_{case}_all_times_mass_zero"]["direct_theorem_constants"])

    def test_path_realization_registration_preserves_raw_execution_and_metadata_scope(self):
        current = self.data["overlays"][10]
        provenance = current["registration_provenance"]
        additions = {"lexical_pr_preflight", "registration_provenance"}
        self.assertEqual(provenance["schema"], "PATH_REALIZATION_REGISTRATION_PROVENANCE_V1")
        self.assertEqual(set(provenance["metadata_additions_only"]), additions)
        self.assertTrue(provenance["raw_evidence_bytes_preserved"])
        self.assertFalse(provenance["consumer_registry_modified"])
        self.assertEqual(provenance["git_object_pr_preflight"], "NOT_PERFORMED_SEPARATE_GATE")
        fingerprint = "de7c7e287bd1b351ed3f790de58bfd71edf18df4013f7e5aaf2af55a6b3f6379"
        self.assertEqual(provenance["source_tree_sha256"], fingerprint)
        self.assertEqual(provenance["baseline_ref"], "d503586107974c56e0773b4ea106b41a7d144b43")
        inputs = provenance["inputs"]
        self.assertEqual(len({(row["role"], row["path"]) for row in inputs}), len(inputs))
        for row in inputs:
            with self.subTest(archived_input=row["path"]):
                path = reuse.REPO / row["path"]
                self.assertTrue(path.resolve().is_relative_to(reuse.REPO.resolve()))
                self.assertEqual(reuse.sha256(path.read_bytes()).hexdigest(), row["sha256"])
        raw_rows = [row for row in inputs if row["role"] == "actual_native_output"
                    and row["path"].endswith("/PATH_REALIZATION_REUSE_OVERLAY_V1.json")]
        self.assertEqual(len(raw_rows), 1)
        raw_path = reuse.REPO / raw_rows[0]["path"]
        raw = json.loads(raw_path.read_text())
        self.assertEqual(set(current) - set(raw), additions)
        self.assertEqual({key: value for key, value in current.items() if key not in additions}, raw)
        archive = raw_path.parent
        self.assertEqual((archive / "REGISTERED_OVERLAY.json").read_bytes(), reuse.OVERLAY_PATHS[10].read_bytes())
        receipt = json.loads((archive / "REGISTRATION_RECEIPT.json").read_text())
        self.assertEqual(receipt["schema"], "PATH_REALIZATION_REGISTRATION_RECEIPT_V1")
        self.assertEqual(receipt["state"], "PASS_METADATA_ONLY_CONSUMER_UNCHANGED")
        self.assertEqual(receipt["raw_overlay_sha256"], raw_rows[0]["sha256"])
        self.assertEqual(receipt["registered_overlay"]["sha256"], reuse.OVERLAY_SHA256S[10])
        self.assertEqual(set(receipt["added_top_level_keys"]), additions)
        self.assertTrue(receipt["stripped_registered_json_equals_raw"])
        self.assertIsNone(receipt["candidate_ref"])
        self.assertEqual(receipt["input_files"], inputs)
        preflight = json.loads((archive / "SOURCE_PREFLIGHT.json").read_text())
        self.assertEqual(preflight["status"], "PENDING_ACTUAL_NATIVE_EXECUTION")
        self.assertEqual(preflight["source_tree_sha256"], fingerprint)
        self.assertEqual(preflight["complete_source_modules"], 691)
        self.assertEqual(preflight["added_modules"], current["added_modules"])
        execution = json.loads((archive / "STATUS.json").read_text())
        self.assertEqual(execution["state"], "PASS_PENDING_INDEPENDENT_REVIEW_AND_REGISTRATION")
        self.assertTrue(current["native_execution"]["fixed_export_equals_initial_native_export"])
        self.assertEqual(json.loads((archive / "observed_first_native.json").read_text()),
                         json.loads((reuse.REPO / current["native_export_evidence"]["path"]).read_text()))
        lexical = current["lexical_pr_preflight"]
        self.assertIsNone(lexical["candidate_ref"])
        self.assertEqual(lexical["new_public_source_theorem_count"], 73)
        self.assertEqual(lexical["base_public_lexical_theorem_count"], 4272)
        self.assertEqual(lexical["candidate_public_lexical_theorem_count"], 4345)
        self.assertEqual(lexical["candidate_registered_public_source_theorem_count"], 4345)
        self.assertEqual(lexical["new_theorems_with_lexical_reuse_candidates"], 25)

    def test_total_kernel_memory_native_ownership_and_registered_edges(self):
        current = self.data["overlays"][11]
        prefix = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure."
        modules = {prefix + name for name in (
            "TotalFiniteWindow", "TotalFiniteWindowWitness", "HomogeneousMemorySurvival")}
        self.assertEqual(current["base_snapshot_modules"], 691)
        self.assertEqual(current["prior_overlay"]["sha256"], reuse.OVERLAY_SHA256S[10])
        self.assertEqual(current["baseline_ref"], "41c4b27ef8d993c797b2414311f0934eeb4cb561")
        self.assertEqual(current["source_checkpoint"],
                         "worktree-sha256:2a0482a9717cc776b76383755a42b327ba132a04fbb6dfaea5c3ddb45da47b24")
        self.assertEqual(current["source_checkpoint_kind"], "FROZEN_SOURCE_CONTENT_BEFORE_GIT_COMMIT")
        self.assertEqual(current["scientific_role"],
                         "UNCOUNTED_TOTAL_CONDITIONED_KERNEL_AND_HOMOGENEOUS_MEMORY_SURVIVAL")
        self.assertEqual(current["counted_core_impact"], "NONE")
        self.assertEqual(current["scientific_closure"], "NOT_ESTABLISHED")
        self.assertNotIn("historical_public_repairs", current)
        self.assertNotIn("existing_proof_dependency_repairs", current)
        self.assertEqual({row["module"] for row in current["added_modules"]}, modules)
        evidence = current["native_export_evidence"]
        artifact = reuse.REPO / evidence["path"]
        native_sha = "0f164136ebca7dd0e3dd3339fe54286be820cce6b285a03ca5ade12cf1422e02"
        self.assertEqual(evidence["sha256"], native_sha)
        self.assertEqual(reuse.sha256(artifact.read_bytes()).hexdigest(), native_sha)
        native = json.loads(artifact.read_text())
        self.assertEqual(native["schema"], "TOTAL_KERNEL_MEMORY_NATIVE_EXPORT_V1")
        self.assertEqual(native["collisions"], [])
        scope = native["all_native_theorem_constants"]
        by_name = {row["name"]: row for row in scope}
        self.assertEqual(len(scope), 80)
        self.assertEqual(len(by_name), len(scope))
        self.assertEqual(sum(row["is_private"] for row in scope), 27)
        self.assertEqual({row["source_module"] for row in scope}, modules)
        fields = {"name", "source_module", "is_private", "level_parameters", "type",
                  "direct_constants", "direct_theorem_constants", "axioms"}
        for row in scope:
            with self.subTest(native_symbol=row["name"]):
                self.assertEqual(set(row), fields)
                self.assertTrue(set(row["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"})
                self.assertTrue(set(row["direct_theorem_constants"]) <= set(row["direct_constants"]))
        public = {row["name"]: row for row in current["public_theorems"]}
        native_public = {row["name"]: row for row in native["public_source_theorems"]}
        self.assertEqual(len(public), 12)
        self.assertEqual(set(public), set(native_public))
        self.assertEqual(sum(not row["is_private"] and row["name"] not in public
                             for row in scope), 41)
        edges = set()
        for name, row in public.items():
            with self.subTest(public_symbol=name):
                full = by_name[name]
                self.assertFalse(full["is_private"])
                self.assertEqual(row["source_module"], full["source_module"])
                for field in ("source_module", "level_parameters", "type", "direct_constants"):
                    self.assertEqual(native_public[name][field], full[field])
                actual = (set(full["direct_constants"]) & set(self.data["graph"])) - {name}
                self.assertEqual(set(row["source_theorem_deps"]), actual)
                self.assertEqual(set(native_public[name]["source_theorem_deps"]), actual)
                edges.update((name, target) for target in actual)
        certified = current["proof_dependency_certification"]
        self.assertEqual(edges, {(row["source"], row["target"]) for row in certified["edges"]})
        self.assertEqual(len(edges), certified["registered_direct_edges"])
        self.assertEqual(len(edges), 27)
        distinct = current["type_distinctness"]
        self.assertEqual(distinct["registered_prior_theorems"], 4345)
        self.assertEqual(distinct["definitionally_equal_matches"], 0)
        for field, expected in (
                ("cross_isDefEq_comparisons", 12 * 4345),
                ("internal_isDefEq_comparisons", 12 * 11 // 2)):
            self.assertEqual(distinct[field], expected)
            self.assertEqual(native[field], expected)

    def test_total_kernel_memory_actual_source_and_canonical_reuse(self):
        prefix = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure."
        expected = {
            "TotalFiniteWindowCheck.windowPathLaw_prefix_atom": {
                "UEOT.V3.PathError.pmfExtend_apply",
                prefix + "SameSourceFiniteWindowCheck.remainingSurvival_nonneg",
                prefix + "TotalFiniteWindowCheck.totalWindowRow_apply_toReal_of_pos"},
            "TotalFiniteWindowCheck.generated_prefix_eq_actual": {
                prefix + "PathObservationEscapeCheck.riskHistoryMap_injective_general",
                prefix + "SameSourceConditionedTerminalCheck.pmf_map_injective_atom",
                prefix + "FiniteWindowDoobCheck.safeInitialRow_nonneg",
                prefix + "SameSourceKilledPathCheck.killedMatrix_nonneg",
                prefix + "TotalFiniteWindowCheck.windowPathLaw_prefix_atom",
                prefix + "SameSourceFiniteWindowCheck.actual_conditioned_prefix_mass",
                prefix + "SameSourceFiniteWindowCheck.state_safe_atom_eq_matrixPathWeight",
                prefix + "FiniteWindowDoobCheck.actual_survival_mass_eq_initial_remaining_sum",
                prefix + "SameSourceFiniteWindowCheck.actual_conditioned_prefix_eq_zero_of_not_survives"},
            "TotalFiniteWindowCheck.generated_ambient_eq_actual": {
                prefix + "TotalFiniteWindowCheck.generated_prefix_eq_actual"},
            "HomogeneousMemorySurvival.closed_loop_eq_augmentedRow": {
                prefix + "HomogeneousMemorySurvival.augmentedModel_transitionPMF",
                prefix + "SourcePolicyPathBridgeCheck.actual_next_state_eq_stationary_row"},
            "HomogeneousMemorySurvival.actual_augmentedTrajMeasure_eq_homogeneous": {
                prefix + "HomogeneousMemorySurvival.closed_loop_eq_augmentedRow"},
            "HomogeneousMemorySurvival.killed_mass_tendsto_actual_infinite_survival": {
                "UEOT.V3.Compression.Objecthood.neverHitSet_eq_iInter_survivalSet",
                "UEOT.V3.RecoveryHittingNonnegative.measurableSet_survivalSet",
                "UEOT.V3.DynamicsKernel.measurable_mapPath",
                prefix + "HomogeneousMemorySurvival.actual_augmentedTrajMeasure_eq_homogeneous",
                prefix + "SameSourceSurvivalTailCheck.killed_survival_mass_tendsto_homogeneous_neverHit_real"},
        }
        for name, deps in expected.items():
            with self.subTest(symbol=name):
                item = reuse.explain(self.data, prefix + name)
                self.assertEqual(set(item["direct_existing_source_theorem_uses"]), deps)
        for row in self.data["overlays"][11]["public_theorems"]:
            item = reuse.explain(self.data, row["name"])
            self.assertEqual(item["role"],
                             "UNCOUNTED_TOTAL_CONDITIONED_KERNEL_AND_HOMOGENEOUS_MEMORY_SURVIVAL")
            self.assertEqual(item["area"], "V3/Compression/TheoryCompletion/UnifiedClosure")

    def test_total_kernel_memory_private_bridges_and_null_witness(self):
        current = self.data["overlays"][11]
        native = json.loads((reuse.REPO / current["native_export_evidence"]["path"]).read_text())
        scope = native["all_native_theorem_constants"]
        by_name = {row["name"]: row for row in scope}
        prefix = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure."

        def helper(module, short_name):
            matches = [row for row in scope if row["source_module"] == prefix + module
                       and row["name"].endswith("." + short_name)]
            self.assertEqual(len(matches), 1)
            row = matches[0]
            self.assertTrue(row["is_private"])
            self.assertNotIn(row["name"], self.data["graph"])
            return row

        endpoint = prefix + "TotalFiniteWindowWitnessCheck.null_row_actual_source_witness"
        public = next(row for row in native["public_source_theorems"] if row["name"] == endpoint)
        # Zero registered public edges does not erase actual private proof reuse.
        self.assertEqual(public["source_theorem_deps"], [])
        witness_helpers = {}
        for name in ("initial_unsafe_mass", "survival_one", "remaining_one",
                     "null_rows_differ", "generated_eq_pure"):
            row = helper("TotalFiniteWindowWitness", name)
            witness_helpers[name] = row
            self.assertIn(row["name"], public["direct_constants"])
            self.assertIn(row["name"], by_name[endpoint]["direct_theorem_constants"])
        conditioned = helper("TotalFiniteWindowWitness", "conditioned_eq_pure")
        self.assertIn(conditioned["name"], witness_helpers["generated_eq_pure"]["direct_theorem_constants"])
        self.assertIn(prefix + "TotalFiniteWindowCheck.generated_ambient_eq_actual",
                      witness_helpers["generated_eq_pure"]["direct_theorem_constants"])
        self.assertIn(prefix + "SameSourceFiniteWindowCheck.actual_conditioned_safe_path_mass",
                      conditioned["direct_theorem_constants"])
        ambient = helper("TotalFiniteWindow", "generated_map_eq_ambient")
        self.assertIn(ambient["name"],
                      by_name[prefix + "TotalFiniteWindowCheck.generated_ambient_eq_actual"]["direct_theorem_constants"])
        for name in ("risk_map_extend_right", "coverage_map_extend_reference"):
            self.assertIn(prefix + name, ambient["direct_theorem_constants"])
        projected = helper("HomogeneousMemorySurvival", "projected_survival_mass")
        self.assertIn(projected["name"],
                      by_name[prefix + "HomogeneousMemorySurvival.actual_finite_survival_eq_killed_mass"]["direct_theorem_constants"])
        for name in ("HomogeneousMemorySurvival.actual_augmentedTrajMeasure_eq_homogeneous",
                     "SameSourceSafePrefixCheck.homogeneous_survival_real_eq_killed_pow_sum"):
            self.assertIn(prefix + name, projected["direct_theorem_constants"])

    def test_total_kernel_memory_registration_preserves_raw_execution(self):
        current = self.data["overlays"][11]
        provenance = current["registration_provenance"]
        additions = {"lexical_pr_preflight", "registration_provenance"}
        self.assertEqual(provenance["schema"], "TOTAL_KERNEL_MEMORY_REGISTRATION_PROVENANCE_V1")
        self.assertEqual(set(provenance["metadata_additions_only"]), additions)
        self.assertTrue(provenance["raw_evidence_bytes_preserved"])
        self.assertFalse(provenance["consumer_registry_modified"])
        self.assertEqual(provenance["git_object_pr_preflight"], "NOT_PERFORMED_SEPARATE_GATE")
        fingerprint = "2a0482a9717cc776b76383755a42b327ba132a04fbb6dfaea5c3ddb45da47b24"
        self.assertEqual(provenance["source_tree_sha256"], fingerprint)
        self.assertEqual(provenance["baseline_ref"], current["baseline_ref"])
        inputs = provenance["inputs"]
        self.assertEqual(len({(row["role"], row["path"]) for row in inputs}), len(inputs))
        for row in inputs:
            with self.subTest(archived_input=row["path"]):
                path = reuse.REPO / row["path"]
                self.assertTrue(path.resolve().is_relative_to(reuse.REPO.resolve()))
                self.assertEqual(reuse.sha256(path.read_bytes()).hexdigest(), row["sha256"])
        raw_rows = [row for row in inputs if row["role"] == "actual_native_output"
                    and row["path"].endswith("/TOTAL_KERNEL_MEMORY_REUSE_OVERLAY_V1.json")]
        self.assertEqual(len(raw_rows), 1)
        raw_path = reuse.REPO / raw_rows[0]["path"]
        raw = json.loads(raw_path.read_text())
        self.assertEqual(set(current) - set(raw), additions)
        self.assertEqual({key: value for key, value in current.items() if key not in additions}, raw)
        archive = raw_path.parent
        self.assertEqual((archive / "REGISTERED_OVERLAY.json").read_bytes(), reuse.OVERLAY_PATHS[11].read_bytes())
        receipt = json.loads((archive / "REGISTRATION_RECEIPT.json").read_text())
        self.assertEqual(receipt["schema"], "TOTAL_KERNEL_MEMORY_REGISTRATION_RECEIPT_V1")
        self.assertEqual(receipt["state"], "PASS_METADATA_ONLY_CONSUMER_UNCHANGED")
        self.assertEqual(receipt["raw_overlay_sha256"], raw_rows[0]["sha256"])
        self.assertEqual(receipt["registered_overlay"]["sha256"], reuse.OVERLAY_SHA256S[11])
        self.assertEqual(set(receipt["added_top_level_keys"]), additions)
        self.assertTrue(receipt["stripped_registered_json_equals_raw"])
        self.assertIsNone(receipt["candidate_ref"])
        self.assertEqual(receipt["input_files"], inputs)
        preflight = json.loads((archive / "SOURCE_PREFLIGHT.json").read_text())
        self.assertEqual(preflight["status"], "PENDING_ACTUAL_NATIVE_EXECUTION")
        self.assertEqual(preflight["source_tree_sha256"], fingerprint)
        self.assertEqual(preflight["complete_source_modules"], 694)
        self.assertEqual(preflight["added_modules"], current["added_modules"])
        execution = json.loads((archive / "STATUS.json").read_text())
        self.assertEqual(execution["state"], "PASS_PENDING_INDEPENDENT_REVIEW_AND_REGISTRATION")
        self.assertTrue(current["native_execution"]["fixed_export_equals_initial_native_export"])
        self.assertEqual(json.loads((archive / "observed_first_native.json").read_text()),
                         json.loads((reuse.REPO / current["native_export_evidence"]["path"]).read_text()))
        for row in current["native_execution"]["results"]:
            log = archive / ("native_export.log" if row["label"] == "native_export" else "fixed_verifier.log")
            self.assertEqual(row["exit_code"], 0)
            self.assertEqual(reuse.sha256(log.read_bytes()).hexdigest(), row["log_sha256"])
        lexical = current["lexical_pr_preflight"]
        self.assertIsNone(lexical["candidate_ref"])
        self.assertEqual(lexical["new_public_source_theorem_count"], 12)
        self.assertEqual(lexical["base_public_lexical_theorem_count"], 4345)
        self.assertEqual(lexical["candidate_public_lexical_theorem_count"], 4357)
        self.assertEqual(lexical["candidate_registered_public_source_theorem_count"], 4357)
        self.assertEqual(lexical["new_theorems_with_lexical_reuse_candidates"], 5)


    def test_executable_support_native_ownership_and_registered_edges(self):
        current = self.data["overlays"][12]
        prefix = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure."
        modules = {prefix + name for name in (
            "ExecutableSupportController", "ExecutableSupportControllerWitness")}
        self.assertEqual(current["base_snapshot_modules"], 694)
        self.assertEqual(current["prior_overlay"]["sha256"], reuse.OVERLAY_SHA256S[11])
        self.assertEqual(current["baseline_ref"], "c54f1a96b25e57a3484da46d38c1c9f668d53a34")
        self.assertEqual(current["source_checkpoint"],
                         "worktree-sha256:f95a19e8c0ad5f7295f8166d5a5fc212af5a8af40e2e2740673aaaf425b6e09d")
        self.assertEqual(current["source_checkpoint_kind"], "FROZEN_SOURCE_CONTENT_BEFORE_GIT_COMMIT")
        self.assertEqual(current["scientific_role"],
                         "UNCOUNTED_EXECUTABLE_SUPPORT_SYNTHESIS")
        self.assertEqual(current["counted_core_impact"], "NONE")
        self.assertEqual(current["scientific_closure"], "NOT_ESTABLISHED")
        self.assertNotIn("historical_public_repairs", current)
        self.assertNotIn("existing_proof_dependency_repairs", current)
        self.assertEqual({row["module"] for row in current["added_modules"]}, modules)
        evidence = current["native_export_evidence"]
        artifact = reuse.REPO / evidence["path"]
        native_sha = "9e2be23986e5d5f38266e267964feac9af18cc8e3f3f17bdf18a356cc8f06592"
        self.assertEqual(evidence["sha256"], native_sha)
        self.assertEqual(reuse.sha256(artifact.read_bytes()).hexdigest(), native_sha)
        native = json.loads(artifact.read_text())
        self.assertEqual(native["schema"], "EXECUTABLE_SUPPORT_NATIVE_EXPORT_V1")
        self.assertEqual(native["collisions"], [])
        scope = native["all_native_theorem_constants"]
        by_name = {row["name"]: row for row in scope}
        self.assertEqual(len(scope), 73)
        self.assertEqual(len(by_name), len(scope))
        self.assertEqual(sum(row["is_private"] for row in scope), 4)
        self.assertEqual({row["source_module"] for row in scope}, modules)
        fields = {"name", "source_module", "is_private", "level_parameters", "type",
                  "direct_constants", "direct_theorem_constants", "axioms"}
        for row in scope:
            with self.subTest(native_symbol=row["name"]):
                self.assertEqual(set(row), fields)
                self.assertTrue(set(row["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"})
                self.assertTrue(set(row["direct_theorem_constants"]) <= set(row["direct_constants"]))
        public = {row["name"]: row for row in current["public_theorems"]}
        native_public = {row["name"]: row for row in native["public_source_theorems"]}
        self.assertEqual(len(public), 33)
        self.assertEqual(set(public), set(native_public))
        self.assertEqual(sum(not row["is_private"] and row["name"] not in public
                             for row in scope), 36)
        edges = set()
        for name, row in public.items():
            with self.subTest(public_symbol=name):
                full = by_name[name]
                self.assertFalse(full["is_private"])
                self.assertEqual(row["source_module"], full["source_module"])
                for field in ("source_module", "level_parameters", "type", "direct_constants"):
                    self.assertEqual(native_public[name][field], full[field])
                actual = (set(full["direct_constants"]) & set(self.data["graph"])) - {name}
                self.assertEqual(set(row["source_theorem_deps"]), actual)
                self.assertEqual(set(native_public[name]["source_theorem_deps"]), actual)
                edges.update((name, target) for target in actual)
        certified = current["proof_dependency_certification"]
        self.assertEqual(edges, {(row["source"], row["target"]) for row in certified["edges"]})
        self.assertEqual(len(edges), certified["registered_direct_edges"])
        self.assertEqual(len(edges), 60)
        distinct = current["type_distinctness"]
        self.assertEqual(distinct["registered_prior_theorems"], 4357)
        self.assertEqual(distinct["definitionally_equal_matches"], 0)
        for field, expected in (
                ("cross_isDefEq_comparisons", 33 * 4357),
                ("internal_isDefEq_comparisons", 33 * 32 // 2)):
            self.assertEqual(distinct[field], expected)
            self.assertEqual(native[field], expected)

    def test_executable_support_same_source_and_semantic_reuse(self):
        prefix = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure."
        synthesis = prefix + "ExecutableSupportSynthesis."
        expected = {
            "selectedAction_step": {
                prefix + "SupportViabilityClosure.supportWinning_step",
                prefix + "SupportViabilityClosure.supportWinning_subset_arena",
                synthesis + "stepCheck_iff"},
            "program_memory_eq_traceSupport": {
                synthesis + "Program.toController_memory", synthesis + "memory_eq_traceSupport"},
            "synthesize_isSome_iff_exists_all_times_policy": {
                synthesis + "synthesize_isSome_iff",
                prefix + "SupportViabilityClosure.finiteMemoryCheck_iff_exists_all_times_policy"},
            "zero_uncovered": {
                prefix + "SupportViabilityClosure.zero_uncovered_iff_support_certified",
                synthesis + "memory_eq_traceSupport", synthesis + "supported_histories_winning",
                synthesis + "selectedAction_step"},
            "all_times_physical_safe": {
                prefix + "FiniteMemoryPhysicalSafety.controller_all_times_physical_safe",
                synthesis + "zero_uncovered"},
            "synthesize_some_killed_mass_one": {
                prefix + "HomogeneousMemorySurvival.actual_finite_survival_eq_killed_mass",
                synthesis + "synthesize_some_zero_uncovered",
                prefix + "FiniteMemoryPhysicalSafety.actual_finite_safety_one"},
        }
        for name, dependencies in expected.items():
            with self.subTest(symbol=name):
                item = reuse.explain(self.data, synthesis + name)
                self.assertEqual(set(item["direct_existing_source_theorem_uses"]), dependencies)
        for row in self.data["overlays"][12]["public_theorems"]:
            item = reuse.explain(self.data, row["name"])
            self.assertEqual(item["role"], "UNCOUNTED_EXECUTABLE_SUPPORT_SYNTHESIS")
            self.assertEqual(item["area"], "V3/Compression/TheoryCompletion/UnifiedClosure")

    def test_executable_support_witnesses_and_actual_runtime(self):
        current = self.data["overlays"][12]
        native = json.loads((reuse.REPO / current["native_export_evidence"]["path"]).read_text())
        by_name = {row["name"]: row for row in native["all_native_theorem_constants"]}
        prefix = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure."
        witness = prefix + "ExecutableSupportControllerWitness."
        for suffix in ("finite_input_checks", "synthesis_rejections", "computed_flip_steps",
                       "action_order_is_effective"):
            row = by_name[witness + suffix]
            self.assertIn("of_decide_eq_true", row["direct_theorem_constants"])
        private = {}
        for suffix in ("empty_memory_uses_fallback", "mixed_support_exact"):
            rows = [row for row in by_name.values() if row["name"].endswith("." + suffix)]
            self.assertEqual(len(rows), 1)
            row = rows[0]
            self.assertTrue(row["is_private"])
            self.assertNotIn(row["name"], self.data["graph"])
            private[suffix] = row
        self.assertIn("of_decide_eq_true", private["empty_memory_uses_fallback"]["direct_theorem_constants"])
        rejected = witness + "mixed_initial_has_no_all_times_policy"
        self.assertIn(private["mixed_support_exact"]["name"], by_name[rejected]["direct_theorem_constants"])
        self.assertEqual(set(reuse.explain(self.data, rejected)["direct_existing_source_theorem_uses"]), {
            prefix + "ExecutableSupportSynthesis.synthesize_isSome_iff_exists_all_times_policy",
            witness + "source_support_exact", witness + "synthesis_rejections"})
        self.assertEqual(set(reuse.explain(self.data, witness + "actual_killed_mass_one")[
            "direct_existing_source_theorem_uses"]), {
                prefix + "ExecutableSupportSynthesis.synthesize_some_killed_mass_one",
                witness + "synthesis_returns_program", witness + "initial_support_exact",
                witness + "model_support_exact", witness + "initial_safe",
                witness + "certified_transition_safe", witness + "source_support_exact"})
        scope = reuse.HERE.parent.parent / "unified_closure" / "executable_support_v1"
        runtime = scope / "actual-execution" / "runtime-02"
        receipt = json.loads((runtime / "RUNTIME_RECEIPT.json").read_text())
        self.assertEqual(receipt["schema"], "EXECUTABLE_SUPPORT_RUNTIME_V1")
        self.assertEqual(receipt["state"], "PASS")
        self.assertEqual(receipt["exit_code"], 0)
        self.assertEqual(receipt["safe_transitions"], 12)
        self.assertEqual(receipt["source_tree_sha256"],
                         "f95a19e8c0ad5f7295f8166d5a5fc212af5a8af40e2e2740673aaaf425b6e09d")
        self.assertEqual(receipt["script_sha256"],
                         reuse.sha256((scope / "EXECUTE_CONTROLLER.lean").read_bytes()).hexdigest())
        log = (runtime / "runtime.log").read_bytes()
        self.assertEqual(receipt["log_sha256"], reuse.sha256(log).hexdigest())
        self.assertIn(b"R1_RUNTIME_PASS: 12 safe transitions", log)
        self.assertIn(b"mixed/incomplete/empty rejected; fallback and list order checked", log)

    def test_executable_support_registration_preserves_raw_execution(self):
        current = self.data["overlays"][12]
        provenance = current["registration_provenance"]
        additions = {"lexical_pr_preflight", "registration_provenance"}
        self.assertEqual(provenance["schema"], "EXECUTABLE_SUPPORT_REGISTRATION_PROVENANCE_V1")
        self.assertEqual(set(provenance["metadata_additions_only"]), additions)
        self.assertTrue(provenance["raw_evidence_bytes_preserved"])
        self.assertFalse(provenance["consumer_registry_modified"])
        self.assertEqual(provenance["git_object_pr_preflight"], "NOT_PERFORMED_SEPARATE_GATE")
        fingerprint = "f95a19e8c0ad5f7295f8166d5a5fc212af5a8af40e2e2740673aaaf425b6e09d"
        self.assertEqual(provenance["source_tree_sha256"], fingerprint)
        self.assertEqual(provenance["baseline_ref"], current["baseline_ref"])
        inputs = provenance["inputs"]
        self.assertEqual(len({(row["role"], row["path"]) for row in inputs}), len(inputs))
        for row in inputs:
            with self.subTest(archived_input=row["path"]):
                path = reuse.REPO / row["path"]
                self.assertTrue(path.resolve().is_relative_to(reuse.REPO.resolve()))
                self.assertEqual(reuse.sha256(path.read_bytes()).hexdigest(), row["sha256"])
        raw_rows = [row for row in inputs if row["role"] == "actual_native_output"
                    and row["path"].endswith("/EXECUTABLE_SUPPORT_REUSE_OVERLAY_V1.json")]
        self.assertEqual(len(raw_rows), 1)
        raw_path = reuse.REPO / raw_rows[0]["path"]
        raw = json.loads(raw_path.read_text())
        self.assertEqual(set(current) - set(raw), additions)
        self.assertEqual({key: value for key, value in current.items() if key not in additions}, raw)
        archive = raw_path.parent
        self.assertEqual((archive / "REGISTERED_OVERLAY.json").read_bytes(), reuse.OVERLAY_PATHS[12].read_bytes())
        receipt = json.loads((archive / "REGISTRATION_RECEIPT.json").read_text())
        self.assertEqual(receipt["schema"], "EXECUTABLE_SUPPORT_REGISTRATION_RECEIPT_V1")
        self.assertEqual(receipt["state"], "PASS_METADATA_ONLY_CONSUMER_UNCHANGED")
        self.assertEqual(receipt["raw_overlay_sha256"], raw_rows[0]["sha256"])
        self.assertEqual(receipt["registered_overlay"]["sha256"], reuse.OVERLAY_SHA256S[12])
        self.assertEqual(set(receipt["added_top_level_keys"]), additions)
        self.assertTrue(receipt["stripped_registered_json_equals_raw"])
        self.assertIsNone(receipt["candidate_ref"])
        self.assertEqual(receipt["input_files"], inputs)
        preflight = json.loads((archive / "SOURCE_PREFLIGHT.json").read_text())
        self.assertEqual(preflight["status"], "PENDING_ACTUAL_NATIVE_EXECUTION")
        self.assertEqual(preflight["source_tree_sha256"], fingerprint)
        self.assertEqual(preflight["complete_source_modules"], 696)
        self.assertEqual(preflight["added_modules"], current["added_modules"])
        execution = json.loads((archive / "STATUS.json").read_text())
        self.assertEqual(execution["state"], "PASS_PENDING_INDEPENDENT_REVIEW_AND_REGISTRATION")
        self.assertTrue(current["native_execution"]["fixed_export_equals_initial_native_export"])
        self.assertEqual(json.loads((archive / "observed_first_native.json").read_text()),
                         json.loads((reuse.REPO / current["native_export_evidence"]["path"]).read_text()))
        for row in current["native_execution"]["results"]:
            log = archive / ("native_export.log" if row["label"] == "native_export" else "fixed_verifier.log")
            self.assertEqual(row["exit_code"], 0)
            self.assertEqual(reuse.sha256(log.read_bytes()).hexdigest(), row["log_sha256"])
        lexical = current["lexical_pr_preflight"]
        self.assertIsNone(lexical["candidate_ref"])
        self.assertEqual(lexical["new_public_source_theorem_count"], 33)
        self.assertEqual(lexical["base_public_lexical_theorem_count"], 4357)
        self.assertEqual(lexical["candidate_public_lexical_theorem_count"], 4390)
        self.assertEqual(lexical["candidate_registered_public_source_theorem_count"], 4390)
        self.assertEqual(lexical["new_theorems_with_lexical_reuse_candidates"], 17)


    def test_noisy_oracle_native_ownership_and_registered_edges(self):
        current = self.data["overlays"][13]
        prefix = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure."
        modules = {prefix + name for name in (
            "FixedSampleSupportNoGo", "NoisyFiniteRiskOracle", "NoisyFiniteRiskOracleWitness")}
        self.assertEqual(current["base_snapshot_modules"], 696)
        self.assertEqual(current["prior_overlay"]["sha256"], reuse.OVERLAY_SHA256S[12])
        self.assertEqual(current["baseline_ref"], "d048429a1f713246dd7a69aa278f71c4d0df1677")
        self.assertEqual(current["source_checkpoint"],
                         "worktree-sha256:4b5145e874601392568293c1d561684e6d0478f2676dc20accf04a8080c3261d")
        self.assertEqual(current["source_checkpoint_kind"], "FROZEN_SOURCE_CONTENT_BEFORE_GIT_COMMIT")
        self.assertEqual(current["scientific_role"],
                         "UNCOUNTED_FINITE_SAMPLE_SUPPORT_BOUNDARY_AND_NOISY_RISK")
        self.assertEqual(current["counted_core_impact"], "NONE")
        self.assertEqual(current["scientific_closure"], "NOT_ESTABLISHED")
        self.assertNotIn("historical_public_repairs", current)
        self.assertNotIn("existing_proof_dependency_repairs", current)
        self.assertEqual({row["module"] for row in current["added_modules"]}, modules)
        evidence = current["native_export_evidence"]
        artifact = reuse.REPO / evidence["path"]
        native_sha = "bbb7551f055b2ec4a5e2d83b9214647e209ae6155e92d5436eba30132c4b54c6"
        self.assertEqual(evidence["sha256"], native_sha)
        self.assertEqual(reuse.sha256(artifact.read_bytes()).hexdigest(), native_sha)
        native = json.loads(artifact.read_text())
        self.assertEqual(native["schema"], "NOISY_ORACLE_NATIVE_EXPORT_V1")
        self.assertEqual(native["collisions"], [])
        scope = native["all_native_theorem_constants"]
        by_name = {row["name"]: row for row in scope}
        self.assertEqual(len(scope), 167)
        self.assertEqual(len(by_name), len(scope))
        self.assertEqual(sum(row["is_private"] for row in scope), 38)
        self.assertEqual({row["source_module"] for row in scope}, modules)
        fields = {"name", "source_module", "is_private", "level_parameters", "type",
                  "direct_constants", "direct_theorem_constants", "axioms"}
        for row in scope:
            with self.subTest(native_symbol=row["name"]):
                self.assertEqual(set(row), fields)
                self.assertTrue(set(row["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"})
                self.assertTrue(set(row["direct_theorem_constants"]) <= set(row["direct_constants"]))
        public = {row["name"]: row for row in current["public_theorems"]}
        native_public = {row["name"]: row for row in native["public_source_theorems"]}
        self.assertEqual(len(public), 43)
        self.assertEqual(set(public), set(native_public))
        self.assertEqual(sum(not row["is_private"] and row["name"] not in public
                             for row in scope), 86)
        edges = set()
        for name, row in public.items():
            with self.subTest(public_symbol=name):
                full = by_name[name]
                self.assertFalse(full["is_private"])
                self.assertEqual(row["source_module"], full["source_module"])
                for field in ("source_module", "level_parameters", "type", "direct_constants"):
                    self.assertEqual(native_public[name][field], full[field])
                actual = (set(full["direct_constants"]) & set(self.data["graph"])) - {name}
                self.assertEqual(set(row["source_theorem_deps"]), actual)
                self.assertEqual(set(native_public[name]["source_theorem_deps"]), actual)
                edges.update((name, target) for target in actual)
        certified = current["proof_dependency_certification"]
        self.assertEqual(edges, {(row["source"], row["target"]) for row in certified["edges"]})
        self.assertEqual(len(edges), certified["registered_direct_edges"])
        self.assertEqual(len(edges), 63)
        distinct = current["type_distinctness"]
        self.assertEqual(distinct["registered_prior_theorems"], 4390)
        self.assertEqual(distinct["definitionally_equal_matches"], 0)
        for field, expected in (
                ("cross_isDefEq_comparisons", 43 * 4390),
                ("internal_isDefEq_comparisons", 43 * 42 // 2)):
            self.assertEqual(distinct[field], expected)
            self.assertEqual(native[field], expected)

    def test_noisy_oracle_same_source_semantic_reuse(self):
        prefix = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure."
        no_go = prefix + "FixedSampleSupportNoGo."
        oracle = prefix + "NoisyFiniteRiskOracle."
        expected = {
            no_go + "trainingLaw_zeroRecord": {
                no_go + "trainingLaw_apply", prefix + "AbsorbingLeakage.kernel_mass"},
            no_go + "certificationProbability_at_zero": {no_go + "trainingLaw_at_zero"},
            no_go + "certificationProbability_ge_zeroPower": {
                no_go + "certificationProbability_eq_sum", no_go + "trainingLaw_zeroRecord"},
            no_go + "exists_positive_source_false_certification": {
                no_go + "certificationProbability_at_zero", no_go + "certificationProbability_ge_zeroPower"},
            no_go + "no_uniform_exact_zero_certificate": {
                no_go + "exists_positive_source_false_certification"},
            oracle + "calibrated_defect_error": {
                "UEOT.V3.StatisticalDefect.responseDefect_error",
                oracle + "empiricalDefect_eq_sourceDefect"},
            oracle + "noisyDecision_certified_sound": {
                "UEOT.V3.Compression.TheoryCompletion.ScientificClosure.decideAt_certified_sound",
                oracle + "calibrated_defect_error"},
            oracle + "noisyDecision_rejected_sound": {
                "UEOT.V3.Compression.TheoryCompletion.ScientificClosure.decideAt_rejected_sound",
                oracle + "calibrated_defect_error"},
            oracle + "selectCandidate_first_on_good": {
                oracle + "scanOutcome_some_iff", oracle + "selectCandidate_eq_some_iff",
                oracle + "noisyDecision_certified_sound", oracle + "noisyDecision_rejected_sound"},
            oracle + "training_calibration": {
                prefix + "VariableRegisteredSamples.product_experiment_calibration"},
            oracle + "synthesized_actual_risk_le_budget_on_good": {
                prefix + "ExecutableSupportSynthesis.synthesize_some_zero_uncovered",
                prefix + "coverage_same_policy_microscopic_failure_risk",
                oracle + "calibrated_reference_row", oracle + "referenceRisk_eq"},
            oracle + "selected_accepts_and_failure_joint_le": {
                oracle + "training_calibration", prefix + "selectedTrainingDeployment_failure_le",
                oracle + "accepts_actual_risk_on_good"},
        }
        for name, dependencies in expected.items():
            with self.subTest(symbol=name):
                self.assertEqual(set(reuse.explain(self.data, name)[
                    "direct_existing_source_theorem_uses"]), dependencies)
        current = self.data["overlays"][13]
        native = json.loads((reuse.REPO / current["native_export_evidence"]["path"]).read_text())
        by_name = {row["name"]: row for row in native["all_native_theorem_constants"]}
        no_go_type = " ".join(by_name[no_go + "no_uniform_exact_zero_certificate"]["type"].split())
        self.assertIn("(rule : " + no_go + "Record N → PMF Bool)", no_go_type)
        self.assertIn("0 < N →", no_go_type)
        self.assertIn("(∀ (p : ↑(Set.Ioo 0 1)),", no_go_type)
        selector_type = " ".join(by_name[oracle + "selectCandidate_first_on_good"]["type"].split())
        self.assertIn("(q : Fin count → X → Y)", selector_type)
        self.assertIn("selectCandidate q sample u tau = some i", selector_type)
        interval = [row for row in by_name.values()
                    if row["name"].endswith(".NoisyFiniteRiskOracle.decideRat_eq_decideAt")]
        self.assertEqual(len(interval), 1)
        self.assertTrue(interval[0]["is_private"])
        self.assertNotIn(interval[0]["name"], self.data["graph"])
        for name in ("noisyDecision_certified_sound", "noisyDecision_rejected_sound"):
            self.assertIn(interval[0]["name"], by_name[oracle + name]["direct_theorem_constants"])
        for row in current["public_theorems"]:
            self.assertEqual(reuse.explain(self.data, row["name"])["role"],
                             "UNCOUNTED_FINITE_SAMPLE_SUPPORT_BOUNDARY_AND_NOISY_RISK")

    def test_noisy_oracle_witnesses_and_preserved_runtime(self):
        current = self.data["overlays"][13]
        native = json.loads((reuse.REPO / current["native_export_evidence"]["path"]).read_text())
        by_name = {row["name"]: row for row in native["all_native_theorem_constants"]}
        prefix = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure."
        witness = prefix + "NoisyFiniteRiskOracleWitness."
        oracle = prefix + "NoisyFiniteRiskOracle."
        expected = {
            "computed_certificate_controls_actual_process": {
                oracle + "accepts_actual_risk_and_safety_on_good", witness + "source_support_exact"},
            "selected_model_joint_risk": {
                oracle + "selected_accepts_and_failure_joint_le", witness + "source_support_exact"},
            "actualGoalRisk_formula": {
                "UEOT.V3.PathError.pmfExtend_apply", "UEOT.V3.PathError.pmfMeasureReal_eq_sum_finset",
                prefix + "AbsorbingLeakage.kernel_mass"},
            "alternate_model_exceeds_cap": {witness + "actualGoalRisk_formula"},
            "alternate_model_rejects_on_good": {
                witness + "computed_certificate_controls_actual_process", witness + "alternate_model_exceeds_cap"},
            "alternate_model_acceptance_probability": {
                witness + "alternate_model_rejects_on_good", oracle + "training_calibration"},
        }
        for name, dependencies in expected.items():
            with self.subTest(symbol=name):
                self.assertEqual(set(reuse.explain(self.data, witness + name)[
                    "direct_existing_source_theorem_uses"]), dependencies)
        for suffix in ("synthesis_returns_program", "initial_mass_exact", "initial_support_exact",
                       "goal_envelope", "initial_safe", "relation_safe"):
            rows = [row for row in by_name.values() if row["name"].endswith("." + witness + suffix)]
            self.assertEqual(len(rows), 1)
            self.assertTrue(rows[0]["is_private"])
            self.assertNotIn(rows[0]["name"], self.data["graph"])
            self.assertIn(rows[0]["name"], by_name[witness +
                "computed_certificate_controls_actual_process"]["direct_theorem_constants"])
            if suffix not in ("initial_safe", "relation_safe"):
                self.assertIn(rows[0]["name"], by_name[witness + "selected_model_joint_risk"][
                    "direct_theorem_constants"])
        scope = reuse.HERE.parent.parent / "unified_closure" / "noisy_oracle_v1"
        runtime = scope / "actual-execution" / "runtime-03"
        receipt = json.loads((runtime / "RUNTIME_RECEIPT.json").read_text())
        self.assertEqual(receipt["schema"], "NOISY_ORACLE_ACTUAL_RUNTIME_V2")
        self.assertEqual(receipt["state"], "ACTUAL_RUNTIME_PASS")
        self.assertEqual(receipt["exit_code"], 0)
        evidence = {
            "script_sha256": (scope / "EXECUTE_NOISY_ORACLE.lean",
                "818494098bb06d4b2aa05591b99c28d104509cc9ae10c04b929a7fa37d4324f3"),
            "sampler_sha256": (scope / "SAMPLE_FINITE_SOURCE.py",
                "5f579f5c112916a45aadbbde1f9587862e8cf8a91d26ec44f852d09edfafe15c"),
            "dataset_sha256": (scope / "actual-execution" / "sampling-01" / "DATASET.json",
                "0d5e5bc9b4f11656986bddb880c493ff2bbd81bf530183af77e3c185c553f6f3"),
            "log_sha256": (runtime / "runtime.log",
                "954bef3665a8b6f8c1adcf38ac775ef13086ac632aa612870223ff4158cc9d54"),
        }
        for field, (path, expected_sha) in evidence.items():
            with self.subTest(runtime_evidence=field):
                self.assertEqual(receipt[field], expected_sha)
                self.assertEqual(reuse.sha256(path.read_bytes()).hexdigest(), expected_sha)
        dataset = json.loads(evidence["dataset_sha256"][0].read_text())
        self.assertEqual(dataset["sample_count"], 4096)
        self.assertEqual([len(row) for row in dataset["rows"]], [4096, 4096, 4096])
        self.assertEqual(dataset["oracle_inputs"], ["sample_count", "rows"])
        log = (runtime / "runtime.log").read_text()
        sampled = [line.removeprefix("R2_SAMPLED_RESULT ") for line in log.splitlines()
                   if line.startswith("R2_SAMPLED_RESULT ")]
        self.assertEqual(len(sampled), 1)
        self.assertEqual(json.loads(sampled[0]), receipt["result"])
        self.assertEqual(receipt["result"], {
            "accepted": True, "coarse_defect": "1539/2048", "defect_interval_radius": "1/10",
            "empirical_progress": "509/2048", "fine_budget": "13939757/20971520",
            "fine_defect": "0", "fine_reference_risk": "2368521/4194304", "first_non_fail": 1,
            "horizon": 2, "queries": [0, 1], "risk_cap": "7/10", "row_tv_radius": "1/20",
            "sample_count": 4096, "selected_candidate": 1, "state": "ACCEPTED", "threshold": "1/8"})
        self.assertIn("R2_FIXED_REGRESSION_PASS: FAIL/PASS; first trace; reference 9/16; budget 53/80; "
                      "contrasting 49/64 rejected; AMBIGUOUS stops; low budget, zero samples and empty family rejected", log)
        self.assertEqual(receipt["sampling"], "Single preserved draw, no resampling")
        self.assertEqual(receipt["external_scientific_evidence"], "UNVERIFIED")
        negative = json.loads((runtime / "NEGATIVE_RECEIPT.json").read_text())
        negative_log = (runtime / "negative-zero.log").read_bytes()
        self.assertEqual(negative["state"], "EXPECTED_REJECTION_PASS")
        self.assertEqual(negative["exit_code"], 1)
        self.assertEqual(negative["expected_error"], "registered sample allocation changed")
        self.assertEqual(negative["log_sha256"],
                         "26b2467d72ad780aabdbbbbc6a9f7ea203649ca4285777464f19d7efa2368cdd")
        self.assertEqual(reuse.sha256(negative_log).hexdigest(), negative["log_sha256"])
        self.assertIn(negative["expected_error"].encode(), negative_log)
        self.assertEqual(json.loads((runtime / "ZERO_SAMPLE_COUNT.json").read_text()),
                         {"sample_count": 0, "rows": []})

    def test_noisy_oracle_registration_preserves_raw_execution(self):
        current = self.data["overlays"][13]
        provenance = current["registration_provenance"]
        additions = {"lexical_pr_preflight", "registration_provenance"}
        self.assertEqual(provenance["schema"], "NOISY_ORACLE_REGISTRATION_PROVENANCE_V1")
        self.assertEqual(set(provenance["metadata_additions_only"]), additions)
        self.assertTrue(provenance["raw_evidence_bytes_preserved"])
        self.assertFalse(provenance["consumer_registry_modified"])
        self.assertEqual(provenance["git_object_pr_preflight"], "NOT_PERFORMED_SEPARATE_GATE")
        fingerprint = "4b5145e874601392568293c1d561684e6d0478f2676dc20accf04a8080c3261d"
        self.assertEqual(provenance["source_tree_sha256"], fingerprint)
        self.assertEqual(provenance["baseline_ref"], current["baseline_ref"])
        inputs = provenance["inputs"]
        self.assertEqual(len({(row["role"], row["path"]) for row in inputs}), len(inputs))
        for row in inputs:
            with self.subTest(archived_input=row["path"]):
                path = reuse.REPO / row["path"]
                self.assertTrue(path.resolve().is_relative_to(reuse.REPO.resolve()))
                self.assertEqual(reuse.sha256(path.read_bytes()).hexdigest(), row["sha256"])
        raw_rows = [row for row in inputs if row["role"] == "actual_native_output"
                    and row["path"].endswith("/NOISY_ORACLE_REUSE_OVERLAY_V1.json")]
        self.assertEqual(len(raw_rows), 1)
        raw_path = reuse.REPO / raw_rows[0]["path"]
        raw = json.loads(raw_path.read_text())
        self.assertEqual(set(current) - set(raw), additions)
        self.assertEqual({key: value for key, value in current.items() if key not in additions}, raw)
        archive = raw_path.parent
        self.assertEqual((archive / "REGISTERED_OVERLAY.json").read_bytes(), reuse.OVERLAY_PATHS[13].read_bytes())
        receipt = json.loads((archive / "REGISTRATION_RECEIPT.json").read_text())
        self.assertEqual(receipt["schema"], "NOISY_ORACLE_REGISTRATION_RECEIPT_V1")
        self.assertEqual(receipt["state"], "PASS_METADATA_ONLY_CONSUMER_UNCHANGED")
        self.assertEqual(receipt["raw_overlay_sha256"], raw_rows[0]["sha256"])
        self.assertEqual(receipt["registered_overlay"]["sha256"], reuse.OVERLAY_SHA256S[13])
        self.assertEqual(set(receipt["added_top_level_keys"]), additions)
        self.assertTrue(receipt["stripped_registered_json_equals_raw"])
        self.assertIsNone(receipt["candidate_ref"])
        self.assertEqual(receipt["input_files"], inputs)
        preflight = json.loads((archive / "SOURCE_PREFLIGHT.json").read_text())
        self.assertEqual(preflight["status"], "PENDING_ACTUAL_NATIVE_EXECUTION")
        self.assertEqual(preflight["source_tree_sha256"], fingerprint)
        self.assertEqual(preflight["complete_source_modules"], 699)
        self.assertEqual(preflight["added_modules"], current["added_modules"])
        frozen = json.loads((archive / "FROZEN_INPUTS.json").read_text())
        self.assertEqual(frozen["source_tree_sha256"], fingerprint)
        self.assertEqual(frozen["new_public"], 43)
        self.assertEqual(frozen["lexical_hinted"], 17)
        self.assertEqual(set(frozen["public_source_names"]),
                         {row["name"] for row in current["public_theorems"]})
        execution = json.loads((archive / "STATUS.json").read_text())
        self.assertEqual(execution["state"], "PASS_PENDING_INDEPENDENT_REVIEW_AND_REGISTRATION")
        self.assertTrue(current["native_execution"]["fixed_export_equals_initial_native_export"])
        self.assertEqual(json.loads((archive / "observed_first_native.json").read_text()),
                         json.loads((reuse.REPO / current["native_export_evidence"]["path"]).read_text()))
        for row in current["native_execution"]["results"]:
            log = archive / ("native_export.log" if row["label"] == "native_export" else "fixed_verifier.log")
            self.assertEqual(row["exit_code"], 0)
            self.assertEqual(reuse.sha256(log.read_bytes()).hexdigest(), row["log_sha256"])
        lexical = current["lexical_pr_preflight"]
        self.assertIsNone(lexical["candidate_ref"])
        self.assertEqual(lexical["new_public_source_theorem_count"], 43)
        self.assertEqual(lexical["base_public_lexical_theorem_count"], 4390)
        self.assertEqual(lexical["candidate_public_lexical_theorem_count"], 4433)
        self.assertEqual(lexical["candidate_registered_public_source_theorem_count"], 4433)
        self.assertEqual(lexical["new_theorems_with_lexical_reuse_candidates"], 17)


    def test_observable_belief_native_ownership_and_registered_edges(self):
        current = self.data["overlays"][14]
        prefix = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure."
        modules = {prefix + name for name in (
            "ObservableBeliefQuotient", "ObservableBeliefQuotientWitness")}
        self.assertEqual(current["base_snapshot_modules"], 699)
        self.assertEqual(current["prior_overlay"]["sha256"], reuse.OVERLAY_SHA256S[13])
        self.assertEqual(current["baseline_ref"], "e045cca43a94abbff00fd0da53e6200e0bd6ae2e")
        self.assertEqual(current["source_checkpoint"],
                         "worktree-sha256:778b37210962b487cedd2d5d50e9fa95c1297987ec4e18630da7fbc1ccd883c2")
        self.assertEqual(current["source_checkpoint_kind"], "FROZEN_SOURCE_CONTENT_BEFORE_GIT_COMMIT")
        self.assertEqual(current["scientific_role"],
                         "UNCOUNTED_OBSERVABLE_BELIEF_KERNEL_DESCENT")
        self.assertEqual(current["counted_core_impact"], "NONE")
        self.assertEqual(current["scientific_closure"], "NOT_ESTABLISHED")
        self.assertNotIn("historical_public_repairs", current)
        self.assertNotIn("existing_proof_dependency_repairs", current)
        self.assertEqual({row["module"] for row in current["added_modules"]}, modules)
        evidence = current["native_export_evidence"]
        artifact = reuse.REPO / evidence["path"]
        native_sha = "3bee681d5f501a9eb2cd397ae5190bbafa73e96a62a8f203284dd5933a5bdf0b"
        self.assertEqual(evidence["sha256"], native_sha)
        self.assertEqual(reuse.sha256(artifact.read_bytes()).hexdigest(), native_sha)
        native = json.loads(artifact.read_text())
        self.assertEqual(native["schema"], "OBSERVABLE_BELIEF_NATIVE_EXPORT_V1")
        self.assertEqual(native["collisions"], [])
        scope = native["all_native_theorem_constants"]
        by_name = {row["name"]: row for row in scope}
        self.assertEqual(len(scope), 84)
        self.assertEqual(len(by_name), len(scope))
        self.assertEqual(sum(row["is_private"] for row in scope), 19)
        self.assertEqual({row["source_module"] for row in scope}, modules)
        fields = {"name", "source_module", "is_private", "level_parameters", "type",
                  "direct_constants", "direct_theorem_constants", "axioms"}
        for row in scope:
            with self.subTest(native_symbol=row["name"]):
                self.assertEqual(set(row), fields)
                self.assertTrue(set(row["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"})
                self.assertTrue(set(row["direct_theorem_constants"]) <= set(row["direct_constants"]))
        public = {row["name"]: row for row in current["public_theorems"]}
        native_public = {row["name"]: row for row in native["public_source_theorems"]}
        self.assertEqual(len(public), 30)
        self.assertEqual(set(public), set(native_public))
        self.assertEqual(sum(not row["is_private"] and row["name"] not in public
                             for row in scope), 35)
        named_instances = {
            prefix + "ObservableBeliefQuotient.observation_isMarkov",
            prefix + "ObservableBeliefQuotient.quotientKernel_isMarkov",
            prefix + "ObservableBeliefQuotientWitness.source_isMarkov",
            prefix + "ObservableBeliefQuotientWitness.badSource_isMarkov",
        }
        other_public = {row["name"] for row in scope if not row["is_private"] and row["name"] not in public}
        self.assertTrue(named_instances <= other_public)
        self.assertEqual(len(other_public - named_instances), 31)
        for name in named_instances:
            self.assertEqual(by_name[name]["source_module"], name.rsplit(".", 1)[0])
            self.assertNotIn(name, self.data["graph"])
        generated = by_name["UEOT.V3.GeneralBayesPosterior.predictedLaw.eq_1"]
        self.assertEqual(generated["source_module"], prefix + "ObservableBeliefQuotient")
        self.assertIn(generated["name"], other_public - named_instances)
        edges = set()
        for name, row in public.items():
            with self.subTest(public_symbol=name):
                full = by_name[name]
                self.assertFalse(full["is_private"])
                self.assertEqual(row["source_module"], full["source_module"])
                for field in ("source_module", "level_parameters", "type", "direct_constants"):
                    self.assertEqual(native_public[name][field], full[field])
                actual = (set(full["direct_constants"]) & set(self.data["graph"])) - {name}
                self.assertEqual(set(row["source_theorem_deps"]), actual)
                self.assertEqual(set(native_public[name]["source_theorem_deps"]), actual)
                edges.update((name, target) for target in actual)
        certified = current["proof_dependency_certification"]
        self.assertEqual(edges, {(row["source"], row["target"]) for row in certified["edges"]})
        self.assertEqual(len(edges), certified["registered_direct_edges"])
        self.assertEqual(len(edges), 29)
        distinct = current["type_distinctness"]
        self.assertEqual(distinct["registered_prior_theorems"], 4433)
        self.assertEqual(distinct["definitionally_equal_matches"], 0)
        for field, expected in (
                ("cross_isDefEq_comparisons", 30 * 4433),
                ("internal_isDefEq_comparisons", 30 * 29 // 2)):
            self.assertEqual(distinct[field], expected)
            self.assertEqual(native[field], expected)

    def test_observable_belief_actual_c1_and_finite_test_reuse(self):
        prefix = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure."
        quotient = prefix + "ObservableBeliefQuotient."
        c1 = "UEOT.V3.Compression.TheoryCompletion.ScientificClosure."
        expected = {
            "coordinate_real_image": {quotient + "coordinate_liftBelief"},
            "coordinate_image_isClosed": {quotient + "coordinate_real_image"},
            "actual_kernel_coordinate_law": {
                c1 + "measurable_c1ParametricPosteriorBelief",
                c1 + "c1BeliefTransitionKernel_apply_eq_map", quotient + "measurable_coordinate"},
            "quotientKernel_factor": {
                quotient + "measurable_coordinate", quotient + "actual_kernel_coordinate_law",
                quotient + "closed_tests_predictive_law", quotient + "coordinate_liftBelief"},
            "quotientKernel_unique": {quotient + "quotientKernel_factor", quotient + "coordinate_liftBelief"},
            "closed_tests_of_quotient": {quotient + "actual_kernel_coordinate_law"},
            "closed_tests_iff_existsUnique_quotient": {
                quotient + "quotientKernel_factor", quotient + "quotientKernel_unique",
                quotient + "closed_tests_of_quotient"},
            "finite_test_response_factors": {quotient + "closed_tests_prefix_response"},
            "same_coordinate_same_tests": {quotient + "finite_test_response_factors"},
            "testExpectation_mem_unit": {quotient + "testResponse_le_one"},
        }
        for name, dependencies in expected.items():
            with self.subTest(symbol=name):
                self.assertEqual(set(reuse.explain(self.data, quotient + name)[
                    "direct_existing_source_theorem_uses"]), dependencies)
        current = self.data["overlays"][14]
        native = json.loads((reuse.REPO / current["native_export_evidence"]["path"]).read_text())
        by_name = {row["name"]: row for row in native["all_native_theorem_constants"]}
        posterior = [row for row in by_name.values()
                     if row["name"].endswith(".ObservableBeliefQuotient.posterior_observable_ae")]
        self.assertEqual(len(posterior), 1)
        self.assertTrue(posterior[0]["is_private"])
        self.assertNotIn(posterior[0]["name"], self.data["graph"])
        self.assertIn(posterior[0]["name"], by_name[quotient + "actual_kernel_coordinate_law"][
            "direct_theorem_constants"])
        self.assertIn(c1 + "c1ParametricPosteriorKernel_ae_eq_existing",
                      posterior[0]["direct_theorem_constants"])
        self.assertTrue(any(name.endswith(".deterministic_comp_posterior")
                            for name in posterior[0]["direct_theorem_constants"]))
        for row in current["public_theorems"]:
            self.assertEqual(reuse.explain(self.data, row["name"])["role"],
                             "UNCOUNTED_OBSERVABLE_BELIEF_KERNEL_DESCENT")

    def test_observable_belief_witness_no_quotient_and_readout_contracts(self):
        current = self.data["overlays"][14]
        native = json.loads((reuse.REPO / current["native_export_evidence"]["path"]).read_text())
        by_name = {row["name"]: row for row in native["all_native_theorem_constants"]}
        prefix = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure."
        quotient = prefix + "ObservableBeliefQuotient."
        witness = prefix + "ObservableBeliefQuotientWitness."
        expected = {
            "probe_test_is_coordinate": {quotient + "first_test_eq_observation", witness + "probe_observation_law"},
            "predictive_equivalence_iff": {
                witness + "probe_test_is_coordinate", quotient + "same_coordinate_same_tests", witness + "source_closed"},
            "actual_C1_descends": {quotient + "quotientKernel_factor", witness + "source_closed"},
            "aliases_have_all_same_future_tests": {witness + "predictive_equivalence_iff"},
            "no_quotient_without_closed_tests": {quotient + "closed_tests_of_quotient"},
            "reward_readout_factors": {quotient + "observation_reward_factors"},
            "safe_readout_factors": {quotient + "safe_class_probability"},
        }
        for name, dependencies in expected.items():
            with self.subTest(symbol=name):
                self.assertEqual(set(reuse.explain(self.data, witness + name)[
                    "direct_existing_source_theorem_uses"]), dependencies)
        aliases = [row for row in by_name.values()
                   if row["name"].endswith(".ObservableBeliefQuotientWitness.alias_coordinates")]
        self.assertEqual(len(aliases), 1)
        self.assertTrue(aliases[0]["is_private"])
        self.assertNotIn(aliases[0]["name"], self.data["graph"])
        for name in ("aliases_have_all_same_future_tests", "hidden_readouts_do_not_descend"):
            self.assertIn(aliases[0]["name"], by_name[witness + name]["direct_theorem_constants"])
        no_quotient = " ".join(by_name[witness + "no_quotient_without_closed_tests"]["type"].split())
        self.assertIn("¬∃", no_quotient.replace(" ", ""))
        self.assertIn("c1BeliefTransitionKernel", no_quotient)
        readouts = by_name[witness + "hidden_readouts_do_not_descend"]["type"]
        self.assertIn("hiddenReward", readouts)
        self.assertIn("hiddenSafe", readouts)

    def test_observable_belief_registration_preserves_raw_execution(self):
        current = self.data["overlays"][14]
        provenance = current["registration_provenance"]
        additions = {"lexical_pr_preflight", "registration_provenance"}
        self.assertEqual(provenance["schema"], "OBSERVABLE_BELIEF_REGISTRATION_PROVENANCE_V1")
        self.assertEqual(set(provenance["metadata_additions_only"]), additions)
        self.assertTrue(provenance["raw_evidence_bytes_preserved"])
        self.assertFalse(provenance["consumer_registry_modified"])
        self.assertEqual(provenance["git_object_pr_preflight"], "NOT_PERFORMED_SEPARATE_GATE")
        fingerprint = "778b37210962b487cedd2d5d50e9fa95c1297987ec4e18630da7fbc1ccd883c2"
        self.assertEqual(provenance["source_tree_sha256"], fingerprint)
        self.assertEqual(provenance["baseline_ref"], current["baseline_ref"])
        inputs = provenance["inputs"]
        self.assertEqual(len({(row["role"], row["path"]) for row in inputs}), len(inputs))
        for row in inputs:
            with self.subTest(archived_input=row["path"]):
                path = reuse.REPO / row["path"]
                self.assertTrue(path.resolve().is_relative_to(reuse.REPO.resolve()))
                self.assertEqual(reuse.sha256(path.read_bytes()).hexdigest(), row["sha256"])
        raw_rows = [row for row in inputs if row["role"] == "actual_native_output"
                    and row["path"].endswith("/OBSERVABLE_BELIEF_REUSE_OVERLAY_V1.json")]
        self.assertEqual(len(raw_rows), 1)
        raw_path = reuse.REPO / raw_rows[0]["path"]
        raw = json.loads(raw_path.read_text())
        self.assertEqual(set(current) - set(raw), additions)
        self.assertEqual({key: value for key, value in current.items() if key not in additions}, raw)
        archive = raw_path.parent
        self.assertEqual((archive / "REGISTERED_OVERLAY.json").read_bytes(), reuse.OVERLAY_PATHS[14].read_bytes())
        receipt = json.loads((archive / "REGISTRATION_RECEIPT.json").read_text())
        self.assertEqual(receipt["schema"], "OBSERVABLE_BELIEF_REGISTRATION_RECEIPT_V1")
        self.assertEqual(receipt["state"], "PASS_METADATA_ONLY_CONSUMER_UNCHANGED")
        self.assertEqual(receipt["raw_overlay_sha256"], raw_rows[0]["sha256"])
        self.assertEqual(receipt["registered_overlay"]["sha256"], reuse.OVERLAY_SHA256S[14])
        self.assertEqual(set(receipt["added_top_level_keys"]), additions)
        self.assertTrue(receipt["stripped_registered_json_equals_raw"])
        self.assertIsNone(receipt["candidate_ref"])
        self.assertEqual(receipt["input_files"], inputs)
        preflight = json.loads((archive / "SOURCE_PREFLIGHT.json").read_text())
        self.assertEqual(preflight["status"], "PENDING_ACTUAL_NATIVE_EXECUTION")
        self.assertEqual(preflight["source_tree_sha256"], fingerprint)
        self.assertEqual(preflight["complete_source_modules"], 701)
        self.assertEqual(preflight["added_modules"], current["added_modules"])
        frozen = json.loads((archive / "FROZEN_INPUTS.json").read_text())
        self.assertEqual(frozen["source_tree_sha256"], fingerprint)
        self.assertEqual(frozen["new_public"], 30)
        self.assertEqual(frozen["lexical_hinted"], 5)
        self.assertEqual(set(frozen["public_source_names"]),
                         {row["name"] for row in current["public_theorems"]})
        execution = json.loads((archive / "STATUS.json").read_text())
        self.assertEqual(execution["state"], "PASS_PENDING_INDEPENDENT_REVIEW_AND_REGISTRATION")
        self.assertTrue(current["native_execution"]["fixed_export_equals_initial_native_export"])
        self.assertEqual(json.loads((archive / "observed_first_native.json").read_text()),
                         json.loads((reuse.REPO / current["native_export_evidence"]["path"]).read_text()))
        for row in current["native_execution"]["results"]:
            log = archive / ("native_export.log" if row["label"] == "native_export" else "fixed_verifier.log")
            self.assertEqual(row["exit_code"], 0)
            self.assertEqual(reuse.sha256(log.read_bytes()).hexdigest(), row["log_sha256"])
        lexical = current["lexical_pr_preflight"]
        self.assertIsNone(lexical["candidate_ref"])
        self.assertEqual(lexical["new_public_source_theorem_count"], 30)
        self.assertEqual(lexical["base_public_lexical_theorem_count"], 4433)
        self.assertEqual(lexical["candidate_public_lexical_theorem_count"], 4463)
        self.assertEqual(lexical["candidate_registered_public_source_theorem_count"], 4463)
        self.assertEqual(lexical["new_theorems_with_lexical_reuse_candidates"], 5)


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
        self.assertEqual(len(live), 701)
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
