#!/usr/bin/env python3
"""Prepare, review and apply the six existing action/gauge/transport consumers.

Run only after the unchanged native gates and metadata-only registration pass.
Preparation writes outside the repository. Application changes exactly the five
existing consumers and the DAG produced by the existing, unchanged generator.
No prior overlay, native export, certificate or clone evidence is rewritten.
"""
from __future__ import annotations

import argparse
import ast
from hashlib import sha256
import importlib.util
import json
import os
from pathlib import Path, PurePosixPath
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
if not __debug__:
    raise RuntimeError("OPTIMIZED_PYTHON_DISABLES_REQUIRED_ASSERTIONS")

CORE = "formalization/ueot-core/"
PACKET = CORE + "docs/compression/theory_completion/unified_closure/"
KNOWLEDGE = CORE + "docs/compression/theory_completion/knowledge/"
REUSE = KNOWLEDGE + "reuse/"
PROTOCOL = PACKET + "action_gauge_transport_v1/native_protocol/"
GENERATOR = PACKET + "build_umc_global_map.py"
DAG = PACKET + "UMC_GLOBAL_MODULE_DAG_V4.json"
CONSUMERS = (KNOWLEDGE + "README.md", REUSE + "fkrg_reuse.py",
             REUSE + "test_fkrg_reuse.py", REUSE + "REBUILD_CLONE_CANDIDATES.py",
             REUSE + "README.md")
SCOPE = (*CONSUMERS, DAG)
NAME = "ACTION_GAUGE_TRANSPORT"
OVERLAY = REUSE + NAME + "_REUSE_OVERLAY_V1.json"
NATIVE = REUSE + NAME + "_NATIVE_V1.json"
VERIFIER = REUSE + "VERIFY_" + NAME + "_OVERLAY_TYPES.lean"
ROLE = "UNCOUNTED_ACTION_REALIZABILITY_GAUGE_AND_CONDITIONED_TRANSPORT"
OLD_SOURCE = "0e17dd5ef3c4a9e3eaea47c8c0b7e83f6ef097915bed6092ca81e3e6c032abe0"
OLD_BASE = "7708a3a1289b1a009c269d81edceef06a4c347dc"
OLD_NATIVE = "00907d59fa7b780759ea4de80ae68a94ac4faebad0eb3492b71539b4f2d619d4"
PREFIX = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure."
MODULES = sorted(PREFIX + x for x in
                 ("FiniteActionRealizability", "FiniteActionRealizabilityWitness",
                  "DualDriveLinearGaugeClassification", "DualDriveOperationalAnchors",
                  "ConditionedActionTransport"))
PRIOR_CENSUS = {
    "module_source_hashes_verified": 703, "ueot_maintained_modules": 692,
    "vendor_modules": 11, "public_source_theorems_with_direct_proof_graph": 4474,
    "overlay_public_theorems": 681, "overlay_lexical_reuse_candidates": 177,
    "overlay_count": 16, "overlay_registered_direct_edges": 1039,
    "verified_equal_type_groups": 37, "equal_type_statement_names": 77,
    "near_type_not_defeq_candidate_pairs": 15,
    "crossfile_exact_code_clone_candidates": 68,
    "overlay_cross_snapshot_defeq_matches": 0,
    "overlay_historical_public_repairs": 1,
    "overlay_existing_registered_direct_edge_repairs": 1,
}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(data):
    return sha256(data).hexdigest()


def encoded(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode()


def git(repo, *args):
    return subprocess.check_output(["git", *args], cwd=repo)


def load_python(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def safe_path(repo, relative):
    relative = PurePosixPath(relative)
    require(not relative.is_absolute() and ".." not in relative.parts and str(relative) != ".",
            "INVALID_REPOSITORY_RELATIVE_PATH")
    path = repo.joinpath(*relative.parts)
    require(path.resolve().is_relative_to(repo) and not path.is_symlink(),
            "REPOSITORY_PATH_ESCAPE: " + str(relative))
    return path


def once(source, old, new):
    require(source.count(old) == 1, "CONSUMER_ANCHOR_DRIFT: " + old)
    return source.replace(old, new, 1)


def methods(source):
    return {n.name: ast.dump(n, include_attributes=False)
            for cls in ast.parse(source).body if isinstance(cls, ast.ClassDef)
            for n in cls.body if isinstance(n, ast.FunctionDef) and n.name.startswith("test_")}


def assignment(tree, name):
    rows = [n for n in tree.body if isinstance(n, ast.Assign)
            and any(isinstance(t, ast.Name) and t.id == name for t in n.targets)]
    require(len(rows) == 1, "REGISTRY_ASSIGNMENT_DRIFT: " + name)
    return rows[0]


def append_registry(source, values):
    """Insert only the four append entries, using their exact AST list bounds."""
    before = ast.parse(source)
    replacements = []
    lines = source.splitlines(keepends=True)
    for name, expression in values.items():
        node = assignment(before, name).value
        require(isinstance(node, ast.List) and len(node.elts) == 16,
                "REGISTRY_MUST_HAVE_EXACTLY_SIXTEEN_OLD_ENTRIES: " + name)
        require(lines[node.end_lineno - 1].strip() == "]", "REGISTRY_LIST_LAYOUT_DRIFT")
        offset = sum(map(len, lines[:node.end_lineno - 1]))
        replacements.append((offset, "    " + expression + ",\n"))
    changed = source
    for offset, addition in sorted(replacements, reverse=True):
        changed = changed[:offset] + addition + changed[offset:]
    changed = once(changed, "noisy-oracle, observable-belief and conditional-stability overlays",
                   "noisy-oracle, observable-belief, conditional-stability and action/gauge/transport overlays")
    after = ast.parse(changed)
    for name in values:
        old, new = assignment(before, name).value, assignment(after, name).value
        require(len(new.elts) == 17 and
                [ast.dump(x) for x in new.elts[:16]] == [ast.dump(x) for x in old.elts],
                "REGISTRY_APPEND_CHANGED_HISTORY: " + name)
    for name in ("EVIDENCE_SHA", "CLONE_SHA256", "LEDGER_SHA256", "BUILD_ENVIRONMENT_SHA256"):
        require(ast.dump(assignment(before, name)) == ast.dump(assignment(after, name)),
                "IMMUTABLE_PIN_CHANGED: " + name)
    return changed


def method_source(source, name):
    rows = [node for node in ast.walk(ast.parse(source))
            if isinstance(node, ast.FunctionDef) and node.name == name]
    require(len(rows) == 1, "MISSING_UNIQUE_PREDECESSOR_TEST: " + name)
    node, lines = rows[0], source.splitlines(keepends=True)
    return "".join(lines[node.lineno - 1:node.end_lineno]).rstrip() + "\n\n"


def new_tests(original, e):
    first = method_source(original, "test_conditional_stability_native_ownership_and_registered_edges")
    for old, new in (
        ('test_conditional_stability_', 'test_action_gauge_transport_'),
        ('["overlays"][15]', '["overlays"][16]'),
        ('"FiniteConditionalStability", "FiniteConditionalStabilityWitness"',
         '"FiniteActionRealizability", "FiniteActionRealizabilityWitness",\n'
         '            "DualDriveLinearGaugeClassification", "DualDriveOperationalAnchors",\n'
         '            "ConditionedActionTransport"'),
        ('["base_snapshot_modules"], 701', '["base_snapshot_modules"], 703'),
        ('reuse.OVERLAY_SHA256S[14]', 'reuse.OVERLAY_SHA256S[15]'),
        (OLD_BASE, e["base"]), (OLD_SOURCE, e["source"]),
        ('UNCOUNTED_FINITE_CONDITIONAL_STABILITY', ROLE),
        (OLD_NATIVE, e["native_sha"]),
        ('CONDITIONAL_STABILITY_NATIVE_EXPORT_V1', NAME + '_NATIVE_EXPORT_V1'),
        ('len(scope), 63', f'len(scope), {e["all_native"]}'),
        ('for row in scope), 34', f'for row in scope), {e["private_native"]}'),
        ('len(public), 11', f'len(public), {e["new_public"]}'),
        ('for row in scope), 18', f'for row in scope), {e["other_public_native"]}'),
        ('len(edges), 19', f'len(edges), {e["new_edges"]}'),
        ('["registered_prior_theorems"], 4463', '["registered_prior_theorems"], 4474'),
        ('11 * 4463', f'{e["new_public"]} * 4474'),
        ('11 * 10 // 2', f'{e["new_public"]} * {e["new_public"] - 1} // 2'),
    ):
        first = once(first, old, new)
    second = '''    def test_action_gauge_transport_actual_actions_initial_law_and_c4_routes(self):
        current = self.data["overlays"][16]
        native = json.loads((reuse.REPO / current["native_export_evidence"]["path"]).read_text())
        by_name = {row["name"]: row for row in native["all_native_theorem_constants"]}
        prefix = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure."
        action = prefix + "FiniteActionRealizabilityCheck."
        witness = prefix + "FiniteActionRealizabilityWitnessCheck."
        transport = prefix + "ConditionedActionTransportCheck."
        required = {
            action + "row_realizable_iff_mem_convexHull": {
                action + "pmf_barycenter_exists_iff_mem_convexHull", action + "realRow_actionMixture"},
            action + "observation_realizable_iff_fiber_convexHull": {
                action + "pmf_barycenter_exists_iff_mem_convexHull", action + "realRow_actionMixture"},
            action + "actual_state_path_eq_target": {
                prefix + "SourcePolicyPathBridgeCheck.actual_state_path_eq_stationary_path",
                action + "stationary_row_eq_actionMixture"},
            action + "initial_tv_le_path_tv": {
                action + "causalLaw_initial_marginal", "UEOT.V3.TotalVariation.tvDist_map_le"},
            witness + "conditional_row_outside_original_action_hull": {
                action + "row_realizable_iff_mem_convexHull",
                witness + "original_actions_have_irreducible_conditional_error"},
            witness + "unchanged_initial_forces_path_error": {
                action + "initial_tv_le_path_tv", witness + "actual_conditioning_changes_initial_tv"},
            transport + "time_action_state_path_eq_mixture": {
                prefix + "SourcePolicyPathBridgeCheck.actual_next_state_eq_stationary_row",
                action + "stationary_row_eq_actionMixture"},
            transport + "occupied_fibers_supply_actual_path": {
                action + "observation_realizable_iff_fiber_convexHull",
                transport + "time_action_state_path_eq_mixture"},
            transport + "occupied_conditioned_fibers_supply_actual_experiment": {
                transport + "occupied_fibers_supply_actual_path",
                prefix + "TotalFiniteWindowCheck.generated_ambient_eq_actual"},
            transport + "state_selection_realizes_its_conditioned_path": {
                transport + "occupied_conditioned_fibers_supply_actual_experiment",
                action + "observation_realizable_iff_fiber_convexHull"},
        }
        for name, dependencies in required.items():
            with self.subTest(symbol=name):
                actual = set(reuse.explain(self.data, name)["direct_existing_source_theorem_uses"])
                self.assertTrue(dependencies <= actual, (name, dependencies - actual))
        for suffix in ("original_actions_have_irreducible_conditional_error",
                       "added_safe_actions_realize_conditional_row",
                       "deterministic_extended_action_does_not_realize",
                       "separately_feasible_hidden_rows", "no_common_policy_for_aliased_rows",
                       "actual_conditioning_changes_initial_tv", "unchanged_initial_forces_path_error"):
            self.assertIn(witness + suffix, self.data["graph"])
        obstruction = "".join(by_name[witness + "original_actions_have_irreducible_conditional_error"]["type"].split())
        for fragment in ("tvDist", "3/4", "1/4", "targetConditionalRow"):
            self.assertIn(fragment, obstruction)
        concrete = by_name[transport + "state_selection_realizes_its_conditioned_path"]["type"]
        for fragment in ("stateSelectionModel", "preparedInitial", "actualConditionedPrefix", "riskMicroControlKernel"):
            self.assertIn(fragment, concrete)
        self.assertNotIn("OccupiedFiberFeasible", concrete)
        for row in current["public_theorems"]:
            self.assertEqual(reuse.explain(self.data, row["name"])["role"],
                             "UNCOUNTED_ACTION_REALIZABILITY_GAUGE_AND_CONDITIONED_TRANSPORT")

'''
    third = '''    def test_action_gauge_transport_inverse_classification_and_operational_anchors(self):
        current = self.data["overlays"][16]
        native = json.loads((reuse.REPO / current["native_export_evidence"]["path"]).read_text())
        by_name = {row["name"]: row for row in native["all_native_theorem_constants"]}
        prefix = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure."
        required = {
            "same_linear_response_iff_unique_gauge": {prefix + "nondegenerate_linear_factorization_unique_gauge"},
            "oriented_axis_rays_iff_positive_diagonal_gauge": {
                prefix + "labelled_axis_lines_iff_nonzero_diagonal_gauge"},
            "registered_unit_interventions_identify_factorization": {
                prefix + "nondegenerate_linear_factorization_unique_gauge",
                prefix + "two_unit_anchors_identify_gauge"},
        }
        for name, dependencies in required.items():
            with self.subTest(symbol=name):
                actual = set(reuse.explain(self.data, prefix + name)["direct_existing_source_theorem_uses"])
                self.assertTrue(dependencies <= actual, (name, dependencies - actual))
        statement = by_name[prefix + "nondegenerate_linear_factorization_unique_gauge"]["type"]
        for fragment in ("Surjective", "Injective", "comp", "symm"):
            self.assertIn(fragment, statement)
        self.assertTrue("∃!" in statement or "ExistsUnique" in statement)
        calibration = by_name[prefix + "registered_unit_interventions_identify_factorization"]["type"]
        for fragment in ("driveUnitAxis", "hanchor", "Injective"):
            self.assertIn(fragment, calibration)
        for suffix in ("one_unit_anchor_leaves_nontrivial_gauge",
                       "two_oriented_axes_do_not_identify_units"):
            self.assertIn(prefix + suffix, self.data["graph"])
            self.assertIn("≠", by_name[prefix + suffix]["type"])

'''
    last = method_source(original, "test_conditional_stability_registration_preserves_raw_execution")
    last = last.replace("CONDITIONAL_STABILITY", NAME)
    for old, new in (
        ('test_conditional_stability_', 'test_action_gauge_transport_'),
        ('["overlays"][15]', '["overlays"][16]'), (OLD_SOURCE, e["source"]),
        ('reuse.OVERLAY_PATHS[15]', 'reuse.OVERLAY_PATHS[16]'),
        ('reuse.OVERLAY_SHA256S[15]', 'reuse.OVERLAY_SHA256S[16]'),
        ('["complete_source_modules"], 703', '["complete_source_modules"], 708'),
        ('["new_public"], 11', f'["new_public"], {e["new_public"]}'),
        ('["lexical_hinted"], 0', f'["lexical_hinted"], {e["hinted"]}'),
        ('["new_public_source_theorem_count"], 11', f'["new_public_source_theorem_count"], {e["new_public"]}'),
        ('["base_public_lexical_theorem_count"], 4463', '["base_public_lexical_theorem_count"], 4474'),
        ('["candidate_public_lexical_theorem_count"], 4474',
         f'["candidate_public_lexical_theorem_count"], {e["total_public"]}'),
        ('["candidate_registered_public_source_theorem_count"], 4474',
         f'["candidate_registered_public_source_theorem_count"], {e["total_public"]}'),
        ('["new_theorems_with_lexical_reuse_candidates"], 0',
         f'["new_theorems_with_lexical_reuse_candidates"], {e["hinted"]}'),
    ):
        last = once(last, old, new)
    return first + second + third + last


def render_consumers(original, e):
    changed = dict(original)
    p = REUSE + "fkrg_reuse.py"
    changed[p] = append_registry(changed[p], {
        "OVERLAY_PATHS": 'HERE / "ACTION_GAUGE_TRANSPORT_REUSE_OVERLAY_V1.json"',
        "OVERLAY_TYPE_CHECKS": 'HERE / "VERIFY_ACTION_GAUGE_TRANSPORT_OVERLAY_TYPES.lean"',
        "OVERLAY_SHA256S": repr(e["overlay_sha"]),
        "OVERLAY_TYPE_CHECK_SHA256S": repr(e["verifier_sha"]),
    })
    p = REUSE + "test_fkrg_reuse.py"
    s = changed[p]
    current = {**PRIOR_CENSUS,
        "module_source_hashes_verified": 708, "ueot_maintained_modules": 697,
        "public_source_theorems_with_direct_proof_graph": e["total_public"],
        "overlay_public_theorems": e["overlay_public"],
        "overlay_lexical_reuse_candidates": e["total_hinted"], "overlay_count": 17,
        "overlay_registered_direct_edges": e["overlay_edges"]}
    for key, new in current.items():
        if new != PRIOR_CENSUS[key]:
            s = once(s, f'self.assertEqual(res["{key}"], {PRIOR_CENSUS[key]})',
                     f'self.assertEqual(res["{key}"], {new})')
    s = once(s, 'for row in self.data["graph"].values()), 5926)',
             f'for row in self.data["graph"].values()), {e["total_edges"]})')
    s = once(s, 'self.assertEqual(len(self.data["overlays"]), 16)',
             'self.assertEqual(len(self.data["overlays"]), 17)')
    s = once(s, 'self.assertEqual(len(live), 703)', 'self.assertEqual(len(live), 708)')
    anchor = '    def test_historical_apostrophe_registration_and_existing_incoming_edge(self):'
    s = once(s, anchor, new_tests(original[p], e) + anchor)
    before, after = methods(original[p]), methods(s)
    require(len(before) == 74 and len(after) == 78 and set(before) <= set(after),
            "REGRESSION_TEST_SET_DRIFT")
    live = {"test_evidence_and_sources_exact_baseline",
            "test_calibrated_defect_overlay_chain_and_kernel_graph",
            "test_new_lean_module_cannot_be_omitted_from_index"}
    require(all(before[name] == after[name] for name in set(before) - live),
            "HISTORICAL_REGRESSION_WAS_CHANGED")
    changed[p] = s

    p = REUSE + "REBUILD_CLONE_CANDIDATES.py"
    s = changed[p]
    for old, new in (
        ('703 modules (692 maintained', '708 modules (697 maintained'),
        ('plus sixteen governed overlays', 'plus seventeen governed overlays'),
        ('noisy-oracle, observable-belief, and conditional-stability. The historical',
         'noisy-oracle, observable-belief, conditional-stability, and action/gauge/transport. The historical'),
    ):
        s = once(s, old, new)
    before, after = ast.parse(original[p]), ast.parse(s)
    require(ast.dump(ast.Module(body=before.body[1:], type_ignores=[])) ==
            ast.dump(ast.Module(body=after.body[1:], type_ignores=[])),
            "CLONE_SCANNER_RUNTIME_WAS_CHANGED")
    changed[p] = s

    p = KNOWLEDGE + "README.md"
    s = changed[p]
    start = s.index('The current conditional-stability source census')
    end = s.index('\n\n', start)
    s = s[:start] + f'''The current action/gauge/transport source census contains **708 bundled Lean modules: 697 UEOT-maintained and 11 adapted upstream modules**, with seventeen additive overlays. The registered public proof graph contains **{e["total_public"]:,} nodes and {e["total_edges"]:,} direct edges**. Five new modules classify finite-action implementation of target rows, derive a concrete occupied-fiber conditional-path consumer, classify nondegenerate linear factorizations up to a unique gauge, and separate calibrated operational anchors from residual scaling freedom. The frozen source fingerprint is `{e["source"]}`. The complete native export retains {e["all_native"]} owned theorem constants, including {e["new_public"]} registered public source theorems, {e["private_native"]} private constants and {e["other_public_native"]} other public native constants. The [layer-seventeen evidence](reuse/README.md#layer-17--action-realizability-gauge-classification-and-conditioned-transport) separates native, source, registration and consumer checks; canonical Git and release states retain their own evidence.''' + s[end:]
    s = once(s, 'The fifteenth overlay retains',
             'The sixteenth overlay retains its historical 703-module conditional-stability census, its two new modules and its own full-build/native results. The fifteenth overlay retains')
    summary = f'''The seventeenth [action/gauge/transport overlay](reuse/ACTION_GAUGE_TRANSPORT_REUSE_OVERLAY_V1.json) adds **{e["new_public"]} public source theorems in five modules**. Their raw stored types underwent **{e["cross_comparisons"]:,} cross-registry and {e["internal_comparisons"]:,} internal** comparisons with zero collisions, and their compiled proofs add **{e["new_edges"]} registered direct edges**. The current totals are {e["overlay_public"]} overlay nodes, {e["overlay_edges"]} outgoing overlay edges and {e["total_hinted"]} lexical hint groups. All prior evidence and the immutable clone table remain pinned.

Finite-action randomization realizes exactly the convex hull of the actual transition rows. Under current-observation feedback, one common mixture must realize the entire occupied observation-fiber family. The existing three-state source supplies strict conditional-row errors `1/4` and `3/4` under its original singleton action set; adding two safe deterministic actions permits the same target by randomization. A separate aliased-observation example isolates the common-mixture obstruction. Every causal scheme retains its initial marginal, and the actual survival tilt of the existing witness yields a `1/4` full-path lower bound if the original initial law is kept. The time-dependent consumer uses the same original model, the correctly prepared initial tilt and the previously derived total conditional window; only occupied fibers before the horizon require feasibility. A fully actuated state-selection family proves its own feasibility. This is concrete finite-horizon operational transport, not ontic parent identification or a general-history impossibility theorem.

For exact linear factorizations with surjective encoders and injective decoders, equality of the complete response is equivalent to one unique invertible latent coordinate change. In the two-dimensional instance, two labelled axis lines leave nonzero diagonal scales, oriented rays leave positive scales, and two independently unit-calibrated input interventions identify both factors. One-unit-anchor shear and uncalibrated positive-scaling examples retain the necessary ambiguity. These assumptions do not follow from a rank upper bound or from fitted latent axes, and no new empirical calibration is claimed. Strong global closure remains `NOT_ESTABLISHED`; external scientific evidence remains `UNVERIFIED`.

'''
    s = once(s, '## Required startup/recovery protocol (every new chat/agent)',
             summary + '## Required startup/recovery protocol (every new chat/agent)')
    changed[p] = s

    p = REUSE + "README.md"
    s = changed[p]
    s = once(s,
        'The current sixteen-layer census is **703 modules = 692 UEOT-maintained + 11\nadapted upstream**, with **4,474 registered public theorem nodes** and\n**5,926 registered direct proof edges**.',
        f'The current seventeen-layer census is **708 modules = 697 UEOT-maintained + 11\nadapted upstream**, with **{e["total_public"]:,} registered public theorem nodes** and\n**{e["total_edges"]:,} registered direct proof edges**.')
    layer = f'''### Layer 17 — action realizability, gauge classification and conditioned transport

This layer is based on `{e["base"]}`
and frozen source fingerprint `{e["source"]}`.
Five modules add **{e["new_public"]} registered public source theorems** and
**{e["new_edges"]} direct registered edges**.

| Evidence | SHA-256 |
| --- | --- |
| [Complete native export](ACTION_GAUGE_TRANSPORT_NATIVE_V1.json) | `{e["native_sha"]}` |
| [Fixed Lean certificate](VERIFY_ACTION_GAUGE_TRANSPORT_OVERLAY_TYPES.lean) | `{e["verifier_sha"]}` |
| [Registered overlay](ACTION_GAUGE_TRANSPORT_REUSE_OVERLAY_V1.json) | `{e["overlay_sha"]}` |

The complete native census retains **{e["all_native"]} owned theorem constants:
{e["new_public"]} public source candidates, {e["private_native"]} private constants and
{e["other_public_native"]} other public native constants**. Actual owners, stored
universes, displayed types, full direct constants, direct theorem constants and
standard-only transitive axiom closures are retained. Compiler ownership can
depend on import order; other-public constants are not automatically new source
declarations or independent mathematical results. Public stored types underwent
**{e["cross_comparisons"]:,} cross-layer** comparisons against 4,474 prior
registrations and **{e["internal_comparisons"]:,} internal** `Meta.isDefEq` comparisons,
with zero collisions. The fixed exporter reproduces the initial native export.
These checks do not prove general logical independence.

The current graph contains **{e["total_public"]:,} nodes and {e["total_edges"]:,} direct
edges**, including **{e["overlay_public"]} overlay nodes and {e["overlay_edges"]} outgoing
overlay edges**. The historical old-node repair remains separate. The {e["hinted"]}
new lexical hint groups bring their total to **{e["total_hinted"]}**. Lexical hints
are distinct from compiled dependencies and independent mathematical review.

`FiniteActionRealizability` converts an actual `PMF.bind` over allowed actions
to finite real convex combinations and proves both directions of implementation
iff convex-hull membership. Its observation criterion uses a single mixture of
entire row families on each observation fiber. Existing actual action/state path
identities supply the whole-path consumer. All causal transition schemes keep
the initial record marginal, giving a TV lower bound from any initial mismatch.

`FiniteActionRealizabilityWitness` conditions the existing singleton-action
three-state source row, rather than choosing an independent target. Its strict
best possible errors are `1/4` and `3/4`; the target is outside the old action
hull. Keeping the old action while adding two deterministic safe actions permits
the same target through fair randomization, but no deterministic member suffices.
Two hidden states can each be feasible while their aliased current observation
admits no common action mixture. In the original path witness, the conditional
initial tilt alone forces at least `1/4` error for every future causal kernel
started from the unchanged initial law.

`ConditionedActionTransport` constructs a time-dependent current-observation
policy from convex feasibility on target-occupied fibers. Erasing actions from
its actual experiment yields the previously constructed total conditional path
of the same source, with the correctly prepared survival-tilted initial law.
Unoccupied and null rows impose no feasibility obligation. An explicit model
with every deterministic state-selection action proves its own feasibility and
therefore implements every declared positive finite conditional window. These
are finite-horizon operational transport claims. They do not assert ontic parent
equality, autonomous initial-law preparation, or a no-go for informative memory.

`DualDriveLinearGaugeClassification` proves that two exact nondegenerate linear
factorizations of the same complete response differ by one unique invertible
latent map. Surjective encoders and injective decoders are explicit hypotheses;
the theorem applies to GL(2) on the existing `TwoDriveLatent` instance. It does not
turn a noisy rank estimate or rank upper bound into exact nondegeneracy.
`DualDriveOperationalAnchors` classifies the residual labelled-axis and oriented-ray
scales, proves identification from two independently unit-calibrated input
interventions, and retains one-anchor shear and uncalibrated-scaling witnesses.
The operational calibration premises are not inferred from the fitted response;
physical axis meanings and empirical selective interventions remain external.

Registration preserves raw execution bytes and adds only lexical preflight and
registration provenance. All sixteen earlier overlays, native exports and fixed
certificates, the historical equal/near-type artifacts and the 68-row clone table
remain immutable. Four added regressions inspect native ownership and edges,
actual action/initial-law/C4 proof routes, inverse-classification and anchor routes,
and registration provenance. Actual command receipts remain separate. Counted
classifications stay unchanged; strong global closure is `NOT_ESTABLISHED` and
external scientific evidence is `UNVERIFIED`.

'''
    s = once(s, '## Run from repository root', layer + '## Run from repository root')
    s = once(s, 'lake env lean docs/compression/theory_completion/knowledge/reuse/VERIFY_CONDITIONAL_STABILITY_OVERLAY_TYPES.lean',
             'lake env lean docs/compression/theory_completion/knowledge/reuse/VERIFY_ACTION_GAUGE_TRANSPORT_OVERLAY_TYPES.lean')
    s = once(s, 'sixteen governed overlays extend the live census to 703 = 692 + 11.',
             'seventeen governed overlays extend the live census to 708 = 697 + 11.')
    s = once(s,
        '3,793 immutable-base public source theorem proofs + 681 governed registrations\n  (including one historical public-name repair) = 4,474 live graph nodes, with\n  5,926 direct registered-source theorem',
        f'3,793 immutable-base public source theorem proofs + {e["overlay_public"]} governed registrations\n  (including one historical public-name repair) = {e["total_public"]:,} live graph nodes, with\n  {e["total_edges"]:,} direct registered-source theorem')
    s = once(s, 'fifteenth adds 29 and the sixteenth adds 19, giving\n  1039 outgoing edges from overlay nodes;',
             f'fifteenth adds 29, the sixteenth adds 19, and the seventeenth adds {e["new_edges"]}, giving\n  {e["overlay_edges"]} outgoing edges from overlay nodes;')
    s = once(s, 'all 703 modules', 'all 708 modules')
    s = once(s, 'exact 703-module live source census', 'exact 708-module live source census')
    changed[p] = s
    require(set(changed) == set(CONSUMERS), "CONSUMER_SCOPE_DRIFT")
    for path, content in changed.items():
        require(content != original[path], "UNCHANGED_CONSUMER: " + path)
        if path.endswith('.py'):
            ast.parse(content, filename=path)
    return changed


def evidence(repo, base, frozen_path):
    """Only completed registration/native evidence can supply live statistics."""
    adapter = load_python("action_gauge_transport_consumer_adapter", repo / PROTOCOL / "protocol_adapter.py")
    frozen, frozen_bytes = adapter.frozen(repo, frozen_path, base)
    base = frozen["baseline_ref"]
    require((frozen["prior_modules"], frozen["prior_registered_public"], frozen["prior_overlays"],
             frozen["complete_modules"]) == (703, 4474, 16, 708), "WRONG_FROZEN_CENSUS")
    helper = load_python("action_gauge_transport_consumer_predecessor", repo / adapter.OLD / "integration_native.py")
    consumer, base_sha = helper.load_base_consumer(repo, base, "action_gauge_transport_consumer_baseline")
    require(base_sha == frozen["baseline_consumer_sha256"], "BASE_CONSUMER_IDENTITY_DRIFT")
    prior = consumer.load(verify_source=False)
    status = consumer.status(prior)
    require(all(status[k] == v for k, v in PRIOR_CENSUS.items()), "WRONG_PRIOR_CONSUMER_CENSUS")
    prior_edges = sum(len(json.loads(row["source_theorem_deps_json"])) for row in prior["graph"].values())
    require(prior_edges == 5926, "WRONG_PRIOR_EDGE_CENSUS")
    inputs = {}

    def read(relative):
        path = safe_path(repo, relative)
        data = path.read_bytes()
        inputs[relative] = digest(data)
        return data

    overlay_bytes, native_bytes, verifier_bytes = read(OVERLAY), read(NATIVE), read(VERIFIER)
    overlay, native = json.loads(overlay_bytes), json.loads(native_bytes)
    require(overlay["schema"] == "FKRG_REUSE_OVERLAY_V1" and
            overlay["overlay_id"] == NAME + "_REUSE_OVERLAY_V1", "WRONG_REGISTERED_OVERLAY")
    require(overlay["baseline_ref"] == base and overlay["base_snapshot_modules"] == 703 and
            overlay["source_checkpoint"] == "worktree-sha256:" + frozen["source_tree_sha256"],
            "REGISTERED_SOURCE_IDENTITY_DRIFT")
    require(overlay["scientific_role"] == ROLE and overlay["counted_core_impact"] == "NONE" and
            overlay["scientific_closure"] == "NOT_ESTABLISHED", "SCIENTIFIC_ROLE_DRIFT")
    require(not {"historical_public_repairs", "existing_proof_dependency_repairs"}.intersection(overlay),
            "UNEXPECTED_HISTORICAL_REPAIR")
    require(sorted(row["module"] for row in overlay["added_modules"]) == MODULES,
            "WRONG_NEW_MODULES")
    require(overlay["prior_overlay"] == {
        "path": consumer.OVERLAY_PATHS[-1].relative_to(repo).as_posix(),
        "sha256": consumer.OVERLAY_SHA256S[-1]}, "OVERLAY_CHAIN_DRIFT")
    require(overlay["native_export_evidence"] == {"path": NATIVE, "sha256": digest(native_bytes)},
            "NATIVE_EVIDENCE_IDENTITY_DRIFT")
    require(native["schema"] == NAME + "_NATIVE_EXPORT_V1" and native["collisions"] == [],
            "NATIVE_NOT_CERTIFIED")
    public = {row["name"]: row for row in overlay["public_theorems"]}
    native_public = {row["name"]: row for row in native["public_source_theorems"]}
    require(len(public) == len(overlay["public_theorems"]) == frozen["new_public"] and
            set(public) == set(frozen["public_source_names"]) == set(native_public) and
            len(native_public) == len(native["public_source_theorems"]) and
            not set(public).intersection(prior["graph"]), "PUBLIC_REGISTRATION_SET_DRIFT")
    scope = native["all_native_theorem_constants"]
    by_name = {row["name"]: row for row in scope}
    require(len(by_name) == len(scope) and set(public) <= set(by_name) and
            {row["source_module"] for row in scope} == set(MODULES), "NATIVE_OWNERSHIP_DRIFT")
    fields = {"name", "source_module", "is_private", "level_parameters", "type",
              "direct_constants", "direct_theorem_constants", "axioms"}
    require(all(set(row) == fields and isinstance(row["is_private"], bool) and
                set(row["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"} and
                set(row["direct_theorem_constants"]) <= set(row["direct_constants"]) for row in scope),
            "NATIVE_FULL_SCOPE_FIELDS_OR_AXIOMS_DRIFT")
    graph_names = set(prior["graph"]) | set(public)
    edges = set()
    for name, row in public.items():
        full, exported = by_name[name], native_public[name]
        require(not full["is_private"] and row["source_module"] == full["source_module"],
                "PUBLIC_NATIVE_OWNERSHIP_DRIFT: " + name)
        require(all(exported[key] == full[key] for key in
                    ("source_module", "level_parameters", "type", "direct_constants")),
                "PUBLIC_NATIVE_FIELDS_DRIFT: " + name)
        actual = (set(full["direct_constants"]) & graph_names) - {name}
        require(set(row["source_theorem_deps"]) == set(exported["source_theorem_deps"]) == actual,
                "PUBLIC_NATIVE_EDGES_DRIFT: " + name)
        edges.update((name, target) for target in actual)
    cert, types = overlay["proof_dependency_certification"], overlay["type_distinctness"]
    require(cert["status"] == types["status"] == "PASS" and
            cert["registered_direct_edges"] == len(edges) and
            edges == {(row["source"], row["target"]) for row in cert["edges"]} and
            types["definitionally_equal_matches"] == 0 and
            types["registered_prior_theorems"] == 4474, "TYPE_OR_EDGE_CERTIFICATE_DRIFT")
    n = frozen["new_public"]
    for key, expected in (("cross_isDefEq_comparisons", n * 4474),
                          ("internal_isDefEq_comparisons", n * (n - 1) // 2)):
        require(types[key] == native[key] == expected, "TYPE_COMPARISON_CENSUS_DRIFT: " + key)
    provenance = overlay["registration_provenance"]
    additions = {"lexical_pr_preflight", "registration_provenance"}
    require(provenance["schema"] == NAME + "_REGISTRATION_PROVENANCE_V1" and
            provenance["baseline_ref"] == base and
            provenance["source_tree_sha256"] == frozen["source_tree_sha256"] and
            set(provenance["metadata_additions_only"]) == additions and
            provenance["raw_evidence_bytes_preserved"] is True and
            provenance["consumer_registry_modified"] is False, "REGISTRATION_PROVENANCE_DRIFT")
    require(len({(row["role"], row["path"]) for row in provenance["inputs"]}) ==
            len(provenance["inputs"]), "DUPLICATE_REGISTRATION_INPUT")
    for row in provenance["inputs"]:
        require(digest(read(row["path"])) == row["sha256"], "ARCHIVED_INPUT_CHANGED: " + row["path"])
    raw_rows = [row for row in provenance["inputs"] if row["role"] == "actual_native_output"
                and row["path"].endswith('/' + NAME + '_REUSE_OVERLAY_V1.json')]
    require(len(raw_rows) == 1, "MISSING_UNIQUE_RAW_OVERLAY")
    raw_path = PurePosixPath(raw_rows[0]["path"])
    archive = raw_path.parent
    raw = json.loads(read(raw_path.as_posix()))
    require(set(overlay) - set(raw) == additions and
            {k: v for k, v in overlay.items() if k not in additions} == raw,
            "REGISTRATION_CHANGED_RAW_PAYLOAD")
    require(read((archive / 'REGISTERED_OVERLAY.json').as_posix()) == overlay_bytes,
            "REGISTERED_ARCHIVE_BYTES_DRIFT")
    require(read((archive / PurePosixPath(NATIVE).name).as_posix()) == native_bytes and
            read((archive / PurePosixPath(VERIFIER).name).as_posix()) == verifier_bytes,
            "REGISTERED_NATIVE_OR_VERIFIER_BYTES_DRIFT")
    require(read((archive / 'FROZEN_INPUTS.json').as_posix()) == frozen_bytes,
            "ARCHIVED_FROZEN_INPUTS_DRIFT")
    receipt = json.loads(read((archive / 'REGISTRATION_RECEIPT.json').as_posix()))
    require(receipt["schema"] == NAME + "_REGISTRATION_RECEIPT_V1" and
            receipt["state"] == "PASS_METADATA_ONLY_CONSUMER_UNCHANGED" and
            receipt["registered_overlay"] == {"path": OVERLAY, "sha256": digest(overlay_bytes)} and
            receipt["raw_overlay_sha256"] == raw_rows[0]["sha256"] and
            set(receipt["added_top_level_keys"]) == additions and
            receipt["stripped_registered_json_equals_raw"] is True and
            receipt["input_files"] == provenance["inputs"], "REGISTRATION_RECEIPT_DRIFT")
    execution = json.loads(read((archive / 'STATUS.json').as_posix()))
    require(execution["state"] == "PASS_PENDING_INDEPENDENT_REVIEW_AND_REGISTRATION" and
            overlay["native_execution"]["fixed_export_equals_initial_native_export"] is True and
            json.loads(read((archive / 'observed_first_native.json').as_posix())) == native,
            "ACTUAL_NATIVE_EXECUTION_NOT_PASSED")
    native_execution = overlay["native_execution"]
    require(native_execution["source_tree_sha256"] == frozen["source_tree_sha256"] and
            native_execution["native_export_exit_code"] == native_execution["fixed_certificate_exit_code"] == 0 and
            native_execution["fixed_certificate_sha256"] == digest(verifier_bytes) and
            native_execution["results"] == execution["results"], "ACTUAL_NATIVE_EXECUTION_IDENTITY_DRIFT")
    axiom_census = overlay["native_axiom_census"]
    require(axiom_census["status"] == "PASS" and
            (axiom_census["physical_source_modules"], axiom_census["theorem_constants"],
             axiom_census["private_theorem_constants"], axiom_census["confirmed_public_source_candidates"],
             axiom_census["other_native_public_constants"]) ==
            (5, len(scope), sum(row["is_private"] for row in scope), n,
             sum(not row["is_private"] and row["name"] not in public for row in scope)),
            "REGISTERED_NATIVE_CENSUS_DRIFT")
    lexical = overlay["lexical_pr_preflight"]
    require((lexical["base_public_lexical_theorem_count"],
             lexical["candidate_public_lexical_theorem_count"],
             lexical["candidate_registered_public_source_theorem_count"],
             lexical["new_public_source_theorem_count"],
             lexical["new_theorems_with_lexical_reuse_candidates"]) ==
            (4474, 4474 + n, 4474 + n, n, frozen["lexical_hinted"]), "LEXICAL_CENSUS_DRIFT")
    # The six output files are the entire mutation scope. Preserve hashes of all
    # previously tracked reuse assets as an independent before/after guard.
    old_paths = git(repo, 'ls-tree', '-r', '--name-only', base, '--', REUSE).decode().splitlines()
    immutable = {}
    for relative in old_paths:
        if relative not in SCOPE:
            immutable[relative] = digest(safe_path(repo, relative).read_bytes())
    changed_old = git(repo, 'diff', '--name-only', '--no-renames', base, '--', REUSE).decode().splitlines()
    require(not (set(changed_old) & set(immutable)), "PREVIOUS_REUSE_ASSET_MODIFIED")
    require((repo / GENERATOR).read_bytes() == git(repo, 'show', base + ':' + GENERATOR),
            "IMMUTABLE_DAG_GENERATOR_CHANGED")
    inputs[GENERATOR] = digest((repo / GENERATOR).read_bytes())
    result = {
        "base": base, "source": frozen["source_tree_sha256"], "new_public": n,
        "hinted": frozen["lexical_hinted"], "new_edges": len(edges),
        "all_native": len(scope), "private_native": sum(row["is_private"] for row in scope),
        "other_public_native": sum(not row["is_private"] and row["name"] not in public for row in scope),
        "overlay_sha": digest(overlay_bytes), "native_sha": digest(native_bytes),
        "verifier_sha": digest(verifier_bytes), "total_public": 4474 + n,
        "overlay_public": 681 + n, "total_hinted": 177 + frozen["lexical_hinted"],
        "overlay_edges": 1039 + len(edges), "total_edges": prior_edges + len(edges),
        "cross_comparisons": types["cross_isDefEq_comparisons"],
        "internal_comparisons": types["internal_isDefEq_comparisons"],
    }
    return result, inputs, immutable, frozen_bytes


def verify_dag(data, source):
    require(data["source_tree_sha256"] == source and data["total_Lean_modules"] == 708 and
            data["reachable_from_UEOT_root"] == 708 and data["not_reachable_from_UEOT_root"] == [] and
            data["cycles_detected"] == [] and data["missing_internal_imports"] == {} and
            set(MODULES) <= set(data["entries"]), "GENERATED_DAG_SCOPE_OR_SOURCE_DRIFT")


def prepare(repo, base, frozen_path, output):
    require(not output.exists() and not output.is_relative_to(repo),
            "NEW_CANDIDATE_DIRECTORY_OUTSIDE_REPOSITORY_REQUIRED")
    e, inputs, immutable, frozen_bytes = evidence(repo, base, frozen_path)
    original = {}
    for relative in SCOPE:
        data = safe_path(repo, relative).read_bytes()
        require(data == git(repo, 'show', e["base"] + ':' + relative),
                "CONSUMER_ALREADY_CHANGED_FROM_BASE: " + relative)
        original[relative] = data
    changed = render_consumers({p: original[p].decode() for p in CONSUMERS}, e)
    output.mkdir(parents=True)
    for relative, content in changed.items():
        target = safe_path(output, relative)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(content)
    # Execute the exact original generator with only its output destination
    # redirected in memory. The generator source and actual source roots remain
    # unchanged, so it computes the genuine current 708-module DAG.
    generator = load_python('action_gauge_transport_original_dag_generator', repo / GENERATOR)
    generator.OUT = safe_path(output, DAG)
    generator.OUT.parent.mkdir(parents=True, exist_ok=True)
    generated = generator.manifest()
    verify_dag(generated, e["source"])
    candidates = {p: safe_path(output, p).read_bytes() for p in SCOPE}
    require(all(original[p] != candidates[p] for p in SCOPE), "UNCHANGED_OUTPUT_IN_SIX_FILE_SCOPE")
    for relative, expected in {**inputs, **immutable}.items():
        require(digest(safe_path(repo, relative).read_bytes()) == expected,
                "INPUT_CHANGED_DURING_PREPARATION: " + relative)
    manifest = {
        "schema": "ACTION_GAUGE_TRANSPORT_CONSUMER_CANDIDATES_V1",
        "state": "PREPARED_NOT_APPLIED_NATIVE_REGISTRATION_VERIFIED",
        "repo": str(repo), "base_ref": e["base"], "source_tree_sha256": e["source"],
        "frozen_inputs": {"path": str(frozen_path), "sha256": digest(frozen_bytes)},
        "preparer_sha256": digest(Path(__file__).read_bytes()), "census": e,
        "new_tests": 4, "total_tests": 78,
        "files": [{"path": p, "original_sha256": digest(original[p]),
                   "candidate_sha256": digest(candidates[p])} for p in SCOPE],
        "evidence_inputs": inputs, "unchanged_prior_reuse_assets": immutable,
        "dag_generator": {"path": GENERATOR, "sha256": inputs[GENERATOR]},
        "consumer_execution": "NOT_RUN", "clone_scan": "NOT_RUN",
    }
    (output / 'MANIFEST.json').write_bytes(encoded(manifest))
    return {"state": manifest["state"], "candidate_directory": str(output),
            "files": len(SCOPE), "census": e, "total_tests": 78,
            "production_files_modified": False}


def replace_bytes(path, data):
    """Replace a regular scoped file atomically, preserving its permission bits."""
    mode = path.stat().st_mode & 0o777
    fd, name = tempfile.mkstemp(prefix='.' + path.name + '.action-gauge-', dir=path.parent)
    tmp = Path(name)
    try:
        with os.fdopen(fd, 'wb') as stream:
            stream.write(data)
        tmp.chmod(mode)
        os.replace(tmp, path)
    finally:
        if tmp.exists():
            tmp.unlink()


def apply(repo, candidate_directory):
    manifest = json.loads((candidate_directory / 'MANIFEST.json').read_bytes())
    require(manifest["schema"] == "ACTION_GAUGE_TRANSPORT_CONSUMER_CANDIDATES_V1" and
            manifest["state"] == "PREPARED_NOT_APPLIED_NATIVE_REGISTRATION_VERIFIED" and
            manifest["repo"] == str(repo) and
            manifest["preparer_sha256"] == digest(Path(__file__).read_bytes()),
            "CANDIDATE_MANIFEST_IDENTITY_DRIFT")
    require([row["path"] for row in manifest["files"]] == list(SCOPE), "EXACT_SIX_FILE_SCOPE_REQUIRED")
    frozen_path = Path(manifest["frozen_inputs"]["path"]).resolve(strict=True)
    require(digest(frozen_path.read_bytes()) == manifest["frozen_inputs"]["sha256"],
            "FROZEN_INPUT_CHANGED_AFTER_PREPARATION")
    e, inputs, immutable, _ = evidence(repo, manifest["base_ref"], frozen_path)
    require(e == manifest["census"] and inputs == manifest["evidence_inputs"] and
            immutable == manifest["unchanged_prior_reuse_assets"], "EVIDENCE_CHANGED_AFTER_PREPARATION")
    originals, candidates = {}, {}
    for row in manifest["files"]:
        relative = row["path"]
        originals[relative] = safe_path(repo, relative).read_bytes()
        candidates[relative] = safe_path(candidate_directory, relative).read_bytes()
        require(digest(originals[relative]) == row["original_sha256"] and
                digest(candidates[relative]) == row["candidate_sha256"],
                "CONSUMER_OR_CANDIDATE_CHANGED: " + relative)
    rerendered = render_consumers({p: originals[p].decode() for p in CONSUMERS}, e)
    require(all(candidates[p] == rerendered[p].encode() for p in CONSUMERS),
            "CANDIDATE_DOES_NOT_MATCH_DETERMINISTIC_RENDER")
    verify_dag(json.loads(candidates[DAG]), e["source"])
    applied = []
    receipt_path = candidate_directory / 'APPLICATION_RECEIPT.json'
    require(not receipt_path.exists(), "APPLICATION_RECEIPT_ALREADY_EXISTS")
    try:
        for relative in SCOPE:
            target = safe_path(repo, relative)
            require(target.read_bytes() == originals[relative], "CONCURRENT_CONSUMER_EDIT: " + relative)
            replace_bytes(target, candidates[relative])
            applied.append(relative)
        current = load_python('action_gauge_transport_live_consumer', repo / REUSE / 'fkrg_reuse.py')
        data = current.load()
        status = current.status(data)
        expected = {**PRIOR_CENSUS, "module_source_hashes_verified": 708,
            "ueot_maintained_modules": 697, "public_source_theorems_with_direct_proof_graph": e["total_public"],
            "overlay_public_theorems": e["overlay_public"], "overlay_count": 17,
            "overlay_lexical_reuse_candidates": e["total_hinted"],
            "overlay_registered_direct_edges": e["overlay_edges"]}
        require(all(status[k] == v for k, v in expected.items()), "LIVE_CONSUMER_CENSUS_DRIFT")
        require(sum(len(json.loads(row["source_theorem_deps_json"])) for row in data["graph"].values()) ==
                e["total_edges"], "LIVE_GRAPH_EDGE_CENSUS_DRIFT")
        for relative, expected_sha in {**inputs, **immutable}.items():
            require(digest(safe_path(repo, relative).read_bytes()) == expected_sha,
                    "PREVIOUS_EVIDENCE_CHANGED_DURING_APPLY: " + relative)
        require(all(safe_path(repo, p).read_bytes() == candidates[p] for p in SCOPE),
                "CONSUMER_CHANGED_DURING_APPLY")
    except Exception as error:
        rolled_back, concurrent = [], []
        for relative in reversed(applied):
            target = safe_path(repo, relative)
            if target.read_bytes() == candidates[relative]:
                replace_bytes(target, originals[relative])
                rolled_back.append(relative)
            else:
                concurrent.append(relative)
        receipt_path.write_bytes(encoded({"state": "FAILED", "error": repr(error),
            "restored_original_files": rolled_back, "concurrent_edits_left_untouched": concurrent}))
        raise
    receipt = {"schema": "ACTION_GAUGE_TRANSPORT_CONSUMER_APPLICATION_V1",
        "state": "PASS_EXACT_SIX_FILES_APPLIED_AND_SOURCE_CENSUS_VERIFIED",
        "base_ref": e["base"], "source_tree_sha256": e["source"],
        "candidate_manifest_sha256": digest((candidate_directory / 'MANIFEST.json').read_bytes()),
        "changed_files": manifest["files"], "census": e,
        "prior_reuse_assets_byte_unchanged": len(immutable),
        "consumer_regression_execution": "NOT_RUN_SEPARATE_COMMAND",
        "clone_scan": "NOT_RUN_SEPARATE_COMMAND"}
    receipt_path.write_bytes(encoded(receipt))
    return receipt


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='mode', required=True)
    p = sub.add_parser('prepare')
    for option in ('repo', 'base-ref', 'frozen-inputs', 'output'):
        p.add_argument('--' + option, required=True)
    p = sub.add_parser('apply')
    p.add_argument('--repo', required=True)
    p.add_argument('--candidates', required=True)
    args = parser.parse_args()
    repo = Path(args.repo).resolve(strict=True)
    if args.mode == 'prepare':
        result = prepare(repo, args.base_ref, Path(args.frozen_inputs).resolve(strict=True),
                         Path(args.output).resolve())
    else:
        candidate_directory = Path(args.candidates).resolve(strict=True)
        require(not candidate_directory.is_relative_to(repo), "CANDIDATES_MUST_BE_OUTSIDE_REPOSITORY")
        result = apply(repo, candidate_directory)
    print(json.dumps(result, ensure_ascii=False, indent=2))
