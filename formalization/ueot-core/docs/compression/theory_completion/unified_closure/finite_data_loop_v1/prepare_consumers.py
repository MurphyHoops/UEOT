#!/usr/bin/env python3
"""Prepare/apply one additive layer using pinned existing six-consumer gates.

Old native/evidence validation, deterministic preparation, atomic apply and
rollback are reused. Only this layer's fixed scope, census and rendering differ.
Preparation writes outside the repository; apply is a separate explicit step.
"""
from __future__ import annotations
import argparse
import ast
from hashlib import sha256
import json
from pathlib import Path
import re
import sys
import types

sys.dont_write_bytecode = True
if not __debug__:
    raise RuntimeError("OPTIMIZED_PYTHON_DISABLES_REQUIRED_ASSERTIONS")
PREDECESSOR = Path(__file__).resolve().parent.with_name("action_certificates_v1") / "prepare_consumers.py"
PREDECESSOR_SHA = "7437ec51040f7089c44dbe6c5e5cf3dc29f4ff177518fcf2579a56a68ad13290"
raw = PREDECESSOR.read_bytes()
if sha256(raw).hexdigest() != PREDECESSOR_SHA:
    raise RuntimeError("IMMUTABLE_PREPARATION_PREDECESSOR_DRIFT")
prior = types.ModuleType("finite_data_loop_pinned_preparation")
prior.__file__ = str(PREDECESSOR)
sys.modules[prior.__name__] = prior
exec(compile(raw, str(PREDECESSOR), "exec"), prior.__dict__)
source = prior.source.replace("action_certificates", "finite_data_loop").replace(
    "ACTION_CERTIFICATES", "FINITE_DATA_LOOP").replace(
    "UNCOUNTED_FINITE_SOURCE_FINITE_DATA_LOOP", "UNCOUNTED_FINITE_DATA_PATH_RISK")
COUNTS = {"708": "712", "712": "724", "697": "701", "701": "713",
          "4504": "4542", "711": "749", "180": "190", "1079": "1159",
          "5966": "6046", "17": "18", "18": "19", "78": "82", "82": "86"}
source = re.sub(r"\b(?:" + "|".join(COUNTS) + r")\b", lambda m: COUNTS[m[0]], source)
old_modules = '("FinitePolicyPath", "FiniteActionCertificate",\n                  "RationalConditionedSource", "FiniteActionCertificateWitness")'
MODULE_NAMES = ("FiniteDataSource", "FiniteDataPathBounds", "FiniteDataConditioned", "FiniteDataNumericalBounds",
                "FiniteDataControl", "FiniteDataCalibration", "FiniteDataObstacles", "FiniteDataCertificate",
                "FiniteDataGeneralRoute", "FiniteDataJoint", "FiniteDataLiteral", "FiniteDataCertifiedConsumer")
if source.count(old_modules) != 1 or source.count('(4, len(scope)') != 1:
    raise RuntimeError("PREDECESSOR_SCOPE_ANCHOR_DRIFT")
source = source.replace(old_modules, repr(MODULE_NAMES)).replace('(4, len(scope)', '(12, len(scope)')
p = types.ModuleType("finite_data_loop_reused_consumer_protocol")
p.__file__ = __file__
sys.modules[p.__name__] = p
exec(compile(source, __file__ + "::adapted_immutable_preparation", "exec"), p.__dict__)


def append_registry(text, values):
    before, lines, changes = ast.parse(text), text.splitlines(keepends=True), []
    for name, expression in values.items():
        node = p.assignment(before, name).value
        p.require(isinstance(node, ast.List) and len(node.elts) == 18,
                  "REGISTRY_MUST_HAVE_EXACTLY_EIGHTEEN_OLD_ENTRIES: " + name)
        p.require(lines[node.end_lineno - 1].strip() == "]", "REGISTRY_LIST_LAYOUT_DRIFT")
        changes.append((sum(map(len, lines[:node.end_lineno - 1])), "    " + expression + ",\n"))
    changed = text
    for offset, addition in sorted(changes, reverse=True):
        changed = changed[:offset] + addition + changed[offset:]
    changed = p.once(changed, "finite-source-action-certificates overlays",
                     "finite-source-action-certificates and finite-data-loop overlays")
    after = ast.parse(changed)
    for name in values:
        old, new = p.assignment(before, name).value, p.assignment(after, name).value
        p.require(len(new.elts) == 19 and [ast.dump(x) for x in new.elts[:18]] ==
                  [ast.dump(x) for x in old.elts], "REGISTRY_APPEND_CHANGED_HISTORY: " + name)
    for name in ("EVIDENCE_SHA", "CLONE_SHA256", "LEDGER_SHA256", "BUILD_ENVIRONMENT_SHA256"):
        p.require(ast.dump(p.assignment(before, name)) == ast.dump(p.assignment(after, name)),
                  "IMMUTABLE_PIN_CHANGED: " + name)
    return changed


def new_tests(original, e):
    first = p.method_source(original, "test_action_certificates_native_ownership_and_registered_edges")
    old_modules = '"FinitePolicyPath", "FiniteActionCertificate",\n            "RationalConditionedSource", "FiniteActionCertificateWitness"'
    for old, new in (
        ("test_action_certificates_", "test_finite_data_loop_"),
        ('["overlays"][17]', '["overlays"][18]'), (old_modules, ', '.join(repr(x) for x in MODULE_NAMES)),
        ('["base_snapshot_modules"], 708', '["base_snapshot_modules"], 712'),
        ('reuse.OVERLAY_SHA256S[16]', 'reuse.OVERLAY_SHA256S[17]'),
        ('61fc3caead1945f72b919973217d573957a1b8d0', e["base"]),
        ('a499c2264c1b0b6b770d4023042187baa0b824de833f1ddf6046bffd22393d82', e["source"]),
        ('UNCOUNTED_FINITE_SOURCE_ACTION_CERTIFICATES', p.ROLE),
        ('caabf5a021abc2f7fc03d26c37354ec1f5a0664a6849f183684acb374fb7291d', e["native_sha"]),
        ('ACTION_CERTIFICATES_NATIVE_EXPORT_V1', p.NAME + '_NATIVE_EXPORT_V1'),
        ('len(scope), 236', f'len(scope), {e["all_native"]}'),
        ('for row in scope), 162', f'for row in scope), {e["private_native"]}'),
        ('len(public), 38', f'len(public), {e["new_public"]}'),
        ('for row in scope), 36', f'for row in scope), {e["other_public_native"]}'),
        ('len(edges), 80', f'len(edges), {e["new_edges"]}'),
        ('["registered_prior_theorems"], 4504', '["registered_prior_theorems"], 4542'),
        ('38 * 4504', f'{e["new_public"]} * 4542'),
        ('38 * 37 // 2', f'{e["new_public"]} * {e["new_public"] - 1} // 2'),
    ):
        first = p.once(first, old, new)
    second = '''    def test_finite_data_loop_same_source_literal_and_full_record_routes(self):
        prefix = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure."
        src, conditioned = prefix + "FiniteDataSource.", prefix + "FiniteDataConditioned."
        literal, endpoint = prefix + "FiniteDataLiteral.", prefix + "FiniteDataCertifiedConsumer."
        required = {
            conditioned + "target_eq_actual": {conditioned + "prepared_initial",
                prefix + "TotalFiniteWindowCheck.generated_ambient_eq_actual"},
            literal + "literal_deployment_eq_direct": {prefix + "FinitePolicyPathCheck.causal_path_eq_iff"},
            literal + "full_experiment_window_eq_literal": {literal + "preparation_state_marginal",
                prefix + "ConditionedActionTransportCheck.time_action_state_path_eq_mixture"},
            src + "statistical_actual_conditioned_path": {conditioned + "target_eq_actual", src + "statistical_approximation"},
            endpoint + "literal_statistical_certificate": {literal + "literal_deployment_eq_direct", src + "statistical_actual_conditioned_path"},
            endpoint + "full_record_statistical_certificate": {literal + "full_experiment_window_eq_literal", endpoint + "literal_statistical_certificate"},
        }
        for name, dependencies in required.items():
            actual = set(reuse.explain(self.data, name)["direct_existing_source_theorem_uses"])
            self.assertTrue(dependencies <= actual, (name, dependencies - actual))
        current = self.data["overlays"][18]
        native = json.loads((reuse.REPO / current["native_export_evidence"]["path"]).read_text())
        by_name = {row["name"]: row for row in native["all_native_theorem_constants"]}
        statement = by_name[endpoint + "literal_statistical_certificate"]["type"]
        for fragment in ("literalDeployment", "actualConditionedPrefix", "Good", "prep", "w"):
            self.assertIn(fragment, statement)
        self.assertNotIn("OccupiedFiberFeasible", statement)

'''
    third = '''    def test_finite_data_loop_scalar_calibration_and_selected_joint_risk_routes(self):
        prefix = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure."
        calibration, joint = prefix + "FiniteDataCalibration.", prefix + "FiniteDataJoint."
        src = prefix + "FiniteDataSource."
        required = {
            calibration + "calibration_bad_le": {prefix + "RowwiseProbeSampling.product_probe_calibration",
                calibration + "good_event_eq", prefix + "FiniteDataNumericalBounds.registeredScalarBudget_lt"},
            joint + "registered_joint_failure_le": {prefix + "selectedTrainingDeployment_failure_le",
                calibration + "calibration_bad_le", joint + "deployment_failure_on_good"},
            src + "general_approximation": {src + "deployed_reference_bound", src + "general_target_stability"},
        }
        for name, dependencies in required.items():
            actual = set(reuse.explain(self.data, name)["direct_existing_source_theorem_uses"])
            self.assertTrue(dependencies <= actual, (name, dependencies - actual))
        current = self.data["overlays"][18]
        for row in current["public_theorems"]:
            self.assertEqual(reuse.explain(self.data, row["name"])["role"], "UNCOUNTED_FINITE_DATA_PATH_RISK")

'''
    last = p.method_source(original, "test_action_certificates_registration_preserves_raw_execution")
    last = last.replace("ACTION_CERTIFICATES", p.NAME)
    for old, new in (
        ('test_action_certificates_', 'test_finite_data_loop_'),
        ('["overlays"][17]', '["overlays"][18]'),
        ('a499c2264c1b0b6b770d4023042187baa0b824de833f1ddf6046bffd22393d82', e["source"]),
        ('reuse.OVERLAY_PATHS[17]', 'reuse.OVERLAY_PATHS[18]'),
        ('reuse.OVERLAY_SHA256S[17]', 'reuse.OVERLAY_SHA256S[18]'),
        ('["complete_source_modules"], 712', '["complete_source_modules"], 724'),
        ('["new_public"], 38', f'["new_public"], {e["new_public"]}'),
        ('["lexical_hinted"], 10', f'["lexical_hinted"], {e["hinted"]}'),
        ('["new_public_source_theorem_count"], 38', f'["new_public_source_theorem_count"], {e["new_public"]}'),
        ('["base_public_lexical_theorem_count"], 4504', '["base_public_lexical_theorem_count"], 4542'),
        ('["candidate_public_lexical_theorem_count"], 4542', f'["candidate_public_lexical_theorem_count"], {e["total_public"]}'),
        ('["candidate_registered_public_source_theorem_count"], 4542', f'["candidate_registered_public_source_theorem_count"], {e["total_public"]}'),
        ('["new_theorems_with_lexical_reuse_candidates"], 10', f'["new_theorems_with_lexical_reuse_candidates"], {e["hinted"]}'),
    ):
        last = p.once(last, old, new)
    return first + second + third + last


def render_consumers(original, e):
    changed = dict(original)
    path = p.REUSE + "fkrg_reuse.py"
    changed[path] = append_registry(original[path], {
        "OVERLAY_PATHS": 'HERE / "FINITE_DATA_LOOP_REUSE_OVERLAY_V1.json"',
        "OVERLAY_TYPE_CHECKS": 'HERE / "VERIFY_FINITE_DATA_LOOP_OVERLAY_TYPES.lean"',
        "OVERLAY_SHA256S": repr(e["overlay_sha"]), "OVERLAY_TYPE_CHECK_SHA256S": repr(e["verifier_sha"]),
    })
    path = p.REUSE + "test_fkrg_reuse.py"
    text = original[path]
    current = {**p.PRIOR_CENSUS, "module_source_hashes_verified": 724, "ueot_maintained_modules": 713,
               "public_source_theorems_with_direct_proof_graph": e["total_public"],
               "overlay_public_theorems": e["overlay_public"], "overlay_count": 19,
               "overlay_lexical_reuse_candidates": e["total_hinted"],
               "overlay_registered_direct_edges": e["overlay_edges"]}
    for key, new in current.items():
        if new != p.PRIOR_CENSUS[key]:
            text = p.once(text, f'self.assertEqual(res["{key}"], {p.PRIOR_CENSUS[key]})',
                          f'self.assertEqual(res["{key}"], {new})')
    for old, new in (
        ('for row in self.data["graph"].values()), 6046)', f'for row in self.data["graph"].values()), {e["total_edges"]})'),
        ('self.assertEqual(len(self.data["overlays"]), 18)', 'self.assertEqual(len(self.data["overlays"]), 19)'),
        ('self.assertEqual(len(live), 712)', 'self.assertEqual(len(live), 724)'),
    ):
        text = p.once(text, old, new)
    anchor = '    def test_historical_apostrophe_registration_and_existing_incoming_edge(self):'
    text = p.once(text, anchor, new_tests(original[path], e) + anchor)
    before, after = p.methods(original[path]), p.methods(text)
    p.require(len(before) == 82 and len(after) == 86 and set(before) <= set(after), "REGRESSION_TEST_SET_DRIFT")
    live = {"test_evidence_and_sources_exact_baseline", "test_calibrated_defect_overlay_chain_and_kernel_graph",
            "test_new_lean_module_cannot_be_omitted_from_index"}
    p.require(all(before[name] == after[name] for name in set(before) - live), "HISTORICAL_REGRESSION_WAS_CHANGED")
    changed[path] = text
    path = p.REUSE + "REBUILD_CLONE_CANDIDATES.py"
    text = original[path]
    for old, new in (
        ('712 modules (701 maintained', '724 modules (713 maintained'),
        ('plus eighteen governed overlays', 'plus nineteen governed overlays'),
        ('and finite-source-action-certificates. The historical',
         'finite-source-action-certificates, and finite-data-loop. The historical'),
    ):
        text = p.once(text, old, new)
    p.require(ast.dump(ast.Module(body=ast.parse(original[path]).body[1:], type_ignores=[])) ==
              ast.dump(ast.Module(body=ast.parse(text).body[1:], type_ignores=[])), "CLONE_SCANNER_RUNTIME_WAS_CHANGED")
    changed[path] = text
    path = p.KNOWLEDGE + "README.md"
    text = original[path]
    start = text.index('The current finite-source action-certificate census')
    end = text.index('\n\n', start)
    summary = f'''The current finite-data path-risk census contains **724 bundled Lean modules: 713 UEOT-maintained and 11 adapted upstream modules**, with nineteen additive overlays. The registered public graph contains **{e["total_public"]:,} nodes and {e["total_edges"]:,} direct edges**. Twelve source modules connect finite scalar calibration, the returned literal preparation/control table, the true source's own conditioned path and the selected joint risk. The frozen source fingerprint is `{e["source"]}`. The complete native export retains {e["all_native"]} owned theorem constants: {e["new_public"]} public source candidates, {e["private_native"]} private and {e["other_public_native"]} other public constants. See [layer nineteen](reuse/README.md#layer-19--finite-data-path-risk); these counts are audit scope, not theoretical or empirical completion.'''
    text = text[:start] + summary + text[end:]
    text = p.once(text, '## Required startup/recovery protocol (every new chat/agent)',
        'The nineteenth [finite-data path-risk overlay](reuse/FINITE_DATA_LOOP_REUSE_OVERLAY_V1.json) preserves the previous eighteen layers. Its statistical path guarantee is conditional on a simultaneous calibration event proved under the registered sampling law; the accepted-and-failed joint risk is distinct from conditional failure given acceptance. Preparation is one actual noisy allowed operation, and the full record projection retains its failure mass. Positive noise, high-noise, initial-law and horizon boundaries concern the same source family. Strong global closure remains `NOT_ESTABLISHED`; external scientific evidence remains `UNVERIFIED`.\n\n## Required startup/recovery protocol (every new chat/agent)')
    changed[path] = text
    path = p.REUSE + "README.md"
    text = original[path]
    for old, new in (
        ('The current eighteen-layer census is **712 modules = 701 UEOT-maintained + 11\nadapted upstream**, with **4,542 registered public theorem nodes** and\n**6,046 registered direct proof edges**.',
         f'The current nineteen-layer census is **724 modules = 713 UEOT-maintained + 11\nadapted upstream**, with **{e["total_public"]:,} registered public theorem nodes** and\n**{e["total_edges"]:,} registered direct proof edges**.'),
        ('lake env lean docs/compression/theory_completion/knowledge/reuse/VERIFY_ACTION_CERTIFICATES_OVERLAY_TYPES.lean',
         'lake env lean docs/compression/theory_completion/knowledge/reuse/VERIFY_FINITE_DATA_LOOP_OVERLAY_TYPES.lean'),
        ('eighteen governed overlays extend the live census to 712 = 701 + 11.', 'nineteen governed overlays extend the live census to 724 = 713 + 11.'),
        ('3,793 immutable-base public source theorem proofs + 749 governed registrations\n  (including one historical public-name repair) = 4,542 live graph nodes, with\n  6,046 direct registered-source theorem',
         f'3,793 immutable-base public source theorem proofs + {e["overlay_public"]} governed registrations\n  (including one historical public-name repair) = {e["total_public"]:,} live graph nodes, with\n  {e["total_edges"]:,} direct registered-source theorem'),
        ('fifteenth adds 29, the sixteenth adds 19, the seventeenth adds 40, and the eighteenth adds 80, giving\n  1159 outgoing edges from overlay nodes;',
         f'fifteenth adds 29, the sixteenth adds 19, the seventeenth adds 40, the eighteenth adds 80, and the nineteenth adds {e["new_edges"]}, giving\n  {e["overlay_edges"]} outgoing edges from overlay nodes;'),
        ('all 712 modules', 'all 724 modules'), ('exact 712-module live source census', 'exact 724-module live source census'),
    ):
        text = p.once(text, old, new)
    layer = f'''### Layer 19 — finite-data path risk

Baseline `{e["base"]}`; frozen source `{e["source"]}`.
Twelve modules add {e["new_public"]} public source declarations and {e["new_edges"]} registered edges.

| Evidence | SHA-256 |
| --- | --- |
| [Complete native export](FINITE_DATA_LOOP_NATIVE_V1.json) | `{e["native_sha"]}` |
| [Fixed Lean certificate](VERIFY_FINITE_DATA_LOOP_OVERLAY_TYPES.lean) | `{e["verifier_sha"]}` |
| [Registered overlay](FINITE_DATA_LOOP_REUSE_OVERLAY_V1.json) | `{e["overlay_sha"]}` |

The native export retains {e["all_native"]} owned theorem constants ({e["new_public"]} public
source, {e["private_native"]} private, {e["other_public_native"]} other public). Stored types
undergo {e["cross_comparisons"]:,} comparisons against 4,542 prior registrations and
{e["internal_comparisons"]:,} internal comparisons with zero definitional collisions.
Complete native owners, direct constants and standard-only axiom closures are retained.
These comparisons do not establish logical independence.

The same finite source supplies training probes, baseline conditioning and deployment.
The returned literal preparation/table is consumed directly, including an explicit
full T+1-operation experiment projected to its post-preparation T-step state window.
Target-support weighted TV bounds retain preparation failure. The actual rank-one
conditional target gives the structural stability route; the existing general
conditional-TV theorem remains a separate rare-event-sensitive route. Four scalar
Hoeffding probes give one simultaneous calibration event before selection. The
selected joint risk bounds Accept AND Fail; it is not a failure-given-Accept guarantee.
Nonzero-noise acceptance and high-noise/initial/horizon obstructions retain their
specified premises. Raw-record parser, RNG and source matching boundaries remain
explicit. No complete search, universal objects/axes or external validation follows.
All eighteen earlier overlays and their tests/artifacts remain pinned.
Strong global closure remains `NOT_ESTABLISHED`; external science remains `UNVERIFIED`.

'''
    changed[path] = p.once(text, '## Run from repository root', layer + '## Run from repository root')
    p.require(set(changed) == set(p.CONSUMERS), "CONSUMER_SCOPE_DRIFT")
    for path, text in changed.items():
        p.require(text != original[path], "UNCHANGED_CONSUMER: " + path)
        if path.endswith('.py'):
            ast.parse(text, filename=path)
    return changed


p.append_registry, p.new_tests, p.render_consumers = append_registry, new_tests, render_consumers


def self_check(repo):
    e = dict(base="f4c23ac61b440df9d88ca1e79a4684d589066489", source="f"*64,
             overlay_sha="a"*64, verifier_sha="b"*64, native_sha="c"*64,
             new_public=100, new_edges=200, hinted=20, total_public=4642,
             overlay_public=849, total_hinted=210, overlay_edges=1359, total_edges=6246,
             all_native=300, private_native=150, other_public_native=50,
             cross_comparisons=454200, internal_comparisons=4950)
    original = {path: (repo/path).read_text() for path in p.CONSUMERS}
    changed = render_consumers(original, e)
    p.require(changed == render_consumers(original,e), "NONDETERMINISTIC_RENDER")
    p.require(all((repo/path).read_text() == text for path,text in original.items()), "SELF_CHECK_MODIFIED_PRODUCTION")
    p.require(len(p.methods(changed[p.REUSE+'test_fkrg_reuse.py'])) == 86, "RENDERED_TEST_CENSUS_DRIFT")
    adapter = p.load_python('finite_data_loop_adapter_self_check', repo/p.PROTOCOL/'protocol_adapter.py')
    real_frozen = adapter.frozen
    fake = {"baseline_ref":e["base"],"source_tree_sha256":e["source"],"new_public":e["new_public"],"lexical_hinted":e["hinted"]}
    try:
        adapter.frozen = lambda *_: (fake,p.encoded(fake))
        for kind in ('full_build','integration_native','register_overlay'):
            driver,archive = adapter.adapted_driver(kind,repo,'NOT_A_REAL_FREEZE',e["base"])
            p.require(callable(driver.run), "MISSING_REUSED_DRIVER_ENTRYPOINT")
            metadata=json.loads(archive['PROTOCOL_ADAPTATION.json'])
            p.require(metadata['adapter_predecessor']['sha256']==adapter._ADAPTER_SHA and
                      bool(metadata['substitutions']), "MISSING_PINNED_ADAPTER_PROVENANCE")
    finally:
        adapter.frozen=real_frozen
    return {"state":"PASS_RENDER_HISTORICAL_TEST_AST_AND_DRIVER_ADAPTATION_GUARDS",
            "production_files_modified":False,"integration_gates_executed":False}


if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    sub=parser.add_subparsers(dest='mode',required=True)
    prep=sub.add_parser('prepare')
    for option in ('repo','base-ref','frozen-inputs','output'):
        prep.add_argument('--'+option,required=True)
    check=sub.add_parser('self-check');check.add_argument('--repo',required=True)
    apply=sub.add_parser('apply');apply.add_argument('--repo',required=True);apply.add_argument('--candidates',required=True)
    args=parser.parse_args();repo=Path(args.repo).resolve(strict=True)
    if args.mode=='self-check':
        result=self_check(repo)
    elif args.mode=='prepare':
        output=Path(args.output).resolve()
        result=p.prepare(repo,args.base_ref,Path(args.frozen_inputs).resolve(strict=True),output)
        (output/'REUSED_PREPARATION_PROTOCOL.json').write_bytes(p.encoded({
            'immutable_predecessor':str(PREDECESSOR),'sha256':PREDECESSOR_SHA,
            'scope_count_substitutions':COUNTS,'executed_predecessor_sha256':sha256(source.encode()).hexdigest(),
            'rendering_driver':{'path':str(Path(__file__).resolve()),'sha256':sha256(Path(__file__).read_bytes()).hexdigest()},
            'rendering':'new layer only; prior test ASTs except existing live-census assertions unchanged'}))
        (output/'immutable_prepare_consumers.py').write_bytes(raw)
        (output/'adapted_immutable_preparation.py').write_text(source)
        (output/'prepare_consumers.py').write_bytes(Path(__file__).read_bytes())
    else:
        candidates=Path(args.candidates).resolve(strict=True)
        p.require(not candidates.is_relative_to(repo),'CANDIDATES_MUST_BE_OUTSIDE_REPOSITORY')
        result=p.apply(repo,candidates)
    print(json.dumps(result,ensure_ascii=False,indent=2))
