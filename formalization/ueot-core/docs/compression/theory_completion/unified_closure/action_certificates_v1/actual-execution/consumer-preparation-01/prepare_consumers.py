#!/usr/bin/env python3
"""Prepare/apply six existing consumers, preserving every prior test and artifact.

Reuse the immutable predecessor's validation, registration-evidence checks,
atomic application and rollback. Only scope/census metadata and new layer
rendering differ. Preparation writes outside the repository; application is a
separate explicit command and changes exactly the five consumers plus the DAG.
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

PREDECESSOR = Path(__file__).resolve().parent.with_name("action_gauge_transport_v1") / "prepare_consumers.py"
PREDECESSOR_SHA = "3c5b55189797e5247f74a8876b18f78f20374fffc4dff4bde52453e6e518f909"
raw = PREDECESSOR.read_bytes()
if sha256(raw).hexdigest() != PREDECESSOR_SHA:
    raise RuntimeError("IMMUTABLE_PREPARATION_PREDECESSOR_DRIFT")
source = raw.decode().replace("action_gauge_transport", "action_certificates").replace(
    "ACTION_GAUGE_TRANSPORT", "ACTION_CERTIFICATES").replace(
    "UNCOUNTED_ACTION_REALIZABILITY_GAUGE_AND_CONDITIONED_TRANSPORT", "UNCOUNTED_FINITE_SOURCE_ACTION_CERTIFICATES")
# Exact token substitutions keep unchanged native/evidence/application gates;
# live rendering and the four new tests are provided below, not inherited.
COUNTS = {"703": "708", "708": "712", "692": "697", "697": "701",
          "4474": "4504", "681": "711", "177": "180", "1039": "1079",
          "5926": "5966", "16": "17", "17": "18", "74": "78", "78": "82"}
source = re.sub(r"\b(?:" + "|".join(COUNTS) + r")\b", lambda m: COUNTS[m[0]], source)
old_modules = '("FiniteActionRealizability", "FiniteActionRealizabilityWitness",\n                  "DualDriveLinearGaugeClassification", "DualDriveOperationalAnchors",\n                  "ConditionedActionTransport")'
new_modules = '("FinitePolicyPath", "FiniteActionCertificate",\n                  "RationalConditionedSource", "FiniteActionCertificateWitness")'
if source.count(old_modules) != 1 or source.count('(5, len(scope)') != 1:
    raise RuntimeError("PREDECESSOR_SCOPE_ANCHOR_DRIFT")
source = source.replace(old_modules, new_modules).replace('(5, len(scope)', '(4, len(scope)')
protocol = types.ModuleType("action_certificates_reused_consumer_protocol")
protocol.__file__ = __file__
sys.modules[protocol.__name__] = protocol
exec(compile(source, __file__ + "::adapted_immutable_preparation", "exec"), protocol.__dict__)
p = protocol


def append_registry(source, values):
    before = ast.parse(source)
    lines, replacements = source.splitlines(keepends=True), []
    for name, expression in values.items():
        node = p.assignment(before, name).value
        p.require(isinstance(node, ast.List) and len(node.elts) == 17,
                  "REGISTRY_MUST_HAVE_EXACTLY_SEVENTEEN_OLD_ENTRIES: " + name)
        p.require(lines[node.end_lineno - 1].strip() == "]", "REGISTRY_LIST_LAYOUT_DRIFT")
        replacements.append((sum(map(len, lines[:node.end_lineno - 1])), "    " + expression + ",\n"))
    changed = source
    for offset, addition in sorted(replacements, reverse=True):
        changed = changed[:offset] + addition + changed[offset:]
    changed = p.once(changed, "conditional-stability and action/gauge/transport overlays",
                     "conditional-stability, action/gauge/transport and finite-source-action-certificates overlays")
    after = ast.parse(changed)
    for name in values:
        old, new = p.assignment(before, name).value, p.assignment(after, name).value
        p.require(len(new.elts) == 18 and [ast.dump(x) for x in new.elts[:17]] ==
                  [ast.dump(x) for x in old.elts], "REGISTRY_APPEND_CHANGED_HISTORY: " + name)
    for name in ("EVIDENCE_SHA", "CLONE_SHA256", "LEDGER_SHA256", "BUILD_ENVIRONMENT_SHA256"):
        p.require(ast.dump(p.assignment(before, name)) == ast.dump(p.assignment(after, name)),
                  "IMMUTABLE_PIN_CHANGED: " + name)
    return changed


def new_tests(original, e):
    first = p.method_source(original, "test_action_gauge_transport_native_ownership_and_registered_edges")
    for old, new in (
        ("test_action_gauge_transport_", "test_action_certificates_"),
        ('["overlays"][16]', '["overlays"][17]'),
        ('"FiniteActionRealizability", "FiniteActionRealizabilityWitness",\n'
         '            "DualDriveLinearGaugeClassification", "DualDriveOperationalAnchors",\n'
         '            "ConditionedActionTransport"',
         '"FinitePolicyPath", "FiniteActionCertificate",\n'
         '            "RationalConditionedSource", "FiniteActionCertificateWitness"'),
        ('["base_snapshot_modules"], 703', '["base_snapshot_modules"], 708'),
        ('reuse.OVERLAY_SHA256S[15]', 'reuse.OVERLAY_SHA256S[16]'),
        ('dd6ab2d4696ce4fa7824baa2faeb993069ee8787', e["base"]),
        ('9a90676af4c234eee2121ac75c0e127f2dd87370e727e5e7189ea99b4b377530', e["source"]),
        ('UNCOUNTED_ACTION_REALIZABILITY_GAUGE_AND_CONDITIONED_TRANSPORT', p.ROLE),
        ('0d47202668032dddb912fce8974606caefecbfd56435d7bc9cbe169af4905a1a', e["native_sha"]),
        ('ACTION_GAUGE_TRANSPORT_NATIVE_EXPORT_V1', p.NAME + '_NATIVE_EXPORT_V1'),
        ('len(scope), 93', f'len(scope), {e["all_native"]}'),
        ('for row in scope), 37', f'for row in scope), {e["private_native"]}'),
        ('len(public), 30', f'len(public), {e["new_public"]}'),
        ('for row in scope), 26', f'for row in scope), {e["other_public_native"]}'),
        ('len(edges), 40', f'len(edges), {e["new_edges"]}'),
        ('["registered_prior_theorems"], 4474', '["registered_prior_theorems"], 4504'),
        ('30 * 4474', f'{e["new_public"]} * 4504'),
        ('30 * 29 // 2', f'{e["new_public"]} * {e["new_public"] - 1} // 2'),
    ):
        first = p.once(first, old, new)
    second = '''    def test_action_certificates_specified_policy_and_prefix_routes(self):
        prefix = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure."
        path = prefix + "FinitePolicyPathCheck."
        required = {
            path + "full_path_eq_prefix": {prefix + "SameSourceKilledExitFluxCheck.causalLaw_map_prefix"},
            path + "causal_path_eq_iff": {path + "full_path_eq_prefix"},
            path + "specified_policy_path_iff": {
                path + "causal_path_eq_iff",
                prefix + "ConditionedActionTransportCheck.time_action_state_path_eq_mixture"},
            path + "specified_policy_conditioned_path_iff": {
                path + "specified_policy_path_iff", prefix + "TotalFiniteWindowCheck.generated_ambient_eq_actual"},
        }
        for name, dependencies in required.items():
            actual = set(reuse.explain(self.data, name)["direct_existing_source_theorem_uses"])
            self.assertTrue(dependencies <= actual, (name, dependencies - actual))
        current = self.data["overlays"][17]
        native = json.loads((reuse.REPO / current["native_export_evidence"]["path"]).read_text())
        by_name = {row["name"]: row for row in native["all_native_theorem_constants"]}
        statement = by_name[path + "specified_policy_path_iff"]["type"]
        for fragment in ("sigma", "occupiedState", "actionMixture", "targetPath"):
            self.assertIn(fragment, statement)
        self.assertNotIn("OccupiedFiberFeasible", statement)

'''
    third = '''    def test_action_certificates_checker_and_same_source_routes(self):
        prefix = "UEOT.V3.Compression.TheoryCompletion.UnifiedClosure."
        cert = prefix + "FiniteActionCertificateCheck."
        path = prefix + "FinitePolicyPathCheck."
        source = prefix + "RationalConditionedSourceCheck."
        required = {
            source + "sourceInitial_eq_prepared": {source + "sourceMass_eq_actual", source + "sourceRemaining_eq_actual"},
            source + "sourceTarget_eq_row": {source + "sourceRemaining_eq_actual", source + "baselineRow_cast"},
            source + "sourceTargetPath_eq_actual": {source + "sourceInitial_eq_prepared", source + "sourceTarget_eq_row",
                prefix + "TotalFiniteWindowCheck.generated_ambient_eq_actual"},
            cert + "checkPositive_sound": {cert + "checkPositive_sound_rows", path + "specified_policy_path_of_rows"},
            cert + "checkNegative_path_no_go": {cert + "checkNegative_sound", path + "specified_policy_path_iff"},
        }
        for name, dependencies in required.items():
            actual = set(reuse.explain(self.data, name)["direct_existing_source_theorem_uses"])
            self.assertTrue(dependencies <= actual, (name, dependencies - actual))
        current = self.data["overlays"][17]
        native = json.loads((reuse.REPO / current["native_export_evidence"]["path"]).read_text())
        by_name = {row["name"]: row for row in native["all_native_theorem_constants"]}
        for suffix, fragments in (
            ("checkPositive_sound", ("policy", "checkPositive", "targetPath")),
            ("checkNegative_path_no_go", ("checkNegative", "targetPath", "sigma")),
        ):
            for fragment in fragments:
                self.assertIn(fragment, by_name[cert + suffix]["type"])
        for row in current["public_theorems"]:
            self.assertEqual(reuse.explain(self.data, row["name"])["role"],
                             "UNCOUNTED_FINITE_SOURCE_ACTION_CERTIFICATES")

'''
    last = p.method_source(original, "test_action_gauge_transport_registration_preserves_raw_execution")
    last = last.replace("ACTION_GAUGE_TRANSPORT", p.NAME)
    for old, new in (
        ('test_action_gauge_transport_', 'test_action_certificates_'),
        ('["overlays"][16]', '["overlays"][17]'),
        ('9a90676af4c234eee2121ac75c0e127f2dd87370e727e5e7189ea99b4b377530', e["source"]),
        ('reuse.OVERLAY_PATHS[16]', 'reuse.OVERLAY_PATHS[17]'),
        ('reuse.OVERLAY_SHA256S[16]', 'reuse.OVERLAY_SHA256S[17]'),
        ('["complete_source_modules"], 708', '["complete_source_modules"], 712'),
        ('["new_public"], 30', f'["new_public"], {e["new_public"]}'),
        ('["lexical_hinted"], 3', f'["lexical_hinted"], {e["hinted"]}'),
        ('["new_public_source_theorem_count"], 30', f'["new_public_source_theorem_count"], {e["new_public"]}'),
        ('["base_public_lexical_theorem_count"], 4474', '["base_public_lexical_theorem_count"], 4504'),
        ('["candidate_public_lexical_theorem_count"], 4504', f'["candidate_public_lexical_theorem_count"], {e["total_public"]}'),
        ('["candidate_registered_public_source_theorem_count"], 4504', f'["candidate_registered_public_source_theorem_count"], {e["total_public"]}'),
        ('["new_theorems_with_lexical_reuse_candidates"], 3', f'["new_theorems_with_lexical_reuse_candidates"], {e["hinted"]}'),
    ):
        last = p.once(last, old, new)
    return first + second + third + last


def render_consumers(original, e):
    changed = dict(original)
    path = p.REUSE + "fkrg_reuse.py"
    changed[path] = append_registry(original[path], {
        "OVERLAY_PATHS": 'HERE / "ACTION_CERTIFICATES_REUSE_OVERLAY_V1.json"',
        "OVERLAY_TYPE_CHECKS": 'HERE / "VERIFY_ACTION_CERTIFICATES_OVERLAY_TYPES.lean"',
        "OVERLAY_SHA256S": repr(e["overlay_sha"]), "OVERLAY_TYPE_CHECK_SHA256S": repr(e["verifier_sha"]),
    })
    path = p.REUSE + "test_fkrg_reuse.py"
    s = original[path]
    current = {**p.PRIOR_CENSUS, "module_source_hashes_verified": 712, "ueot_maintained_modules": 701,
               "public_source_theorems_with_direct_proof_graph": e["total_public"],
               "overlay_public_theorems": e["overlay_public"], "overlay_count": 18,
               "overlay_lexical_reuse_candidates": e["total_hinted"],
               "overlay_registered_direct_edges": e["overlay_edges"]}
    for key, new in current.items():
        if new != p.PRIOR_CENSUS[key]:
            s = p.once(s, f'self.assertEqual(res["{key}"], {p.PRIOR_CENSUS[key]})',
                       f'self.assertEqual(res["{key}"], {new})')
    for old, new in (
        ('for row in self.data["graph"].values()), 5966)', f'for row in self.data["graph"].values()), {e["total_edges"]})'),
        ('self.assertEqual(len(self.data["overlays"]), 17)', 'self.assertEqual(len(self.data["overlays"]), 18)'),
        ('self.assertEqual(len(live), 708)', 'self.assertEqual(len(live), 712)'),
    ):
        s = p.once(s, old, new)
    anchor = '    def test_historical_apostrophe_registration_and_existing_incoming_edge(self):'
    s = p.once(s, anchor, new_tests(original[path], e) + anchor)
    before, after = p.methods(original[path]), p.methods(s)
    p.require(len(before) == 78 and len(after) == 82 and set(before) <= set(after), "REGRESSION_TEST_SET_DRIFT")
    live = {"test_evidence_and_sources_exact_baseline", "test_calibrated_defect_overlay_chain_and_kernel_graph",
            "test_new_lean_module_cannot_be_omitted_from_index"}
    p.require(all(before[name] == after[name] for name in set(before) - live), "HISTORICAL_REGRESSION_WAS_CHANGED")
    changed[path] = s
    path = p.REUSE + "REBUILD_CLONE_CANDIDATES.py"
    s = original[path]
    for old, new in (
        ('708 modules (697 maintained', '712 modules (701 maintained'),
        ('plus seventeen governed overlays', 'plus eighteen governed overlays'),
        ('conditional-stability, and action/gauge/transport. The historical',
         'conditional-stability, action/gauge/transport, and finite-source-action-certificates. The historical'),
    ):
        s = p.once(s, old, new)
    p.require(ast.dump(ast.Module(body=ast.parse(original[path]).body[1:], type_ignores=[])) ==
              ast.dump(ast.Module(body=ast.parse(s).body[1:], type_ignores=[])), "CLONE_SCANNER_RUNTIME_WAS_CHANGED")
    changed[path] = s
    path = p.KNOWLEDGE + "README.md"
    s = original[path]
    start = s.index('The current action/gauge/transport source census')
    end = s.index('\n\n', start)
    summary = f'''The current finite-source action-certificate census contains **712 bundled Lean modules: 701 UEOT-maintained and 11 adapted upstream modules**, with eighteen additive overlays. The registered public graph contains **{e["total_public"]:,} nodes and {e["total_edges"]:,} direct edges**. Four modules certify exact rational source conditioning, positive and negative action certificates, and complete paths of the specified current-observation policy. The frozen source fingerprint is `{e["source"]}`. The complete native export retains {e["all_native"]} owned theorem constants: {e["new_public"]} public source candidates, {e["private_native"]} private and {e["other_public_native"]} other public constants. See [layer eighteen](reuse/README.md#layer-18--finite-source-action-certificates); these counts do not measure independent principles or empirical validity.'''
    s = s[:start] + summary + s[end:]
    s = p.once(s, '## Required startup/recovery protocol (every new chat/agent)',
        f'The eighteenth [finite-source action-certificate overlay](reuse/ACTION_CERTIFICATES_REUSE_OVERLAY_V1.json) retains the previous seventeen layers unchanged and adds {e["new_edges"]} registered proof edges. The same specified policy table is certified; negative certificates use target-positive occupied observation fibers and exclude this finite current-observation policy class. Initial preparation remains explicit. General search completeness, richer-information policies and empirical calibration are outside the contract. Strong global closure remains `NOT_ESTABLISHED`; external scientific evidence remains `UNVERIFIED`.\n\n## Required startup/recovery protocol (every new chat/agent)')
    changed[path] = s
    path = p.REUSE + "README.md"
    s = original[path]
    replacements = (
        ('The current seventeen-layer census is **708 modules = 697 UEOT-maintained + 11\nadapted upstream**, with **4,504 registered public theorem nodes** and\n**5,966 registered direct proof edges**.',
         f'The current eighteen-layer census is **712 modules = 701 UEOT-maintained + 11\nadapted upstream**, with **{e["total_public"]:,} registered public theorem nodes** and\n**{e["total_edges"]:,} registered direct proof edges**.'),
        ('lake env lean docs/compression/theory_completion/knowledge/reuse/VERIFY_ACTION_GAUGE_TRANSPORT_OVERLAY_TYPES.lean',
         'lake env lean docs/compression/theory_completion/knowledge/reuse/VERIFY_ACTION_CERTIFICATES_OVERLAY_TYPES.lean'),
        ('seventeen governed overlays extend the live census to 708 = 697 + 11.', 'eighteen governed overlays extend the live census to 712 = 701 + 11.'),
        ('3,793 immutable-base public source theorem proofs + 711 governed registrations\n  (including one historical public-name repair) = 4,504 live graph nodes, with\n  5,966 direct registered-source theorem',
         f'3,793 immutable-base public source theorem proofs + {e["overlay_public"]} governed registrations\n  (including one historical public-name repair) = {e["total_public"]:,} live graph nodes, with\n  {e["total_edges"]:,} direct registered-source theorem'),
        ('fifteenth adds 29, the sixteenth adds 19, and the seventeenth adds 40, giving\n  1079 outgoing edges from overlay nodes;',
         f'fifteenth adds 29, the sixteenth adds 19, the seventeenth adds 40, and the eighteenth adds {e["new_edges"]}, giving\n  {e["overlay_edges"]} outgoing edges from overlay nodes;'),
        ('all 708 modules', 'all 712 modules'), ('exact 708-module live source census', 'exact 712-module live source census'),
    )
    for old, new in replacements:
        s = p.once(s, old, new)
    layer = f'''### Layer 18 — finite-source action certificates

Baseline `{e["base"]}`; frozen source `{e["source"]}`.
Four modules add {e["new_public"]} public source declarations and {e["new_edges"]} registered edges.

| Evidence | SHA-256 |
| --- | --- |
| [Complete native export](ACTION_CERTIFICATES_NATIVE_V1.json) | `{e["native_sha"]}` |
| [Fixed Lean certificate](VERIFY_ACTION_CERTIFICATES_OVERLAY_TYPES.lean) | `{e["verifier_sha"]}` |
| [Registered overlay](ACTION_CERTIFICATES_REUSE_OVERLAY_V1.json) | `{e["overlay_sha"]}` |

The export retains {e["all_native"]} owned theorem constants ({e["new_public"]} public source,
{e["private_native"]} private, {e["other_public_native"]} other public). Stored types undergo
{e["cross_comparisons"]:,} comparisons against 4,504 prior registrations and
{e["internal_comparisons"]:,} internal comparisons, with zero definitional collisions.
Actual direct constants, owners and standard-only transitive axiom closures are retained;
these comparisons do not assert logical independence.

Exact rational certificates bind the original finite source. The positive consumer uses
the same accepted policy table and its actual initial law; the path iff determines the
initial law and precisely the positive occupied target rows. Strict separating scores
exclude real action mixtures on a common occupied observation fiber. The same-source
recursion connects conditioning to the original experiment. Null rows and zero horizon
retain their separate semantics; zero survival leaves conditioning undefined.
The search is outside the trusted checker and is not claimed complete. No richer-history
policy impossibility or empirical source calibration follows. Four added regressions check
native ownership, prefix/policy routes, checker routes and raw registration provenance.
All seventeen earlier overlays, 68 clone rows and prior regressions stay pinned.
Strong global closure remains `NOT_ESTABLISHED`; external science remains `UNVERIFIED`.

'''
    changed[path] = p.once(s, '## Run from repository root', layer + '## Run from repository root')
    p.require(set(changed) == set(p.CONSUMERS), "CONSUMER_SCOPE_DRIFT")
    for path, text in changed.items():
        p.require(text != original[path], "UNCHANGED_CONSUMER: " + path)
        if path.endswith('.py'):
            ast.parse(text, filename=path)
    return changed


def self_check(repo):
    """Exercise new deterministic rendering without registration or file writes."""
    e = dict(base="61796c5d2181cfa4d8bd9132f902d4c02658b8b6", source="f" * 64,
             overlay_sha="a" * 64, verifier_sha="b" * 64, native_sha="c" * 64,
             new_public=40, new_edges=70, hinted=4, total_public=4544,
             overlay_public=751, total_hinted=184, overlay_edges=1149, total_edges=6036,
             all_native=90, private_native=30, other_public_native=20,
             cross_comparisons=180160, internal_comparisons=780)
    original = {path: (repo / path).read_text() for path in p.CONSUMERS}
    rendered = render_consumers(original, e)
    p.require(rendered == render_consumers(original, e), "NONDETERMINISTIC_RENDER")
    p.require(all((repo / path).read_text() == text for path, text in original.items()),
              "SELF_CHECK_MODIFIED_PRODUCTION")
    p.require(len(p.methods(rendered[p.REUSE + "test_fkrg_reuse.py"])) == 82,
              "RENDERED_TEST_CENSUS_DRIFT")
    adapter = p.load_python("action_certificates_adapter_self_check", repo / p.PROTOCOL / "protocol_adapter.py")
    actual_frozen = adapter.frozen
    fake = {"baseline_ref": e["base"], "source_tree_sha256": e["source"],
            "new_public": e["new_public"], "lexical_hinted": e["hinted"]}
    try:
        adapter.frozen = lambda *_: (fake, p.encoded(fake))
        for kind in ("full_build", "integration_native", "register_overlay"):
            driver, archive = adapter.adapted_driver(kind, repo, "NOT_A_REAL_FREEZE", e["base"])
            p.require(callable(driver.run), "MISSING_REUSED_DRIVER_ENTRYPOINT")
            metadata = json.loads(archive["PROTOCOL_ADAPTATION.json"])
            p.require(bool(metadata["substitutions"]), "MISSING_EXACT_SCOPE_ADAPTATION")
    finally:
        adapter.frozen = actual_frozen
    return {"state": "PASS_RENDER_HISTORICAL_TEST_AST_AND_DRIVER_ADAPTATION_GUARDS",
            "production_files_modified": False, "integration_gates_executed": False}


p.append_registry, p.new_tests, p.render_consumers = append_registry, new_tests, render_consumers

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='mode', required=True)
    prepare = sub.add_parser('prepare')
    for option in ('repo', 'base-ref', 'frozen-inputs', 'output'):
        prepare.add_argument('--' + option, required=True)
    check = sub.add_parser('self-check')
    check.add_argument('--repo', required=True)
    apply = sub.add_parser('apply')
    apply.add_argument('--repo', required=True)
    apply.add_argument('--candidates', required=True)
    args = parser.parse_args()
    repo = Path(args.repo).resolve(strict=True)
    if args.mode == 'self-check':
        result = self_check(repo)
    elif args.mode == 'prepare':
        output = Path(args.output).resolve()
        result = p.prepare(repo, args.base_ref, Path(args.frozen_inputs).resolve(strict=True), output)
        (output / 'REUSED_PREPARATION_PROTOCOL.json').write_bytes(p.encoded({
            "immutable_predecessor": str(PREDECESSOR), "sha256": PREDECESSOR_SHA,
            "scope_count_substitutions": COUNTS, "executed_predecessor_sha256": sha256(source.encode()).hexdigest(),
            "rendering_driver": {"path": str(Path(__file__).resolve()), "sha256": sha256(Path(__file__).read_bytes()).hexdigest()},
            "rendering": "new layer only; all prior test ASTs except existing live-census tests unchanged"}))
        (output / 'immutable_prepare_consumers.py').write_bytes(raw)
        (output / 'adapted_immutable_preparation.py').write_text(source)
        (output / 'prepare_consumers.py').write_bytes(Path(__file__).read_bytes())
    else:
        candidates = Path(args.candidates).resolve(strict=True)
        p.require(not candidates.is_relative_to(repo), "CANDIDATES_MUST_BE_OUTSIDE_REPOSITORY")
        result = p.apply(repo, candidates)
    print(json.dumps(result, ensure_ascii=False, indent=2))
