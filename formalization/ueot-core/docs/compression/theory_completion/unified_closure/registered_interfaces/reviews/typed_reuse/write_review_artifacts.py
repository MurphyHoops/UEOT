#!/usr/bin/env python3
"""Materialize the independent, source-bound semantic review; no project writes."""
from pathlib import Path
from hashlib import sha256
from collections import Counter
import csv
import json

ROOT = Path('/workspace/scratch/9a8d58b21e30')
REPO = ROOT / 'ueot-integration'
OUT = Path(__file__).resolve().parent
PREFLIGHT = ROOT / 'tmp/registered-interfaces-20261021/local-source-preflight-1/PR_PREFLIGHT.json'
IDENTITY = ROOT / 'tmp/registered-interfaces-20261021/linux-build-attempt-7/SOURCE_MANIFEST.json'
def digest(p):
    return sha256(p.read_bytes()).hexdigest()

assert digest(PREFLIGHT) == 'ac5ec378ef71525a0b780eb698a6293bb480f5d5ab639eb50ab3ea6ce48345db'
assert digest(IDENTITY) == '47b089acd78085c3d3ba4871d981f841064943cddde4487046f65a3addd638e1'
preflight = json.loads(PREFLIGHT.read_text())
identity = json.loads(IDENTITY.read_text())
groups = [x for x in preflight['new_public_source_theorems'] if x.get('reuse_candidates')]
assert len(groups) == 18
assert sum(len(g['reuse_candidates']) for g in groups) == 39

# Entries follow the exact candidate order of the immutable PR_PREFLIGHT input.
# E: actual existing theorem used; A: adapter/generalization; D: different proposition.
judgments = [
 [('D', 'Old CoreOperationalAssembly compares two finite controlled models under a stationary policy and a uniform row error, using a product bound. The new theorem permits a general causal history policy and arbitrary Y, factors live observations through a finite carrier, and bounds actual occupation-weighted additive row TV. The old theorem cannot replace these premises and this conclusion.'),
  ('E', 'The proof directly applies coverage_same_policy_path_error to the finite Option I escape construction. escape_path_tv, escape_deployment_row_law and escape_transition_row_tv transport the conclusion back to the actual Y-valued reference, policy and deployment row law. This is explicit reuse of the existing finite theorem through a proved adapter.'),
  ('D', 'same_policy_coordinate_path_error supplies a uniform coordinate-error/product estimate for a finite observation type. Its premises and coordinate metric differ from the actual occupation-weighted TV sum here.'),
  ('D', 'same_policy_projected_path_error assumes a uniform row error in [0,1] and has a product conclusion. The new bound is an additive sum weighted by the actual deployment row law, without imposing finiteness on Y.'),
  ('D', 'coverage_same_policy_certified_path_error adds a certification predicate and an uncovered-mass budget. Those are downstream budget assumptions; the new theorem is the underlying raw row-TV estimate and does not assume them.')],
 [('A', 'The old theorem requires Fintype Y. The new theorem retains the same actual uncovered occupation and certified-row budget but obtains the path comparison from the finite-carrier escape adapter. The proof reuses coverage_expected_error_le. An infinite Y cannot be passed directly to the old finite-Y endpoint.')],
 [('A', 'The old empirical endpoint additionally packages fixed-N calibration and fit assumptions and obtains a finite-Y risk bound. The new theorem takes a sampling-independent certified row-TV premise, permits arbitrary Y, and requires measurable F explicitly. Empirical row calibration is reusable upstream; this old endpoint cannot replace the broader risk transfer.'),
  ('A', 'The finite-Y endpoint and the new endpoint express related event transfer, but the old environment supplies finite history measurability. The new theorem states MeasurableSet F explicitly and uses the arbitrary-Y path theorem. It reuses risk_microscopic_event_le_envelope and risk_event_transfer, preserving the same real Q experiment.')],
 [('A', 'The old finite-alphabet lemma uses absolute discrepancies over all finite sets. The new theorem works for arbitrary measurable observation spaces and signed forward discrepancies over measurable events; probability-measure complement identities supply the opposite sign. The finite-alphabet lemma does not remove its finite-type assumption.'),
  ('D', 'expectation_le_of_tvDist_le consumes a TV bound to bound the expectation of a [0,1]-valued observable. The new theorem constructs a TV bound from the family of all measurable-event inequalities.'),
  ('D', 'abs_tvDist_sub_tvDist_le is a perturbation inequality for two TV distances using four measures. It is not the event-supremum characterization proved here.'),
  ('D', 'tvEvent_le bounds one event discrepancy by TV. The new theorem proves the converse universal inference from all measurable-event inequalities, using tvEventSet_nonempty, the supremum bound and probability complements.')],
 [('A', 'The atom formula agrees after imposing finiteness, but PathError.pmfExtend_apply requires finite history and next-state types. The new theorem removes these assumptions using PMF.bind_apply, PMF.map_apply and two tsum_eq_single reductions. It is needed for histories over arbitrary Y; finite support is not substituted for a Fintype instance.')],
 [('D', 'The new statement is injectivity of the explicit map Bool → Nat sending false to 0 and true to 2, discharged by the four cases. BindingIsolation.injective instead infers injectivity of a general map from a positive metric lower-bound certificate. It would require an additional metric/certificate construction and is not the same proposition.')],
 [('D', 'The new statement says two explicitly encoded probability references have TV distance zero, using reference_encoded and tvDist_self_eq_zero. reference_ne_zero proves nonzero mass for a scaled continuous-time reference measure. The names are a heuristic false positive; no common theorem claim or missing reuse is indicated.')],
 [('D', 'The new recursive CausalHistory lemma states composition of maps on the initial record and every appended record. DynamicsKernel.mapHistory_comp_appendHistory states that one state map commutes with append in a different, Finset.Iic-indexed history representation. Neither the history type nor the identity is the same; the new induction is appropriate.')],
 [('D', 'This theorem specializes riskHistoryMap_comp_general to observation maps preserving action coordinates. The old DynamicsKernel statement concerns append naturality in another history representation, rather than composition of two observation maps.'),
  ('D', 'compProd_map_historyGraph is a joint-measure/kernel graph embedding identity for an S-finite composition product. The new theorem is equality of concrete finite recursive histories; no composition-product law replaces it.')],
 [('D', 'The new theorem lifts observationHistoryMap_comp through PMF.map_comp. The old append-naturality identity has another history representation and does not assert PMF pushforward composition.'),
  ('D', 'The old historyGraph theorem concerns a measurable graph map and a kernel composition product. Here ordinary PMF pushforward functoriality and the preceding deterministic history-composition identity are the direct reusable primitives.')],
 [('A', 'deployment_rowLaw_congr_through compares two policies in one fixed observation alphabet assuming prefix agreement. The escape theorem changes the observation alphabet between Y and Option I and proves equality after decoding actual microscopic histories. escape_micro_control_kernel and escapePolicy_actual_history justify the exact state/action PMF equality; fixed-alphabet congruence alone cannot type this adapter.')],
 [('A', 'The new registration assigns N j samples to each fixed row, so its sample index and concentration budget depend on j. The old theorem assumes one uniform N. The new proof uses VariableRegisteredSamples.registered_row_calibration and the same event-inclusion argument; constant N is an adapter case, not the general signature.')],
 [('A', 'Three premise changes are substantive: dependent row sample counts, arbitrary Y with selected-event measurability on Good, and envelope assumptions only for the selected candidate on that same Good. The old endpoint requires finite Y, uniform N and an envelope for every candidate. The proof reuses selectedTrainingDeployment_failure_le, empirical_coarse_row_tv and the occupation budget, with the new arbitrary-observation risk theorem. The training law, select function, P and selected policy remain identical across fit, cap, envelope, checked event and final joint law.'),
  ('D', 'The old viable theorem chooses a specific viableFamilyPolicy and derives its zero uncovered occupation internally from viable initial fibers. The new cap theorem accepts a general policy with an occupation bound and does not require viability. A restricted viable-policy theorem cannot replace this general endpoint; the old uniform-N/finite-Y assumptions also differ.')],
 [('A', 'The new measurable projection uses dependent coordinates Sigma j, Fin (N j); the old one uses J × Fin N. Both correctly reuse measurable_pi_apply. A constant-N coordinate equivalence gives an adapter, but the old signature is not the general dependent sample space.'),
  ('D', 'Joint independence is a property of the entire family and its probability law. It is not the measurability assertion for one coordinate.'),
  ('D', 'The marginal pushforward equality is a property of the probability law, stronger and different from coordinate measurability.'),
  ('A', 'sourceSample_measurable specializes to controlled source rows with a uniform count and a time-bound wrapper. The new theorem is the generic dependent-coordinate projection for arbitrary registered rows; the old specialization cannot replace it.')],
 [('A', 'The old marginal law has a product coordinate with a uniform count; the new marginal law has a dependent Sigma coordinate with row-specific count. Both reuse measurePreserving_eval.map_eq for the same real product construction, without assuming the desired law.'),
  ('D', 'Independence does not state which marginal distribution a coordinate has. The new pushforward equality identifies that marginal with the registered row distribution.'),
  ('D', 'Measurability alone does not determine a marginal distribution. The actual product-law equality remains a separate required property.')],
 [('A', 'The new proof reuses coordinate_iIndep and iIndepFun.precomp with the injective embedding Fin (N j) → Sigma j, Fin (N j). The old proof uses Fin N → J × Fin N. The actual product law and coordinate independence are proved in both cases, but the dependent family requires the new adapter.'),
  ('D', 'Correct one-coordinate marginal laws do not imply independence of samples. This old theorem is therefore not a replacement for the independence statement.'),
  ('D', 'Measurability of projections does not imply their probabilistic independence.'),
  ('A', 'sourceSample_independent is a controlled-row, uniform-N specialization with an n < T wrapper. The new theorem proves independence for a fixed generic row with its own N j and dependent sample coordinate type.')],
 [('E', 'The proof actually applies coverage_registered_row_calibration to Unit separately for each j at N j and then combines the resulting row failure bounds by a finite union bound. It reuses the existing concentration result instead of reproving it. Registration and counts are fixed before data; cross-row independence is not added as a hidden assumption.'),
  ('A', 'coverage_registered_source_calibration specializes the old uniform-count theorem to controlled source rows. The new theorem is generic in the finite registered row type and permits unequal sample counts; the source specialization is narrower.')],
 [('A', 'The new theorem uses the same existing viableFamilyPolicy construction and proves its own zero uncovered occupation with viablePolicy_zero_uncovered. It extends the old endpoint to row-specific counts, arbitrary Y and selected Good-only measurability/envelope assumptions. In the new call to VariableRegisteredJoint the cap is derived internally with kappa = 0 for that exact policy and Good; no cap of another policy is borrowed.'),
  ('A', 'The old cap theorem can be specialized to a viable policy only within its fixed-N, finite-Y, all-candidate-envelope scope. The new proof composes the generalized cap endpoint with the existing viability result. The viability derivation is an explicit adapter and is not an assumption replacing the required zero-occupation proof.')],
]

labels = {'E':'EXISTING_THEOREM_REUSED', 'A':'ADAPTER_OR_GENERALIZATION', 'D':'DIFFERENT_PROPOSITION'}
assert len(judgments) == len(groups)
reviewed = []
for index, (g, js) in enumerate(zip(groups, judgments), 1):
    assert len(g['reuse_candidates']) == len(js)
    reviewed.append({
        'id':f'R{index:02}', 'new_symbol':g['symbol'], 'new_path':g['path'], 'new_line':g['line'],
        'status':'SEMANTIC_CLEAR_NATIVE_PENDING',
        'candidates':[dict(c, classification=labels[k], reasoning=reason,
                           semantic_outcome='CLEAR', kernel_type_outcome='PENDING_ACTUAL_NATIVE')
                      for c,(k,reason) in zip(g['reuse_candidates'],js)]})

paths = {g['path'] for g in groups} | {c['path'] for g in groups for c in g['reuse_candidates']}
paths.add('formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion.lean')
paths.add('formalization/ueot-core/UEOT/V3/FreeInformationValue.lean')
expected = {r['path']:r for r in identity['build_identity']['source_files']}
source_bindings = []
for path in sorted(paths):
    actual = digest(REPO/path)
    assert actual == expected[path]['sha256'], path
    source_bindings.append({'path':path, 'sha256':actual, 'matches_pinned_full_source_identity':True})

counts = Counter(c['classification'] for g in reviewed for c in g['candidates'])
result = {
 'schema':'UEOT_INDEPENDENT_TYPED_REUSE_SEMANTIC_REVIEW_V1',
 'reviewer':'/root/audit_resume', 'status':'SEMANTIC_CLEAR_NATIVE_PENDING',
 'base_sha':'65db00a12d20be41cd6c8befacb9ba2e74a2a8a9',
 'candidate_source_commit':'c30aa219b90173ca15e0eb9878f244de363e1fc3',
 'preflight':{'path':str(PREFLIGHT), 'sha256':digest(PREFLIGHT),
              'new_public_lexical_theorems':52, 'groups':18, 'pairs':39},
 'build_identity':{'path':str(IDENTITY), 'sha256':digest(IDENTITY),
                   'module_count':identity['build_identity']['module_count'],
                   'source_tree_sha256':identity['build_identity']['source_tree_sha256'],
                   'review_action':'Rehashed the files read for this review against the existing complete identity; no build or complete re-export rerun.'},
 'reviewed_file_bindings':source_bindings, 'classification_counts':dict(counts), 'groups':reviewed,
 'source_changes_required_by_semantic_review':[],
 'catalog_gap':{'status':'REAL_HISTORICAL_PUBLIC_THEOREM_OMISSION',
                'symbol':"UEOT.V3.FreeInformationValue.integrable_finset_sup'",
                'details':'BASE_LEXICAL_CATALOG_DIFF.json',
                'old_registered_scope':4094, 'historical_supplement':1,
                'repair_status':'REQUIRES_ACTUAL_NATIVE_AND_GOVERNED_ADDITIVE_REGISTRATION'},
 'pending_gates':[
   'Actual native ownership, types, direct proof constants and allowed axiom closure for all seven new source modules plus the unchanged historical repair module.',
   '52 new public source declarations plus one explicitly historical public repair: 53*4094 cross comparisons and 53*52/2 internal comparisons, including all 52 new-versus-repair comparisons.',
   'Actual compiled proof-edge evidence for the repair and p_ref_03; preserve frozen CSV and the old registered scope identity.',
   'Independent binding to the actual native/fixed-verifier outputs after execution; no type-distinctness, no-collision or full-build PASS is asserted here.',
   'Canonical authorization, actual-base parser/preflight and complete FKRG integration gates remain the root task; this semantic review does not substitute for them.'
 ],
 'non_claims':['No Lean or project test executed by this review.', 'No production, Mac, Git or remote mutation.',
               'No conclusion of kernel definitional inequality inferred from names or source prose.',
               'No mathematical theorem strengthened from zero uncertified occupation to zero physical risk or infinite survival.',
               'No repair of the frozen fkrg.py parser asserted.'],
}
(OUT/'REVIEW.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
md = ['# Independent semantic review of the registered-interfaces reuse candidates','',
 '**Status: `SEMANTIC_CLEAR_NATIVE_PENDING`.** All 18 flagged declarations and all 39 candidate pairs have been reviewed against their actual source. No mathematical source change is required by these reuse hints. This is a semantic clearance; compiled type comparisons and native evidence remain pending.','',
 '## Evidence and exact scope','',
 f"- Actual base: `{result['base_sha']}`.", f"- Candidate source commit: `{result['candidate_source_commit']}`.",
 f"- PR preflight SHA256: `{digest(PREFLIGHT)}`; 52 new lexical public theorems, 18 flagged groups, 39 pairs.",
 f"- Complete identity receipt SHA256: `{digest(IDENTITY)}`.",
 f"- Complete source fingerprint: `{result['build_identity']['source_tree_sha256']}`; 666 modules.",
 '- The individual files read below were rehashed against that complete identity. Existing mathematical and boundary reviews are reused; no Lean build, project test or native export was run by this review.',
 '- The original preflight and its pending review fields are preserved. This separate receipt records the independent result.','',
 '## Classification','',
 '| Classification | Pairs | Meaning |','|---|---:|---|',
 *[f'| `{key}` | {counts[key]} | '+{'EXISTING_THEOREM_REUSED':'The hinted theorem is actually called through a justified adapter.','ADAPTER_OR_GENERALIZATION':'The relationship is real, but types, quantifiers or assumptions differ.','DIFFERENT_PROPOSITION':'The hint does not identify a replacement for the new proposition.'}[key]+' |' for key in labels.values()], '',
 'These categories are not a claim that the Lean kernel has checked definitional inequality. Only the actual native comparison can supply that separate result.','',
 '## Pair-by-pair findings','']
for g in reviewed:
    md += [f"### {g['id']} — `{g['new_symbol']}`",'',f"Source: `{g['new_path']}`, declaration at line {g['new_line']}.", '']
    for c in g['candidates']:
        md += [f"**`{c['symbol']}` — `{c['classification']}`.** {c['reasoning']}",'']
md += ['## Historical omission discovered during scope reconciliation','',
 "The 4,095 actual-base lexical declarations and the 4,094 registered graph nodes differ by exactly `UEOT.V3.FreeInformationValue.integrable_finset_sup'`. The unchanged source really declares this public theorem. The historical declaration CSV truncated the trailing apostrophe, marked the resulting name `UNRESOLVED`, and omitted the actual declaration from the proof graph. Its source SHA is `e4375851def0e735d54c7d3f56ba48517040e064073fdc1283a006f1d33c1a87`. This is an actual audit gap, not merely a display-count convention.",'',
 "The old `fkrg.py` regex ends the identifier pattern with `\\b`; after a trailing apostrophe, that boundary fails and the regex can backtrack to the preceding letter. The frozen parser is not modified by this review. The precise declaration must instead be confirmed by actual native ownership/type/axiom extraction and added through an explicit historical repair record. The historical CSV and original 4,094-node identity remain immutable.",'',
 "The registered `p_ref_03` proof explicitly invokes this helper, while its frozen registered dependency list is empty. An additive existing-node edge repair is therefore required after native direct-constant confirmation. See the separate repair protocol; neither a comparison supplement nor a new graph edge is certified merely by this lexical observation.",'',
 '## Pending execution and canonical gates','',
 *['- '+x for x in result['pending_gates']], '',
 '## Source bindings','', '| Source | SHA256 |', '|---|---|',
 *[f"| `{x['path']}` | `{x['sha256']}` |" for x in source_bindings], '',
 'The structured receipt contains every exact candidate name and its source path. The candidate pairs are generated from the immutable preflight input, so neither an unreviewed hint nor a name-similarity-only conclusion is silently dropped.','']
(OUT/'REVIEW.md').write_text('\n'.join(md))

audit = REPO/'formalization/ueot-core/docs/compression/theory_completion/knowledge/audits/2026-10-10'
csv_evidence = {}
for name in ('EVERY_DECLARATION_5553_COMPACT.csv','all_3793_theorem_direct_reuse_graph.csv','EVERY_FILE_633_DETAILED_METRICS.csv'):
    p = audit/name
    with p.open() as s:
        records = [r for r in csv.DictReader(s) if 'FreeInformationValue' in str(r)]
    csv_evidence[name] = {'sha256':digest(p), 'unchanged_relevant_rows':records}
(OUT/'HISTORICAL_OMISSION_EVIDENCE.json').write_text(json.dumps({
    'status':'SOURCE_AND_FROZEN_CSV_OMISSION_CONFIRMED_NATIVE_PENDING',
    'comparison_receipt':'BASE_LEXICAL_CATALOG_DIFF.json',
    'comparison_receipt_sha256':digest(OUT/'BASE_LEXICAL_CATALOG_DIFF.json'),
    'source_path':'formalization/ueot-core/UEOT/V3/FreeInformationValue.lean',
    'source_sha256':digest(REPO/'formalization/ueot-core/UEOT/V3/FreeInformationValue.lean'),
    'old_registered_scope':4094,'supplement_count':1,
    'actual_symbol':"UEOT.V3.FreeInformationValue.integrable_finset_sup'",
    'truncated_historical_candidate':'UEOT.V3.FreeInformationValue.integrable_finset_sup',
    'frozen_csv_evidence':csv_evidence,
    'explicit_source_references':[{'line':28,'role':'declaration'},{'line':66,'role':'p_ref_03 proof use'}],
    'expected_existing_edge_repair':{'source':'UEOT.V3.FreeInformationValue.p_ref_03',
        'prior_source_theorem_deps':[],
        'added_source_theorem_deps':["UEOT.V3.FreeInformationValue.integrable_finset_sup'"],
        'status':'PENDING_ACTUAL_NATIVE_DIRECT_CONSTANTS'},
    'frozen_parser_modified':False, 'historical_csv_modified':False,
},ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'status':result['status'],'groups':18,'pairs':39,'classification_counts':dict(counts),
 'review_json_sha256':digest(OUT/'REVIEW.json'),'review_md_sha256':digest(OUT/'REVIEW.md')},indent=2))
