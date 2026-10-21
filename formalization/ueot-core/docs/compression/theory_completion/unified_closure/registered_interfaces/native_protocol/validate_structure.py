#!/usr/bin/env python3
"""AST and pure in-memory protocol checks ONLY; no Lean, Git, build or export.

The synthetic incoming-edge examples below are not native evidence and are not
written to disk. A concrete exporter preview is generated as unexecuted source.
"""
import ast
import copy
import csv
from hashlib import sha256
import json
from pathlib import Path

import prepare_registered_interfaces_export as export_helper
import prepare_registered_interfaces_fixed_certificate as fixed_helper

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
REPO = ROOT/'ueot-integration'
ORIGINAL = HERE.with_name('native-tools')
def sha(path):
    return sha256(path.read_bytes()).hexdigest()


def main():
    checks = []
    for p in sorted(HERE.glob('*.py')):
        ast.parse(p.read_text(), filename=str(p))
        checks.append('AST:'+p.name)
    copied = json.loads((HERE/'UPSTREAM_COPY_MANIFEST.json').read_text())
    for row in copied['files']:
        assert sha(ORIGINAL/row['name']) == row['sha256'], row['name']
    assert (HERE/'build_identity.py').read_bytes() == (ORIGINAL/'build_identity.py').read_bytes()
    checks += ['six_original_files_unchanged','complete_build_identity_helper_byte_identical']

    registry = ast.parse((REPO/fixed_helper.PREFIX/'fkrg_reuse.py').read_text())
    overlay_filenames = next([node.right.value for node in stmt.value.elts]
        for stmt in registry.body if isinstance(stmt, ast.Assign) and
        any(isinstance(target, ast.Name) and target.id == 'OVERLAY_PATHS' for target in stmt.targets))
    assert len(overlay_filenames) == 7
    prior_names = [row['name'] for name in overlay_filenames
        for row in json.loads((REPO/fixed_helper.PREFIX/name).read_text())['public_theorems']]
    base_graph = REPO/'formalization/ueot-core/docs/compression/theory_completion/knowledge/audits/2026-10-10/all_3793_theorem_direct_reuse_graph.csv'
    with base_graph.open() as stream:
        base_names = [row['name'] for row in csv.DictReader(stream)]
    assert len(base_names) == 3793 and len(prior_names) == 301
    prior = set(base_names + prior_names)
    assert len(prior) == 4094
    preflight = json.loads((ROOT/'tmp/registered-interfaces-20261021/local-source-preflight-1/PR_PREFLIGHT.json').read_text())
    new = [{
        'name': row['symbol'], 'path':row['path'], 'line':row['line'],
        'module':row['path'].removeprefix(export_helper.CORE_PREFIX).removesuffix('.lean').replace('/','.'),
        'source_origin':'UEOT_MAINTAINED','registration_kind':'new_source_public',
    } for row in preflight['new_public_source_theorems']]
    historical = [dict(x) for x in export_helper.HISTORICAL_PUBLIC_REPAIRS]
    assert len(new) == 52 and len(historical) == 1
    assert not prior & {x['name'] for x in new + historical}
    modules = []
    for row in new:
        if row['module'] not in {x['module'] for x in modules}:
            modules.append({'module':row['module']})
    assert len(modules) == 7
    native_modules = modules + [{'module':historical[0]['module']}]
    assert len({x['module'] for x in native_modules}) == 8
    assert sha(REPO/historical[0]['path']) == historical[0]['content_sha256']
    preview = export_helper.render_export(prior_names,new+historical,native_modules,historical)
    assert '__PRIOR_NAMES__' not in preview and '__HISTORICAL_REPAIR_NAMES__' not in preview
    for anchor in (
        '  let mut nativeScope : Array Json := #[]',
        '    let deps := constants.filter fun dep => dep != name && allRegistered.contains dep',
        '  let mut registeredScanned := 0',
        '      let actualDeps := constants.filter fun dep => dep != name && allRegistered.contains dep',
        '  let historicalScan := Json.mkObj [',
        '  let mut cross := 0',
    ):
        assert preview.count(anchor) == 1, anchor
    assert 'let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]' in preview
    assert preview.count('let eq ← liftTermElabM do Meta.isDefEq') == 2
    assert 'for name in registered do' in preview and 'let constants := decl.value.getUsedConstants.toList' in preview
    (HERE/'UNEXECUTED_NATIVE_EXPORT_PREVIEW.lean').write_text(preview)
    checks += ['real_source_names_partition_52_plus_1','real_registered_catalog_preserved_4094',
               'added_scope_7_native_scope_8','pinned_historical_source_unchanged',
               'all_fixed_verifier_insertion_points_unique','same_axiom_whitelist_and_fresh_type_comparison_protocol',
               'unexecuted_exporter_preview_only']

    # Pure structural fixtures: neither these fictional callers nor the two-row
    # fixture scan are evidence about the actual 4094 compiled declarations.
    helper = historical[0]['name']
    known = 'UEOT.V3.FreeInformationValue.p_ref_03'
    second = 'STRUCTURAL_FIXTURE.secondCaller'
    older = 'STRUCTURAL_FIXTURE.existingDependency'
    path = historical[0]['path']; module = historical[0]['module']
    graph = {name:{'path':path,'line':'48','source_theorem_deps_json':json.dumps(deps)}
             for name,deps in ((known,[]),(second,[older]),(older,[]))}
    previous = {'graph':graph,'modules':[{'path':path,'module':module}]}
    rows = [{'name':known,'source_module':module,'direct_constants':[helper],
             'historical_repair_deps':[helper],'actual_source_theorem_deps':[helper]},
            {'name':second,'source_module':module,'direct_constants':[older,helper],
             'historical_repair_deps':[helper],'actual_source_theorem_deps':[older,helper]}]
    fixture = {'historical_repair_incoming_scan':{
        'registered_theorems_scanned':len(graph),'historical_public_repair_targets':[helper],
        'incoming_rows':rows}}
    registered = set(graph)|{helper}
    found = fixed_helper.existing_dependency_repairs(previous,fixture,registered,{},REPO)
    assert {x['name'] for x in found} == {known,second}
    assert next(x for x in found if x['name']==second)['prior_source_theorem_deps']==[older]
    checks.append('synthetic_structure_only_preserves_prior_edges_and_accepts_every_observed_caller')
    mutations = {}
    bad=copy.deepcopy(fixture);bad['historical_repair_incoming_scan']['registered_theorems_scanned']+=1
    mutations['wrong_scan_count']=bad
    bad=copy.deepcopy(fixture);bad['historical_repair_incoming_scan']['incoming_rows'].append(copy.deepcopy(rows[0]))
    mutations['duplicate_caller']=bad
    bad=copy.deepcopy(fixture);bad['historical_repair_incoming_scan']['incoming_rows'][1]['actual_source_theorem_deps']=[helper]
    mutations['drop_prior_edge']=bad
    bad=copy.deepcopy(fixture);bad['historical_repair_incoming_scan']['incoming_rows'][0]['actual_source_theorem_deps']=[helper,older]
    mutations['invent_direct_edge']=bad
    bad=copy.deepcopy(fixture);bad['historical_repair_incoming_scan']['incoming_rows']=rows[1:]
    mutations['missing_known_source_call']=bad
    bad=copy.deepcopy(fixture);bad['historical_repair_incoming_scan']['incoming_rows'][0]['source_module']='STRUCTURAL_FIXTURE.wrongOwner'
    mutations['wrong_owner']=bad
    for label,bad in mutations.items():
        try:
            fixed_helper.existing_dependency_repairs(previous,bad,registered,{},REPO)
        except RuntimeError:
            checks.append('synthetic_structure_only_rejects_'+label)
        else:
            raise AssertionError('did not reject fixture: '+label)
    result = {
        'status':'AST_AND_PURE_STRUCTURE_CLEAR_NATIVE_NOT_RUN',
        'native_execution_performed':False,'prepare_execution_performed':False,
        'project_tests_or_builds_performed':False,'production_or_git_mutation_performed':False,
        'checks':checks,
        'expected_counts_not_observations':{
            'new_source_declarations':52,'historical_public_repairs':1,'registered_prior':4094,
            'new_source_cross':52*4094,'historical_repair_cross':4094,'total_cross':53*4094,
            'new_source_internal':52*51//2,'new_to_repair':52,'total_internal':53*52//2,
            'added_modules':7,'native_audit_modules':8,'complete_source_modules':666,
        },
        'unexecuted_exporter_preview_sha256':sha(HERE/'UNEXECUTED_NATIVE_EXPORT_PREVIEW.lean'),
        'protocol_files':[{'path':p.name,'sha256':sha(p)} for p in sorted(HERE.iterdir())
                          if p.suffix=='.py' or p.name=='SOURCE_SCOPE.json'],
        'caveat':'Synthetic incoming-edge fixtures are in-memory structural checks, not native data. Lean parsing/elaboration, all counts actually observed, collisions, axiom closures and actual repair callers remain pending.',
    }
    (HERE/'STRUCTURAL_CHECKS.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'checks':len(checks),
                      'receipt_sha256':sha(HERE/'STRUCTURAL_CHECKS.json')},indent=2))

if __name__=='__main__':
    main()
