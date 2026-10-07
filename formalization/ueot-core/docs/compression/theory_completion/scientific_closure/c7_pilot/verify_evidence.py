#!/usr/bin/env python3
import argparse
import json
from pathlib import Path

REPS=5

def registered_runs():
    """Authoritative preregistered metadata and expected outputs for all 45 runs."""
    runs={}
    for n in [1,2,3]:
        candidate_ids=[f'W{i}' for i in range(1,n+1)]
        for rep in range(1,REPS+1):
            read_id=f'cert-n{n}-read-r{rep}'
            runs[read_id]={
                'split':'certification',
                'protocol':'P_READ',
                'candidate_ids':candidate_ids,
                'expected':{'query':'OK'},
            }
            fault_id=f'cert-n{n}-single-r{rep}'
            runs[fault_id]={
                'split':'certification',
                'protocol':'P_SINGLE_FAULT',
                'candidate_ids':candidate_ids,
                'expected':{'query':'OK' if n >= 3 else 'UNAVAILABLE'},
            }
    for rep in range(1,REPS+1):
        replace_id=f'holdout-replace-r{rep}'
        runs[replace_id]={
            'split':'holdout',
            'protocol':'P_REPLACE_HELDOUT',
            'candidate_ids_before':['W1','W2','W3'],
            'candidate_ids_after':['W1','W2','W4'],
            # An execution error can occur before replacement completes; the
            # runner records the registered source candidate in that case.
            'error_candidate_ids':['W1','W2','W3'],
            'expected':{'read_query':'OK','single_fault_query':'OK'},
        }
        negative_id=f'neg-double-r{rep}'
        runs[negative_id]={
            'split':'negative_control',
            'protocol':'P_DOUBLE_FAULT',
            'candidate_ids':['W1','W2','W3'],
            'expected':{'query':'UNAVAILABLE'},
        }
        baseline_id=f'baseline-single-r{rep}'
        runs[baseline_id]={
            'split':'baseline',
            'protocol':'P_SINGLE_FAULT',
            'candidate_ids':['W1'],
            'expected':{'query':'UNAVAILABLE'},
        }
    return runs

def expected_run_ids():
    return list(registered_runs())

def load(path):
    rows=[]
    with open(path,encoding='utf-8') as f:
        for line_no,line in enumerate(f,1):
            try:
                value=json.loads(line)
                # Preserve malformed JSON values as an integrity failure that
                # can still produce an UNRESOLVED result file, rather than
                # crashing later on `.get` or subscription.
                rows.append(value if isinstance(value,dict) else {'_malformed_json_value':value})
            except Exception as e:
                raise SystemExit(f'invalid JSON line {line_no}: {e}')
    return rows

def select(rows,prefix):
    selected=[]
    for row in rows:
        run_id=row.get('run_id') if isinstance(row,dict) else None
        if isinstance(run_id,str) and run_id.startswith(prefix):
            selected.append(row)
    return selected

def observed(rows):
    return [r for r in rows if isinstance(r,dict) and r.get('record_status') != 'EXECUTION_ERROR']

def service_output(row, field='query'):
    if not isinstance(row,dict):
        return None
    value=row.get(field)
    return value.get('service_output') if isinstance(value,dict) else None

def observed_schema_complete(row):
    if not isinstance(row,dict):
        return False
    if row.get('record_status') == 'EXECUTION_ERROR':
        return (
            all(k in row for k in (
                'timestamp_utc','run_id','split','protocol','candidate_ids',
                'matches_expected','error_type','error_message')) and
            row.get('matches_expected') is False
        )
    if not all(k in row for k in ('timestamp_utc','run_id','split','protocol','matches_expected')):
        return False
    protocol=row.get('protocol')
    if protocol == 'P_REPLACE_HELDOUT':
        replacement=row.get('replacement')
        return (
            service_output(row,'read_query') in {'OK','UNAVAILABLE'} and
            service_output(row,'single_fault_query') in {'OK','UNAVAILABLE'} and
            isinstance(replacement,dict) and
            all(k in replacement for k in ('old_id','new_id','old_pid','new_pid'))
        )
    if protocol in {'P_READ','P_SINGLE_FAULT','P_DOUBLE_FAULT'}:
        return service_output(row) in {'OK','UNAVAILABLE'}
    return False

def registered_metadata_match(row, registry):
    if not isinstance(row,dict):
        return False
    run_id=row.get('run_id')
    if not isinstance(run_id,str):
        return False
    spec=registry.get(run_id)
    if spec is None:
        return False
    if row.get('split') != spec['split'] or row.get('protocol') != spec['protocol']:
        return False
    if row.get('record_status') == 'EXECUTION_ERROR':
        expected_ids=spec.get('error_candidate_ids',spec.get('candidate_ids'))
        return row.get('candidate_ids') == expected_ids
    if spec['protocol'] == 'P_REPLACE_HELDOUT':
        return (
            row.get('candidate_ids_before') == spec['candidate_ids_before'] and
            row.get('candidate_ids_after') == spec['candidate_ids_after']
        )
    return row.get('candidate_ids') == spec['candidate_ids']

def observed_outcome_matches_registration(row, registry):
    if not isinstance(row,dict) or row.get('record_status') == 'EXECUTION_ERROR':
        return False
    run_id=row.get('run_id')
    spec=registry.get(run_id) if isinstance(run_id,str) else None
    if spec is None:
        return False
    return all(service_output(row,field) == expected for field,expected in spec['expected'].items())

def producer_match_flag_consistent(row, registry):
    if not isinstance(row,dict):
        return False
    if row.get('record_status') == 'EXECUTION_ERROR':
        return row.get('matches_expected') is False
    return row.get('matches_expected') is observed_outcome_matches_registration(row,registry)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('raw')
    ap.add_argument('--out',required=True)
    args=ap.parse_args()
    rows=load(args.raw)
    registry=registered_runs()
    expected=list(registry)
    expected_set=set(expected)
    row_ids=[r.get('run_id') if isinstance(r,dict) else None for r in rows]
    valid_row_ids=[run_id for run_id in row_ids if isinstance(run_id,str)]
    row_id_set=set(valid_row_ids)
    malformed_run_id_count=len(rows)-len(valid_row_ids)
    execution_errors=[
        r for r in rows if isinstance(r,dict) and r.get('record_status') == 'EXECUTION_ERROR']
    observed_rows=observed(rows)
    checks={}
    checks['record_count_45']=len(rows)==45
    checks['unique_run_ids']=malformed_run_id_count==0 and len(row_id_set)==len(rows)
    checks['registered_run_ids_complete']=row_id_set==expected_set
    checks['no_execution_errors']=not execution_errors
    checks['durable_attempt_logging_present']=all(
        isinstance(r,dict) and r.get('record_status') in {'OBSERVED','EXECUTION_ERROR'} for r in rows)
    checks['observed_schema_complete']=all(observed_schema_complete(r) for r in rows)
    checks['registered_metadata_match']=all(registered_metadata_match(r,registry) for r in rows)
    checks['all_have_timestamp']=all(
        isinstance(r,dict) and bool(r.get('timestamp_utc')) for r in rows)
    checks['all_registered_outcomes_match']=checks['no_execution_errors'] and all(
        observed_outcome_matches_registration(r,registry) for r in observed_rows)
    checks['producer_match_flag_consistent']=all(
        producer_match_flag_consistent(r,registry) for r in rows)

    candidates={}
    first_good=None
    for n in [1,2,3]:
        read=select(observed_rows,f'cert-n{n}-read-')
        fault=select(observed_rows,f'cert-n{n}-single-')
        read_ok=len(read)==REPS and all(service_output(r)=='OK' for r in read)
        survives=len(fault)==REPS and all(service_output(r)=='OK' for r in fault)
        candidates[str(n)]={'read_repetitions':len(read),'fault_repetitions':len(fault),
                            'healthy_read_ok':read_ok,'survives_single_fault':survives}
        if read_ok and survives and first_good is None:
            first_good=n
    checks['registered_candidate_counts']=all(
        c['read_repetitions']==REPS and c['fault_repetitions']==REPS for c in candidates.values())
    checks['all_candidate_healthy_reads_ok']=all(c['healthy_read_ok'] for c in candidates.values())
    checks['first_good_is_three']=first_good==3

    hold=select(observed_rows,'holdout-replace-')
    neg=select(observed_rows,'neg-double-')
    base=select(observed_rows,'baseline-single-')
    checks['heldout_count_5']=len(hold)==REPS
    checks['heldout_read_and_fault_ok']=all(
        service_output(r,'read_query')=='OK' and service_output(r,'single_fault_query')=='OK'
        for r in hold)
    checks['replacement_is_structurally_real']=all(
        isinstance(r.get('replacement'),dict) and
        r['replacement'].get('old_id')=='W3' and r['replacement'].get('new_id')=='W4' and
        r['replacement'].get('old_pid') != r['replacement'].get('new_pid') for r in hold)
    checks['double_fault_negative_count_5']=len(neg)==REPS
    checks['double_fault_unavailable']=all(service_output(r)=='UNAVAILABLE' for r in neg)
    checks['baseline_count_5']=len(base)==REPS
    checks['single_worker_baseline_unavailable']=all(service_output(r)=='UNAVAILABLE' for r in base)

    collection_complete=(
        checks['record_count_45'] and
        checks['unique_run_ids'] and
        checks['registered_run_ids_complete'] and
        checks['no_execution_errors'] and
        checks['durable_attempt_logging_present'] and
        checks['observed_schema_complete'] and
        checks['registered_metadata_match'] and
        checks['all_have_timestamp']
    )

    if collection_complete:
        claim_verdicts={
          'C7-LOCAL-FORM-01':'SUPPORTED_LOCAL' if (
              checks['registered_candidate_counts'] and
              checks['all_candidate_healthy_reads_ok'] and
              checks['first_good_is_three']) else 'REJECTED_LOCAL',
          'C7-LOCAL-FBT-01':'SUPPORTED_LOCAL' if (
              checks['heldout_count_5'] and
              checks['heldout_read_and_fault_ok'] and
              checks['replacement_is_structurally_real']) else 'REJECTED_LOCAL',
          'C7-LOCAL-NEG-01':'SUPPORTED_LOCAL' if (
              checks['double_fault_negative_count_5'] and
              checks['double_fault_unavailable']) else 'REJECTED_LOCAL',
        }
    else:
        claim_verdicts={
          'C7-LOCAL-FORM-01':'UNRESOLVED',
          'C7-LOCAL-FBT-01':'UNRESOLVED',
          'C7-LOCAL-NEG-01':'UNRESOLVED',
        }

    result={
      'kind':'RAW_EVIDENCE_RECOMPUTATION',
      'raw_file':Path(args.raw).name,
      'checks':checks,
      'execution_errors':execution_errors,
      'malformed_run_id_count':malformed_run_id_count,
      'missing_run_ids':sorted(expected_set-row_id_set),
      'unexpected_run_ids':sorted(row_id_set-expected_set),
      'candidate_results':candidates,
      'first_good_nested_candidate_size':first_good,
      'claim_verdicts':claim_verdicts,
      'all_checks_pass':all(checks.values()),
      'independent_review':'REVIEW_PENDING',
      'real_world_support':'UNVERIFIED'
    }
    Path(args.out).write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))
    if not result['all_checks_pass']:
        raise SystemExit(1)

if __name__=='__main__':
    main()
