#!/usr/bin/env python3
import argparse
import json
from pathlib import Path

REPS=5

def expected_run_ids():
    ids=[]
    for n in [1,2,3]:
        for rep in range(1,REPS+1):
            ids.append(f'cert-n{n}-read-r{rep}')
            ids.append(f'cert-n{n}-single-r{rep}')
    for rep in range(1,REPS+1):
        ids.append(f'holdout-replace-r{rep}')
        ids.append(f'neg-double-r{rep}')
        ids.append(f'baseline-single-r{rep}')
    return ids

def load(path):
    rows=[]
    with open(path,encoding='utf-8') as f:
        for line_no,line in enumerate(f,1):
            try:
                rows.append(json.loads(line))
            except Exception as e:
                raise SystemExit(f'invalid JSON line {line_no}: {e}')
    return rows

def select(rows,prefix):
    return [r for r in rows if r['run_id'].startswith(prefix)]

def observed(rows):
    return [r for r in rows if r.get('record_status') != 'EXECUTION_ERROR']

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('raw')
    ap.add_argument('--out',required=True)
    args=ap.parse_args()
    rows=load(args.raw)
    expected=expected_run_ids()
    expected_set=set(expected)
    row_ids=[r.get('run_id') for r in rows]
    row_id_set=set(row_ids)
    execution_errors=[r for r in rows if r.get('record_status') == 'EXECUTION_ERROR']
    observed_rows=observed(rows)
    checks={}
    checks['record_count_45']=len(rows)==45
    checks['unique_run_ids']=len(row_id_set)==len(rows) and None not in row_id_set
    checks['registered_run_ids_complete']=row_id_set==expected_set
    checks['no_execution_errors']=not execution_errors
    checks['durable_attempt_logging_present']=all(
        r.get('record_status') in {'OBSERVED','EXECUTION_ERROR'} for r in rows)
    checks['all_have_timestamp']=all(bool(r.get('timestamp_utc')) for r in rows)
    checks['all_registered_matches']=checks['no_execution_errors'] and all(
        r.get('matches_expected') is True for r in observed_rows)

    candidates={}
    first_good=None
    for n in [1,2,3]:
        read=select(observed_rows,f'cert-n{n}-read-')
        fault=select(observed_rows,f'cert-n{n}-single-')
        read_ok=len(read)==REPS and all(
            r.get('query',{}).get('service_output')=='OK' for r in read)
        survives=len(fault)==REPS and all(
            r.get('query',{}).get('service_output')=='OK' for r in fault)
        candidates[str(n)]={'read_repetitions':len(read),'fault_repetitions':len(fault),
                            'healthy_read_ok':read_ok,'survives_single_fault':survives}
        if survives and first_good is None:
            first_good=n
    checks['registered_candidate_counts']=all(
        c['read_repetitions']==REPS and c['fault_repetitions']==REPS for c in candidates.values())
    checks['first_good_is_three']=first_good==3

    hold=select(observed_rows,'holdout-replace-')
    neg=select(observed_rows,'neg-double-')
    base=select(observed_rows,'baseline-single-')
    checks['heldout_count_5']=len(hold)==REPS
    checks['heldout_read_and_fault_ok']=all(
        r['read_query']['service_output']=='OK' and r['single_fault_query']['service_output']=='OK'
        for r in hold)
    checks['replacement_is_structurally_real']=all(
        r['replacement']['old_id']=='W3' and r['replacement']['new_id']=='W4' and
        r['replacement']['old_pid'] != r['replacement']['new_pid'] for r in hold)
    checks['double_fault_negative_count_5']=len(neg)==REPS
    checks['double_fault_unavailable']=all(r['query']['service_output']=='UNAVAILABLE' for r in neg)
    checks['baseline_count_5']=len(base)==REPS
    checks['single_worker_baseline_unavailable']=all(r['query']['service_output']=='UNAVAILABLE' for r in base)

    collection_complete=(
        checks['record_count_45'] and
        checks['unique_run_ids'] and
        checks['registered_run_ids_complete'] and
        checks['no_execution_errors'] and
        checks['durable_attempt_logging_present']
    )

    if collection_complete:
        claim_verdicts={
          'C7-LOCAL-FORM-01':'SUPPORTED_LOCAL' if checks['first_good_is_three'] else 'REJECTED_LOCAL',
          'C7-LOCAL-FBT-01':'SUPPORTED_LOCAL' if checks['heldout_read_and_fault_ok'] and checks['replacement_is_structurally_real'] else 'REJECTED_LOCAL',
          'C7-LOCAL-NEG-01':'SUPPORTED_LOCAL' if checks['double_fault_unavailable'] else 'REJECTED_LOCAL',
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
      'missing_run_ids':sorted(expected_set-row_id_set),
      'unexpected_run_ids':sorted(row_id_set-expected_set, key=lambda x: '' if x is None else x),
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
