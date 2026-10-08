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
                'terminated_ids':[],
                'expected':{'query':'OK'},
            }
            fault_id=f'cert-n{n}-single-r{rep}'
            runs[fault_id]={
                'split':'certification',
                'protocol':'P_SINGLE_FAULT',
                'candidate_ids':candidate_ids,
                'terminated_ids':[candidate_ids[-1]],
                'expected':{'query':'OK' if n >= 3 else 'UNAVAILABLE'},
            }
    for rep in range(1,REPS+1):
        replace_id=f'holdout-replace-r{rep}'
        runs[replace_id]={
            'split':'holdout',
            'protocol':'P_REPLACE_HELDOUT',
            'candidate_ids_before':['W1','W2','W3'],
            'candidate_ids_after':['W1','W2','W4'],
            'terminated_ids':['W4'],
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
            'terminated_ids':['W2','W3'],
            'expected':{'query':'UNAVAILABLE'},
        }
        baseline_id=f'baseline-single-r{rep}'
        runs[baseline_id]={
            'split':'baseline',
            'protocol':'P_SINGLE_FAULT',
            'candidate_ids':['W1'],
            'terminated_ids':['W1'],
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

def _plain_int(value):
    return isinstance(value,int) and not isinstance(value,bool)

def action_entry_matches(action, worker_id):
    return (
        isinstance(action,dict) and
        action.get('terminated') == worker_id and
        _plain_int(action.get('pid')) and action.get('pid') > 0 and
        _plain_int(action.get('returncode')) and action.get('returncode') != 0
    )

def reply_pid_map(row, field='query'):
    query=row.get(field) if isinstance(row,dict) else None
    replies=query.get('worker_replies') if isinstance(query,dict) else None
    if not isinstance(replies,list):
        return None
    result={}
    for reply in replies:
        if not isinstance(reply,dict):
            return None
        worker_id=reply.get('worker_id')
        pid=reply.get('pid')
        if not isinstance(worker_id,str) or not _plain_int(pid) or pid <= 0:
            return None
        if worker_id in result or pid in result.values():
            return None
        result[worker_id]=pid
    return result

def expected_reply_token(row, field='query'):
    """Return the runner-issued request token for one recorded service query."""
    if not isinstance(row,dict):
        return None
    run_id=row.get('run_id')
    if not isinstance(run_id,str):
        return None
    if field == 'query':
        return run_id
    if row.get('protocol') == 'P_REPLACE_HELDOUT':
        if field == 'read_query':
            return run_id + '-read'
        if field == 'single_fault_query':
            return run_id + '-single-fault'
    return None

def query_matches_intervention(
        row, candidate_ids, terminated_ids, field='query', terminated_pids=()):
    """Check that a service query is the query implied by the registered intervention.

    In this local subprocess pilot, every non-terminated candidate is queried
    exactly once and terminated candidates must not appear in worker replies.
    The aggregate counters/output must then be recomputable from those replies.
    """
    query=row.get(field) if isinstance(row,dict) else None
    if not isinstance(query,dict):
        return False
    if query.get('candidate_size') != len(candidate_ids):
        return False
    expected_quorum=len(candidate_ids)//2 + 1
    if query.get('quorum') != expected_quorum:
        return False
    replies=query.get('worker_replies')
    if not isinstance(replies,list):
        return False
    expected_token=expected_reply_token(row,field)
    if expected_token is None:
        return False
    expected_survivors=[worker_id for worker_id in candidate_ids if worker_id not in terminated_ids]
    reply_ids=[]
    reply_pids=set()
    ok_replies=0
    for reply in replies:
        if not isinstance(reply,dict):
            return False
        worker_id=reply.get('worker_id')
        reply_pid=reply.get('pid')
        if (
            not isinstance(worker_id,str) or
            worker_id not in candidate_ids or
            worker_id in terminated_ids or
            worker_id in reply_ids or
            not _plain_int(reply_pid) or reply_pid <= 0 or
            reply_pid in reply_pids or
            reply_pid in terminated_pids or
            reply.get('status') not in {'OK','NO_REPLY','DEAD'}
        ):
            return False
        if reply.get('status') == 'OK' and reply.get('token') != expected_token:
            return False
        reply_ids.append(worker_id)
        reply_pids.add(reply_pid)
        if reply.get('status') == 'OK':
            ok_replies += 1
    if sorted(reply_ids) != sorted(expected_survivors):
        return False
    if query.get('ok_replies') != ok_replies:
        return False
    recomputed_output='OK' if ok_replies >= expected_quorum else 'UNAVAILABLE'
    return query.get('service_output') == recomputed_output

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
    if protocol == 'P_READ':
        return row.get('action') == 'none' and service_output(row) in {'OK','UNAVAILABLE'}
    if protocol == 'P_SINGLE_FAULT':
        return isinstance(row.get('action'),dict) and service_output(row) in {'OK','UNAVAILABLE'}
    if protocol == 'P_DOUBLE_FAULT':
        return isinstance(row.get('action'),list) and service_output(row) in {'OK','UNAVAILABLE'}
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

def registered_intervention_match(row, registry):
    if not isinstance(row,dict):
        return False
    if row.get('record_status') == 'EXECUTION_ERROR':
        # An execution error may occur before the registered intervention has
        # completed. It is already fatal to collection completeness.
        return True
    run_id=row.get('run_id')
    spec=registry.get(run_id) if isinstance(run_id,str) else None
    if spec is None:
        return False
    protocol=spec['protocol']
    if protocol == 'P_READ':
        return (
            row.get('action') == 'none' and
            query_matches_intervention(row,spec['candidate_ids'],[])
        )
    if protocol == 'P_SINGLE_FAULT':
        terminated=spec['terminated_ids']
        action=row.get('action')
        return (
            len(terminated)==1 and
            action_entry_matches(action,terminated[0]) and
            query_matches_intervention(
                row,spec['candidate_ids'],terminated,
                terminated_pids=(action['pid'],))
        )
    if protocol == 'P_DOUBLE_FAULT':
        terminated=spec['terminated_ids']
        actions=row.get('action')
        return (
            isinstance(actions,list) and
            len(actions)==len(terminated) and
            all(action_entry_matches(action,worker_id)
                for action,worker_id in zip(actions,terminated)) and
            len({action['pid'] for action in actions}) == len(actions) and
            query_matches_intervention(
                row,spec['candidate_ids'],terminated,
                terminated_pids=tuple(action['pid'] for action in actions))
        )
    if protocol == 'P_REPLACE_HELDOUT':
        replacement=row.get('replacement')
        if not isinstance(replacement,dict):
            return False
        read_pids=reply_pid_map(row,'read_query')
        fault_pids=reply_pid_map(row,'single_fault_query')
        if read_pids is None or fault_pids is None:
            return False
        return (
            replacement.get('old_id') == 'W3' and
            replacement.get('new_id') == 'W4' and
            _plain_int(replacement.get('old_pid')) and replacement.get('old_pid') > 0 and
            _plain_int(replacement.get('new_pid')) and replacement.get('new_pid') > 0 and
            replacement.get('old_pid') != replacement.get('new_pid') and
            _plain_int(replacement.get('old_returncode')) and
            replacement.get('old_returncode') != 0 and
            _plain_int(replacement.get('new_returncode_after_fault')) and
            replacement.get('new_returncode_after_fault') != 0 and
            read_pids.get('W4') == replacement.get('new_pid') and
            replacement.get('old_pid') not in read_pids.values() and
            replacement.get('old_pid') not in fault_pids.values() and
            all(read_pids.get(worker_id) == fault_pids.get(worker_id)
                for worker_id in ('W1','W2')) and
            query_matches_intervention(row,spec['candidate_ids_after'],[],'read_query') and
            query_matches_intervention(
                row,spec['candidate_ids_after'],spec['terminated_ids'],'single_fault_query',
                terminated_pids=(replacement['new_pid'],))
        )
    return False

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
    checks['registered_intervention_match']=all(
        registered_intervention_match(r,registry) for r in rows)
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
        checks['registered_intervention_match'] and
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
