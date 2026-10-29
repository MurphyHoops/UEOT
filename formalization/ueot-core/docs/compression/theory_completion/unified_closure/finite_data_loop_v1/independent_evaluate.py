#!/usr/bin/env python3
"""Independent truth-owning evaluation; imports neither selector nor generator.

Exact raw recount and safe-path enumeration check the saved returned policy.
Truth is used only here, never to choose a policy or replace a training record.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
import json
from pathlib import Path

if not __debug__:
    raise RuntimeError("OPTIMIZED_PYTHON_DISABLES_REQUIRED_ASSERTIONS")

N, D = 262144, F(1, 250)
PROBES = ('risk0_safe', 'risk1_safe', 'select0_failure', 'select1_failure')
EXPECTED = {'A': ('3/4','1/4','1/200','1/200'),
            'B': ('4/5','1/5','1/300','1/250'), 'C': ('3/4','1/4','1/20','1/20')}
HORIZONS = {'A': (2,10), 'B': (2,10), 'C': (10,)}


def sha(p):
    return sha256(p.read_bytes()).hexdigest()


def evaluate(batch):
    batch = Path(batch).resolve(strict=True)
    frozen = json.loads((batch/'FREEZE.json').read_text())
    private = json.loads((batch/'generator-private.json').read_text())
    assert sha(batch/'generator-private.json') == frozen['private_generator_sha256']
    assert sha(batch/'NUMERICAL_PROOF.json') == frozen['numerical_receipt_sha256']
    summary = json.loads((batch/'SAMPLE_RESULT.json').read_text())
    assert summary['state'] == 'COMPLETE_ALL_RECORDS'
    rows = []
    for name, horizons in HORIZONS.items():
        theta = tuple(map(F, private[name]['theta']))
        assert theta == tuple(map(F, EXPECTED[name]))
        r0,r1,e0,e1 = theta
        record = batch/'records'/name
        meta = json.loads((record/'training.json').read_text())
        assert meta['n'] == N and tuple(meta['probe_order']) == PROBES and len(meta['probes']) == 4
        assert meta['freeze_sha256'] == sha(batch/'FREEZE.json')
        counts = []
        for key, entry in zip(PROBES, meta['probes']):
            raw = record/(key+'.bin')
            assert entry == {'name':key,'file':key+'.bin','sha256':sha(raw)}
            bits = raw.read_bytes()
            assert len(bits) == N//8
            counts.append(sum((byte >> bit)&1 for byte in bits for bit in range(8)))
        means = tuple(F(k,N) for k in counts)
        sh = means[0]+means[1]
        nh = (means[0]/sh,means[1]/sh)
        nt = (r0/(r0+r1),r1/(r0+r1))
        good_audit = all(abs(x-y)<=D for x,y in zip(means,theta))
        for T in horizons:
            proposal_path = batch/'decisions'/f'{name}-T{T}.json'
            p = json.loads(proposal_path.read_text())
            assert p['counts'] == counts and tuple(map(F,p['estimate'])) == means
            prep = tuple(map(F,p['preparation']))
            weights = [tuple(map(F,w)) for w in p['weights']]
            assert prep == (0,*nh)
            assert weights == [(0,*nh)]*(T-1)+[(0,F(1,2),F(1,2))]
            beta = min(F(1),(T+1)*max(means[2:])+(T+1)*D+T*D/sh)
            floor = min(F(1,6),max(F(0),means[2]-D),max(F(0),means[3]-D))
            lower = 1-(1-floor)**T
            assert F(p['beta_prep']) == beta and F(p['failure_probability_lower']) == lower
            row = {'record':name,'T':T,'counts':counts,'estimate':means,
                   'candidate_sha256':sha(proposal_path),'beta':beta,'lower':lower,
                   'simulation_truth_calibration_audit':good_audit}
            deployment = json.loads((batch/'deployments'/f'{name}-T{T}.json').read_text())
            if beta<=F(1,5):
                assert p['decision']=='ACCEPT' and deployment['status']=='CANDIDATE_DEPLOYMENT_REALIZATION'
                # All safe actual atoms are products of the literal noisy
                # selection rows, independently of the prior hidden safe state.
                factors = [(w[1]*(1-e0),w[2]*(1-e1)) for w in [prep,*weights]]
                actual_safe,baseline_safe,gap = F(0),F(0),F(0)
                z = ((r0+r1)/2)**T
                for path in product((0,1),repeat=T+1):
                    actual,baseline,conditioned = F(1),F(1,2),F(1,2)
                    for t,x in enumerate(path):
                        actual *= factors[t][x]
                        if t<T:
                            baseline *= (r0,r1)[x]/2
                            conditioned *= nt[x]
                    assert baseline/z == conditioned
                    actual_safe += actual
                    baseline_safe += baseline
                    gap += abs(actual-conditioned)
                assert baseline_safe == z
                failure = 1-actual_safe
                variation = (gap+failure)/2
                # Truth is available to this independent simulation evaluator,
                # so the required actual demonstrations are checked directly.
                assert failure<=variation<=beta<=F(1,5)
                ops = deployment['operations']
                assert len(ops)==T+1 and deployment['operation_count']==T+1
                x = deployment['initial_state_before_preparation']
                assert x in (0,1)
                for k,(op,w) in enumerate(zip(ops,[prep,*weights])):
                    assert op['operation']==k and op['before_state']==x
                    assert op['phase']==('prepare' if k==0 else 'deploy')
                    a,z1 = op['action'],op['after_state']
                    assert a in (1,2) and w[a]>0 and z1 in (0,1,2)
                    if x==2: assert z1==2
                    else: assert z1 in (a-1,2)
                    x=z1
                assert deployment['post_preparation_window']==[op['after_state'] for op in ops]
                assert deployment['failure']==any(op['after_state']==2 for op in ops)
                row.update(actual_tv=variation,actual_failure_probability=failure,
                           realization_failure=deployment['failure'],actual_operations=T+1,
                           source_survival_mass=z)
            else:
                assert lower>F(1,5) and p['decision']=='REJECT_STATISTICAL_LOWER'
                assert deployment['status']=='REJECTED_NO_DEPLOYMENT'
                known_lower = 1-(1-min(F(1,6),e0,e1))**T
                assert known_lower>F(1,5)
                row.update(known_parameter_lower=known_lower,actual_operations=0)
            rows.append(row)
    return {'schema':'UEOT/INDEPENDENT_FINITE_DATA_EVALUATION/V1','status':'PASS',
            'scope':'All registered raw bits, literal policies, exact safe/dead path masses and complete unfiltered realizations; truth-owning evaluation only',
            'script_sha256':sha(Path(__file__)),'freeze_sha256':sha(batch/'FREEZE.json'),
            'registered_record_count':3,'bernoulli_results_recounted':3*4*N,'results':rows,
            'boundary':'Simulation source/RNG match remains a declared experiment assumption; no world validation or conditional-on-Accept upgrade.'}


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('batch',type=Path);parser.add_argument('--output',required=True,type=Path)
    args=parser.parse_args();result=evaluate(args.batch)
    with args.output.open('x') as stream:json.dump(result,stream,indent=2,default=str);stream.write('\n')
    print(json.dumps({'status':result['status'],'receipt':str(args.output)}))
