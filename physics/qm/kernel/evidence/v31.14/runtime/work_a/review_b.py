"""Independent read-back of B certificates and explicit A/B Choi conventions."""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
from fractions import Fraction as F
import hashlib
import importlib.util
import itertools
import json
import math
from pathlib import Path
import time
import numpy as np

from finite_operations import (FiniteTest, frame, probabilities,
                               reconstruct_blocks, trace_norm)

ZERO=(F(0),F(0))

def ca(a,b): return (a[0]+b[0],a[1]+b[1])
def cm(a,b): return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def cs(a,b): return (a[0]*b,a[1]*b)
def cc(a): return (a[0],-a[1])

def dyadic(t):
    sign,man,exp,bc=map(int,t)
    if not man: return F(0)
    return (-1 if sign else 1)*F(man)*(F(2)**exp)

def sqrt_up(x,den=10**40):
    if x<0: raise ValueError('nonnegative radicand required')
    n=math.isqrt(x.numerator*den*den//x.denominator)
    if n*n*x.denominator < x.numerator*den*den: n+=1
    return F(n,den)

def det(matrix):
    n=len(matrix); ans=ZERO
    for p in itertools.permutations(range(n)):
        inversions=sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))
        value=(F(-1 if inversions%2 else 1),F(0))
        for i in range(n): value=cm(value,matrix[i][p[i]])
        ans=ca(ans,value)
    return ans

def psd_principal_minors(matrix):
    n=len(matrix)
    assert all(matrix[i][j]==cc(matrix[j][i]) for i in range(n) for j in range(n))
    values=[]
    for k in range(1,n+1):
        for indices in itertools.combinations(range(n),k):
            value=det([[matrix[i][j] for j in indices] for i in indices])
            assert value[1]==0 and value[0]>=0
            values.append(value[0])
    return {'count':len(values),'strictly_positive_count':sum(x>0 for x in values),
            'smallest_display':float(min(values))}

def decode(pairs):
    return [[(F(z[0]),F(z[1])) for z in row] for row in pairs]

def to_float(matrix):
    return np.array([[complex(float(z[0]),float(z[1])) for z in row] for row in matrix])

def source_check(path,bdir):
    data=json.loads(path.read_text())
    for name,sha in data['source_sha256'].items():
        assert hashlib.sha256((bdir/name).read_bytes()).hexdigest()==sha, (path,name)
    if data['represented_backend']=='galerkin':
        assert data['galerkin_cutoff_if_applicable']==20
    bound=F(0); raw={}
    for label,entries in data['choi_blocks'].items():
        square=F(0); matrix=[]
        for row in entries:
            nr=[]
            for z in row:
                real=F.from_float(float.fromhex(z['stored_binary64_real_hex']))
                imag=F.from_float(float.fromhex(z['stored_binary64_imag_hex']))
                nr.append((real,imag))
                rr=max(abs(dyadic(z['real'][0])-real),abs(dyadic(z['real'][1])-real))
                ii=max(abs(dyadic(z['imag'][0])-imag),abs(dyadic(z['imag'][1])-imag))
                square+=rr*rr+ii*ii
            matrix.append(nr)
        bound+=2*sqrt_up(square)
        raw[label]=[ [cs(ca(matrix[i][j],cc(matrix[j][i])),F(1,2))
                      for j in range(4)] for i in range(4)]
    assert bound<F(1,10**12)
    repair=data['physical_repair']
    delta=F(repair['delta']);scale=F(repair['scale'])
    assert scale==1/(1+20*delta) and bound<delta
    r=decode(repair['residual_exact_fraction_pairs'])
    blocks={label:decode(v) for label,v in repair['choi_blocks_exact_fraction_pairs'].items()}
    for label,block in blocks.items():
        for i in range(4):
            for j in range(4):
                expected=cs(ca(raw[label][i][j],(delta if i==j else F(0),F(0))),scale)
                if label=='f' and i<2 and j<2: expected=ca(expected,r[i][j])
                assert block[i][j]==expected
    for i in range(2):
        for j in range(2):
            actual=ZERO
            for block in blocks.values(): actual=ca(actual,ca(block[i][j],block[i+2][j+2]))
            assert actual==(F(1,2) if i==j else F(0),F(0))
    psd={label:psd_principal_minors(block) for label,block in blocks.items()}
    rpsd=psd_principal_minors(r)
    precise_bound=scale*(40*delta+2*bound)
    assert precise_bound<F(1,10**8)
    return {'file':path.name,'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
            'represented_backend':data['represented_backend'],
            'galerkin_cutoff':data['galerkin_cutoff_if_applicable'],
            'raw_error_rational_upper':str(bound),'raw_error_upper_display':float(bound),
            'physical_error_upper_display':float(precise_bound),
            'exact_repair_formula_match':True,'exact_trace_preservation':True,
            'exact_principal_minor_psd':psd,'residual_psd':rpsd}, blocks

def kraus_from_choi(blocks,swap=True,scale=2):
    order=np.array([0,2,1,3])
    branches={}
    for label,j in blocks.items():
        unnormalized=scale*(j[np.ix_(order,order)] if swap else j)
        w,v=np.linalg.eigh(unnormalized)
        assert w.min()>-1e-13
        branches[label]=tuple((np.sqrt(max(0,x))*v[:,k]).reshape(2,2,order='F')
                               for k,x in enumerate(w))
    return FiniteTest(2,2,branches)

def interface_check(exact_blocks,bdir):
    spec=importlib.util.spec_from_file_location('b_dynamics_independent_read',bdir/'dynamics.py')
    dynamics=importlib.util.module_from_spec(spec);spec.loader.exec_module(dynamics)
    j={label:to_float(v) for label,v in exact_blocks.items()}
    test=kraus_from_choi(j);complete=test.validate()
    _,states,dual=frame(2)
    labels,p=probabilities(test,states,states)
    p_direct=np.zeros_like(p)
    for r,rho in enumerate(states):
        out=dynamics.apply_stored_choi(j,rho)
        for y,label in enumerate(labels):
            for q,effect in enumerate(states): p_direct[y,q,r]=np.trace(effect@out[label]).real
    probability_error=float(np.max(np.abs(p-p_direct)))
    assert probability_error<1e-13
    rng=np.random.default_rng(7001)
    a=rng.normal(size=(6,6))+1j*rng.normal(size=(6,6))
    rho=a@a.conj().T;rho/=np.trace(rho)
    reconstructed=reconstruct_blocks(p,dual,dual,rho,reference_dim=3)
    direct=dynamics.apply_stored_choi(j,rho)
    error=sum(trace_norm(z-direct[y]) for y,z in zip(labels,reconstructed))/2
    assert error<1e-13
    source=dynamics.exact_output(.3,rho_sr=rho)
    source_error=sum(trace_norm(direct[y]-source[y]) for y in labels)/2
    assert source_error<1e-8
    # An actual convention negative control: omitting either normalization or swap.
    no_scale=kraus_from_choi(j,scale=1)
    assert no_scale.completeness_residual()>.49
    no_swap=kraus_from_choi(j,swap=False)
    _,p_wrong=probabilities(no_swap,states,states)
    wrong_swap=float(np.max(np.abs(p_wrong-p_direct)))
    assert wrong_swap>1e-3
    return {'incoming_convention':'B normalized Choi in output S tensor input/reference order',
            'outgoing_convention':'A unnormalized Choi in input tensor output order',
            'conversion':'C_A=2*SWAP*J_B*SWAP; permutation (0,2,1,3)',
            'numerical_kraus_extraction_status':'finite guard only; exact rational PSD checked separately',
            'completeness_residual':complete,'preparation_count':4,'binary_effect_count':4,
            'full_terminal_labels':labels,'test_probability_max_residual':probability_error,
            'executed_reference_dimension':3,
            'reconstruction_vs_B_direct_full_trace_distance':error,
            'repaired_vs_source_executed_input_trace_distance':source_error,
            'missing_scale_completeness_residual':no_scale.completeness_residual(),
            'missing_swap_probability_gap':wrong_swap}

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--bdir',type=Path,default=Path(__file__).parent.parent/'work_b')
    parser.add_argument('--output',type=Path,default=Path(__file__).with_name('A_REVIEW_B_CHECK.json'))
    args=parser.parse_args();start=time.perf_counter()
    index=json.loads((args.bdir/'interval_certificate_index.json').read_text())
    certificates=[];original=None
    for item in index:
        check,blocks=source_check(args.bdir/item['file'],args.bdir)
        certificates.append(check)
        if item['file']=='interval_generator_original_weyl.json': original=blocks
    assert original is not None
    memory_path=args.bdir/'memory_event_witness.json'
    memory=json.loads(memory_path.read_text())
    for name,sha in memory['source_sha256'].items():
        assert hashlib.sha256((args.bdir/name).read_bytes()).hexdigest()==sha
    event_gap=dyadic(memory['reset_event_probability_interval'][0])-dyadic(memory['true_event_probability_interval'][1])
    assert event_gap>F(3,100)
    assert dyadic(memory['reset_minus_true_gap_interval'][0])>F(3,100)
    result={'schema':'ueot-physics-a-review-b/1',
            'time_utc':datetime.now(timezone.utc).isoformat(),
            'status':'PASS_EXACT_CERTIFICATE_READBACK_AND_DECLARED_INTERFACE',
            'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in
                             [Path(__file__),Path(__file__).with_name('finite_operations.py'),
                              args.bdir/'dynamics.py',args.bdir/'interval_certificate.py']},
            'certificates':certificates,'interface':interface_check(original,args.bdir),
            'fixed_source_memory_event':{'sha256':hashlib.sha256(memory_path.read_bytes()).hexdigest(),
                'event':'ppp AND X_S tensor X_R = +1',
                'independently_subtracted_rational_gap_lower':str(event_gap),
                'gap_lower_display':float(event_gap),'strictly_larger_than':'3/100'},
            'limitations':'Independent certificate endpoint/Fraction read-back and finite interface; no new Lean or device measurement'}
    result['runtime_seconds']=time.perf_counter()-start
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'certificate_count':len(certificates),
                     'exact_principal_minors_checked':sum(sum(x['count'] for x in c['exact_principal_minor_psd'].values())+c['residual_psd']['count'] for c in certificates),
                     'interface':result['interface'],'runtime_seconds':result['runtime_seconds'],
                     'output':str(args.output)},indent=2))

if __name__=='__main__': main()
