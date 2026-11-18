"""A strict observed-event gap for the frozen three-slot reset counterexample."""
from __future__ import annotations
import hashlib,json
from pathlib import Path
from mpmath import iv,mp
from interval_certificate import rational,eye,zero_matrix,multiply,conjugate,interval_choi,raw_interval


def adjoint(a):
    return [[conjugate(a[j][i]) for j in range(len(a))] for i in range(len(a))]


def on_system(a):
    return [[a[i//2][j//2] if i%2==j%2 else iv.mpc(0) for j in range(4)] for i in range(4)]


def congruence(a,rho):
    return multiply(multiply(a,rho),adjoint(a))


def reset_output(lam):
    ts=['2/3','3/4','1/2'];sq2=iv.sqrt(2);sq3=iv.sqrt(3)
    ry=[[1/sq2,-1/sq2],[1/sq2,1/sq2]]
    rx=[[sq3/2,iv.mpc(0,-rational('1/2'))],[iv.mpc(0,-rational('1/2')),sq3/2]]
    rotations=[ry,rx,eye()];p,f=zero_matrix(),zero_matrix()
    p[0][0],p[1][1]=iv.sqrt(rational('7/8')),iv.sqrt(rational('3/4'))
    f[0][0],f[1][1]=iv.sqrt(rational('1/8')),rational('1/2')
    active=zero_matrix(4)
    for i in (0,3):
        for j in (0,3):active[i][j]=rational('1/2')
    out={}
    for k,tt in enumerate(ts):
        t=rational(tt)
        coherence=iv.exp(-4*lam**2*((1-iv.cos(t))+rational('4/25')*(1-iv.cos(rational('3/2')*t))))
        for i in range(4):
            for j in range(4):
                if i//2!=j//2:active[i][j]*=coherence
        out['p'*k+'f']=congruence(on_system(f),active)
        active=congruence(on_system(multiply(rotations[k],p)),active)
    out['ppp']=active
    return out


def event_probability(block):
    # Effect (I + X tensor X)/2, with no detector imperfection.
    result=iv.mpc(0)
    for i in range(4):
        result+=(block[i][i]+block[3-i][i])/2
    return result.real


def main():
    iv.dps=80;mp.dps=110
    true=interval_choi('3/10',80)
    reset=reset_output(rational('3/10'))
    true_p=event_probability(true['ppp'])
    reset_p=event_probability(reset['ppp'])
    gap=reset_p-true_p
    assert mp.mpf(gap._mpi_[0])>mp.mpf(rational('3/100')._mpi_[1])
    result={
        'schema':'ueot.persistent_bath.memory_event_witness.v1',
        'status':'STRICT_INTERVAL_EVENT_GAP_CERTIFIED',
        'source':'same frozen three-slot source, lambda=3/10, Bell input',
        'competitor':'same isolated per-slot channels with a fresh vacuum bath after every slot',
        'single_slot_equality':'exact for every input/reference: both use the same vacuum one-slot channel and same complete F/P instrument',
        'event':'terminal record ppp AND +1 outcome of X_S tensor X_R',
        'actual_detector_in_this_witness':'ideal eta=1 as an allowed mathematical terminal tester, not the synthetic calibrated detector estimate',
        'true_event_probability_interval':raw_interval(true_p),
        'reset_event_probability_interval':raw_interval(reset_p),
        'reset_minus_true_gap_interval':raw_interval(gap),
        'gap_lower_display':mp.nstr(mp.mpf(gap._mpi_[0]),32),
        'strict_event_gap_lower_rational':'3/100',
        'full_CQ_trace_distance_strict_lower_rational':'3/100',
        'reason':'a complete-output event probability gap lower-bounds trace distance',
        'arithmetic':'80-digit mpmath.iv; exact dyadic endpoints exported',
        'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__),Path(__file__).with_name('interval_certificate.py')]},
        'not_claimed':['trace-norm interval evaluation of diagnostic 0.1012518562','real-device memory','different causal-break protocol substituted for this source']}
    out=Path(__file__).with_name('memory_event_witness.json')
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'gap_lower_display':result['gap_lower_display'],'strict_lower':'3/100'},indent=2))


if __name__=='__main__':main()
