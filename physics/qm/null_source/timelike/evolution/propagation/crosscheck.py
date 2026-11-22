"""Independent high precision diagnostics; not the interval certificate."""
from fractions import Fraction as Q
from pathlib import Path
import argparse
import hashlib
import json
import sys
from mpmath import mp
from background import I, derivative_box, q_box, lower, upper
from finite_modes import TARGETS

HERE=Path(__file__).resolve().parent
mp.dps=65


def point(value):
    v=Q(value)
    return mp.mpf(v.numerator)/v.denominator


def complex_point(pair):
    return mp.mpc(point(pair[0]),point(pair[1]))


def fundamental(k,t):
    """Ferrers pair for u,p; determinant exactly 2 in exact arithmetic."""
    degree=mp.mpf(k-1)/2
    x=mp.sin(2*t);c=mp.cos(2*t)
    columns=[]
    def value(n,second):
        if x==0:
            # Closed values avoid a hypergeometric 0/0 evaluation at exact zeros.
            ratio=mp.gamma((n+1)/2)/(mp.sqrt(mp.pi)*mp.gamma(1+n/2))
            return -mp.pi*mp.sinpi(n/2)*ratio/2 if second else mp.cospi(n/2)*ratio
        return (mp.legenq if second else mp.legenp)(n,0,x,type=2)
    for second in (False,True):
        y=value(degree,second)
        previous=value(degree-1,second)
        dy=degree*(previous-x*y)/(1-x*x)
        columns.append([y/mp.sqrt(3),2*mp.sqrt(3)*c*c*dy])
    return mp.matrix([[columns[j][i] for j in range(2)] for i in range(2)])


def run():
    raw=(HERE/'result.json').read_bytes()
    receipt=json.loads(raw)
    for name,expected in receipt['source_sha256'].items():
        assert hashlib.sha256((HERE/name).read_bytes()).hexdigest()==expected
    table={t:{r['k']:r for r in row['modes']} for t,row in receipt['targets'].items()}
    rows=[]
    for k in (2,3,8,16,32,64):
        original=table['0'][k]
        start=mp.matrix([complex_point(original['u_center']),complex_point(original['p_center'])])
        constants=mp.lu_solve(fundamental(k,mp.mpf(0)),start)
        for eta in TARGETS[1:]:
            t=point(eta);r=table[str(eta)][k]
            f=fundamental(k,t)
            predicted=f*constants
            actual=mp.matrix([complex_point(r['u_center']),complex_point(r['p_center'])])
            du,dp=predicted[0]-actual[0],predicted[1]-actual[1]
            a=mp.sqrt(3*mp.cos(2*t));omega=mp.sqrt(k*k-1)
            distance=mp.sqrt(omega*a*a*abs(du)**2+abs(dp)**2/(omega*a*a))
            budget=point(original['norm_error_radius'])/mp.sqrt(mp.cos(2*t))+point(r['norm_error_radius'])
            determinant_error=abs(mp.det(f)-2)
            assert distance<budget
            assert determinant_error<mp.mpf('1e-55')
            rows.append(dict(k=k,eta=str(eta),
                weighted_center_difference=mp.nstr(distance,25),
                certified_two_ball_budget=mp.nstr(budget,25),
                diagnostic_difference_to_budget_ratio=mp.nstr(distance/budget,25),
                Ferrers_determinant_error=mp.nstr(determinant_error,12)))
    # Independently re-enter the archived preparation formula to check values.
    def scalar_a(t):
        if t<=-mp.mpf(1)/8:return mp.sqrt(3)
        target=mp.sqrt(3*mp.cos(2*t))
        if t>=-mp.mpf(1)/16:return target
        x=16*(t+mp.mpf(1)/8)
        numerator=mp.exp(-1/x)
        s=numerator/(numerator+mp.exp(-1/(1-x)))
        return mp.sqrt(3)+(target-mp.sqrt(3))*s
    jet_rows=[]
    for t0 in (Q(-127,1024),Q(-15,128),Q(-3,32),Q(-9,128),Q(-65,1024),Q(0),Q(11,64)):
        t=point(t0);jet=derivative_box(t0,t0,4)
        errors=[]
        for j in range(5):
            observed=mp.diff(scalar_a,t,j)/mp.factorial(j)
            center=(lower(jet.c[j])+upper(jet.c[j]))/2
            discrepancy=abs(observed-center)
            assert discrepancy<mp.mpf('1e-50')*max(1,abs(observed))
            errors.append(mp.nstr(discrepancy,12))
        jet_rows.append(dict(eta=str(t0),diagnostic_derivative_discrepancies=errors))
    return dict(status='INDEPENDENT_DIAGNOSTIC_NOT_A_CERTIFICATE',
        receipt_sha256=hashlib.sha256(raw).hexdigest(),
        source_sha256={name:hashlib.sha256((HERE/name).read_bytes()).hexdigest()
                       for name in ('background.py','finite_modes.py','crosscheck.py')},
        primary_reference='https://dlmf.nist.gov/14.2, equations 14.2.1 and 14.2.4',
        Ferrers_tests=rows,independent_preparation_derivative_tests=jet_rows,
        all_diagnostics_passed=True)


if __name__=='__main__':
    if not __debug__:
        raise RuntimeError('Do not use -O')
    parser=argparse.ArgumentParser()
    parser.add_argument('--write',action='store_true')
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    result=run()
    if args.check:
        assert result==json.loads((HERE/'crosscheck.json').read_text())
    if args.write:
        (HERE/'crosscheck.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'Ferrers_pairs':len(result['Ferrers_tests']),
        'preparation_points':len(result['independent_preparation_derivative_tests']),
        'all_diagnostics_passed':True,'replay_passed':args.check},indent=2))
