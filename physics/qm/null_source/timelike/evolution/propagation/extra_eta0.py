"""Certified extra modes only at eta=0, with a stress-sum exit criterion."""
from fractions import Fraction as Q
from pathlib import Path
import argparse
import hashlib
import json
import sys
import time
from mpmath import iv
import finite_modes as fm
from background import I, derivative_box, upper

HERE=Path(__file__).resolve().parent
SOURCE_NAMES=('background.py','finite_modes.py','extra_eta0.py')


def calculate(first=65,last=256,degree=12,tolerance='1e-10',rho_budget='0.01'):
    assert 2<=first<=last
    start=time.monotonic()
    frozen={name:hashlib.sha256((HERE/name).read_bytes()).hexdigest() for name in SOURCE_NAMES}
    # The existing mesh builder reads this explicitly documented target list.
    # No input source file or archived state preparation is modified.
    fm.TARGETS=(Q(0),)
    cells=fm.make_mesh(last,degree,tolerance)
    print(f'Certified eta0 mesh: {len(cells)} cells',file=sys.stderr,flush=True)
    a=derivative_box(Q(0),Q(0),0).c[0]
    rows=[]
    for k in range(first,last+1):
        omega=iv.sqrt(k*k-1);a0=iv.sqrt(3)
        u,du=fm.recenter(iv.mpc(1/(a0*iv.sqrt(2*omega)),0))
        p,dp=fm.recenter(iv.mpc(0,-a0*iv.sqrt(omega/2)))
        error=fm.bound(iv.sqrt(omega*a0*a0*du*du+dp*dp/(omega*a0*a0)))
        for cell in cells:
            u,p,error=fm.step(u,p,error,cell,k,degree)
        rows.append(fm.report_mode(u,p,error,a,cells[-1]['h_end'],k))
        if k%16==0 or k==last:
            print(f'Certified extra k={k}, energy radius={float(upper(error)):.3e}',file=sys.stderr,flush=True)
    rho_error=I(0)
    raw_rho=I(0)
    raw_pressure=I(0)
    for row in rows:
        weight=I(row['k']**2)/(4*iv.pi**2*a**4)
        rho_error+=weight*I(Q(row['e_s_error_radius']))
        raw_rho+=weight*fm.box(Q(row['e'][0]),Q(row['e'][1]))
        raw_pressure+=weight*fm.box(Q(row['s'][0]),Q(row['s'][1]))
    assert upper(rho_error)<fm.lower(I(rho_budget)), ('finite rho error budget',rho_error)
    assert frozen=={name:hashlib.sha256((HERE/name).read_bytes()).hexdigest() for name in SOURCE_NAMES}, 'source changed during verification'
    return dict(status='VALIDATED_EXTRA_FINITE_MODES_AT_ETA0_ONLY',
        first_nonzero_mode=first,last_nonzero_mode=last,degree=degree,
        precision_decimal=iv.dps,requested_sum_local_relative_budget=tolerance,
        requested_rho_error_budget=rho_budget,
        finite_rho_and_pressure_error_upper=fm.decimal_box(rho_error)[1],
        raw_finite_rho=fm.decimal_box(raw_rho),
        raw_finite_pressure=fm.decimal_box(raw_pressure),
        canonical_reference='instrument.state_scale; interpolate a not a²; k1 excluded',
        energy_norm='E²=omega*a²*|delta u|²+|delta p|²/(omega*a²)',
        mesh_cells=len(cells),mesh=[[str(c['lo']),str(c['hi'])] for c in cells],
        log_energy_growth_upper=fm.decimal_box(sum((c['variation'] for c in cells),I(0)))[1],
        sum_local_relative_remainder_upper=fm.decimal_box(sum((c['remainder'] for c in cells),I(0)))[1],
        max_energy_radius=max(float(Q(row['norm_error_radius'])) for row in rows),
        targets={'0':dict(eta='0',a=fm.decimal_box(a),modes=rows)},
        source_sha256=frozen,numerical_tail_beyond_cutoff='NOT_IN_THIS_CERTIFICATE',
        dynamic_absolute_stress='requires UV tail and same-scheme local additions',
        diagnostic_wall_seconds=round(time.monotonic()-start,3))


if __name__=='__main__':
    if not __debug__:
        raise RuntimeError('Validated propagation requires assertions; do not use -O')
    parser=argparse.ArgumentParser()
    parser.add_argument('--first',type=int,default=65)
    parser.add_argument('--last',type=int,default=256)
    parser.add_argument('--degree',type=int,default=12)
    parser.add_argument('--tolerance',default='1e-10')
    parser.add_argument('--rho-budget',default='0.01')
    parser.add_argument('--output',type=Path,default=HERE/'extra_eta0_256.json')
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    result=calculate(args.first,args.last,args.degree,args.tolerance,args.rho_budget)
    if args.check:
        old=json.loads(args.output.read_text())
        for key in set(old)|set(result):
            if key!='diagnostic_wall_seconds':
                assert old[key]==result[key],('receipt mismatch',key)
        print('PASS: extra eta0 finite modes and exact receipt replay')
    else:
        args.output.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
        print(f'Saved {args.output}; certified finite rho error <= {float(Q(result["finite_rho_and_pressure_error_upper"])):.3e}')
