"""New critical-branch algebra using frozen JSON parameters, never old modules."""
from common import iv,box,interval,load,above,require,outward
HISTORY='physics/qm/null_source/timelike/joint_history/history.json'
def parameters():
    data=load(HISTORY)
    return box(data['cases']['unfiltered']['A']),box(data['fixed_U0'])
def branch_box(lo,hi,nlo,nhi):
    A,U=parameters();V=2*iv.pi**2;n=iv.mpf(2)
    u=interval(lo,hi);a2=A*A*iv.exp(2*u)
    ac=n/480;lam=n/240;Ec=n/240
    q=3*V*a2/2;r=V*U*a2*a2
    B=lam-q;D=q-r+lam/2
    t=Ec+interval(nlo,nhi)-D
    disc=B*B-4*ac*t
    require(above(-B) and above(t) and above(disc),'lower branch not admitted')
    root=iv.sqrt(disc)
    x=2*t/(-B+root)
    require(above(x),'expanding branch')
    return {'u':u,'a':iv.sqrt(a2),'a2':a2,'q':q,'r':r,
            'B':B,'D':D,'disc':disc,'sqrt_disc':root,
            'kappa2':x,'kappa':iv.sqrt(x),
            'energy_ceiling':D+B*B/(4*ac)}
def chart(nlo=0,nhi=100,segments=200):
    lo=iv.mpf(27)/50;hi=iv.mpf(14)/25;du=(hi-lo)/segments
    # Endpoints are exact rationals supplied as decimal strings.
    rows=[]
    for j in range(segments):
        a=f'0.{5400+j:04d}' if segments==200 else None
        b=f'0.{5401+j:04d}' if segments==200 else None
        if a is None:raise ValueError('Declared exact 200-cell chart only')
        row=branch_box(a,b,nlo,nhi)
        require(above(row['u'].b-row['u'].a,'0.000099999999999') and bool((row['u'].b-row['u'].a).b<iv.mpf('0.000100000000001')),'chart cell width')
        rows.append(row)
    require(bool(rows[0]['u'].a <= lo.a) and bool(rows[-1]['u'].b >= hi.b),'chart endpoint coverage')
    require(bool(abs(rows[0]['u'].a-lo.a).b<iv.mpf('1e-90')) and bool(abs(rows[-1]['u'].b-hi.b).b<iv.mpf('1e-90')),'exact chart endpoints')
    return rows,du
def extrema(rows,key):
    return iv.mpf([min(row[key].a for row in rows),max(row[key].b for row in rows)])
