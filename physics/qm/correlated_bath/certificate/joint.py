"""Convex outer confidence polytope, vertex Choi checks and interpolation remainder."""
import argparse
import hashlib
import itertools
import json
import tempfile
from fractions import Fraction as F
from pathlib import Path
from mpmath import iv
import complete as cp


def cross(a,b):
    return [a[(i+1)%3]*b[(i+2)%3]-a[(i+2)%3]*b[(i+1)%3] for i in range(3)]


def dot(a,b):
    return sum(x*y for x,y in zip(a,b))


def vertices(planes):
    answer = set()
    for (a,r),(b,s),(c,t) in itertools.combinations(planes,3):
        y,z,h = cross(b,c),cross(c,a),cross(a,b)
        det = dot(a,y)
        if det:
            v=tuple(F(r*i+s*j+t*k,det) for i,j,k in zip(y,z,h))
            if all(dot(row,v)<=hi for row,hi in planes):
                answer.add(v)
    return sorted(answer)


def bracket(row,lo,hi):
    return [(row,F(hi)),(tuple(-v for v in row),-F(lo))]


def ramsey(t):
    d=[]
    for om,g in [(cp.exact(1),cp.exact(1)),(cp.exact('3/2'),cp.exact('3/5'))]:
        d.append(g/om*(1-iv.exp(iv.mpc(0,om*cp.exact(t)))))
    A=2*sum(z.real**2+z.imag**2 for z in d)
    B=8*(d[0].real*d[1].real+d[0].imag*d[1].imag)
    return A,B


def hull(fit):
    out=fit["simultaneous_outer"]
    planes=bracket((0,0,1),max(F('1/25'),F(out['w'][0])),min(F('4/25'),F(out['w'][1])))
    planes += [((-1,2,1),0),((-1,-2,1),0),((1,0,F('-11/5')),0)]
    elo,ehi=map(cp.exact,fit['ramsey_mean_outer']['eta'])
    for time,key in [('3/4','m_short'),('3/2','m_long')]:
        A,B=ramsey(time)
        ml,mh=map(cp.exact,fit['ramsey_mean_outer'][key])
        lo=cp.dyadic(iv.ln(elo/mh)._mpi_[0])
        hi=cp.upper(iv.ln(ehi/ml))
        # Freeze rational mid coefficients, pay their whole error; |u|,|v|<=1.
        a,b=(F(round(float(v.mid)*10**10),10**10) for v in [A,B])
        pad=cp.upper(abs(A-cp.exact(a))+abs(B-cp.exact(b)))
        planes+=bracket((a,b,0),lo-pad,hi+pad)
    return planes


def kernel(A,B,P,v):
    return iv.exp(iv.mpc(-A*v[0]-B*v[1],P*v[2]))


def block_at(prior,rows,point):
    mat=prior.zero_matrix(4)
    for A,B,P,entries in rows:
        value=kernel(A,B,P,point)
        for i,j,k in entries:
            mat[i][j]+=k*value
    return mat


def assess(prior,times,nom,cells):
    vertices_all=sorted(set().union(*(set(cell) for cell in cells)))
    vi={v:tuple(cp.exact(x) for x in v) for v in vertices_all}
    point_bound={v:F(0) for v in vi}
    remainder=[F(0)]*len(cells)
    for stop in range(4):
        rows=list(cp.terms(prior,stop,list(map(cp.exact,times))))
        base=block_at(prior,rows,nom)
        for v,p in vi.items():
            mat=block_at(prior,rows,p)
            diff=[[s-t for s,t in zip(a,b)] for a,b in zip(mat,base)]
            point_bound[v]+=cp.upper(2*cp.frobenius(diff))
        for A,B,P,entries in rows:
            weight=cp.upper(iv.sqrt(sum(abs(k.real)**2+abs(k.imag)**2 for _,_,k in entries)))
            if not weight:
                continue
            re={v:(A*p[0]+B*p[1]) for v,p in vi.items()}
            im={v:P*p[2] for v,p in vi.items()}
            for j,cell in enumerate(cells):
                def width(values):
                    return max(cp.upper(values[v]) for v in cell)-min(cp.dyadic(values[v]._mpi_[0]) for v in cell)
                remainder[j]+=weight*(width(re)**2+width(im)**2)/4  # 2 * (VarRe + VarIm)/2
    budgets=[max(point_bound[v] for v in cell)+r for cell,r in zip(cells,remainder)]
    return dict(cells=len(cells),distinct_vertices=len(vi),
                max_vertex=cp.ceiling(max(point_bound.values())),
                max_interpolation=cp.ceiling(max(remainder)),
                joint_parameter_upper=cp.ceiling(max(budgets)))


def main():
    p=argparse.ArgumentParser()
    p.add_argument("fit",type=Path);p.add_argument("protocol",type=Path)
    p.add_argument("point_certificate",type=Path);p.add_argument("output",type=Path)
    p.add_argument("--repo",type=Path,required=True)
    args=p.parse_args()
    fit=json.loads(args.fit.read_text()); proto=json.loads(args.protocol.read_text())
    def digest(path):
        return hashlib.sha256(path.read_bytes()).hexdigest()
    freeze_path=args.fit.parent/"freeze.json"
    freeze=json.loads(freeze_path.read_text())
    raw=args.fit.parent/"calibration.npz"
    if (digest(freeze_path)!=fit["freeze_hash"] or digest(raw)!=fit["calibration_hash"]
            or digest(args.protocol)!=freeze["files"]["protocol.json"] or freeze["upstream_commit"]!=cp.REVISION):
        raise ValueError("calibration freeze binding mismatch")
    cert=json.loads(args.point_certificate.read_text())
    assert fit["witness_status"]=="VERIFIED_NONEMPTY" and cert["upstream"]==cp.REVISION
    assert all(fit["nominal"][k]==cert["input"]["nominal"][k] for k in ('u','v','w','eta'))
    nom=tuple(F(fit["nominal"][k]) for k in ('u','v','w'))
    planes=hull(fit)
    assert all(dot(a,nom)<=b for a,b in planes)
    extremes=vertices(planes)
    assert len(extremes)>=4
    # One split in each of u and w; tiny exact polytopes instead of an outer independent box.
    cells=[planes]
    for i in (0,2):
        mid=(min(v[i] for v in extremes)+max(v[i] for v in extremes))/2
        axis=tuple(int(j==i) for j in range(3))
        cells=[cell+[plane] for cell in cells for plane in [(axis,mid),(tuple(-x for x in axis),-mid)]]
    cells=[v for c in cells if (v:=vertices(c))]
    results=[]
    with tempfile.TemporaryDirectory() as tmp:
        prior=cp.load_prior(args.repo,tmp)
        for timing,point in zip(cp.TIMES,cert["results"]):
            assert tuple(point['timing'])==timing
            stats=assess(prior,timing,tuple(cp.exact(x) for x in nom),cells)
            full=F(stats['joint_parameter_upper'])+F(point['physical_repair']['certified_half_diamond_rational_upper'])
            readout=max(abs(F(fit['nominal']['eta'])-F(e)) for e in fit['simultaneous_outer']['eta'])/2
            event=4*F(str(proto['bias_event']))
            total=full+readout+event
            grid=F(4,2**proto["grid_bits"])
            results.append(dict(timing=timing,**stats,complete_upper=cp.ceiling(full),
                        terminal_visibility_upper=cp.ceiling(readout),eight_cell_bias_upper=str(event),
                        terminal_upper=cp.ceiling(total),sampler_tv_allowance=str(grid),terminal_digitized_upper=cp.ceiling(total+grid),target="1/20",verdict="CERTIFIED_SYNTHETIC" if total+grid<=F(1,20) else "NOT_CERTIFIED"))
    paths=[args.fit,args.protocol,args.point_certificate,freeze_path,raw]
    out=dict(dependencies={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
             physical_outer_vertices=[[str(x) for x in v] for v in extremes],results=results)
    args.output.write_text(json.dumps(out,indent=2)+"\n")
    for r in results: print(r['timing'],float(F(r['complete_upper'])),float(F(r['terminal_upper'])),r['verdict'])


if __name__=="__main__":
    main()
