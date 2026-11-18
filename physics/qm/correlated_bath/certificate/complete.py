"""Fixed-policy normalized Choi enclosure and all-input calibration transport."""
import argparse
import importlib.util
import itertools
import json
import subprocess
import sys
import tempfile
from fractions import Fraction
from pathlib import Path

import numpy as np
from mpmath import iv

REVISION = "44b6cd200cd01eccf15d4dc817311388d317a1af"
SOURCE = "physics/qm/persistent_bath/"
LABELS = ("f", "pf", "ppf", "ppp")
TIMES = (("2/3","3/4","1/2"), ("3/4","2/3","1/2"))
iv.dps = 60


def load_prior(repo, staging):
    # Exact source files, fresh process, no imports from other working-tree versions.
    for name in ("dynamics", "interval_certificate"):
        data = subprocess.check_output(["git", "-C", str(repo), "show", REVISION+":"+SOURCE+name+".py"])
        path = Path(staging, name+".py")
        path.write_bytes(data)
        spec = importlib.util.spec_from_file_location(name, path)
        module = importlib.util.module_from_spec(spec)
        sys.modules[name] = module
        spec.loader.exec_module(module)
    return module


def exact(x):
    f = Fraction(str(x))
    return iv.mpf(f.numerator)/f.denominator


def vector_histories(prior, stop, times):
    p, f = prior.zero_matrix(), prior.zero_matrix()
    p[0][0], p[1][1] = iv.sqrt(exact('7/8')), iv.sqrt(exact('3/4'))
    f[0][0], f[1][1] = iv.sqrt(exact('1/8')), exact('1/2')
    r = 1/iv.sqrt(2)
    ry = [[r,-r],[r,r]]
    rx = [[iv.sqrt(3)/2,iv.mpc(0,-exact('1/2'))],[iv.mpc(0,-exact('1/2')),iv.sqrt(3)/2]]
    slots = [prior.multiply(op,p) for op in (ry,rx,prior.eye())[:stop]]
    if stop < 3:
        slots.append(f)
    T = sum(times[:len(slots)])
    frames = [iv.exp(iv.mpc(0,om*T)) for om in [exact(1),exact('3/2')]]
    rows = []
    for word in itertools.product((0,1),repeat=len(slots)):
        op = prior.eye()
        for bit,slot in zip(word,slots):
            proj = prior.zero_matrix()
            proj[bit][bit] = 1
            op = prior.multiply(prior.multiply(slot,proj),op)
        beta, phase = prior.interval_history(exact(1),times,[1-2*x for x in word])
        rows.append(([x*r for row in op for x in row], [f*b for f,b in zip(frames,beta)],phase))
    return rows


def terms(prior, stop, times):
    rows = vector_histories(prior,stop,times)
    for a,x,px in rows:
        for b,y,py in rows:
            z = [m-n for m,n in zip(x,y)]
            A = sum(v.real**2+v.imag**2 for v in z)/2
            B = 2*(prior.conjugate(z[0])*z[1]).real
            P = px-py+sum((prior.conjugate(n)*m).imag for m,n in zip(x,y))
            entries = [(i,j,left*prior.conjugate(right)) for i,left in enumerate(a)
                       for j,right in enumerate(b) if left != 0 and right != 0]
            yield A,B,P,entries


def frobenius(mat):
    return iv.sqrt(sum(abs(v.real)**2+abs(v.imag)**2 for row in mat for v in row))


def dyadic(raw):
    sign,man,exp,_ = raw
    return (-1)**sign*Fraction(man)*Fraction(2)**exp


def upper(interval):
    return dyadic(interval._mpi_[1])


def ceiling(x, decimals=12):
    scale=10**decimals
    return str(Fraction(-(-x*scale//1),scale))


def certify(prior,timing,nom,box):
    fields = ("u","v","w")
    point = [exact(nom[k]) for k in fields]
    domain = [iv.mpf([exact(box[k][0]).a,exact(box[k][1]).b]) for k in fields]
    radius = [max(abs(Fraction(str(nom[k]))-Fraction(str(s))) for s in box[k]) for k in fields]
    derivatives = [iv.mpf(0) for _ in fields]
    numerical = iv.mpf(0)
    floating = {}
    for stop,label in enumerate(LABELS):
        block = prior.zero_matrix(4)
        jac = [prior.zero_matrix(4) for _ in fields]
        for A,B,P,entries in terms(prior,stop,list(map(exact,timing))):
            a = iv.exp(iv.mpc(-A*point[0]-B*point[1],P*point[2]))
            b = iv.exp(iv.mpc(-A*domain[0]-B*domain[1],P*domain[2]))
            for i,j,z in entries:
                block[i][j] += a*z
                for mat,coef in zip(jac,(-A,-B,iv.mpc(0,P))):
                    mat[i][j] += coef*b*z
        floating[label] = np.array([[complex(float(v.real.mid),float(v.imag.mid)) for v in row] for row in block])
        delta = [[v-iv.mpc(float(floating[label][i,j].real),float(floating[label][i,j].imag))
                  for j,v in enumerate(row)] for i,row in enumerate(block)]
        numerical += 2*frobenius(delta)
        derivatives = [d+2*frobenius(mat) for d,mat in zip(derivatives,jac)]
    assert upper(numerical) < Fraction(1,10**12)
    repaired = prior.rational_physical_repair(floating)
    param = sum(upper(d)*r for d,r in zip(derivatives,radius))
    full = param + Fraction(repaired['certified_half_diamond_rational_upper'])
    eta_rad = max(abs(Fraction(str(nom["eta"]))-Fraction(str(v))) for v in box["eta"])
    return dict(timing=timing,parameter_order=fields,lipschitz_upper=[ceiling(upper(d)) for d in derivatives],
                parameter_half_diamond_upper=ceiling(param),nominal_roundoff_upper=ceiling(upper(numerical),24),
                complete_half_diamond_upper=ceiling(full),fixed_binary_readout_upper=ceiling(full+eta_rad/2),
                physical_repair=repaired)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("input",type=Path)
    parser.add_argument("output",type=Path)
    parser.add_argument("--repo",type=Path,required=True)
    args=parser.parse_args()
    x=json.loads(args.input.read_text())
    nom,box=x["nominal"],x["box"]
    assert all(Fraction(str(lo))<=Fraction(str(nom[k]))<=Fraction(str(hi)) for k,(lo,hi) in box.items())
    u,v,w=[Fraction(str(nom[k])) for k in ('u','v','w')]
    assert Fraction(1,25)<=w<=Fraction(4,25) and w+2*abs(v)<=u<=Fraction(11,5)*w
    assert Fraction(9,10)<=Fraction(str(nom['eta']))<=1
    with tempfile.TemporaryDirectory() as tmp:
        prior=load_prior(args.repo,tmp)
        results=[certify(prior,t,nom,box) for t in TIMES]
    args.output.write_text(json.dumps(dict(upstream=REVISION,input=x,results=results),indent=2)+"\n")


if __name__ == "__main__":
    main()
