"""Exact rational Bell-input terminal probabilities from the repaired Choi map."""
from __future__ import annotations

import json
from fractions import Fraction as F
from pathlib import Path


def add(a,b): return (a[0]+b[0],a[1]+b[1])
def mul(a,b): return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])


def pauli(name):
    zero=(F(0),F(0)); one=(F(1),F(0)); minus=(F(-1),F(0))
    matrices={'I':[[one,zero],[zero,one]],'X':[[zero,one],[one,zero]],
              'Y':[[zero,(F(0),F(-1))],[(F(0),F(1)),zero]],
              'Z':[[one,zero],[zero,minus]]}
    a,b=matrices[name[0]],matrices[name[1]]
    return [[mul(a[i//2][j//2],b[i%2][j%2]) for j in range(4)] for i in range(4)]


def load_repaired_choi(path):
    certificate=json.loads(Path(path).read_text())
    raw=certificate['physical_repair']['choi_blocks_exact_fraction_pairs']
    return {label:[[(F(z[0]),F(z[1])) for z in row] for row in block]
            for label,block in raw.items()}


def event_probabilities(path,eta,name):
    """Eight exact fractions: f-/f+/pf-/pf+/ppf-/ppf+/ppp-/ppp+.

    The certificate's normalized Choi is its output for a normalized Bell input.
    The visibility must be the same declared symmetric detector law.
    """
    eta=F(eta)
    if not 0 <= eta <= 1: raise ValueError('visibility must be in [0,1]')
    blocks=load_repaired_choi(path); obs=pauli(name); result=[]
    for label in ('f','pf','ppf','ppp'):
        block=blocks[label]
        weight=sum(block[i][i][0] for i in range(4))
        mean=(F(0),F(0))
        for i in range(4):
            for j in range(4): mean=add(mean,mul(obs[i][j],block[j][i]))
        assert mean[1]==0
        result.extend(((weight-eta*mean[0])/2,(weight+eta*mean[0])/2))
    assert sum(result)==1 and min(result)>=0
    return result


if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser()
    parser.add_argument('certificate',type=Path)
    parser.add_argument('--eta',default='0.959480000000')
    args=parser.parse_args()
    print(json.dumps({name:[str(x) for x in event_probabilities(args.certificate,args.eta,name)]
                      for name in ('XX','XY','YZ','ZZ')},indent=2))
