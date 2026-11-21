"""Reproducible quadrature diagnostics, explicitly not rigorous interval certificates."""
from __future__ import annotations
import argparse,hashlib,json,os
os.environ.setdefault("OPENBLAS_NUM_THREADS","1")
import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.optimize import brentq
from pathlib import Path
HERE=Path(__file__).resolve().parent
def solve(order):
    q,wg=leggauss(order)
    def bump(x):
        x=np.asarray(x);out=np.zeros_like(x,dtype=float);inside=np.abs(x)<1
        out[inside]=np.exp(-2/(1-x[inside]**2));return out
    norm=float(wg@bump(q));n=21;tau=1/420
    centers=-1+(2*np.arange(n)+1)/n
    boundaries=-1+2*np.arange(1,n)/n
    def cdf(y):
        xx=(y[:,None]+1)*(q[None,:]+1)/2-1
        return (y+1)/2*(bump(xx)@wg)/norm
    cuts=np.unique(np.r_[-1,boundaries-tau,boundaries+tau,1])
    xs=[];weights=[]
    for a,b in zip(cuts[:-1],cuts[1:]):
        xs.append((a+b)/2+(b-a)*q/2);weights.append((b-a)*wg/2)
    x=np.concatenate(xs);wt=np.concatenate(weights)*bump(x)/norm
    m=np.zeros((len(x),n));dm=np.zeros_like(m)
    index=np.clip(((x+1)*n/2).astype(int),0,n-1)
    m[np.arange(len(x)),index]=1
    for j,bound in enumerate(boundaries):
        ix=np.flatnonzero(np.abs(x-bound)<tau);y=(x[ix]-bound)/tau
        theta=np.pi*cdf(y)/2;der=np.pi*bump(y)/(2*tau*norm)
        m[ix,:]=0;m[ix,j]=np.cos(theta);m[ix,j+1]=np.sin(theta)
        dm[ix,j]=-np.sin(theta)*der;dm[ix,j+1]=np.cos(theta)*der
    G=m.T@(wt[:,None]*m);b=m.T@wt
    eig,vec=np.linalg.eigh(G);be=(vec.T@b)**2
    distance=brentq(lambda lam:lam-1+np.sum(be/(lam+eig)),.8,1,xtol=1e-14)
    source_var=float(wt@(x*x))
    residual=float(np.sum(wt[:,None]*m*m*(x[:,None]-centers[None,:])**2))
    iz=float(np.sum(wt[:,None]*dm*dm))
    vz=float(np.sum(wt[:,None]*m*m*centers[None,:]**2))
    cross=float(np.sum(wt[:,None]*m*m*x[:,None]*centers[None,:]))
    entropy=float(-np.sum(eig[eig>0]*np.log(eig[eig>0])))
    return dict(order=order,normalization=float(wt.sum()),mu2=source_var,
        partition_max_absolute_defect=float(np.max(abs(np.sum(m*m,axis=1)-1))),
        gram_trace=float(np.trace(G)),gram_smallest_eigenvalue=float(eig[0]),
        bare_trace_distance=distance,support_leakage=1-float(b@b),
        residual_variance_over_B_squared=residual,residual_variance_over_source_variance=residual/source_var,
        pointer_variance_over_B_squared=vz,covariance_C_pointer_over_B_squared=cross,
        I_times_B_squared=iz,memory_entropy_nats=entropy,
        gram_matrix=G.tolist(),overlap_vector=b.tolist(),
        pointer_probabilities=np.diag(G).tolist())
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument("--write",action="store_true",required=True)
    ap.parse_args();lo=solve(128);hi=solve(256)
    fields=["mu2","bare_trace_distance","support_leakage","residual_variance_over_B_squared",
            "I_times_B_squared","memory_entropy_nats"]
    diffs={f:abs(hi[f]-lo[f]) for f in fields}
    assert hi["bare_trace_distance"]>.8 and 1/21168<hi["residual_variance_over_B_squared"]<1/400
    assert hi["I_times_B_squared"]>1000 and hi["partition_max_absolute_defect"]<1e-12
    result={"schema":"ueot-lapse-boundary-smooth-record-diagnostic/1",
      "status":"OBSERVED_NUMERICAL_DIAGNOSTIC","rigorous_interval_enclosure":False,
      "complete_normal_state_and_strict_bounds_proved_separately":"SMOOTH_PREPARATION.md",
      "method":"Gauss-Legendre 128 and 256, split at every transition endpoint; nested smooth-step integral at matching order",
      "source_sha256":{p.name:hashlib.sha256(p.read_bytes()).hexdigest()
        for p in [Path(__file__),HERE/"SMOOTH_PREPARATION.md"]},
      "coarse":{k:v for k,v in lo.items() if k not in {"gram_matrix","overlap_vector","pointer_probabilities"}},
      "fine":hi,"observed_absolute_differences":diffs,
      "old_scientific_modules_executed_or_imported":0,"ODE_integrations":0}
    out=HERE/"smooth_record_diagnostic.json"
    out.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    print(json.dumps({k:hi[k] for k in fields},indent=2))
    print("Observed 128/256 differences:",diffs)
if __name__=="__main__":main()
