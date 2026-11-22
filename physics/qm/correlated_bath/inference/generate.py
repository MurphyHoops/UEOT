"""Producer only. Float upstream Gaussian histories; digitized CDFs verified independently after scoring."""
import sys
import time
from fractions import Fraction
import numpy as np
from shared import ROOT, historic, read, settings, sha, verify_freeze, write

def main(phase):
    verify_freeze()
    if phase not in ("calibration","holdout"):
        raise ValueError(phase)
    if sha("truth.json")!=read("freeze.json")["files"]["truth.json"]:
        raise ValueError("truth changed")
    if phase=="holdout" and read("predictions.json")["calibration_hash"]!=sha("calibration.npz"):
        raise ValueError("missing calibration binding")
    start=time.perf_counter()
    cfg=read("protocol.json")
    lam,n,c,eta,offset,gain,violation=[float(Fraction(read("truth.json")[k])) for k in
        ("lambda","n","c","eta","break_offset","Y_relative_gain","challenge_eta")]
    dyn=historic("dynamics")
    cov=np.block([[(n+.5)*np.eye(2),c*np.eye(2)],[c*np.eye(2),(n+.5)*np.eye(2)]])
    def factor(times,left,right):
        b,p=dyn.bath_path(lam,times,left)
        bp,pp=dyn.bath_path(lam,times,right)
        return dyn.gaussian_influence(b,p,bp,pp,sum(times),covariance=cov)
    def probs(key):
        if key.startswith("R"):
            t={"R0":0,"Rshort":.75,"Rlong":1.5}[key]
            mean=eta*factor([t],[1],[-1]).real
        elif "_" not in key:
            s=1 if key.endswith("p") else -1
            t=[1 if key.startswith("H") else 2/3,.75]
            z=eta*np.exp(1j*offset)*factor(t,[s,1],[s,-1])
            mean=z.real if key.startswith("X") else -gain*z.imag
        else:
            family,obs=key.rsplit("_",1)
            from source_snapshot import event_probabilities
            timing="changed_intervals" if family=="swap" else "deployment"
            if family!="readout_challenge":
                return event_probabilities(lam,n,c,eta,obs,timing)
            ideal=event_probabilities(lam,n,c,1,obs,timing).reshape(4,2)
            return (((1+violation)*ideal+(1-violation)*ideal[:,::-1])/2).ravel()
        return np.array([(1-mean)/2,(1+mean)/2])

    plan=settings(phase)
    seed=cfg["cal_seed" if phase=="calibration" else "hold_seed"]
    schedule_seed,draw_seed=np.random.SeedSequence(seed).spawn(2)
    order=np.repeat(np.arange(len(plan),dtype=np.uint8),[count//cfg["block"] for count in plan.values()])
    np.random.Generator(np.random.PCG64(schedule_seed)).shuffle(order)
    Q=2**cfg["grid_bits"]
    cut=[np.rint(np.cumsum(probs(key))[:-1]*Q).astype(np.int64) for key in plan]
    rng=np.random.Generator(np.random.PCG64(draw_seed))
    rows=np.empty((len(order),cfg["block"]),np.uint8)
    for i,j in enumerate(order):
        rows[i]=np.searchsorted(cut[j],rng.integers(Q,size=cfg["block"]),side="right")
    np.savez_compressed(ROOT/(phase+".npz"),block_setting=order,ordered_codes=rows)
    write(phase+"_source_cdf.json",{k:a.tolist() for k,a in zip(plan,cut)})
    write(phase+"_receipt.json",{"raw_sha256":sha(phase+".npz"),"freeze_sha256":sha("freeze.json"),
        "prediction_sha256":sha("predictions.json") if phase=="holdout" else None,
        "cdf_sha256":sha(phase+"_source_cdf.json"),
        "seed":seed,"shots":int(rows.size),"bytes":(ROOT/(phase+".npz")).stat().st_size,
        "wall_seconds":time.perf_counter()-start,"numpy":np.__version__})
    print(phase,rows.size,sha(phase+".npz"))

if __name__=="__main__":
    main(sys.argv[1])
