"""Estimator/predictor. Only the protocol, frozen programs and calibration shots enter."""
import numpy as np
from scipy.optimize import least_squares
from interval_model import (Fr,iv,q,DET,row,response,box,bounds,endpoints,intersect,
                           expand,attenuation,calmean,bell,altrule,radius)
from shared import read,write,sha,verify_freeze,unpack,settings

def main():
    verify_freeze()
    cfg=read("protocol.json")
    receipt=read("calibration_receipt.json")
    assert receipt["raw_sha256"]==sha("calibration.npz") and receipt["freeze_sha256"]==sha("freeze.json")
    counts=unpack("calibration")
    nset=len(counts)
    mean={k:q(2*x[1])/sum(x)-1 for k,x in counts.items()}
    grid=q(1)/2**cfg["grid_bits"]
    bands={k:expand(m,2*radius(sum(counts[k]),nset,cfg["alpha_cal"])+q(cfg["bias_mean"])+2*grid)
           for k,m in mean.items()}
    eta=intersect(bands["R0"],.9,1)
    # For the two positive Ramsey means, physicality supplies a global lower floor.
    ram=[eta]+[intersect(bands[k],endpoints(q(".9")*iv.exp(-q(".544")*row(t)[0]))[0],1)
               for k,t in (("Rshort","3/4"),("Rlong","3/2"))]
    logs=list(map(iv.ln,ram))
    atten=lambda A,B:attenuation(A,B,logs)
    u=intersect(atten(q(1),q(0)),.04,.352)
    v=intersect(atten(q(0),q(1)),-.096,.096)
    if all(endpoints(bands["X"+s])[0]>0 for s in "pm"):
        ap,am=[iv.atan2(-bands["Y"+s],bands["X"+s]) for s in "pm"]
        w=intersect((ap-am)/(2*response("2/3")),.04,.16)
        delta=intersect((ap+am)/2,-.02,.02)
    else:
        w=box(".04",".16")
        delta=box("-.02",".02")
    # Floating optimization only proposes the subsequently interval-checked witness.
    names=list(mean)
    A=np.array([[float(x.mid) for x in row(t)] for t in ("0","3/4","3/2")]+
               [[float(x.mid) for x in row("3/4","2/3")]]*4)
    f=float(response("2/3").mid)
    targets=np.array([float(mean[k].mid) for k in names])
    weights=np.sqrt([sum(counts[k]) for k in names])
    def residual(theta):
        l,n,frac,e,d=theta
        u,v=l*l*(2*n+1),l*l*n*frac
        phi=d+np.array([1,-1,1,-1])*l*l*f
        pred=e*np.exp(-A@np.array([u,v]))*np.r_[np.ones(3),np.cos(phi[:2]),-np.sin(phi[2:])]
        return weights*(pred-targets)
    fit=least_squares(residual,[.28,.3,0,.95,0],bounds=([.2,0,-1,.9,-.02],[.4,.6,1,1,.02]))
    if not fit.success:
        raise ValueError("nominal optimizer failed")
    l,n,frac,e,d=fit.x
    point={k:format(x,".12f") for k,x in zip(("lambda","n","c","eta","delta"),(l,n,n*frac,e,d))}
    l,n,c,e,d=[Fr(x) for x in point.values()]
    assert Fr("0.2")<=l<=Fr("0.4") and abs(c)<=n<=Fr(".6") and Fr(".9")<=e<=1 and abs(d)<=Fr(".02")
    p={"u":l*l*(2*n+1),"v":l*l*c,"w":l*l}
    point.update({k:str(x) for k,x in p.items()})
    pointatten=lambda a,b:a*q(p["u"])+b*q(p["v"])
    for k in mean:
        # Sufficient witness: stated ideal expectations inside the allowed likelihood-free bands.
        lo,hi=endpoints(calmean(k,q(e),q(p["w"]),q(d),pointatten))
        bl,bh=endpoints(bands[k])
        assert bl<=lo<=hi<=bh, "no verified feasible witness"
    domain={"u":u,"v":v,"w":w,"eta":eta,"delta":delta,"lambda":iv.sqrt(w),
            "n":intersect((u/w-1)/2,0,.6),"c":intersect(v/w,-.6,.6)}
    cal={"calibration_hash":sha("calibration.npz"),"freeze_hash":sha("freeze.json"),
         "confidence_coverage_lower":"0.99","nominal":point,"nominal_decimal_enclosures":{k:bounds(q(x)) for k,x in p.items()},
         "simultaneous_outer":{k:bounds(val) for k,val in domain.items()},
         "ramsey_mean_outer":dict(zip(("eta","m_short","m_long"),map(bounds,ram))),
         "seven_mean_bands":{k:bounds(val) for k,val in bands.items()},"counts":counts,
         "ramsey_matrix_det":bounds(DET),"response_F":bounds(response("2/3")),"witness_status":"VERIFIED_NONEMPTY"}
    write("calibration_fit.json",cal)
    pred={}; nominal={}
    for key in cfg["holdout_phase"]:
        pred[key]=[(1+s*calmean(key,eta,w,delta,atten))/2 for s in (-1,1)]
        nominal[key]=[(1+s*calmean(key,q(e),q(p["w"]),q(d),pointatten))/2 for s in (-1,1)]
    for family in cfg["holdout_families"]:
        times=cfg["swap" if family=="swap" else "original"]
        for dic,result in ((pred,bell(times,eta,w,atten)),(nominal,bell(times,q(e),q(p["w"]),pointatten))):
            dic.update({family+"_"+obs:pp for obs,pp in result.items()})
    def encode(dic,error):
        return {k:[bounds(intersect(expand(x,error),0,1)) for x in arr] for k,arr in dic.items()}
    write("predictions.json",{"calibration_hash":sha("calibration.npz"),"fit_hash":sha("calibration_fit.json"),
        "freeze_hash":sha("freeze.json"),"outer_event_probability":encode(pred,q(cfg["bias_event"])+grid),
        "nominal_ideal_probability":encode(nominal,q(0)),
        "power_calibration":altrule("2/3",320000),"power_heldout":altrule("1",120000)})
    print(cal["nominal"],cal["simultaneous_outer"])

if __name__=="__main__":
    main()
