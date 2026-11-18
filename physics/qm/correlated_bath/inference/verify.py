"""Post-score independent interval CDF audit, raw replay, inverse checks and counted resources."""
import hashlib
import os
import sys
import time
import resource
from fractions import Fraction as Fr
import numpy as np
from shared import ROOT,NAMES,blob,read,write,sha,settings,verify_freeze
from interval_model import (q,iv,box,bounds,endpoints,row,response,coordinates,calmean,
                           bell,DET,A1,A2,B1,B2,radius)
from source_snapshot import event_probabilities

def main():
    start=time.perf_counter()
    cpu=time.process_time()
    verify_freeze()
    freeze=read("freeze.json")
    assert sha("truth.json")==freeze["files"]["truth.json"]
    for name in NAMES:
        assert hashlib.sha256(blob(name)).hexdigest()==freeze["upstream_git_blob_sha256"][name]
    fit=read("calibration_fit.json")
    preds=read("predictions.json")
    result=read("holdout_results.json")
    cfg=read("protocol.json")
    assert result["predictions_sha256"]==sha("predictions.json")
    assert result["holdout_sha256"]==sha("holdout.npz")
    truth={k:Fr(x) for k,x in read("truth.json").items()}
    l,n,c,e,d=[q(truth[k]) for k in ("lambda","n","c","eta","break_offset")]
    w=l*l
    atten=lambda a,b:w*((2*n+1)*a+c*b)
    full={}
    for fam in cfg["holdout_families"]:
        eta=q(truth["challenge_eta"]) if fam=="readout_challenge" else e
        ts=cfg["swap" if fam=="swap" else "original"]
        full.update({fam+"_"+o:arr for o,arr in bell(ts,eta,w,atten).items()})
    Q=2**cfg["grid_bits"]
    cdf_counts=0; max_grid=Fr(0); total_time=Fr(0); slots=0; post_pass=[0,0]; breaks=0; bellpreps=0
    for phase in ("calibration","holdout"):
        receipt=read(phase+"_receipt.json")
        assert receipt["freeze_sha256"]==sha("freeze.json") and receipt["cdf_sha256"]==sha(phase+"_source_cdf.json")
        thresholds=read(phase+"_source_cdf.json"); plan=settings(phase)
        sched,draw=np.random.SeedSequence(receipt["seed"]).spawn(2)
        keys=list(plan)
        order=np.repeat(np.arange(len(plan),dtype=np.uint8),[v//cfg["block"] for v in plan.values()])
        np.random.Generator(np.random.PCG64(sched)).shuffle(order)
        rng=np.random.Generator(np.random.PCG64(draw))
        with np.load(ROOT/(phase+".npz")) as raw:
            assert np.array_equal(raw["block_setting"],order)
            draws=raw["ordered_codes"]
        for i,idx in enumerate(order):
            vals=rng.integers(Q,size=cfg["block"])
            assert np.array_equal(np.searchsorted(thresholds[keys[idx]],vals,side="right"),draws[i])
        for key,count in plan.items():
            if key in full:
                probabilities=full[key]
                ts=list(map(Fr,cfg["swap" if key.startswith("swap_") else "original"]))
                observed=result["settings"][key]["counts"]
                byrecord=[a+b for a,b in zip(observed[::2],observed[1::2])]
                reached=[count,sum(byrecord[1:]),sum(byrecord[2:])]
                total_time+=sum(x*y for x,y in zip(reached,ts))
                slots+=sum(reached); post_pass=[x+y for x,y in zip(post_pass,reached[1:])]; bellpreps+=count
            else:
                m=calmean(key,e,w,d,atten)
                if key.startswith(("H","Y")):
                    m*=q(truth["Y_relative_gain"])
                probabilities=[(1-m)/2,(1+m)/2]
                if key.startswith("R"):
                    t={"R0":0,"Rshort":Fr(3,4),"Rlong":Fr(3,2)}[key]
                    slots+=count*int(t>0)
                    total_time+=count*t
                else:
                    breaks+=count;slots+=2*count
                    total_time+=(Fr(1) if key.startswith("H") else Fr(2,3))*count+Fr(3,4)*count
            cdf=q(0)
            for x,code in zip(probabilities[:-1],thresholds[key]):
                cdf+=x
                lo,hi=endpoints(cdf*Q-code)
                max_grid=max(max_grid,abs(lo),abs(hi)); cdf_counts+=1
                assert -Fr(1,2)<=lo<=hi<=Fr(1,2), (key,code,float(lo),float(hi))
    # Same information, same tests, standard joint Gaussian process formula.
    point=fit["nominal"]
    maxdiff=0
    for fam in ("original","swap"):
        for obs in cfg["bell_tests"]:
            arr=event_probabilities(*[float(point[k]) for k in ("lambda","n","c","eta")],obs,
                                      "changed_intervals" if fam=="swap" else "deployment")
            for x,(lo,hi) in zip(arr,preds["nominal_ideal_probability"][fam+"_"+obs]):
                maxdiff=max(maxdiff,abs(x-(float(lo)+float(hi))/2))
                assert float(lo)-1e-14<=x<=float(hi)+1e-14
    p1=(Fr(3,10),Fr(1,2),Fr(1,4))
    p2=(Fr(1,3),Fr(31,100),Fr(81,400))
    for l0,n0,c0 in (p1,p2):
        assert l0*l0*(2*n0+1)==Fr(9,50) and l0*l0*c0==Fr(9,400)
    pairatten=lambda a,b:q("9/50")*a+q("9/400")*b
    # A conventional deployed event actually varies along the exact Ramsey equivalence class.
    eqw=box(Fr(9,110),Fr(27,200))
    bypair={}
    for fam in ("original","swap"):
        values=[bell(cfg[fam],q(".96"),ww,pairatten)["YZ"][6] for ww in
                (q(p1[0]**2),q(p2[0]**2),eqw)]
        bypair[fam]={"ppp_YZ_minus_at_P1":bounds(values[0]),"at_P2":bounds(values[1]),
                     "difference":bounds(values[0]-values[1]),"entire_fiber_outer":bounds(values[2])}
        assert endpoints(values[0]-values[1])[0]>0
    a1,a2=row("3/4")[0],row("3/2")[0]
    ab=row("3/4","2/3")[0]
    m1,m2,r=[q(".9")*iv.exp(-q(".544")*A) for A in (a1,a2,ab)]
    coeffs=[]
    for args in ((q(1),q(0)),(q(0),q(1))):
        h1,h2=coordinates(*args)
        coeffs.append(abs(h1+h2)/q(".9")+abs(h1)/m1+abs(h2)/m2)
    lu,lv=coeffs
    lw=iv.pi*iv.sqrt(2)/(2*r*response("2/3"))
    L={"u":lu,"v":lv,"w":lw,"lambda":lw/q(".4"),
       "n":(lu+q("2.2")*lw)/q(".08"),"c":(lv+q(".6")*lw)/q(".04"),"eta":q(1)}
    num_shots=sum(settings("calibration").values())+sum(settings("holdout").values())
    for name,expected in (("original","NOT_REJECTED"),("swap","NOT_REJECTED"),
                          ("readout_challenge","REJECTED"),("independent_break","NOT_REJECTED")):
        assert result["families"][name]==expected
    assert result["aligned_phase"]["two_named_alternatives_choice"]=="first"
    assert result["aligned_phase"]["reset_or_zero_response_rejected_at_1_percent"]
    for k,actual in {"u":Fr(9,50),"v":Fr(9,400),"w":Fr(9,100),"eta":truth["eta"]}.items():
        lo,hi=map(Fr,read("joint_domain.json")["simultaneous_outer"][k]); assert lo<=actual<=hi
    for row0 in read("joint_domain.json")["facets_au_bv_cw_dlogeta_le_rhs"]:
        a,b,c,d,rhs=map(Fr,row0)
        assert (q(a*Fr(9,50)+b*Fr(9,400)+c*Fr(9,100))+q(d)*iv.ln(e)).b<=q(rhs).a
    out={"status":"PASS","upstream_blobs_sha256":freeze["upstream_git_blob_sha256"],
         "rounded_CDF_thresholds_checked":cdf_counts,"max_CDF_error_in_grid_units":bounds(q(max_grid)),
         "all_raw_draws_regenerated":num_shots,"standard_nominal_64_cells_vs_interval_midpoint_max":maxdiff,
         "equal_Ramsey_two_point_deployment_witness":bypair,"whole_domain_Lipschitz_upper":{k:bounds(x) for k,x in L.items()},
         "ramsey_minima_eta_short_long_break":[bounds(x) for x in (q(".9"),m1,m2,r)],
         "source_snapshot_sha256":sha("source_snapshot.py"),
         "live_dynamics_api_identical_at_audit":sha("../dynamics/correlated_cq.py")==sha("source_snapshot.py") if (ROOT.parent/"dynamics/correlated_cq.py").exists() else None,
         "logical_resources":{"started_shots":num_shots,"fresh_bath_preparations_and_end_resets_each":num_shots,
         "heldout_Bell_preparations":bellpreps,"eigenstate_preparations":breaks,"causal_repreparations":breaks,
         "nonzero_source_intervals":slots,"dimensionless_total_interaction_time":str(total_time),
         "Ry_postpass":post_pass[0],"Rx_postpass":post_pass[1],"terminal_measurements":num_shots,
         "separate_hardware_reference_calibrations":0,"physical_device_calls":0},
         "audit_resources":{"wall_seconds":time.perf_counter()-start,"cpu_seconds":time.process_time()-cpu,
         "peak_RSS_bytes_on_macOS":resource.getrusage(resource.RUSAGE_SELF).ru_maxrss if sys.platform=="darwin" else None}}
    write("verification.json",out)
    print(out["status"],cdf_counts,"CDF cuts,",num_shots,"raw outcomes;",out["logical_resources"])
if __name__=="__main__":
    main()
