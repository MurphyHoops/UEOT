"""Reconstruct Overstreet et al. Fig. 2C from the author's immutable deposit."""
from collections import defaultdict
import csv
import hashlib
import json
import math
from pathlib import Path

DATA=Path(__file__).with_name("Fig2.csv")
SHA="6bcd79fa411d837349097e59a1abed9ab309d0dd97db9541f74fa966e469e726"


def main():
    payload=DATA.read_bytes()
    assert len(payload)==1146 and hashlib.sha256(payload).hexdigest()==SHA
    assert hashlib.md5(payload).hexdigest()=="1a2124c61db8b44110c2c8bd7fa88342"
    rows=csv.reader(payload.decode("utf-8-sig").splitlines())
    columns=[v.strip() for v in next(rows)]
    assert columns[:2]==["Rx (m)","Run"] and len(columns)==8
    assert all("scaled by 52/4" in v for v in columns[4:])
    groups=defaultdict(list)
    seen=set()
    for rx,run,*values in rows:
        key=float(rx),int(run)
        assert key not in seen
        seen.add(key)
        large,sl,upper,su,lower,sd=map(float,values)
        assert min(sl,su,sd)>0
        val=large-(upper+lower)/2
        variance=sl**2+(su**2+sd**2)/4
        groups[float(rx)].append((val,variance,sl+(su+sd)/2))
    output={}
    for rx,rows in groups.items():
        weights=[1/v for _,v,_ in rows]
        total=sum(weights)
        mean=sum(w*r[0] for w,r in zip(weights,rows))/total
        sd=1/math.sqrt(total)
        # For these same weights, triangle inequality in L² over arbitrary valid correlations.
        covariance_free_sd=sum(w*r[2] for w,r in zip(weights,rows))/total
        output[str(rx)]=dict(runs=len(rows),beyond_midpoint_mrad=mean*1000,
                            propagated_sigma_mrad=sd*1000,
                            max_sigma_from_given_marginals_mrad=covariance_free_sd*1000)
    assert len(seen)==9 and len(groups)==6
    for rx,comparison in [(0.043118634,(-125,24)), (0.089483193,(-182,28))]:
        row=output[str(rx)]
        assert (round(row['beyond_midpoint_mrad']),round(row['propagated_sigma_mrad']))==comparison
    # One descriptive contrast across the two heights bracketing the reported midpoint zero.
    positions=[.043118634,.089483193]
    weighted=[(row,1/(2*len(groups[rx]))) for rx in positions for row in groups[rx]]
    contrast=1000*sum(w*val for (val,_,_),w in weighted)
    worst=1000*sum(w*cap for (_,_,cap),w in weighted)
    gaussian=[contrast-1.96*worst,contrast+1.96*worst]
    chebyshev=[contrast-math.sqrt(20)*worst,contrast+math.sqrt(20)*worst]
    assert gaussian[1]<0<chebyshev[1]
    joint=dict(equal_height_and_run_mean_mrad=contrast,worst_sd_mrad=worst,
               gaussian_95_if_covariance_unknown=gaussian,chebyshev_95=chebyshev)
    return dict(cross_height=joint,source_doi="10.7910/DVN/O9IS7Y",version="2.0",file_id=5257879,sha256=SHA,
                groups=output)


if __name__=="__main__":
    print(json.dumps(main(),indent=2))
