"""Calibration-only rational polytope enclosing the same frozen seven-setting confidence set."""
from fractions import Fraction as F
from itertools import combinations
from interval_model import q,iv,row,box,bounds
from shared import read,write,sha

def vertex(rows):
    m=[list(r) for r in rows]
    for i in range(4):
        j=next((j for j in range(i,4) if m[j][i]),None)
        if j is None:
            return None
        m[i],m[j]=m[j],m[i]
        m[i]=[x/m[i][i] for x in m[i]]
        for j in range(4):
            if j!=i:
                m[j]=[a-m[j][i]*b for a,b in zip(m[j],m[i])]
    return tuple(r[-1] for r in m)

def main():
    fit=read("calibration_fit.json")
    raw=fit["seven_mean_bands"]
    bands={k:box(*v) for k,v in raw.items()}
    mag={s:iv.sqrt(bands["X"+s]**2+bands["Y"+s]**2) for s in "pm"}
    limits=fit["simultaneous_outer"]
    lo,hi=map(F,limits["w"])
    H=[]
    def add(*r):
        H.append(tuple(map(F,r)))
    add(0,0,1,0,hi); add(0,0,-1,0,-lo)
    add(-1,0,1,0,0); add(1,0,"-2.2",0,0)
    add(-1,2,1,0,0); add(-1,-2,1,0,0)
    for moment,(A,B) in [(bands["R0"],row("0")),(bands["Rshort"],row("3/4")),
                  (bands["Rlong"],row("3/2"))]+[(m,row("3/4","2/3")) for m in mag.values()]:
        aa=list(map(F,bounds(A)));bb=list(map(F,bounds(B)))
        # Center each interval exactly and pay its radius using global |u|,|v|.
        a,b=sum(aa)/2,sum(bb)/2
        err=(aa[1]-aa[0])*F(".352")/2+(bb[1]-bb[0])*F(".096")/2
        low,high=map(F,bounds(iv.ln(moment)))
        add(-a,-b,0,1,high+err);add(a,b,0,-1,-low+err)
    vertices=set()
    for rows in combinations(H,4):
        v=vertex(rows)
        if v and all(sum(a*b for a,b in zip(r,v))<=r[-1] for r in H):
            vertices.add(v)
    assert vertices
    names=("u","v","w","log_eta")
    dom={k:bounds(box(min(v[i] for v in vertices),max(v[i] for v in vertices)))
         for i,k in enumerate(names)}
    dom["eta"]=bounds(iv.exp(box(*dom["log_eta"])))
    for name,f in (("n",lambda u,v,w,h:(u/w-1)/2),("c",lambda u,v,w,h:v/w)):
        vals=[f(*v) for v in vertices]
        dom[name]=bounds(box(min(vals),max(vals)))
    point=fit["nominal"]
    pt=[q(point[k]) for k in names[:3]]+[iv.ln(q(point["eta"]))]
    # Inequalities can be tight exactly at n=.6; evaluate physical faces rationally.
    for r in H:
        if r[3]==0:
            assert sum(a*F(point[k]) for a,k in zip(r,names[:3]))<=r[4]
        else:
            assert sum(q(a)*b for a,b in zip(r,pt)).b<=q(r[4]).a
    write("joint_domain.json",{"fit_sha256":sha("calibration_fit.json"),"nominal":point,
        "nominal_decimal_enclosures":fit["nominal_decimal_enclosures"],"confidence_coverage_lower":"0.99",
        "order":names,"simultaneous_outer":dom,"facets_au_bv_cw_dlogeta_le_rhs":[list(map(str,r)) for r in H],
        "vertices_exact":[list(map(str,v)) for v in sorted(vertices)],
        "status":"CALIBRATION_ONLY_IMPLIED_OUTER_POLYTOPE; frozen holdout classification uses predictions.json"})
    print(len(vertices),"vertices",dom)
if __name__=="__main__":
    main()
