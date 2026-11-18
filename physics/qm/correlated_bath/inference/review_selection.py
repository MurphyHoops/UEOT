"""Independent C review. Exact operational witnesses plus measured simultaneous bands."""
from fractions import Fraction as F
from sympy import Matrix, eye, diag, Rational as Q, I, kronecker_product as K
from shared import read,sha,write

def main():
    eye2=eye(2); x=Matrix([[0,1],[1,0]]);y=Matrix([[0,-I],[I,0]]);z=diag(1,-1)
    a,b=[(eye(4)+s*K(x,eye2)/2)/4 for s in (-1,1)]
    obs=[K(x,x),K(x,y),K(y,z),K(z,z)]
    for state in (a,b):
        assert state.trace()==1 and set(state.eigenvals())=={Q(1,8),Q(3,8)}
    assert all(((a-b)*o).trace()==0 for o in obs)
    assert ((b-a)*(eye(4)+K(x,eye2))/2).trace()==Q(1,2)
    ray=Matrix([3,4])/5
    pure=ray*ray.T
    replace=lambda state:state.trace()*pure
    assert replace(diag(1,0))==replace(diag(0,1)) and pure*pure==pure
    # Direct-sum detector projectors and separated central weights.
    pvis=diag(1,0,0); phid=diag(0,0,1)
    central=diag(1,1,0)
    assert (central*pvis).trace()==1 and (central*phid).trace()==0
    mid=(pvis+phid)/2
    assert (mid*central).trace()==Q(1,2) and mid*mid!=mid
    # Inspect actual held-out joint cell intervals. The pre-existing simultaneous cover
    # allows this derived post hoc witness without modifying a classification.
    res=read("holdout_results.json")
    out={}
    for fam in ("original","swap"):
        xx=res["settings"][fam+"_XX"]; zz=res["settings"][fam+"_ZZ"]
        xminus,xplus=xx["frequency_bands"][:2]; zminus=zz["frequency_bands"][0]
        slack=4*(F(".0005")+F(1,2**40))
        lower=F(xplus[0])-F(xminus[1])-2*F(zminus[1])-slack
        raw=F(xx["counts"][1]-xx["counts"][0]-2*zz["counts"][0],24000)
        assert lower>0
        out[fam]={"observed_contrast":str(raw),"lower_rational_after_systematics_and_grid":str(lower),
                  "lower_decimal_floor_12":format((lower*10**12).__floor__()/10**12,".12f")}
    write("selection_review_result.json",{"status":"PASS","reviewed":{
          name:sha("../selection/"+name) for name in ("SELECTION.md","check_selection.py","selection_run.txt")},
          "holdout_sha256":sha("holdout.npz"),"hidden_center_weights":[1,0],"mixed_midpoint_weight":"1/2",
          "undetected_finite_tester_example_added_XI_plus_gap":"1/2",
          "replacement_distinct_inputs_same_output":True,"separable_source_posthoc_witness":out})
    print(out)
if __name__=="__main__":
    main()
