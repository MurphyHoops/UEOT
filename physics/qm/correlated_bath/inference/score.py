"""Frozen classifier; reads measured counts and pre-sampling predictions."""
from fractions import Fraction as Fr
from shared import read,write,sha,settings,unpack,verify_freeze
from interval_model import q,iv,bounds,endpoints,expand,intersect,radius

def main():
    verify_freeze()
    cfg=read("protocol.json")
    predictions=read("predictions.json")
    receipt=read("holdout_receipt.json")
    assert receipt["prediction_sha256"]==sha("predictions.json") and receipt["raw_sha256"]==sha("holdout.npz")
    assert predictions["calibration_hash"]==sha("calibration.npz") and predictions["fit_hash"]==sha("calibration_fit.json")
    counts=unpack("holdout")
    cells=sum(map(len,counts.values()))
    decisions={f:[] for f in ["independent_break"]+cfg["holdout_families"]}
    rows={}
    for key,arr in counts.items():
        pred=predictions["outer_event_probability"][key]
        n=sum(arr)
        r=radius(n,cells,cfg["alpha_hold"])
        measured=[bounds(intersect(expand(q(x)/n,r),0,1)) for x in arr]
        failures=[i for i,((a,b),(c,d)) in enumerate(zip(pred,measured))
                  if Fr(b)<Fr(c) or Fr(d)<Fr(a)]
        fam=key.rsplit("_",1)[0] if "_" in key else "independent_break"
        decisions[fam].extend([key+"/"+str(i) for i in failures])
        rows[key]={"counts":arr,"frequency_bands":measured,"disjoint":failures}
    signed=counts["Hp"][0]+counts["Hm"][1]
    observed=Fr(signed,sum(counts["Hp"])+sum(counts["Hm"]))
    threshold=list(map(Fr,predictions["power_heldout"]["threshold"]))
    verdict="first" if observed<threshold[0] else ("second" if observed>threshold[1] else "boundary")
    # Reset/zero-response source with common phase has equal signed-Y means.
    # Sign alignment makes its pooled p exactly 1/2 before bounded residual bias.
    reset_radius=radius(120000,1,.01)
    reset_reject=observed>endpoints(q(".5")+q(cfg["bias_mean"])/2+q(1)/2**cfg["grid_bits"]+reset_radius)[1]
    # f, ZZ minus has p = (3/32)(1-eta); covers the full physical calibration set.
    n=cfg["shots_per_bell_setting"]
    grid=q(1)/2**cfg["grid_bits"]
    gap=q(3)/32*(q(".9")-q(".65"))-2*(q(cfg["bias_event"])+grid)
    margin=gap-q("0.000000000004")-radius(n,cells,cfg["alpha_hold"])
    assert endpoints(margin)[0]>0
    power=1-iv.exp(-2*n*margin**2)
    records={}
    for f in cfg["holdout_families"]:
        vals=[counts[f+"_"+o] for o in cfg["bell_tests"]]
        records[f]=[sum(x[j]+x[j+1] for x in vals) for j in range(0,8,2)]
    result={"holdout_sha256":sha("holdout.npz"),"predictions_sha256":sha("predictions.json"),
        "calibration_alpha":cfg["alpha_cal"],"holdout_alpha":cfg["alpha_hold"],"number_of_cells":cells,
        "families":{f:("REJECTED" if failures else "NOT_REJECTED") for f,failures in decisions.items()},
        "failed_cells":decisions,"settings":rows,"aligned_phase":{"count":signed,"of":120000,
        "frequency":str(observed),"two_named_alternatives_choice":verdict,
        "reset_or_zero_response_rejected_at_1_percent":reset_reject},
        "readout_challenge_design":{"first_slot_f_ZZ_minus_composite_gap":bounds(gap),
        "single_prespecified_cell_sampling_power_lower":bounds(power),"conditional_on_valid_calibration_outer":True},
        "terminal_record_counts":records,"strong_baseline":"EQUIVALENT_NO_ADDED_GAIN",
        "device":"NOT_CERTIFIED","all_input_CQ":"DEFER_TO_ROOT_SEPARATE_CERTIFICATE"}
    write("holdout_results.json",result)
    print(result["families"],result["aligned_phase"],result["readout_challenge_design"])

if __name__=="__main__":
    main()
