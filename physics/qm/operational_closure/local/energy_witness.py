"""All-start mean-energy witness for the extended fixed-lab-axis C pulse."""
import argparse
import hashlib
import json
from fractions import Fraction as F
from math import exp, sqrt
from pathlib import Path

from scipy.stats import binom

import verify_local as local

HERE = Path(__file__).resolve().parent
WORK = ("on", "off")
C_ARMS = ("pre", "post")
STANDARDS = ("start_log", "source_transfer", "energy_bound_meter",
             "work_meter_transfer", "binary_readout_transfer", "first_law_channels")
COUNTS = {**{j:4_000_000 for j in WORK},
          **{f"{j}_{r}":1_000_000 for j in WORK for r in ("minus8","plus8")},
          **{f"energy_{j}":250_000 for j in WORK},
          **{j:2_000_000 for j in C_ARMS},
          **{f"{j}_{r}":100_000 for j in C_ARMS for r in ("g","e")}}
GAP = F(1,64)
P_RADIUS = F("0.0023")
W_RADIUS = F("0.004")
BALANCE = F("0.0002")
FIELD_RADIUS = W_RADIUS + GAP*P_RADIUS + BALANCE


def design():
    src = HERE/"result.json"
    assert hashlib.sha256(src.read_bytes()).hexdigest()=="aaf6ebda1186771b18ad55a49e037842df20c55a73215d7fc87b15a45dd269e0"
    gate = json.loads(src.read_bytes())["cases"]["chapter71_local"]["+"]["fixed_lab_axis"]
    iv = local.iv
    A = B = local.rat(0)
    for j in range(local.M+1):
        w,g = local.probe.mode(j)
        A += g*g/w
        B += g*g
    pref = 2*(80/iv.pi)**8
    A += iv.mpf([0,1])*pref/(9*local.probe.beta**2*local.M**9)
    B += iv.mpf([0,1])*pref/(8*local.probe.beta*local.M**8)
    second = (iv.sqrt(2*A)+iv.sqrt(2*A+B))**2/100
    assert second<local.rat(".18335")
    assert (1.001*sqrt(.18335)+.04)**2 < .23
    assert (1.001*sqrt(.03167)+.04)**2 < .05 and B/100<local.rat(".03167")
    assert 2*(.001*sqrt(.18335)+.0001)<.0011
    alpha = {"energy_qualification":2*16/250_000/.12**2,
             "gain_qualification":2*.05/(2*1_000_000*8**2)/.00045**2,
             "binary_calibration":4*float(binom.cdf(5,100_000,.0002)),
             "work":(2*.23/4_000_000+.05/1_000_000)/.0029**2,
             "occupancy":2*exp(-2_000_000*.0017**2)}
    beta = sum(alpha.values())+4*float(binom.sf(5,100_000,.00001))
    assert sum(alpha.values())<.039 and beta<.042
    assert F(gate["delta_E_F"][1])+2*FIELD_RADIUS<0
    assert F(gate["delta_p_e"][0])-2*P_RADIUS>0
    assert F(gate["net_switch_work"][1])+2*(W_RADIUS+F(".00019"))<0
    return {"starts":sum(COUNTS.values()),"allocation":COUNTS,"A":local.bounds(A),"B":local.bounds(B),
            "true_edge_second_moment_upper":local.bounds(second)[1],
            "field_radius":str(float(FIELD_RADIUS)),"union_error":sum(alpha.values()),
            "nominal_noncertification_upper":beta,"old_field_upper":gate["delta_E_F"][1],
            "old_delta_p_lower":gate["delta_p_e"][0]}


def template():
    return {"evidence":{s:None for s in STANDARDS},
            "arms":{j:{"starts":n,"lost":None,"total":None} for j,n in COUNTS.items()}}


def evaluate(data):
    arms = data["arms"]
    if set(arms)!=set(COUNTS):
        raise ValueError("incomplete or unexpected arm set")
    means = {}
    for j,n in COUNTS.items():
        rec = arms[j]
        if type(rec["starts"]) is not int or rec["starts"]!=n:
            raise ValueError(f"{j}: all scheduled starts required")
        lost = rec["lost"]
        if type(lost) is not int or not 0<=lost<=n:
            raise ValueError(f"{j}: invalid loss count")
        count = F(str(rec["total"]))
        if j.startswith(("pre","post")):
            ref = j not in C_ARMS
            if count.denominator!=1 or not (lost if ref else 0)<=count<=(n if ref else n-lost):
                raise ValueError(f"{j}: invalid binary count")
        elif lost==n and count:
            raise ValueError(f"{j}: every analog reading lost; zero-filled total must be zero")
        means[j] = count/n
    missing = [j for j,n in COUNTS.items() if arms[j]["lost"]==n]
    if missing:
        return {"status":"inconclusive_no_readings","arms":missing}
    evidence = data.get("evidence", {})
    if not isinstance(evidence,dict) or any(not isinstance(evidence.get(s),str) or not evidence[s].strip() for s in STANDARDS):
        return {"status":"inconclusive_missing_external_evidence"}
    for j in C_ARMS:
        for r in ("g","e"):
            tag = f"{j}_{r}"
            if means[tag]*COUNTS[tag]>5:
                return {"status":"inconclusive_binary_calibration","arm":tag}
    w = F(0)
    for j in WORK:
        if means[f"energy_{j}"]+F(".14")>2:
            return {"status":"inconclusive_energy_envelope","arm":j}
        a,b = means[f"{j}_minus8"],means[f"{j}_plus8"]
        if abs((b-a)/16-1)>F(".00055"):
            return {"status":"inconclusive_work_meter_gain","arm":j}
        w += means[j]-(a+b)/2
    d = means["post"]-means["pre"]
    upper = w-GAP*d+FIELD_RADIUS
    lower_p = d-P_RADIUS
    lower_c = (GAP-(1 if lower_p>=0 else -1)*F(".00001"))*lower_p
    upper_net = w+W_RADIUS+F(".00019")
    return {"status":"numerical_thresholds_only","hardware_verdict":"not_assessed",
            "upper_delta_E_F":str(upper),"lower_delta_E_C":str(lower_c),
            "upper_total_drive":str(upper_net),"field_upper_negative":upper<0,
            "probe_lower_positive":lower_c>0,"drive_upper_negative":upper_net<0}


def controls():
    # Constructed sufficient statistics exercise the decision logic; no shot simulation.
    doc = template()
    doc["evidence"] = dict.fromkeys(STANDARDS,"synthetic fixture")
    mu = {"on":"-.023", "off":".013", "pre":".18", "post":".189"}
    for j,n in COUNTS.items():
        mean = mu.get(j,"0")
        if j.startswith("energy_"):
            mean = "1.55"
        if j.endswith(("minus8","plus8")):
            mean = "-8" if j.endswith("minus8") else "8"
        doc["arms"][j].update(lost=0,total=str(F(mean)*n))
    good = evaluate(doc)
    assert good["field_upper_negative"] and good["probe_lower_positive"] and good["drive_upper_negative"]
    doc["arms"]["off"]["total"] = 120000  # Same C data, W_off=+.030.
    bad = evaluate(doc)
    assert bad["probe_lower_positive"] and not bad["field_upper_negative"]
    doc["arms"]["energy_off"]["total"] = 500000
    assert evaluate(doc)["status"]=="inconclusive_energy_envelope"
    for j in ("on","off_plus8","energy_off"):
        saved = doc["arms"][j].copy()
        doc["arms"][j].update(lost=COUNTS[j],total=1)
        try:
            evaluate(doc)
        except ValueError as err:
            assert "zero-filled total" in str(err)
        else:
            raise AssertionError(f"{j}: impossible all-lost record accepted")
        doc["arms"][j]["total"] = 0
        assert evaluate(doc)["status"]=="inconclusive_no_readings"
        doc["arms"][j] = saved
    return {"constructed_field_upper":float(F(good["upper_delta_E_F"])),
            "same_C_different_work_upper":float(F(bad["upper_delta_E_F"])),
            "all_lost_with_nonzero_total":"rejected for science, reference and energy arms"}


if __name__=="__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--summary",type=Path,help="evaluate registered real all-start totals")
    group.add_argument("--template",action="store_true",help="print the empty input schema")
    args = parser.parse_args()
    if args.template:
        out = template()
    elif args.summary:
        out = evaluate(json.loads(args.summary.read_text(),parse_float=str))
    else:
        out = {"design":design(),"decision_controls":controls(),"hardware_data":"absent"}
    print(json.dumps(out,indent=2))
