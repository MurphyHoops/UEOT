"""Audit frozen synthetic records and run three-slot reporting/phase ablations.
Run with -B; --check compares the recomputation with record_controls.json.
"""
import argparse
import json
import os
from fractions import Fraction as F

import numpy as np
import shared

HERE = shared.ROOT
# Use the supplied checkout (including shared clones) for the pinned interval helpers.
shared.REPO = os.environ.get("UEOT_UPSTREAM_REPO") or str(HERE.parent)
os.environ.update(GIT_NO_REPLACE_OBJECTS="1", GIT_NO_LAZY_FETCH="1", GIT_TERMINAL_PROMPT="0", GIT_ALLOW_PROTOCOL="")
from interval_model import bell, bounds, endpoints, q

CFG = shared.read("protocol.json")
RECORDS = CFG["records"]
COLUMNS = {
    "stored": {"block_setting": "uint8 setting index for each chronological 1000-shot row",
               "ordered_codes": "uint8 simulated outcome at [block, within_block]"},
    "decoded": {"phase_and_ordinal": "Archive name and array position; zero-based logical time.",
                "session_batch": "Calibration or holdout archive; setting comes from protocol insertion order.",
                "initial_state_reference_pulses": "Commanded preparation, S operations, durations and nominal shot-zero frame.",
                "failure_stop": "Bell code // 2 selects f, pf, ppf, ppp; the prefix determines the slots actually reached in simulation.",
                "readout": "Bell code % 2 or scalar code indexes minus/plus; Bell readout is one Pauli product, without individual qubit bits."},
    "synthetic_assumptions": ["Fresh bath at every start; end reset charged once per start.",
                              "Ideal designated pulses, phase lock and common offset plus specified detector/gain model.",
                              "Zero intrinsic leakage, lost rows and injected drift; statistical independence given schedule."],
    "device_fields_absent": ["wall-clock time and hardware trigger/attempt ID", "per-shot preparation or pulse telemetry",
                             "measured phase reference, drift and calibration provenance", "leakage/invalid-readout flag",
                             "reset acknowledgement, loss/dead time, actual work or energy and device raw record"]
}


def check(condition, label):
    if not condition:
        raise ValueError(label)


def decode(phase, index, code, ordinal):
    name = list(shared.settings(phase))[index]
    result = dict(phase=phase, ordinal=ordinal, block=ordinal//CFG["block"], within_block=ordinal%CFG["block"],
                  block_setting=index, ordered_code=code, setting=name, terminal_sign=2*(code%2)-1)
    if "_" in name:
        family, observable = name.rsplit("_", 1)
        record = RECORDS[code//2]
        durations = CFG["swap" if family=="swap" else "original"][:len(record)]
        rotations = [op for op,flag in zip(("Ry(pi/2)","Rx(pi/3)","I"),record) if flag=="p"]
        result.update(prep="Bell SR", reference="qubit R untouched until terminal tester", tester=observable,
                      prefix=record, post_pass_operations=rotations)
    elif name.startswith("R"):
        durations = [{"R0":"0", "Rshort":"3/4", "Rlong":"3/2"}[name]]
        result.update(prep="+X", reference="preparation clock; no spectator", tester="X", prefix=None)
    else:
        durations = ["1" if name.startswith("H") else "2/3", "3/4"]
        result.update(prep="Z eigenvalue "+("+1" if name.endswith("p") else "-1"),
                      reference="shared break frame; no spectator", insertion="trace S, prepare +X, retain E",
                      tester="X" if name.startswith("X") else "Y", prefix=None)
    return dict(result, commanded_durations=durations)


def audit_raw():
    ledger = shared.read("verification.json")["logical_resources"]
    counts, examples, identities = {}, [], {}
    starts = slots = breaks = bell_preps = ry = rx = 0
    exposure = F(0)
    for phase in ("calibration","holdout"):
        receipt = shared.read(phase+"_receipt.json")
        digest = shared.sha(phase+".npz")
        check(digest==receipt["raw_sha256"] and receipt["freeze_sha256"]==shared.sha("freeze.json"),phase+" byte binding")
        counts[phase] = shared.unpack(phase)
        with np.load(HERE/(phase+".npz"), allow_pickle=False) as data:
            check(set(data.files)=={"block_setting","ordered_codes"}, phase+" stored field names")
            order, rows = data["block_setting"], data["ordered_codes"]
        check(order.dtype==np.uint8 and order.shape==(rows.shape[0],),phase+" block encoding")
        identities[phase] = {"sha256":digest,"blocks":len(order),"shots":int(rows.size)}
        archived = (shared.read("calibration_fit.json")["counts"] if phase=="calibration" else
                    {k:r["counts"] for k,r in shared.read("holdout_results.json")["settings"].items()})
        check(counts[phase]==archived,phase+" full count tables differ")
        for index,(name,arr) in enumerate(counts[phase].items()):
            for code,number in enumerate(arr):
                shot = decode(phase,index,code,0)
                durations = list(map(F,shot["commanded_durations"]))
                starts += number
                slots += number*sum(t>0 for t in durations)
                exposure += number*sum(durations)
                if shot["prefix"] is not None:
                    bell_preps += number
                    ry += number*int("Ry(pi/2)" in shot["post_pass_operations"])
                    rx += number*int("Rx(pi/3)" in shot["post_pass_operations"])
                elif "insertion" in shot:
                    breaks += number
            if name in ("Rshort","Yp","original_YZ"):
                block = int(np.flatnonzero(order==index)[0])
                j = int(np.flatnonzero(rows[block]//2==1)[0]) if name=="original_YZ" else 0
                examples.append(decode(phase,index,int(rows[block,j]),block*CFG["block"]+j))
    reconstructed = dict(started_shots=starts,terminal_measurements=starts,heldout_Bell_preparations=bell_preps,
                         causal_repreparations=breaks,eigenstate_preparations=breaks,nonzero_source_intervals=slots,
                         dimensionless_total_interaction_time=str(exposure),Ry_postpass=ry,Rx_postpass=rx)
    for key,value in reconstructed.items():
        check(ledger[key]==value, f"resource {key}: decoded {value}, registered {ledger[key]}")
    check(ledger["fresh_bath_preparations_and_end_resets_each"]==starts,"one contractual reset per started shot")
    return counts["holdout"], dict(archives=identities,field_dictionary=COLUMNS,decoded_examples=examples,
                                  checked_prefix_resources=reconstructed,source_ledger="inference/verification.json")


def phase_control(timing, truth, hold):
    w = q(F(truth["lambda"])**2)
    n,c,eta = [q(truth[k]) for k in ("n","c","eta")]
    def atten(a,b):
        return w*((2*n+1)*a+c*b)
    times = CFG[timing]
    full = bell(times,eta,w,atten)
    # Only suppress the imaginary Weyl exchange exponent. Keep the original
    # real attenuation, its inter-slot covariance, every Kraus map and readout.
    off = bell(times,eta,q(0),atten)
    tv,disjoint = {},[]
    allowance = F(str(CFG["bias_event"])) + F(1,2**CFG["grid_bits"])
    cuts = shared.read("holdout_source_cdf.json")
    for obs,p in full.items():
        key = timing+"_"+obs
        cumulative = q(0)
        for x,cut in zip(p[:-1],cuts[key],strict=True):
            cumulative += x
            lo,hi = endpoints(cumulative*2**CFG["grid_bits"]-cut)
            check(-F(1,2)<=lo<=hi<=F(1,2),key+" source mismatch")
        z = off[obs]
        lo,hi = endpoints(sum(z))
        check(lo<=1<=hi and all(endpoints(x)[0]>=0 for x in z),key+" phase-free event law")
        delta = [x-y for x,y in zip(p,z)]
        tv[obs] = bounds(sum(map(abs,delta))/2)
        for i,(x,band) in enumerate(zip(z,hold["settings"][key]["frequency_bands"])):
            lo,hi = endpoints(x)
            if lo-allowance>F(band[1]) or hi+allowance<F(band[0]):
                disjoint.append([obs,i])
    check(F(tv["YZ"][0])>F(".004"),timing+" erased phase has no expected Bell witness")
    s = sum(full["YZ"][6:])
    b, d = q("3/4"), q("7/8")
    return {"timing":times,"source_vs_phase_free_event_TV_outward":tv,
            "signed_YZ_ppp_minus_full_minus_phase_free":bounds(full["YZ"][6]-off["YZ"][6]),
            "point_phase_free_cells_disjoint_from_archived_simultaneous_bands":disjoint,
            "model_success_mass":bounds(s),"success_only_as_complete_TV":bounds(1-s),
            "last_pass_veto_TV":bounds((1-b)*s),"veto_visible_success_mass":bounds(b*s),
            "terminal_leak_visible_success_mass":bounds(d*s),
            "model_starts_per_visible_success":{"baseline":bounds(1/s),"veto":bounds(1/(b*s)),"leak":bounds(1/(d*s))}}


def reporting_controls(timing, counts, hold):
    """Apply two stochastic channels exactly to the observed per-tester laws.

    Reroute 1/4 of final ppp to ppf, with its state and sign retained (extra
    terminal failure Kraus on the last pass). Separately, erase S into an
    orthogonal leakage level with probability 1/8 just before the readout.
    The complete logger has one extra (prefix,leak) cell per prefix; the
    defective logger drops those rows. All attempts pay their entire prefix.
    These are exact weighted counterfactuals, not extra acquired shots.
    """
    veto,leak = F(1,4),F(1,8)
    tv = lambda a,b:sum(abs(x-y) for x,y in zip(a,b,strict=True))/2
    by_record = [0]*4
    for obs in CFG["bell_tests"]:
        arr = counts[timing+"_"+obs]
        p = [F(x,sum(arr)) for x in arr]
        s = sum(p[6:])
        post = [F(0)]*6 + [x/s for x in p[6:]]
        rerouted = p[:]
        for j in (6,7):
            rerouted[j-2] += veto*p[j]
            rerouted[j] -= veto*p[j]
        valid = [(1-leak)*x for x in p]
        lost = [leak*(p[i]+p[i+1]) for i in range(0,8,2)]
        check(sum(rerouted)==sum(valid+lost)==1,obs+" normalization")
        check([x/sum(valid) for x in valid]==p,obs+" distribution among logged rows")
        for reported in (rerouted,valid):
            check([x/sum(reported[6:8]) for x in reported[6:8]]==post[6:],obs+" conditional success signs")
        check(tv(p,post)==1-s and tv(p,rerouted)==veto*s and tv(p+[0]*4,valid+lost)==leak,
              obs+" joint law TV")
        by_record = [a+b+c for a,b,c in zip(by_record,arr[::2],arr[1::2])]
        if obs=="YZ":
            witness = {"observed_cells_minus_then_plus":arr,"success_conditional_minus_plus":list(map(str,post[6:])),
                       "veto_joint_probabilities":list(map(str,rerouted)),
                       "leak_joint_probabilities_eight_valid_then_four_flagged":list(map(str,valid+lost))}
    check(by_record==hold["terminal_record_counts"][timing],timing+" observed stopped counts")
    total,success = sum(by_record),by_record[-1]
    reached = [total,sum(by_record[1:]),sum(by_record[2:])]
    exposure = sum(t*r for t,r in zip(map(F,CFG[timing]),reached))
    mass = F(success,total)
    cost = {}
    for name,survival in (("baseline",F(1)),("last_pass_veto",1-veto),("unrecorded_leak",1-leak)):
        usable = success*survival
        cost[name] = {"cost_multiplier_vs_baseline":str(1/survival), "yield_per_started_shot":str(usable/total),"starts_and_charged_resets_each_per_usable_success":str(total/usable),
                      "executed_source_intervals_per_usable_success":str(sum(reached)/usable),
                      "interaction_time_per_usable_success":str(exposure/usable)}
    return {"started":total,"record_counts_f_pf_ppf_ppp":by_record,"source_interval_uses":sum(reached),
            "interaction_time":str(exposure),"successful_rows_only_discard":total-success,
            "success_only_as_complete_TV":str(1-mass),"last_pass_veto_unconditional_TV":str(veto*mass),
            "leak_flag_included_TV":str(leak),"leak_conditioned_on_any_logged_row_TV":"0",
            "conditional_success_sign_TV_both_controls_all_four_testers":"0","costs":cost,"YZ_example":witness}


def compute():
    shared.verify_freeze()
    check(shared.sha("truth.json")==shared.read("freeze.json")["files"]["truth.json"],"truth hash")
    counts,raw = audit_raw()
    truth,hold = shared.read("truth.json"),shared.read("holdout_results.json")
    reset = hold["aligned_phase"]
    check(reset["count"]==counts["Hp"][0]+counts["Hm"][1] and reset["reset_or_zero_response_rejected_at_1_percent"],
          "archived reset decision vs raw signs")
    wrong_clock = shared.read("../dynamics/observed.json")["wrong_clock"]
    for key,row in wrong_clock.items():
        check(row["Fock_K20_vs_API"]<1e-6 and row["Fock_K20_vs_wrong_frame"]>.01,key+" wrong-frame control")
    return {"schema":"three-slot-record-controls/1","status":"PASS","device":"NOT_CERTIFIED",
            "freeze_sha256":shared.sha("freeze.json"),"resource_ledger_sha256":shared.sha("verification.json"),
            "raw":raw,"synthetic_truth":truth,"counterfactual":{"last_pass_veto":"1/4 of ppp relabelled ppf, same terminal state",
            "unrecorded_leak":"1/8 independent terminal erasure on every stopped prefix. Full alphabet includes (prefix,leak); defective logger drops these attempts.",
            "cost_basis":"unit cost per start and reset, source slots charged through physical stopping even when readout is lost",
            "scope":"post hoc diagnostic on the synthetic Bell source; fractions are exact observed-law transformations; model intervals are directed outward"},
            "timings":{t:{"exact_Weyl_model":phase_control(t,truth,hold),"observed_law":reporting_controls(t,counts,hold)}
                       for t in ("original","swap")},
            "reused":{"reset":{"source":"inference/holdout_results.json","result":reset},
                      "wrong_clock":{"source":"dynamics/observed.json","point_diagnostics":wrong_clock},
                      "phase_crosscheck_other_inputs":"selection/review_dynamics.py and selection/dynamics_review_run.txt (mixed SR, dim R=3)"}}


if __name__=="__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check",action="store_true",help="verify published JSON and exit; otherwise emit JSON to stdout")
    args = parser.parse_args()
    result = compute()
    if args.check:
        saved = shared.read("record_controls.json")
        check(saved.keys()==result.keys(),"record-controls receipt fields differ")
        for field,value in result.items():
            check(value==saved[field],"record-controls receipt differs in "+field)
        print("PASS: 1,128,000 ordered shots; both Bell timings, three reporting/phase controls and archived reset/frame witnesses.")
    else:
        print(json.dumps(result,indent=2,allow_nan=False))
