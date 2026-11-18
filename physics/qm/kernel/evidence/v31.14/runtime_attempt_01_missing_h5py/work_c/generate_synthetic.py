"""The sole reader of SYNTHETIC_TRUTH.json; generates labelled synthetic shots.

Calibration and holdout are separate invocations. Holdout requires an already
frozen NOMINAL_MODEL.json. No fitted parameter is obtained from this file.
"""
from __future__ import annotations
import argparse, datetime, time
from pathlib import Path
import numpy as np
from common_c import BASE, digest, dump_json, dynamics, event_probabilities, load_json, rational

def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("phase", choices=["calibration", "holdout"])
    args=parser.parse_args()
    contract=load_json(BASE/"CALIBRATION_CONTRACT.json")
    frozen=load_json(BASE/"FROZEN_CALIBRATION_IDENTITY.json")
    if frozen["contract_sha256"] != digest(BASE/"CALIBRATION_CONTRACT.json"):
        raise RuntimeError("calibration contract changed after freezing")
    truth=load_json(BASE/"SYNTHETIC_TRUTH.json")
    lam=rational(truth["lambda"]); eta=rational(truth["eta"])
    dyn, source_path=dynamics()
    begin=now(); wall=time.perf_counter(); cpu=time.process_time()
    arrays={}; metadata=[]
    if args.phase == "calibration":
        seed_sequence=np.random.SeedSequence(contract["calibration"]["seed"])
        for setting, seed in zip(contract["calibration"]["settings"],seed_sequence.spawn(2)):
            rng=np.random.default_rng(seed)
            p=(1+eta*dyn.cal_coherence(lam,rational(setting["time"])))/2
            shots=(rng.random(setting["shots"]) < p).astype(np.uint8)
            arrays[setting["id"]]=shots
            metadata.append({"setting_id":setting["id"],"shots":len(shots),"codes":["-1","+1"],
                             "all_outcomes_retained":True,"generator_probability_plus":float(p),"seed_spawn_key":list(seed.spawn_key)})
        output=BASE/"calibration_shots.npz"
        np.savez_compressed(output, **arrays)
        nominal_sha=None
    else:
        nominal=load_json(BASE/"NOMINAL_MODEL.json")
        if nominal["contract_sha256"] != frozen["contract_sha256"]:
            raise RuntimeError("nominal model is not bound to this contract")
        nominal_sha=digest(BASE/"NOMINAL_MODEL.json")
        holdout_plan=load_json(BASE/"FROZEN_HOLDOUT_PLAN.json")
        if holdout_plan["nominal_sha256"] != nominal_sha:
            raise RuntimeError("holdout plan does not bind the nominal model")
        for family in contract["holdout"]["families"]:
            detector=rational(truth["detector_violation_eta"]) if family["id"]=="detector_violation" else eta
            ts=[rational(t) for t in family["times"]]
            blocks=dyn.exact_output(lam,times=ts)
            seeds=np.random.SeedSequence(family["seed"]).spawn(4)
            for obs, seed in zip(contract["holdout"]["observables"],seeds):
                rng=np.random.default_rng(seed)
                p=event_probabilities(blocks,detector,obs)
                p=np.maximum(p,0); p=p/p.sum()
                shots=rng.choice(8,size=contract["holdout"]["shots_per_setting"],p=p).astype(np.uint8)
                key=family["id"]+"__"+obs
                arrays[key]=shots
                metadata.append({"setting_id":key,"shots":len(shots),"codes":[r+s for r in contract["holdout"]["records"] for s in ("/-","/+")],
                                 "all_outcomes_retained":True,"generator_probabilities":p.tolist(),"seed_spawn_key":list(seed.spawn_key)})
        output=BASE/"holdout_shots.npz"
        np.savez_compressed(output, **arrays)
    dump_json(BASE/(args.phase+"_generation_receipt.json"),{
      "schema":"synthetic-shot-generation/1","status":"SYNTHETIC_ONLY","started_at":begin,"finished_at":now(),
      "contract_sha256":frozen["contract_sha256"],"truth_sha256":digest(BASE/"SYNTHETIC_TRUTH.json"),
      "nominal_sha256":nominal_sha,"generator_sha256":digest(__file__),"dynamics_sha256":digest(source_path),
      "data_file":output.name,"data_sha256":digest(output),"total_shots":sum(len(v) for v in arrays.values()),
      "settings":metadata,"wall_seconds":time.perf_counter()-wall,"cpu_seconds":time.process_time()-cpu,
      "bytes_compressed":output.stat().st_size,"hardware_calls":0,"hardware_data":False})
    print(f"{args.phase}: {sum(len(v) for v in arrays.values())} synthetic shots; {output.name}")

if __name__ == "__main__":
    main()
