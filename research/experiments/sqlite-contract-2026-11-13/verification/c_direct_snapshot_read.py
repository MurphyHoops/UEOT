#!/usr/bin/env python3
"""C-owned SQLite reads of cloned calibration snapshots; no producer imports."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import sqlite3
import sys
import time

def load(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def image(directory):
    result = {}
    for p in sorted(Path(directory).iterdir()):
        if not p.is_file() or p.is_symlink():
            raise RuntimeError("unexpected entry")
        data = p.read_bytes()
        result[p.name] = {"bytes":len(data),"sha256":hashlib.sha256(data).hexdigest(),
                          "first28":data[:28].hex() if p.name.endswith("-journal") else None}
    return result

def states_from_requests(case):
    state = load(case/"oracle/initial.json")
    states = [state]
    events = [json.loads(s) for s in (case/"parent-events.jsonl").read_text().splitlines()]
    for e in events:
        if e["event"] != "PARENT_SENT" or e["message"]["cmd"] != "TRANSACTION":
            continue
        request = e["message"]["request"]
        by_key = {x[0]:list(x) for x in state["business"]}
        for key,value,token in request["updates"]:
            count = request["payload_length"]
            by_key[key] = [key,value,(token*(count//len(token)+1))[:count]]
        state = {"business":[by_key[k] for k in sorted(by_key)],
                 "transactions":state["transactions"]+[[request["seq"],request["txn_id"],request["request_hash"]]]}
        states.append(state)
    return states

def inspect(source, destination, expected):
    original = image(source)
    destination.mkdir(parents=True,exist_ok=False)
    for p in source.iterdir():
        shutil.copyfile(str(p),str(destination/p.name))
    before = image(destination)
    if before != original:
        raise RuntimeError("C clone mismatch before open")
    start = time.monotonic_ns()
    connection = sqlite3.connect(str(destination/"db.sqlite"), isolation_level=None)
    try:
        runtime = {"version":connection.execute("select sqlite_version()").fetchone()[0],
                   "source_id":connection.execute("select sqlite_source_id()").fetchone()[0]}
        structure = [list(x) for x in connection.execute("pragma integrity_check")]
        foreign = [list(x) for x in connection.execute("pragma foreign_key_check")]
        business = [list(x) for x in connection.execute("select id,value,payload from business order by id")]
        transactions = [list(x) for x in connection.execute("select seq,txn_id,request_hash from transactions order by seq")]
    finally:
        connection.close()
    state = {"business":business,"transactions":transactions}
    matched = state == expected
    if image(source) != original:
        raise RuntimeError("original modified")
    return {"source":str(source),"copy":str(destination),"before":before,"after":image(destination),
            "runtime":runtime,"weak_projection":{"opened":True,"integrity":structure,"foreign_keys":foreign},
            "state":state,"exact_expected_state_match":matched,"elapsed_ns_in_C_process":time.monotonic_ns()-start,
            "source_unchanged":True}

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--root",required=True)
    parser.add_argument("--outdir",required=True)
    args=parser.parse_args()
    root=Path(args.root).resolve(); out=Path(args.outdir).resolve()
    out.mkdir(parents=True,exist_ok=False)
    rows=[]
    for spec in load(root/"RUNS_PLANNED.json"):
        case=root/spec["run_id"]; states=states_from_requests(case)
        if spec["scenario"]=="STALE_BACKUP":
            current=inspect(case/"pre_replacement_current",out/spec["run_id"]/"current",states[-1])
            old=inspect(case/"postfault_raw",out/spec["run_id"]/"stale",states[1])
            same_projection=current["weak_projection"]==old["weak_projection"]
            difference=current["state"]!=old["state"]
            entries={"current":current,"stale":old}
            rows.append({"run_id":spec["run_id"],"scenario":spec["scenario"],"observations":entries,
                         "same_registered_structure_projection":same_projection,
                         "different_full_state":difference,
                         "same_H_current_allowed":current["state"]==states[-1],
                         "same_H_stale_allowed":old["state"]==states[-1]})
        if spec["scenario"]=="PRECOMMIT_KILL":
            obs=inspect(case/"postfault_raw",out/spec["run_id"]/"precommit",states[-2])
            journal=obs["before"].get("db.sqlite-journal",{})
            magic=journal.get("first28","")[:16]
            rows.append({"run_id":spec["run_id"],"scenario":spec["scenario"],"observation":obs,
                         "hot_magic_present":magic=="d9d505f920a163d7",
                         "journal_removed_after_read":"db.sqlite-journal" not in obs["after"],
                         "database_bytes_changed":obs["before"]["db.sqlite"]["sha256"]!=obs["after"]["db.sqlite"]["sha256"]})
    output={"checker":"C_DIRECT_SNAPSHOT_READ_V1","checker_sha256":sha(Path(__file__)),
            "root":str(root),"purpose":"calibration only; fresh clones read with C-owned sqlite3 queries, no B verdict functions",
            "results":rows}
    (out/"C_DIRECT_READ.json").write_text(json.dumps(output,ensure_ascii=False,indent=2)+"\n")
    compact=[]
    for row in rows:
        compact.append({k:v for k,v in row.items() if k not in ["observation","observations"]})
    print(json.dumps(compact))
    print("C_DIRECT_READ_SHA256",sha(out/"C_DIRECT_READ.json"))
    all_matches=[]
    for row in rows:
        if "observation" in row: all_matches.append(row["observation"]["exact_expected_state_match"])
        else: all_matches.extend(v["exact_expected_state_match"] for v in row["observations"].values())
    return 0 if rows and all(all_matches) else 2

if __name__=="__main__":
    sys.exit(main())

