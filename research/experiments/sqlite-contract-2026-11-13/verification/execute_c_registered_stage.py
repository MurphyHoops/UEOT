#!/usr/bin/env python3
"""C's fixed-scope post-registration execution; no producer verdict imports."""
import datetime
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT=Path("/Users/murphyhoops/Documents/ueot-sqlite-study-20261113")
C=ROOT/"independent-C"
SOURCE=C/"registered-source"
COMMIT="26902c25152ca3676b4844d2156f028145f62fe2"
EXPECTED={
    SOURCE/"sqlite_study.py":"bdbe87252da0b107602f7e30509b4b094f53d97a647ac9dc34cb378195dd92d9",
    SOURCE/"protocol.json":"f68c5e9b643738563eebdce032bf13126e63036b2b473f889840355af5e00566",
    SOURCE/"RUN_ALLOCATION.json":"2561677d933aec2ceef8ca3a80a6d480a5cebc32a55a99a0dbdfeb63f6e66b02",
    C/"tools/c_independent_check_v2.py":"40e9f2816a73f041bd1bb7f368b96303cea54c8208e8100c7994fab1279d7b38",
    C/"tools/c_direct_snapshot_read_v2.py":"20a04e92c6b74c90e87da9e8e1735e66002edebbf0b92bea02470b06207d384a",
}
def now(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
def load(p): return json.loads(p.read_text())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def need(v,why):
    if not v: raise RuntimeError(why)

receipt={"started_utc":now(),"preregistration_commit":COMMIT,"steps":[],
         "C_wrapper_sha256":sha(Path(__file__)),"scope":"28 existing B trials audited; exactly seven new registered C replication trials"}
def step(label,argv):
    out=C/(label+".stdout.log");err=C/(label+".stderr.log")
    entry={"label":label,"argv":argv,"started_utc":now()}
    with out.open("xb") as fo,err.open("xb") as fe:
        process=subprocess.run(argv,stdout=fo,stderr=fe,check=False)
    entry.update(finished_utc=now(),returncode=process.returncode,stdout_sha256=sha(out),stderr_sha256=sha(err))
    receipt["steps"].append(entry)
    print(json.dumps(entry),flush=True)
    need(process.returncode==0,label+" returned nonzero")
    return entry
status=1
try:
    need(not (C/"C_EXECUTION_RECEIPT.json").exists(),"receipt already exists")
    receipt["source_bindings"]=[]
    for path,digest in EXPECTED.items():
        actual=sha(path);need(actual==digest,"source differs: "+str(path))
        receipt["source_bindings"].append({"path":str(path),"sha256":actual})
    auth=load(SOURCE/"authorization.json")
    need(auth.get("approved") is True and auth["preregistration_commit"]==COMMIT and "replication" in auth["allowed_splits"],"wrong authorization")
    need(auth["runner_sha256"]==EXPECTED[SOURCE/"sqlite_study.py"] and auth["protocol_sha256"]==EXPECTED[SOURCE/"protocol.json"],"auth source differs")
    receipt["authorization_sha256"]=sha(SOURCE/"authorization.json")
    allocation=load(SOURCE/"RUN_ALLOCATION.json")
    cert=ROOT/"certification/run-v1"
    need(sha(cert/"FILE_MANIFEST.json")=="ed4da14df4cf913032e8e505118a52b783650d1118f94e4981d6e9d8beed7073","B final manifest differs")
    cm=load(cert/"RUN_MANIFEST.json")
    need(cm["authorization"]==auth,"B authorization differs")
    need(cm["runner_sha256"]==EXPECTED[SOURCE/"sqlite_study.py"] and cm["protocol_sha256"]==EXPECTED[SOURCE/"protocol.json"],"B executed source binding differs")
    need(load(cert/"RUNS_PLANNED.json")==allocation["certification"],"actual B plan differs from preregistration")
    need(cm["started_utc"]>auth["issued_at_utc"],"B run not after go")
    receipt["B_manifest_sha256"]=sha(cert/"FILE_MANIFEST.json")
    receipt["B_started_utc"]=cm["started_utc"]
    step("01-certification-check",[sys.executable,str(C/"tools/c_independent_check_v2.py"),"--root",str(cert),"--out",str(C/"certification-check-v1.json"),"--preregistration-commit",COMMIT])
    step("02-certification-direct-read",[sys.executable,str(C/"tools/c_direct_snapshot_read_v2.py"),"--root",str(cert),"--outdir",str(C/"certification-direct-read")])
    replica=C/"replication/run-v1"
    step("03-replication-controller",[sys.executable,str(SOURCE/"sqlite_study.py"),"run","--split","replication","--protocol",str(SOURCE/"protocol.json"),"--out",str(replica),"--authorization",str(SOURCE/"authorization.json")])
    need(load(replica/"RUNS_PLANNED.json")==allocation["replication"],"C actual plan differs")
    step("04-replication-check",[sys.executable,str(C/"tools/c_independent_check_v2.py"),"--root",str(replica),"--out",str(C/"replication-check-v1.json"),"--preregistration-commit",COMMIT])
    step("05-replication-direct-read",[sys.executable,str(C/"tools/c_direct_snapshot_read_v2.py"),"--root",str(replica),"--outdir",str(C/"replication-direct-read")])
    receipt["status"]="C_EXECUTED_REVIEW_REQUIRED"
    status=0
except Exception as error:
    receipt["status"]="C_FAILED_OR_BLOCKED"
    receipt["error"]={"type":type(error).__name__,"message":str(error)}
finally:
    receipt["finished_utc"]=now()
    with (C/"C_EXECUTION_RECEIPT.json").open("x") as f: json.dump(receipt,f,ensure_ascii=False,indent=2);f.write("\n")
    print(json.dumps({"status":receipt["status"],"steps":len(receipt["steps"]),"finished_utc":receipt["finished_utc"]}),flush=True)
sys.exit(status)

