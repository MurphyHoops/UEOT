"""Current-cohort source bindings, immutable identities and honest timing."""
from __future__ import annotations
import ast,json,subprocess
from datetime import datetime,timezone
from pathlib import Path
from common import HERE,REPO,sha,require,finish
SCI=['rare_preparation', 'adiabatic_connection', 'initial_layer', 'bounded_witness', 'local_constraint', 'rescaled_kernel', 'snapshot_spectrum', 'scalar_counterterm', 'dephasing_control', 'interior_collapse', 'ordering_sweep', 'rare_fisher', 'gaussian_control', 'probe_response', 'memory_action', 'memory_influence']
PREFIX="physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_propagation/"
ROUTES=[".github/workflows/ueot-physics-source-response.yml","physics/qm/README.md","physics/qm/ROADMAP.md","physics/qm/null_source/timelike/README.md"]
allowed={"__future__","numpy","sympy","common","collections"}
for name in SCI:
    py=HERE/(name+".py"); tree=ast.parse(py.read_text())
    for node in ast.walk(tree):
        if isinstance(node,ast.Import):
            require(all(a.name.split(".")[0] in allowed for a in node.names),"Unexpected scientific import")
        if isinstance(node,ast.ImportFrom):
            require(node.level==0 and (node.module or "").split(".")[0] in allowed,"Unexpected scientific import-from")
        if isinstance(node,ast.Call) and isinstance(node.func,ast.Attribute):
            require(node.func.attr not in {"solve_ivp","odeint","run","Popen","system","exec"},"Old/ODE/external science execution")
    d=json.loads((HERE/(name+".json")).read_text())
    require(d["status"]=="PASS" and d["physical_unification"]=="OPEN","Scientific exit inflation")
    require(d["predecessor_scientific_modules_imported_or_executed"]==d["mode_ODE_integrations"]==d["geometry_ODE_integrations"]==0,"Execution scope")
    for rel,digest in d["source_sha256"].items():
        require(sha((REPO/rel).read_bytes())==digest,"Scientific source binding: "+rel)
aud=json.loads((HERE/"source_audits.json").read_text())
require(len(aud["native_agents"])==len(set(aud["native_agents"]))==3,"Exactly three readonly agents")
identities=[]; coverage={}
for row in aud["checkpoints"]:
    require(row["agent"] in aud["native_agents"] and row["status"] in {"PASS","FINDINGS","FINDINGS_ADDRESSED"},"Audit actor/status")
    for rel,blob in row["files"].items():
        actual=subprocess.check_output(["git","rev-parse",row["commit"]+":"+rel],cwd=REPO,text=True).strip()
        require(actual==blob,"Immutable audited file identity")
        identities.append((row["commit"],row["agent"],rel))
        cur=subprocess.check_output(["git","hash-object",str(REPO/rel)],cwd=REPO,text=True).strip()
        if cur==blob:coverage.setdefault(rel,set()).add(row["agent"])
require(len(identities)==len(set(identities))==aud["immutable_review_file_identities"],"Audit count/duplicates")
if aud["status"]=="COMPLETE":
    require(all(row["status"]!="FINDINGS" for row in aud["checkpoints"]),"Unresolved immutable audit finding")
    for name in SCI:
        for suffix in [".py",".md"]:
            rel=PREFIX+(name.upper() if suffix==".md" else name)+suffix
            require(rel in coverage,"Current science not immutably audited: "+rel)
    for name in ["INITIAL_LAYER.md","INTERIOR_COLLAPSE.md"]:
        require(len(coverage.get(PREFIX+name,set()))==3,"Critical proof requires all three readers")
    for name in ["GAUSSIAN_CONTROL.md","PROBE_RESPONSE.md"]:
        require(len(coverage.get(PREFIX+name,set()))>=2,"New preparation/probe proof needs independent rereading")
    for name in ["MEMORY_ACTION.md","MEMORY_INFLUENCE.md"]:
        require(len(coverage.get(PREFIX+name,set()))>=2,"Memory action/influence needs independent rereading")
    for name in ["common.py","run_verification.py","review.py"]:
        require(PREFIX+name in coverage,"Verification infrastructure not immutably reviewed")
tim=json.loads((HERE/"session_timing.json").read_text())
start=datetime.fromisoformat(tim["start_utc"])
require(start.isoformat()=="2026-11-21T14:47:45+00:00" and not tim["previous_session_counted"],"New session clock")
if tim["phase"]=="COMPLETE":
    end=datetime.fromisoformat(tim["observed_finish_utc"])
    require((end-start).total_seconds()==tim["elapsed_seconds"]>=10800,"Three actual hours not met")
    require(end<=datetime.now(timezone.utc),"Future finish cannot be claimed")
    require(aud["status"]=="COMPLETE","Final immutable audit incomplete")
else:require(tim["phase"]=="IN_PROGRESS" and tim["observed_finish_utc"] is None,"Intermediate timing")
runner=ast.parse((HERE/"run_verification.py").read_text())
entries=next(ast.literal_eval(n.value) for n in runner.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=="ENTRIES" for t in n.targets))
require(entries==SCI+["review"],"Runner entry list")
inputs=[str(p.relative_to(REPO)) for p in HERE.iterdir()
        if p.is_file() and p.name not in {"review.json","verification.json"} and p.suffix in {".md",".py",".json"}]+ROUTES
finish("review.py",{"new_scientific_entries":len(SCI),"new_scope_entries":1,
"native_readonly_agents":3,"immutable_review_file_identities":len(identities),
"immutable_review_status":aud["status"],"session_phase":tim["phase"],
"three_hour_condition_fulfilled":tim["phase"]=="COMPLETE",
"frozen_predecessor_entries_expected":231,"frozen_scientific_files_expected":859,
"source_binding_scope":"new cohort and declared routes only"},
inputs=inputs,proof="REVIEW.md")
