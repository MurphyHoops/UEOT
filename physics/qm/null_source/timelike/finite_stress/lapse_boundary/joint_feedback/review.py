"""Source-bound scope check; no predecessor science execution."""
import ast,json
from pathlib import Path
from common import *
SCIENCE=['weighted_evolution', 'raw_ward', 'pressure_witness', 'positive_window', 'closure_counterexample', 'near_recovery', 'geometry_curvature', 'advanced_cutoff', 'prepared_limit']
allowed={"common","sympy","math","json","fractions","itertools","mpmath"}
for name in SCIENCE:
    src=(HERE/(name+".py")).read_text();tree=ast.parse(src)
    for node in ast.walk(tree):
        if isinstance(node,ast.Import):
            require(all(n.name.split(".")[0] in allowed for n in node.names),"Unexpected science import")
        if isinstance(node,ast.ImportFrom):
            require(node.level==0 and (node.module or "").split(".")[0] in allowed,"Predecessor/relative import prohibited")
    d=json.loads((HERE/(name+".json")).read_text())
    require(d["status"]=="PASS" and d["physical_unification"]=="OPEN" and not d["full_field_Einstein_CTP_device_solution"],"Scope flags")
    for rel,digest in d["source_sha256"].items():require(sha((REPO/rel).read_bytes())==digest,"Science binding mismatch: "+rel)
finish("review.py",dict(
 scientific_entry_count=len(SCIENCE),scientific_entries=SCIENCE,
 predecessor_execution_allowed=False,full_physics_completion_claimed=False,
 native_agents_are_external_human_review=False,
 proof_reading_separate_from_automatic_checks=True),
 [str((HERE/(n+".json")).relative_to(REPO)) for n in SCIENCE]+
 [str((HERE/n).relative_to(REPO)) for n in ["CONTRACT.md","REFERENCES.md","run_verification.py"]],
 proof="REVIEW.md")
