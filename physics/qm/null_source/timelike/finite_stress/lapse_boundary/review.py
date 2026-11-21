"""Scope and exact-source binding checks; no predecessor science is imported."""
import ast,json
from common import HERE,REPO,require,sha,finish
ENTRIES=["action_boundary","endpoint_domain","tensor_noise","dynamic_witness","source_ctp",
         "smooth_preparation","operational_state","retarded_response","quiet_window",
         "causal_domain","finite_causal","finite_source_domain","action_response","covariant_response",
         "actual_inverse","prepared_readout","constraint_residual","action_lift",
         "mixed_boundary","readout_witness","canonical_preparation","hadamard_gate","prepared_mean","incoming_preparation","quantum_endpoint","relational_domain"]
allowed={"common","sympy","fractions","itertools","math","mpmath"}
for name in ENTRIES:
    result=json.loads((HERE/(name+".json")).read_text())
    require(result["status"]=="PASS" and result["whole_physical_unification"]=="OPEN","Scope marker")
    require(result["full_joint_Einstein_CTP_device_solution"] is False,"Inflated closure")
    for rel,digest in result["source_sha256"].items():
        require(sha((REPO/rel).read_bytes())==digest,"Changed scientific binding: "+rel)
    tree=ast.parse((HERE/(name+".py")).read_text())
    for node in ast.walk(tree):
        if isinstance(node,ast.Import):
            require(all(a.name.split(".")[0] in allowed for a in node.names),"Unexpected scientific import")
        if isinstance(node,ast.ImportFrom):
            require(node.level==0 and node.module in allowed,"Predecessor import forbidden")
        if isinstance(node,ast.Call) and isinstance(node.func,ast.Name):
            require(node.func.id not in {"eval","exec","compile","__import__"},"Dynamic execution forbidden")
require(json.loads((HERE/"operational_state.json").read_text())["operational_quotient_principle_reused_from_RELATIONAL"],"Prior result miscount")
require(json.loads((HERE/"quiet_window.json").read_text())["original_fixed_c_history_extended"] is False,"History relabel")
finish("review.py",dict(scientific_entries_bound=ENTRIES,
 old_scientific_imports=0, explicit_new_science_source_bindings=True,
 automatic_entries_are_not_theorem_or_external_review_count=True,
 native_read_only_agent_reviews_recorded_separately=True,
 Core_read_only=True, GI_excluded=True, merge_authorized_or_performed=False),
 proof="REVIEW.md")
