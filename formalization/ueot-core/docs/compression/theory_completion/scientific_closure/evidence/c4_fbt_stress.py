#!/usr/bin/env python3
import json
from pathlib import Path

cases=[
  {"name":"exact", "L":1.0,"epsF":0.0,"epsB":0.0,"margin":0.0},
  {"name":"small_defects", "L":1.0,"epsF":0.02,"epsB":0.01,"margin":0.04},
  {"name":"sensitive_binding", "L":4.0,"epsF":0.02,"epsB":0.01,"margin":0.05},
  {"name":"looser_margin", "L":4.0,"epsF":0.02,"epsB":0.01,"margin":0.10},
]
for c in cases:
    c["fbt_upper"] = c["L"]*c["epsF"]+c["epsB"]
    c["certified"] = c["fbt_upper"] <= c["margin"]

out={
  "kind":"FBT_METHOD_STRESS_NOT_REAL_WORLD_IDENTITY_VALIDATION",
  "cases":cases,
  "formation_without_binding_counterexample":{
      "formation_relation":"universal True relation on Bool",
      "formation_transport":"identity / exact",
      "binding0":"constant false",
      "binding1":"constant true",
      "realized_transport":"identity",
      "binding_transport_compatible":False
  },
  "assertions":{
      "exact_certifies":cases[0]["certified"],
      "small_certifies":cases[1]["certified"],
      "sensitive_fails_tight_margin":not cases[2]["certified"],
      "same_sensitive_case_passes_only_looser_margin":cases[3]["certified"],
  }
}
assert all(out["assertions"].values())
Path(__file__).with_name('c4_fbt_stress.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
