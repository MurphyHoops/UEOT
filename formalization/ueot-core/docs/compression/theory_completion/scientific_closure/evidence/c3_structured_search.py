#!/usr/bin/env python3
import json
from pathlib import Path

def first_good_nested(defects, tolerance):
    for i, d in enumerate(defects):
        if d <= tolerance:
            return i
    return None

rows=[]
for n in [8, 16, 24, 32]:
    rows.append({
        "components": n,
        "powerset_candidates": 2**n,
        "nested_candidates": n+1,
        "ratio": (n+1)/(2**n),
    })

# Nested monotone special case: only last 3 candidates are good.
defects=[0.30,0.22,0.15,0.10,0.07,0.04,0.02]
first=first_good_nested(defects,0.05)

# Frame/noise example: same abstract ordered candidates but a physical-coordinate
# perturbation moves the first certified point. This is a boundary witness, not
# a theorem about all physical frames.
noisy=[0.31,0.23,0.17,0.12,0.08,0.055,0.025]
first_noisy=first_good_nested(noisy,0.05)

out={
  "kind":"METHOD_BENCHMARK_NOT_GENERAL_ALGORITHM",
  "complexity_table":rows,
  "nested_example":{"defects":defects,"tolerance":0.05,"first_good_index":first},
  "frame_noise_example":{"defects":noisy,"tolerance":0.05,"first_good_index":first_noisy},
  "assertions":{
      "restricted_search_not_powerset": all(r["nested_candidates"] < r["powerset_candidates"] for r in rows),
      "nested_first_good": first==5,
      "frame_can_change_selected_index": first_noisy!=first,
  }
}
assert all(out["assertions"].values())
p=Path(__file__).with_name('c3_structured_search.json')
p.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
