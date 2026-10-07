#!/usr/bin/env python3
import json
from pathlib import Path

# Registered toy mechanism-observation examples.  This is a semantic stress test,
# not a claim about a natural system.
examples = {
  "unfaithful_constant_observation": {
    "observations": {"m0":"same","m1":"same"},
    "orderings": {"m0":["false<true"],"m1":["true<false"]},
    "faithful": False
  },
  "faithful_class_observation": {
    "observations": {"m0":"class_A","m1":"class_A"},
    "orderings": {"m0":["false<true"],"m1":["false<true"]},
    "faithful": True
  }
}

out={
  "kind":"SEMANTIC_METHOD_STRESS_NOT_REAL_WORLD_PURPOSE_IDENTIFICATION",
  "examples":examples,
  "gates":{
    "G1_mechanism_observation_identified":"required",
    "G2_contract_representation":"required",
    "G3_bellman_or_causal_faithfulness":"required",
    "G4_object_viability":"required"
  },
  "assertions":{
    "same_raw_observation_can_fail_teleological_identification":
      not examples["unfaithful_constant_observation"]["faithful"],
    "faithful_bridge_targets_ordering_class":
      examples["faithful_class_observation"]["faithful"]
  }
}
assert all(out["assertions"].values())
Path(__file__).with_name('c6_purpose_bridge_stress.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
