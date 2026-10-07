# C2 Minimal Data Dictionary

Status: **FROZEN FOR LOCAL METHOD BENCHMARK**

Every C2 run record must contain at least:

| Field | Meaning |
|---|---|
| `run_id` / `episode_id` | immutable run identity |
| `timestamp` / `step` | ordering inside the run |
| `protocol_version` | frozen protocol definition used for the sample |
| `action` | applied intervention/action |
| `allocation_probability` | assignment probability when randomized; otherwise explicit deterministic marker |
| `raw_observation` | unencoded observation used to recompute estimators |
| `candidate_encoder_version` | registered representation/candidate family version |
| `declared_future` | future response variable and horizon being certified |
| `intervention_cost` | declared cost/unit, if used |
| `error_or_fault_label` | registered fault/measurement flag, never silently dropped |
| `split` | `discovery`, `certification`, or `holdout` |
| `missing_reason` | explicit reason for missing data |

## Hard rules

1. discovery and certification run IDs are disjoint;
2. candidate/protocol selection freezes before certification data are inspected;
3. low protocol/action coverage produces `UNCERTIFIED`, not imputation-based success;
4. the registered candidate universe is finite in C2; no claim is made to have
   discovered every possible real-world object;
5. a β-mixing or other dependence radius is model input/evidence, not inferred
   merely from the number of raw time points;
6. drift is a separate bias radius and is never absorbed into the sampling
   radius without provenance.
