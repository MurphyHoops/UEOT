# SISC v2 — observed-protocol nonvacuity gate

Status: **PROVED FINITE BOUNDARY**, not a claim of general identifiability.

## Why this is scientifically important

The positive SI-3 theorem uses

`FormedByResponse actual predict tau x p := ∀ observed_coordinate j, ...`.

Formal proofs remain valid when the coordinate type is *empty*; then every
candidate satisfies formation, regardless of response semantics or tolerance.
`empty_protocol_forms_every_candidate` exhibits this exact failure mode.
An empty protocol can therefore make a mathematically correct "formation
certificate" entirely evidentially empty. The missing condition must not be
silently supplied by informal talk of 'measurements'.

With `[Nonempty Obs]`, `formed_has_nonnegative_budget` derives `tau ≥ 0`
from any formed witness, but nonemptiness **alone** does not establish
discrimination. Candidate response separation, protocol causal coverage,
pre-registration and missingness remain distinct conditions.

## Upgrade to scientific use

Future SI-3/C4 empirical adapters MUST record the observation protocol,
nonempty registered measurement coordinates, intervention coverage,
candidate universe and a margin against distinct competing parent responses.
Observed data should be allowed to return `UNRESOLVED` when those conditions
fail. No generic proof may treat a vacuous `∀ j` as physically useful
formation evidence.
