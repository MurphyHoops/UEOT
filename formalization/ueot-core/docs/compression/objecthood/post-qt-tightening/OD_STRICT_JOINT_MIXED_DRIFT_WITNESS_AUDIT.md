# O-D — Strict joint mixed-drift witness audit

Status: **LOCAL PASS**

Track: O

Risk tier: L1 additive, uncounted

Base stage: O-C local commit `03bb104`

## Witness

A finite three-state recurrent-homeostasis system is constructed with states
`low`, `nominal`, and `damaged`.

- `low` and `nominal` are legitimate;
- the repair kernel sends `nominal -> low` and `damaged -> nominal`;
- the fault kernel sends `nominal -> damaged`;
- the potential values are `0, 1, 2`;
- repair drift is `1` and fault hazard is `1/2`.

The system satisfies the existing RH2 repair-side drift premise.

## Strict separation

Lean proves:

- `canonicalFaultBurden = 1`;
- at the standard RH coefficient
  `kappa = (1 - faultHazard) * repairDrift`,
  `canonicalJointMixedDriftResidual = 0`;
- hence
  `canonicalJointMixedDriftResidual < faultHazard * canonicalFaultBurden`.

The strict gain comes from state correlation.  The only positive fault excess
occurs at `nominal`, where the repair row has unused negative drift slack.  The
separated RH/QT envelope discards that correlation; the joint mixed certificate
retains it.

This proves the O-C construction is not a cosmetic reformulation.

## Validation

- focused Lean compile: PASS;
- no `sorry`, `admit`, or new axiom declarations;
- `git diff --check`: PASS;
- counted core impact: NONE.
