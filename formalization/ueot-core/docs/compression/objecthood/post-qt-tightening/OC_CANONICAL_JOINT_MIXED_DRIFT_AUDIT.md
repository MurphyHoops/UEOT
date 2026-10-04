# O-C — Canonical joint mixed-drift audit

Status: **LOCAL PASS**

Track: O

Risk tier: L1 additive, uncounted

Base stage: O-A/O-B local commit `de5d966`

## Result

For every finite `RecurrentHomeostasisSystem` and fixed damaged-occupation
coefficient `kappa`, define the statewise positive mixed-drift excess

`(E_mixed W + kappa * 1_damaged - W)_+`

and take its finite carrier supremum. The resulting
`canonicalJointMixedDriftResidual S kappa` satisfies:

1. it directly certifies the carrier-wise mixed-drift inequality;
2. it is the least uniform residual among all constants satisfying that same
   fixed-`kappa` inequality;
3. it is finite whenever the potential is finite on the carrier and `kappa` is
   finite;
4. at the existing RH coefficient
   `kappa = (1 - faultHazard) * repairDrift`, it is no larger than
   `faultHazard * C.burden` for every RH1 fault certificate `C` satisfying the
   existing repair-side drift premise;
5. therefore it is no larger than the QT canonical envelope
   `faultHazard * canonicalFaultBurden S`.

This is a strictly stronger optimization target than QT in formulation: QT
canonicalizes the fault coordinate before mixing, while O-C canonicalizes the
actual mixed one-step inequality consumed by the occupation telescope.

## Boundary

No strict separation is claimed yet in O-C. A finite witness is required before
calling the new residual scientifically non-cosmetic.

No pathwise recurrence or phase-transition necessity is inferred.

## Validation

- focused Lean compile: PASS;
- `git diff --check`: PASS;
- proof-escape scan: CLEAR;
- counted core impact: NONE.
