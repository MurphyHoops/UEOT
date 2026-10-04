# O-E/O-G — Joint mixed-drift downstream closure audit

Status: **LOCAL PASS**

Track: O

Risk tier: L1 additive, uncounted

Base stages: O-C `03bb104`, O-D `7340801`

## Result

The canonical joint mixed-drift residual is now consumed directly by the generic
RH3/RH4 telescope and Cesaro machinery.

For any positive finite `kappa`:

1. finite-horizon damaged occupation is bounded by
   `initialPotential + N * canonicalJointMixedDriftResidual`;
2. asymptotic mean damaged occupation is bounded by
   `canonicalJointMixedDriftResidual.toReal / kappa.toReal`;
3. every convergent Cesaro subsequence has an invariant limit whose damaged mass
   is bounded by the same ratio;
4. an invariant Cesaro cluster point with that bound exists by the existing
   P-GOA/M-OI compactness adapter.

At the standard RH choice
`kappa = (1 - faultHazard) * repairDrift`, the final real ratio is proved no
larger than the prior QT canonical ratio based on
`faultHazard * canonicalFaultBurden`.

An Objecthood mean-homeostasis specialization is included. The RH4 theorem is
kept at the generic recurrent-homeostasis level rather than adding a redundant
specialized wrapper; instantiating the generic theorem with the Objecthood
system gives the same result.

## Scientific interpretation

The old RH/QT pipeline is a separable worst-case relaxation. The new theorem
optimizes the exact statewise mixed inequality actually used by the occupation
telescope. Together with the O-D strict witness, this establishes a genuine
state-coupled quantitative strengthening of RH3/RH4.

## Boundaries

- no pathwise recurrent-legitimacy theorem is inferred;
- no necessary phase-transition threshold is claimed;
- `kappa` is fixed in this cycle; optimization over `kappa` is deliberately not
  introduced before the fixed-`kappa` gain is fully audited;
- counted core impact: NONE.

## Validation

- focused Lean compile: PASS;
- proof-escape scan: CLEAR;
- `git diff --check`: PASS.
