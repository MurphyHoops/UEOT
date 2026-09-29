# UEOT Core Compression — Post-Gate-D Expanded-Core Ablation Audit

Status: **EXPERIMENTAL / PRE-PROMOTION / NOT COUNTED**

Candidate enlarged core under test:

```text
{M-QD-01, M-TC-01, M-PE-01, M-OI-01}
```

Historical Gate-D core:

```text
{M-QD-01, M-TC-01, M-PE-01}
```

This document does not change the frozen ledger.  It answers a necessary
minimality question that arises only if M-OI later clears its independent
promotion review: adding a generator changes every *remaining-core* deletion
set, so the three historical nonredundancy witnesses must be rechecked with
M-OI available.

The derivation-system rules are exactly those in historical
`COMPRESSION_ABLATION.md`: canonical theorem surfaces of all remaining counted
generators, already registered source/domain adapters, specialization,
composition, definitional reduction, equality rewriting, and routine Mathlib
side conditions are allowed.  A fresh macro theorem that reconstructs the
deleted primitive is not an existing edge.

## 1. Remove M-QD-01

Remaining candidate core:

```text
{M-TC-01, M-PE-01, M-OI-01}
```

Historical witness: **P-PRED-01**.

Required missing primitive:

- countable almost-everywhere family descent through one representation;
- construction of one common conull set;
- one measurable product decoder for the countable protocol family.

Retained historical P-PRED-01 adapters remain:

- `PredictionAE.aeFactors_sigmaLE`;
- `PredictionDependent.coordinateKernel`;
- supplied measurable coordinate kernels and their protocolwise a.e.
  factorizations.

### M-OI reachability check

M-OI consumes:

- a convergent state sequence;
- continuous separating observables;
- continuous evolved observables;
- a vanishing asymptotic evolution residual.

It concludes invariance of the limiting state under an evolution map.  It has
no quotient map, fibre-compatibility relation, countable family of exceptional
sets, measurable decoder construction, or common-null-set theorem.

Therefore adding M-OI creates no edge to the P-PRED-01 quotient/descent
witness.  M-TC and M-PE were already audited in historical Gate C and remain
irrelevant to countable a.e. descent.

Result under the enlarged declared DAG:

```text
M-QD-01: nonredundant_under_declared_derivation_system
broken witness: P-PRED-01
remaining generators: {M-TC-01, M-PE-01, M-OI-01}
```

## 2. Remove M-TC-01

Remaining candidate core:

```text
{M-QD-01, M-PE-01, M-OI-01}
```

Historical witness: **P-DYN-03**.

Required missing primitive:

- multi-step multiplicative certificate recurrence producing the sharp
  `1 - product(1-epsilon_t)` path-TV control.

Retained historical source adapters remain the finite-PMF common-mass and
one-step TV/coupling facts recorded in `COMPRESSION_ABLATION.md`.

### M-OI reachability check

M-OI is asymptotic/topological limit invariance.  It provides neither:

- finite-horizon multiplicative survival accumulation;
- a product recurrence;
- path coupling/common-mass propagation;
- a replacement for `multiplicative_chain_lower_bound`.

Its residual tends-to-zero premise cannot manufacture the finite exact product
certificate required by P-DYN-03, and P-DYN-03 has no long-run cluster-point
premise to which M-OI could specialize.

M-QD and M-PE remain unable to supply the historical missing recurrence.

Result under the enlarged declared DAG:

```text
M-TC-01: nonredundant_under_declared_derivation_system
broken witness: P-DYN-03
remaining generators: {M-QD-01, M-PE-01, M-OI-01}
```

## 3. Remove M-PE-01

Remaining candidate core:

```text
{M-QD-01, M-TC-01, M-OI-01}
```

Historical witness: **P-EVO-04**.

Required missing primitive:

- positive right-eigenstructure readout;
- transport of the Perron right eigenrelation through conditional-mean
  reproduction;
- normalized reproductive-value martingale;
- nonnegativity, integrability, adaptedness bundle and constant expectation.

### M-OI reachability check

M-OI concludes deterministic/topological invariance of a limit from continuous
observable residuals.  P-EVO-04 instead requires a stochastic one-step
conditional-expectation identity at every finite time and uses a positive
right eigenvector to normalize the process into a martingale.

M-OI contains no:

- conditional expectation operator;
- filtration/adaptedness interface;
- integrability theorem;
- positive eigenvector/eigenvalue data;
- martingale or constant-expectation conclusion.

Converting the reproductive process to a limit-invariance problem would add
new convergence assumptions absent from frozen P-EVO-04 and still would not
recover its finite-time martingale bundle.  Thus M-OI cannot replace M-PE on
the historical witness.

M-QD and M-TC remain unable to generate the right-eigenvector stochastic
calculus, as recorded by historical Gate C.

Result under the enlarged declared DAG:

```text
M-PE-01: nonredundant_under_declared_derivation_system
broken witness: P-EVO-04
remaining generators: {M-QD-01, M-TC-01, M-OI-01}
```

## 4. Remove M-OI-01

Remaining candidate core:

```text
{M-QD-01, M-TC-01, M-PE-01}
```

Candidate witness: **P-GOA-01** invariant-cluster-point clause.

The exact witness-specific adapter surface, all theorem/definition nodes of the
remaining counted core, and the detailed reachability analysis are frozen in:

`POST_GATE_D_M_OI_ABLATION.md`.

That audit records that:

- the finite source surface supplies Cesaro construction, compact subsequence
  extraction and vanishing raw evolution residual;
- M-QD has quotient/factorization structure but no limit-invariance bridge;
- M-TC has finite transport/defect recurrences but no limit-invariance bridge;
- M-PE's superficially related `invariantWeight_stationary` requires positive
  bi-eigenstructure and proves stationarity for a Doob transform, assumptions
  and target kernel not supplied by P-GOA-01;
- after M-OI deletion no registered node consumes the P-GOA cluster-point,
  continuity and vanishing-residual data to produce `nu P = nu`.

Provisional result under the enlarged declared DAG:

```text
M-OI-01: nonredundant_under_declared_derivation_system
broken witness: P-GOA-01
remaining generators: {M-QD-01, M-TC-01, M-PE-01}
```

This fourth result remains conditional on independent CLEAR review of the M-OI
non-cosmeticity and deletion-surface audit.

## 5. Pairwise/substitution sanity check

The four witness mechanisms occupy distinct typed interfaces:

| generator | witness | missing primitive under deletion |
|---|---|---|
| M-QD-01 | P-PRED-01 | countable a.e. quotient descent / common measurable decoder |
| M-TC-01 | P-DYN-03 | finite multiplicative certificate recurrence |
| M-PE-01 | P-EVO-04 | positive-eigenvector stochastic martingale calculus |
| M-OI-01 | P-GOA-01 | continuous-observable asymptotic residual -> invariant limit |

No candidate theorem surface supplies another row's typed primitive without
introducing new assumptions or a new macro theorem node.

## 6. Expanded-core conclusion

If, and only if, M-OI independently clears promotion review, the candidate
four-generator set has a complete scoped deletion witness for every member:

```text
{M-QD-01, M-TC-01, M-PE-01, M-OI-01}
```

with the permitted claim:

```text
nonredundant_under_declared_derivation_system
```

This remains architectural minimality relative to the declared theorem-surface
DAG, not absolute model-theoretic or logical independence.

Until promotion lifecycle and resulting-main/ledger CI complete, the official
frozen core remains the historical three-generator set and official generated
coverage remains 9/106.
