# UEOT Core Compression — Post-Gate-D Expanded-Core Ablation Audit

Status: **INDEPENDENT REVIEW CLEAR / PRE-INTEGRATION / NOT COUNTED**

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

## 0. Full retained M-OI theorem surface

When one of the historical generators is deleted, M-OI is *retained* in the
candidate enlarged core.  Therefore the deletion DAG must admit the complete
public theorem/definition surface of
`Compression/OccupationLimitInvariance.lean`, not only its preferred canonical
theorem.

Mechanical declaration enumeration at experiment head `baf8987` gives exactly
**9 public theorem declarations + 1 public definition**:

- `equal_at_limit_of_residual`;
- `observable_invariance_of_residual`;
- `invariant_of_observable_residual`;
- `invariant_of_continuous_observable_residual`;
- `finite_invariant_of_cesaro_tendsto`;
- `p_goa_01_via_occupationLimit`;
- `fellerAdvancePM`;
- `fellerAdvancePM_toMeasure`;
- `feller_invariant_of_occupation_tendsto`;
- `p_per_02_via_occupationLimit`.

These nodes fall into three typed interface groups.

### 0.1 Abstract residual/observable nodes

`equal_at_limit_of_residual`, `observable_invariance_of_residual`,
`invariant_of_observable_residual`, and
`invariant_of_continuous_observable_residual` consume convergence,
continuity/separation data and an asymptotically vanishing evolution residual.
They conclude equality/invariance of a limiting state.  They do not construct:

- quotient maps or measurable decoders;
- finite-horizon multiplicative product recurrences;
- eigenvectors/eigenvalues;
- filtrations, conditional expectations, martingales, or integrability data.

### 0.2 Finite-Cesaro nodes

`finite_invariant_of_cesaro_tendsto` and
`p_goa_01_via_occupationLimit` specialize the abstract mechanism to a finite
row-stochastic matrix and its Cesaro averages.  Their conclusions concern an
invariant probability row for the *same* finite Markov kernel.  Their premises
and conclusions contain no quotient/factorization interface, path-TV
certificate recurrence, or reproductive-value martingale calculus.

### 0.3 Feller-occupation nodes

`fellerAdvancePM`, `fellerAdvancePM_toMeasure`,
`feller_invariant_of_occupation_tendsto`, and
`p_per_02_via_occupationLimit` specialize the same mechanism to Feller
occupation measures.  They construct/evaluate Markov-kernel pushforward on
probability measures and prove invariant weak occupation limits (plus the
P-PER-02 support clause in the full wrapper).  They do not create quotient
descent, finite multiplicative coupling certificates, or right-eigenvector
martingale structure.

### 0.4 Composition check against the three historical witnesses

The full M-OI surface is now admitted in each historical deletion experiment,
including arbitrary composition with the other retained counted generators and
registered witness adapters.

For **P-PRED-01**, no M-OI output supplies the missing countable family of
almost-everywhere factorization maps, common conull set, or measurable product
decoder.  Feeding an invariant probability law produced by the finite/Feller
wrappers into M-TC or M-PE still does not create a quotient map or a
fibre-compatible decoder; both remaining generators require their own typed
transport/eigenstructure inputs.

For **P-DYN-03**, no M-OI output supplies the finite-horizon recurrence
`1 - product(1-epsilon_t)` or any pathwise TV/common-mass accumulation.  The
finite-Cesaro wrapper concerns asymptotic averaging for one Markov kernel, and
the Feller wrapper concerns weak occupation limits; composing either with M-QD
or M-PE does not manufacture the missing exact finite product recurrence.

For **P-EVO-04**, no M-OI output supplies a positive right eigenvector,
eigenvalue, conditional-mean reproduction identity, adapted process,
integrability proof, or martingale/constant-expectation conclusion.  An
invariant probability law from the M-OI specializations cannot be converted by
M-QD or M-TC into the missing positive-eigenstructure stochastic calculus.

Thus the reachability statements in §§1–3 below are made against the **entire
retained M-OI module surface**, not merely
`invariant_of_continuous_observable_residual`.

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

The full retained M-OI surface is the 10-node surface frozen in §0.  None of
those nodes has a quotient map, fibre-compatibility relation, countable family
of exceptional sets, measurable decoder construction, or common-null-set
theorem in its conclusion or a route to construct one from the registered
P-PRED adapters.

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

The full retained M-OI surface is admitted.  Its abstract and specialized
finite/Feller nodes provide neither:

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

The full retained M-OI surface concludes deterministic/topological invariance
of finite/Feller long-run limits.  P-EVO-04 instead requires a stochastic one-step
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

Independent Codex review has returned CLEAR/no-major-issues for the M-OI
non-cosmeticity/deletion surface at `69919a22...` and for this expanded-core
audit at `9a6f29d...`.

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

The candidate four-generator set now has independently reviewed scoped deletion
witnesses for every member:

```text
{M-QD-01, M-TC-01, M-PE-01, M-OI-01}
```

with the permitted claim:

```text
nonredundant_under_declared_derivation_system
```

This remains architectural minimality relative to the declared theorem-surface
DAG, not absolute model-theoretic or logical independence.

This review CLEAR authorizes a **promotion attempt**, not an automatic ledger
rewrite.  Until the dedicated integration lifecycle and resulting-main/ledger
CI complete, the official current counted core remains the historical
three-generator set and official generated coverage remains 9/106.
