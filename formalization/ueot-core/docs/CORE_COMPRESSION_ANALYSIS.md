# UEOT Core v3 — Post-106 Compression Analysis

Status: **active research / meta-formalization**

Baseline:
- frozen Core v3 P-IDs: **106**
- source-theorem ledger: **106/106 FULL-GREEN**
- canonical baseline main: `29d946422f02bb025bd5d450acc434486ecdb422`
- compression live issue: **#146**
- compression branch: `ops/core-compression-v0`

This work does **not** reopen, weaken, or renumber any frozen P-ID.  It asks a
different question: how many mathematically independent generators are really
needed to recover the 106 source theorems?

## 1. Three distinct notions of compression

The project must keep three questions separate.

### 1.1 Proof-dependency compression

Which Lean theorems/imports dominate the actual proof DAG?

This is a code/proof-architecture question.  It can identify highly reused
lemmas, articulation points, and leaf theorems, but by itself it does not reveal
the scientific primitives of UEOT.

### 1.2 Semantic/schema compression

Which source theorems are instances of the same abstract mathematical law after
domain-specific notation is erased?

Examples under active test:
- quotient descent / factorization;
- exact naturality and approximate transport;
- contraction + triangle + additive defect accumulation;
- realization/blocker duality;
- contraction/fixed-point/spectral stabilization;
- variational/information-cost identities.

### 1.3 Scientific-primitive compression

Which concepts must remain primitive in the theory, and which can be defined
from a smaller structure?

The current candidate is a hypothesis to test, not a conclusion:

```
Protocol
  -> Predictive quotient
  -> Realization
  -> Transport
  -> Certificate
```

with a still more compressed candidate:

```
Quotient + Realization + Transport + Certification
```

The Π/Φ layer is **not** assumed to be primitive.  The audit must determine
whether it is a lower-level generator or a valuation/variational adapter built
on top of a more general transport architecture.

## 2. Hard methodological constraints

1. Frozen source semantics remain authoritative.
2. No original P-ID may be rewritten merely to improve apparent compression.
3. A claimed compression must be witnessed by an explicit Lean specialization
   or wrapper.
4. Exact and approximate statements remain distinct.
5. Set-level quotient descent is not silently upgraded to measurable,
   continuous, kernel-valued, or topological descent.
6. Standard mathematics and UEOT-specific bridge structure must be labeled
   separately.
7. Boundary/no-go theorems are first-class results; compression must not erase
   them.
8. No `sorry`, Lean `admit`, `native_decide` bypass, custom axiom, or
   `opaque` escape.

## 3. 106-theorem audit plan

Every frozen P-ID will receive one row with at least:

1. P-ID and frozen source location;
2. canonical Lean theorem and module;
3. exact assumptions and quantifier order;
4. exact conclusion;
5. mathematical universe/scope
   (finite/countable/Standard-Borel/Polish/compact/manifold/continuous-time);
6. direct theorem dependencies;
7. external standard theorem dependencies;
8. candidate semantic schema;
9. classification:
   - kernel,
   - bridge,
   - domain adapter,
   - empirical/statistical certificate,
   - boundary/no-go;
10. downstream P-IDs that depend on it;
11. observable/falsifiable content, if any;
12. whether removing it breaks the proposed minimal generating core.

The source-only seed index is
`CORE_COMPRESSION_THEOREM_INDEX.csv`.  It contains all 106 P-IDs and is the
starting point for the richer source/Lean matrix.

## 4. Candidate generator families to test

These are research hypotheses, not yet established equivalences.

### M1 — quotient descent / factorization

Core pattern:

```
q : X -> Y
g : X -> Z
g constant on fibres of q
--------------------------------
exists unique gbar : Y -> Z
gbar ∘ q = g
```

Candidate reach:
- P-PRED-01;
- P-DYN-01 / P-DYN-02;
- exact control quotients;
- stable-partition quotients;
- structured sufficient-state factorization.

Critical boundary:
set-level factorization does not automatically give a measurable map or
probability kernel.

### M2 — transport/certificate calculus

Core pattern:

```
old defect
   -- non-expansive transport -->
transported old defect
   + fresh local defect
   -- triangle -->
composite defect
```

Finite chains telescope by summing local defects.

Candidate reach:
- P-MET-01;
- P-DYN-03 / P-DYN-04;
- P-ID-01;
- P-STAT-09;
- P-API-01;
- portions of P-FAC-01 and P-CORE-01.

### M3 — realization / destruction duality

Candidate pattern:

```
minimal sufficient realizations
  <-> blocker hypergraph of minimal destructive sets
  <-> resolution transport / adjunction
```

Candidate reach:
- P-CAR-01..04;
- P-RES-01..06;
- P-OMG-01..02;
- carrier-facing composition theorems.

### M4 — operator stabilization

Candidate pattern:
contraction, invariant/fixed-point structure, spectral gap, or positive
operator eigenstructure controls long-time behavior.

Candidate reach:
- P-CTL;
- P-PER / P-QSD / P-GOA;
- portions of P-EVO.

This may split into more than one irreducible generator.

### M5 — variational / information-cost layer

Candidate reach:
- P-KL;
- P-DDH-02/03;
- P-TEL;
- control/action-value variational statements.

The audit must determine whether these really share a generator or merely share
notation.

## 5. Machine-verified compression results so far

### 5.1 M1 quotient descent — GREEN

Module:
`UEOT/V3/Compression/QuotientDescent.lean`

Proved:
- `FiberCompatible`;
- `descend_comp`;
- uniqueness of descended maps;
- exact universal property:
  fibre compatibility iff unique factorization through a surjective
  representation;
- a P-DYN-01 specialization:
  strong lumpability makes the one-step pushed-forward law fibre-compatible;
- therefore a surjective strongly lumpable representation determines a unique
  **set-level** macro one-step law.

Important negative result preserved by the formal interface:
the descended object is `DM -> Measure DM`, not automatically
`Kernel DM DM`.  Measurability remains a separate P-DYN-01 obligation.

### 5.2 M2 transport/certificate calculus — GREEN

Module:
`UEOT/V3/Compression/TransportCertificate.lean`

Proved:
- generic two-stage approximate transport bound;
- exact two-stage composition;
- heterogeneous finite-chain additive defect accumulation;
- P-API-01 approximate composition reconstructed from the generic theorem;
- P-API-01 exact naturality reconstructed from exact composition;
- P-ID-01 pointwise defect accumulation reconstructed from the generic chain
  theorem.

This is the first concrete cross-family compression:

```
P-API-01
P-ID-01
    |
    v
contraction / exact transport
+ triangle
+ local defect
+ finite accumulation
```

The abstraction keeps probability/measurability assumptions in the
specializations rather than pretending the contraction law is unconditional.

## 6. Detailed execution plan

### Phase A — source/Lean matrix

- finish all 106 source rows;
- identify canonical Lean theorem for every P-ID, including the families whose
  source-facing statement is assembled from multiple helper theorems;
- record direct imports and source-facing dependencies.

Exit condition: 106/106 rows have source and Lean identities.

### Phase B — dependency DAG

- parse imports and theorem references;
- distinguish module dependency from theorem dependency;
- compute high-outdegree generators, dominators, articulation points, and
  near-leaf source theorems.

Exit condition: graph is reproducible from repository state.

### Phase C — semantic normalization

For each P-ID, rewrite the theorem into an abstract schema without changing its
quantifier order or scope.  Group only when a concrete map from source theorem
to schema is explicit.

Exit condition: every grouping is labeled
`conjectured`, `partially formalized`, or `Lean-derived`.

### Phase D — minimal generating core v0

Propose a small list `M1 ... Mk` and a coverage map:

```
Mi -> {P-...}
```

Do not optimize theorem count prematurely.  A larger honest kernel is better
than a smaller kernel obtained by hiding domain assumptions.

### Phase E — theorem ablation

For every candidate generator, ask:
- which original theorems stop being derivable if it is removed?
- can it itself be derived from the remaining generators?

This distinguishes a genuine primitive from a convenient lemma.

### Phase F — Lean meta-layer

Create `UEOT.V3.Compression.*` modules only.  Existing source-facing theorem
files remain untouched until a compression wrapper is independently green.

For each meta-theorem:
1. prove generic result;
2. instantiate to at least two existing P-ID families where possible;
3. compare the recovered statement against the frozen source theorem;
4. audit axioms and proof escapes.

### Phase G — wrapper experiment

Only after independent compression theorems are stable, create thin
source-equivalent wrapper proofs in the compression namespace.  Do not replace
the original theorem yet.

The strongest evidence of real compression is that a source theorem can be
re-derived by a short wrapper from the meta-layer.

### Phase H — compression metrics

Report at least:
- theorem coverage by meta-generators;
- number of irreducible domain adapters;
- assumptions eliminated vs assumptions merely relocated;
- standard-math vs UEOT-specific bridge fraction;
- dependency-depth reduction;
- wrapper proof size compared with original proof architecture.

No single scalar “compression ratio” is sufficient.

### Phase I — Core v4 decision gate

Do **not** write a compressed v4 source until the meta-layer demonstrates real
coverage.  v4 is justified only if the new organization is machine-backed and
semantically cleaner than the 106-theorem presentation.

## 7. Current provisional scientific picture

The evidence currently favors the following interpretation:

> UEOT Core is not primarily a collection of 106 independent laws.  A
> significant subset is generated by protocol-relative quotienting,
> realization constraints, functorial/approximate transport, and certificates
> controlling what transport preserves or loses.

The first Lean compression result already supports the transport/certificate
part of this picture across two previously separate source families.  The
remaining project is to determine how far this unification actually extends
before the domain-specific mathematics becomes irreducible.
