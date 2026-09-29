# UEOT Core Compression — Post-Gate-D M-OI Deletion Audit

Status: **EXPERIMENTAL / NOT COUNTED**

Candidate: `M-OI-01 — Occupation-Limit Invariance`

Frozen historical baseline: Gate-D main
`8d0fce85ee6b7a5cfd002894d4d08b82e2bfefb2`.

V2 code checkpoint:
`74f29187b0429707a1a15ef5cbdeba64c0e0d330`.

This audit is deliberately separate from the frozen Gate-C ablation report.
It tests whether the newly formalized post-Gate-D candidate deserves a later
promotion.  It does not mutate the historical ledger or minimal-core claim.

## 1. Deletion question

The proposed nonredundancy witness is **P-GOA-01 only**.

P-PER-02 is excluded as an ablation witness because the frozen source already
contains `PersistenceOccupation.invariant_of_occupation_tendsto`, so the
source theorem remains reconstructible after deleting M-OI.

The deletion question is:

> After removing every M-OI theorem/wrapper and excluding the frozen
> P-GOA-01 endpoint itself, can the pre-registered P-GOA adapter surface reach
> the invariant-cluster-point conclusion without adding a new macro theorem?

This is the same **registered theorem-surface DAG** notion used by the original
Gate-C audit.  It is not a claim of logical independence from Lean/Mathlib.

## 2. Exact witness statement

The witness is the invariant half of frozen P-GOA-01:

```text
forall (nu : stdSimplex R S) (phi : Nat -> Nat),
  StrictMono phi ->
  Tendsto (cesaroRow P hP mu0 o phi) atTop (nhds nu) ->
  Matrix.vecMul nu.1 P = nu.1
```

The experimental wrapper
`p_goa_01_via_occupationLimit` has the same full source-facing signature as
`FiniteCesaroInvariant.p_goa_01`; this equality was mechanically checked by
normalizing the two theorem signatures before this audit.

## 3. Frozen witness-specific adapter surface

The allowed non-M-OI nodes for the P-GOA witness are fixed **before** deletion.

### 3.1 Source/domain nodes

- `FiniteCesaroInvariant.cesaroRow`;
- `FiniteCesaroInvariant.cesaro_residual_eq_boundary`;
- `FiniteCesaroInvariant.boundary_tendsto_zero`;
- `FiniteCesaroInvariant.cesaro_residual_tendsto_zero`.

These nodes construct the finite Cesaro object and establish its vanishing
one-step evolution residual.  They do **not** state that a cluster point is
invariant.

### 3.2 Extraction node

- `CompactSpace.tendsto_subseq` on the finite probability simplex.

This supplies existence of a convergent subsequence only.

### 3.3 Routine side-condition nodes

The following are allowed only as local continuity, coordinate, rewriting, and
extensionality tools:

- `continuous_subtype_val`;
- `Continuous.matrix_vecMul`;
- `continuous_apply`;
- `funext` / subtype coercion simplification;
- composition/specialization of already registered nodes.

They are not registered as a new theorem that consumes
`cluster-point + vanishing residual` and returns invariance.

## 4. Explicitly forbidden deletion shortcuts

When M-OI is deleted, the audit may not:

- call `FiniteCesaroInvariant.p_goa_01`;
- call `p_goa_01_via_occupationLimit`;
- call `finite_invariant_of_cesaro_tendsto`;
- call `observable_invariance_of_residual`;
- call `invariant_of_observable_residual`;
- call `invariant_of_continuous_observable_residual`;
- synthesize a fresh macro proof whose new node is exactly the missing
  continuity/residual/limit-uniqueness-to-invariance bridge.

Routine Mathlib normalization is still allowed around registered nodes.  As in
the original Gate-C audit, writing a new four-line or forty-line replacement
proof after deletion is not an allowed edge: that replacement would itself be
a newly discovered candidate theorem node and would require registration and
promotion before participating in a future ablation.

## 5. Candidate M-OI theorem surface

The v2 reusable theorem is
`invariant_of_continuous_observable_residual`.

It owns the following macro step:

```text
state sequence -> limit
+ separating observables
+ continuity of base observables
+ continuity of evolved observables
+ observable evolution residual -> 0
-------------------------------------------------------
evolved limit = limit
```

For P-GOA-01 the adapter instantiation is:

- `State = S -> R`;
- one evolution label with `advance(mu) = mu P`;
- observables are coordinate evaluations `mu |-> mu(j)`;
- source state convergence comes from the convergent simplex subsequence;
- residual convergence comes from
  `cesaro_residual_tendsto_zero` restricted to that subsequence.

The source-specific Cesaro telescope remains outside M-OI.

## 6. Deletion result under the declared DAG

With M-OI present, the witness is reachable:

```text
CompactSpace.tendsto_subseq
        +
cesaro_residual_tendsto_zero
        +
finite continuity/coordinate adapters
        |
        v
invariant_of_continuous_observable_residual
        |
        v
P-GOA-01 invariant-cluster-point clause
```

After deleting M-OI, the registered surface terminates at:

- a convergent subsequence;
- a vanishing raw evolution residual;
- pointwise continuity facts.

There is no pre-registered non-M-OI theorem node on this witness surface whose
conclusion is `Matrix.vecMul nu.1 P = nu.1` from those inputs.

Therefore the witness is **unreachable in the declared theorem-surface DAG**
after M-OI deletion.

This conclusion is intentionally scoped.  It does **not** say that P-GOA-01 is
logically unprovable without M-OI; Mathlib can of course be used to write a new
limit-uniqueness proof.  The claim is only that such a proof would be a new
macro derivation node, exactly as specified by the historical Gate-C rules.

## 7. Non-cosmeticity remains a separate gate

Passing the declared-DAG deletion test is not sufficient for promotion.

Codex round-1 review correctly observed that the first M-OI theorem was too
close to raw Hausdorff limit uniqueness.  V2 moves continuity passage and
observable separation into the common theorem and routes both P-GOA-01 and
P-PER-02 through that theorem, but independent review must still decide whether
this is enough architectural compression to justify a counted UEOT generator.

Accordingly the present deletion status is:

**SCOPED DAG WITNESS CONSTRUCTED; PROMOTION NOT CLEAR.**

## 8. Promotion rule

M-OI may be promoted only if a fresh independent review returns CLEAR on all
three questions:

1. exact source equivalence of both wrappers;
2. no adapter smuggling or hidden stronger assumptions;
3. v2 common theorem is materially reusable architecture, not merely a renamed
   standard final-step lemma.

Until then, frozen coverage remains **9/106 generated** and the frozen counted
core remains `{M-QD-01, M-TC-01, M-PE-01}`.
