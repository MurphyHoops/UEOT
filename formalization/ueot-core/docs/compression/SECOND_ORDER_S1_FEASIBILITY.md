# Second-Order Structural Defect Compression — S1 Feasibility Audit

Status: **EXPERIMENTAL / S1 UNDER AUDIT / NO GENERATOR REPLACEMENT CLAIM**

Baseline counted core:
\[
\{M\text{-QD-01},M\text{-TC-01},M\text{-PE-01},M\text{-OI-01}\}.
\]

Candidate second-order layer:
\`UEOT.V3.Compression.StructuralDefectClosure\`.

This audit asks one narrow question:

> Can the second-order structural-defect layer make at least two existing
> counted generator surfaces materially thinner **without strengthening their
> assumptions or merely moving the old proofs into a new namespace**?

A negative answer is scientifically acceptable and leaves the candidate as a
bridge architecture.

## 1. M-QD-01

Canonical low-level surface:

- \`FiberCompatible\`;
- \`descend\`;
- \`descend_comp\`;
- \`existsUnique_descend\`;
- \`fiberCompatible_of_comp_eq\`;
- \`fiberCompatible_iff_existsUnique_descend\`.

### Essential generality

The canonical M-QD theorem is purely set-level:

\[
q:X\to Y,\qquad g:X\to Z,
\]

with **arbitrary codomain** \(Z\).  Exact fibre constancy plus surjectivity is
enough for unique descent.  No topology, metric, measurability, probability,
or continuity is assumed.

The present SDC asymptotic theorem requires a metric codomain in order to state
a numerical fibre defect and its convergence to zero.

Therefore replacing the canonical M-QD theorem by the current SDC theorem
would strengthen the theorem from arbitrary \(Z\) to metric \(Z\), violating
S1.

### Current S1 verdict for M-QD

**NO REPLACEMENT.**

SDC can *feed* M-QD by proving \`FiberCompatible\` in an asymptotic metric
setting, but M-QD remains the strictly more general exact descent endpoint.

Correct relation:

\[
\text{SDC asymptotic certificate}
\Longrightarrow
\text{M-QD fibre compatibility}
\Longrightarrow
\text{unique descent}.
\]

This is bridge composition, not compression of M-QD.

## 2. M-TC-01

Canonical quantitative core includes:

- \`twoStage_bound\`;
- \`chain_bound\`;
- \`weighted_chain_bound\`;
- \`multiplicative_chain_lower_bound\`.

The strongest generic additive/weighted theorem handles heterogeneous stage
types and stage-dependent local amplification:

\[
\delta_n
\le
\left(\prod_{j<n}L_j\right)\delta_0+
\sum_{k<n}\epsilon_k\prod_{k<j<n}L_j.
\]

### Dependency direction in the current SDC experiment

The theorem

\`fiber_dist_tendsto_zero_of_weighted_transport\`

calls \`TransportCertificate.weighted_chain_bound\` directly.

Hence the current second-order layer does not derive or shorten the M-TC
recurrence; it consumes it.

Moving the weighted recurrence proof into SDC would not by itself constitute
compression.  It would merely rename or relocate the existing M-TC primitive
unless a smaller theorem simultaneously removed proof obligations elsewhere.

### Current S1 verdict for M-TC

**NO REPLACEMENT YET.**

The new layer establishes an important composition rule:

\[
\text{M-TC finite certificate}
+
\text{certificate envelope}\to0
\Longrightarrow
\text{asymptotic zero defect}.
\]

But M-TC remains the quantitative propagation engine.

## 3. M-OI-01

Canonical reusable core:

\`invariant_of_continuous_observable_residual\`.

It owns:

- convergence of the state sequence;
- continuity of base observables;
- continuity of evolved observables;
- separating observables;
- vanishing observable evolution residual;
- exact invariance of the limiting state.

The new theorem

\`invariant_of_weighted_observable_transport\`

is designed to call that M-OI theorem after deriving its residual premise from
an M-TC weighted certificate.

Thus the current dependency is:

\[
M\text{-TC}
\Longrightarrow
\text{residual}\to0
\Longrightarrow
M\text{-OI}
\Longrightarrow
\text{limit invariance}.
\]

### Current S1 verdict for M-OI

**NO REPLACEMENT YET.**

The second-order theorem supplies a new route into M-OI but does not reduce the
topological/observable closure obligations already owned by M-OI.

## 4. Immediate second-order conclusion

At the present theorem surface, the candidate does **not** justify

\[
\{M\text{-QD},M\text{-TC},M\text{-OI}\}
\longrightarrow
\{M2\text{-SDC}\}.
\]

What is supported is a directional composition architecture:

\[
M\text{-TC}
\to
\begin{cases}
\text{asymptotic fibre compatibility}
  \to M\text{-QD},\\
\text{asymptotic observable residual}
  \to M\text{-OI}.
\end{cases}
\]

This is already a substantive second-order relationship, but it is a
**BRIDGE** unless S1 later changes.

## 5. Why a naive common abstraction would be cosmetic

One can define a generic structure containing:

1. a defect function;
2. a finite recurrence bound;
3. a topology in which zero defect is closed.

Such a record would syntactically contain M-TC and M-OI, but unless it removes
duplicated proof obligations it is only a product packaging of the existing
generators.

Likewise, imposing a metric on M-QD solely to make it fit the same record would
destroy the arbitrary-codomain exact theorem and is forbidden.

Therefore a future S1 PASS requires more than a common record or common name.

## 6. Remaining route that could change S1

There is one legitimate route left to test.

Construct a lower-level theorem on a **relation with a separately supplied
defect presentation**:

- the exact relation itself is structure-free;
- a metric/observable defect is only an optional certificate that presents
  approximation to that relation;
- finite transport acts on the certificate;
- topological closure turns vanishing certificate into exact relation.

If this relation-level theorem can:

1. recover M-QD exact descent without imposing metric structure on \(Z\);
2. materially shorten M-OI's observable closure theorem;
3. use M-TC recurrence without merely copying it;

then S1 may reopen.

At present there is no Lean evidence that all three conditions can hold
simultaneously.

## 7. Recommended disposition if current result survives review

If the current M-TC->M-QD and M-TC->M-OI composition theorems compile and pass
independent review, classify SDC as:

**SECOND-ORDER BRIDGE ARCHITECTURE / NOT A GENERATOR REPLACEMENT.**

Then move effort to S5:

- demonstrate a new independent assembly theorem;
- test approximate-to-exact quotient/control closure;
- test whether M-PE can enter via a normalization/projective bridge.

Only reopen generator-count reduction if those new results expose a genuinely
smaller theorem surface.
