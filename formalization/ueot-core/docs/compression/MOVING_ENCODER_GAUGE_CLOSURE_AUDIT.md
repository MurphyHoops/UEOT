# Moving Encoder Gauge Closure — Audit

Status: **LOCAL LEAN PASS / EVENTUAL EXACT REPRESENTATION LOCK ESTABLISHED / UNCOUNTED**

Baseline counted Core compression remains unchanged:

\[
\{M\text{-QD-01},M\text{-TC-01},M\text{-PE-01},M\text{-OI-01}\}.
\]

Module:

`UEOT/V3/Compression/MovingEncoderGaugeClosure.lean`

This lane tests whether occupation-weighted approximate representation
convergence can close back onto exact M-QD quotient identity.

## 1. Setting

Let the finite source be `X`, the quotient carrier be one finite type `S`, and
fix one source law

\[
\mu\in\Delta(X).
\]

Let

\[
C_*:X\to S
\]

be a fixed reference encoder and

\[
C_n:X\to S
\]

be a sequence of moving encoders.

All encoders are assumed surjective.

The representation error is the occupation-weighted quotient gauge

\[
d_{G,\mu}(C_n,C_*),
\]

which already minimizes over quotient-state relabelings.

## 2. Finite positive gap

For one finite source law define

\[
m_\mu=\min_{x\in X}\mu(x).
\]

Lean definitions/theorems:

- `sourceMasses`;
- `minSourceMass`;
- `minSourceMass_mem`;
- `minSourceMass_le`.

Under full support,

\[
\mu(x)>0\quad\forall x,
\]

the theorem `minSourceMass_pos` proves

\[
m_\mu>0.
\]

## 3. Nonzero gauge mismatch has a finite cost floor

If one chosen relabeling fails at any source point, its weighted mismatch is at
least `m_mu`:

\[
e(qx)\neq r(x)
\Longrightarrow
m_\mu\le m_{e,\mu}(q,r).
\]

Lean theorem:

`minSourceMass_le_weightedMismatch_of_mismatch`.

Minimizing over all relabelings gives the discrete gap theorem

\[
d_{G,\mu}(q,r)\neq0
\Longrightarrow
m_\mu\le d_{G,\mu}(q,r).
\]

Lean theorem:

`minSourceMass_le_weightedGaugeMismatch_of_ne_zero`.

This theorem itself does not need full support.  If `m_mu = 0`, it is simply a
weak lower bound.  Full support becomes essential only when we need a strictly
positive threshold.

## 4. Falling below the gap forces exact zero

The theorem

`weightedGaugeMismatch_eq_zero_of_lt_minSourceMass`

proves

\[
d_{G,\mu}(q,r)<m_\mu
\Longrightarrow
d_{G,\mu}(q,r)=0.
\]

This is a finite/discrete exactification phenomenon: once representation drift
falls below the least mass of any source atom, there is no room for even one
remaining positive-mass partition mismatch.

## 5. Main moving-encoder theorem

Assume full support and

\[
d_{G,\mu}(C_n,C_*)\to0.
\]

Because `m_mu > 0`, convergence implies that eventually

\[
d_{G,\mu}(C_n,C_*)<m_\mu.
\]

Therefore eventually

\[
d_{G,\mu}(C_n,C_*)=0.
\]

The full-support zero theorem from `WeightedQuotientGauge` then gives

\[
\boxed{
\exists N,\ \forall n\ge N,
\operatorname{SameFibers}(C_n,C_*)
}.
\]

Lean theorems:

- `eventually_sameFibers_of_weightedGaugeMismatch_tendsto_zero`;
- `exists_eventual_exact_gauge_lock`.

Thus the moving encoder does not merely converge to the reference partition in
a numerical sense.  It eventually enters the exact quotient-gauge class and
remains there.

## 6. Relation to M-QD

The theorem closes an approximate representation path back onto the exact
M-QD identity notion:

\[
\text{weighted gauge drift}\to0
\Longrightarrow
\text{eventual exact SameFibers}.
\]

This is another M-QD-derived exactification interface, not a new generator.

Recommended classification:

**MOVING REPRESENTATION EXACTIFICATION OVER M-QD: PASS, UNCOUNTED.**

## 7. Why the result is stronger than ordinary metric convergence

In a continuous metric space, convergence to zero normally gives only smaller
and smaller error.

Here the representation space modulo finite relabeling has a discrete positive
gap under one full-support finite source law.  Nonzero weighted mismatch cannot
be arbitrarily small: it costs at least the least positive source mass.

That discreteness upgrades convergence into **eventual exact identity**.

## 8. Essential boundaries

### Finite source is essential to the present proof

The positive gap is obtained from a finite minimum.  For infinite source
spaces, positive point masses can tend to zero and no uniform gap need exist.

### Fixed full-support law is essential

The theorem uses one fixed `mu` with

\[
\inf_x\mu(x)>0.
\]

If the comparison law varies with `n`, or if its minimum mass tends to zero,
weighted mismatch may converge to zero while a structural mismatch keeps
moving into lower-mass states.  Eventual global gauge lock then need not follow.

### Same quotient carrier in the current theorem

All `C_n` and `C_*` map into the same finite carrier `S`.  Label gauge is still
optimized internally, but quotient dimension is fixed.  Split/merge events are
not covered.

### Surjectivity is required for exact SameFibers interpretation

The gauge distance itself can be computed without surjectivity, but the final
exact relation is stated through the M-QD quotient-gauge theorem for surjective
encoders.

### No semantic/control exactness yet

Eventually identical fibres do not by themselves imply reward closure,
transition closure, optimal-value equality, or GOA equality.

Those require separate semantic defect hypotheses.  This theorem only locks the
representation partition.

## 9. Compression significance

The representation side now has a complete finite chain:

\[
\text{exact quotient gauge}
\to
\text{approximate gauge distance}
\to
\text{occupation-weighted gauge}
\to
\text{moving-encoder convergence}
\to
\text{eventual exact quotient identity}.
\]

This is a genuine new consequence of the post-FINAL compression architecture:
the M-QD quotient notion acts as both the exact endpoint and the zero-set
structure around which approximate representation dynamics can be organized.

The counted four-generator core remains unchanged.

## 10. Next pressure test — semantic transfer after gauge lock

The next theorem should combine this exact representation lock with the
existing history-encoder semantic defects.

A clean target is:

1. `C_n` eventually has the same fibres as `C_*`;
2. within-fibre reward/encoded-transition defects of `C_n` vanish;
3. use exact fibre identity to transfer those semantic defects to the reference
   partition;
4. feed the transferred defects into `HistoryEncoderExactClosure`;
5. obtain an exact control quotient for `C_*` and P-QUO-01 exact control
   consequences.

The technically nontrivial part is transition semantics: pushforward laws under
two gauge-equivalent quotient labels must be compared through the induced
finite equivalence.  That bridge should be formalized explicitly rather than
treated as obvious label invariance.
