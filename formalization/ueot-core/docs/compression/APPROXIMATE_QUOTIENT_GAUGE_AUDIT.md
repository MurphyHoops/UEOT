# Approximate Quotient Gauge — Finite Representation Distance Audit

Status: **LOCAL LEAN PASS / APPROXIMATE REPRESENTATION GAUGE ESTABLISHED / UNCOUNTED**

Baseline counted Core compression remains unchanged:

\[
\{M\text{-QD-01},M\text{-TC-01},M\text{-PE-01},M\text{-OI-01}\}.
\]

This audit extends the exact M-QD-derived `QuotientGauge` result to finite
representations that are not exactly equal up to relabeling.

Module:

`UEOT/V3/Compression/ApproximateQuotientGauge.lean`

## 1. Problem

Two learned or moving encoders can represent nearly the same partition of one
source while using unrelated quotient-state labels.  Directly comparing the
raw labels `q x` and `r x` is therefore coordinate-dependent.

The exact `QuotientGauge` theorem already proves that two surjective encoders
with identical fibres are uniquely equivalent up to quotient-state relabeling.
The approximate question is:

> after optimizing over all finite relabelings, how many source points still
> disagree?

## 2. Relabeling mismatch

For finite source `X`, encoders

\[
q:X\to Y,
\qquad
r:X\to Z,
\]

and one equivalence `e : Y ≃ Z`, define

\[
m_e(q,r)=\#\{x\in X:e(qx)\neq r(x)\}.
\]

Lean definition:

`mismatchCount q r e`.

The theorem `mismatchCount_eq_zero_iff` proves

\[
m_e(q,r)=0\iff e\circ q=r.
\]

## 3. Gauge mismatch

When the finite quotient carriers have the same cardinality, define

\[
d_G(q,r)=\min_{e:Y\simeq Z}m_e(q,r).
\]

Lean definition:

`gaugeMismatch q r`.

Because the relabeling space is finite, `exists_optimalEquiv` proves that an
optimal alignment is attained.

## 4. Exact-zero characterization

`gaugeMismatch_eq_zero_iff_exists_equiv` proves

\[
d_G(q,r)=0
\iff
\exists e:Y\simeq Z,\ e\circ q=r.
\]

For surjective encoders, exact `QuotientGauge` then gives

\[
\boxed{d_G(q,r)=0\iff\operatorname{SameFibers}(q,r)}.
\]

Lean theorem:

`gaugeMismatch_eq_zero_iff_sameFibers`.

Thus zero approximate gauge mismatch recovers the old exact quotient structure,
not merely a weaker zero-radius certificate.

## 5. Symmetry

Inverse relabeling preserves mismatch count:

\[
m_{e^{-1}}(r,q)=m_e(q,r),
\]

so

\[
\boxed{d_G(q,r)=d_G(r,q)}.
\]

Lean theorems:

- `mismatchCount_symm`;
- `gaugeMismatch_symm`.

## 6. Triangle inequality

If `e : Y ≃ Z` and `f : Z ≃ W`, every source point that fails the composite
alignment `f ∘ e` must fail the first or second component alignment.  Hence

\[
m_{f\circ e}(q,s)\le m_e(q,r)+m_f(r,s).
\]

Minimizing over optimal component alignments yields

\[
\boxed{d_G(q,s)\le d_G(q,r)+d_G(r,s)}.
\]

Lean theorems:

- `mismatchCount_trans_le`;
- `gaugeMismatch_triangle`.

Together with `gaugeMismatch_self`, this makes `gaugeMismatch` a
**pseudometric-like finite representation distance modulo relabeling**.

It is not installed as a Mathlib `PseudoMetricSpace`: compared encoders may
have different finite codomain types, and the distance is currently `Nat`.

## 7. Relation to M-QD

This is downstream of M-QD, not a new counted generator.

M-QD supplies exact quotient descent.  Exact `QuotientGauge` uses that universal
property to identify same-fibre quotients up to unique relabeling.  The present
lane adds a finite combinatorial distance around the exact zero set.

Recommended classification:

**M-QD-DERIVED APPROXIMATE REPRESENTATION GAUGE: PASS, UNCOUNTED.**

## 8. Scientific meaning

For learned/moving effective-state encoders, quotient labels are gauge.  The
scientific structure is the source partition they induce.  The new distance
answers:

> after the best possible label alignment, how many source points still change
> effective-state membership?

This separates:

1. **pure gauge drift:** labels changed only, so `d_G = 0`;
2. **structural representation drift:** fibre membership changed, so `d_G > 0`.

That separation is a prerequisite for meaningful moving-encoder convergence.

## 9. Essential boundaries

### Equal quotient cardinality

The first construction minimizes over equivalences `Y ≃ Z`.  Split/merge moves
that change quotient dimension require correspondences, partial matchings, or
transport plans and are not covered.

### Unweighted source count

Every source point contributes one unit.  Rare and high-occupancy states are
treated equally.

### No control guarantee from gauge mismatch alone

Small `d_G` does **not** imply small reward error, transition-TV error, value
loss, or GOA displacement.  One mismatched source state can carry arbitrarily
large decision relevance unless additional boundedness/weighting assumptions
are provided.

Therefore `gaugeMismatch` must not be fed directly into a near-GOD or near-GOA
claim.

### No statistical learning theorem

The encoders are supplied.  There is no estimation or generalization theorem.

### Exact versus almost-sure zero

The unweighted finite count sees every source point, so zero means exact global
alignment.  A future occupation-weighted version may imply only almost-sure
alignment unless the weighting law has full support.

## 10. Compression significance

The post-FINAL representation/control chain is now:

\[
\text{exact quotient gauge}
\to
\text{approximate gauge distance}
\to
\text{encoder fibre defects}
\to
\text{approximate control quotient}
\to
\text{near-GOD / near-GOA}
\to
\text{vanishing-defect exactification}.
\]

This strengthens the interpretation of M-QD as the anchor of a
representation-stability layer.  It still does not justify changing the
four-generator count.

## 11. Next pressure test

The strongest immediate extension is an occupation-weighted gauge mismatch

\[
d_{G,\mu}(q,r)
=
\min_e\mu\{x:e(qx)\neq r(x)\}.
\]

That construction would distinguish high-occupancy drift from negligible
drift and connect naturally to M-OI occupation laws.

A subsequent moving-encoder theorem should:

1. gauge-align each encoder to a reference representation;
2. bound representation drift in the weighted gauge;
3. separately bound aligned reward/transition defects;
4. feed only the certified dynamical/control defects into M-TC.

This separation prevents arbitrary coordinate drift from being mistaken for
physical or decision-relevant change.
