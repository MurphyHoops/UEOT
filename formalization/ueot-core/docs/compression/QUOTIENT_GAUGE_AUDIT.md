# Quotient Gauge Audit — Exact Representations Up to Relabeling

Status: **LOCAL LEAN PASS / M-QD-DERIVED GAUGE INTERFACE / UNCOUNTED**

Module:

`UEOT/V3/Compression/QuotientGauge.lean`

This lane addresses a structural issue that appears as soon as one tries to
compare a sequence of effective-state encoders.

Two encoders may represent exactly the same quotient structure while using
different state labels.  Any convergence or stability statement that compares
raw labels directly is therefore coordinate-dependent unless a relabeling
gauge has first been fixed.

## 1. Exact same-fibre relation

For two surjective maps

\[
q:X\to Y,
\qquad
r:X\to Z,
\]

define `SameFibers q r` by

\[
q(x)=q(x')
\Longleftrightarrow
r(x)=r(x')
\quad\forall x,x'.
\]

This says the two encoders induce exactly the same partition of the source.

It does **not** say their labels are equal or even live in the same type.

## 2. M-QD generates both directions

If the fibres agree, then:

- `r` is fibre-compatible with `q`, so M-QD descends `r` through `q`;
- `q` is fibre-compatible with `r`, so M-QD descends `q` through `r`.

These two descended maps are inverse because both recover the original source
representations on every represented point.

`quotientEquiv` packages the two descents as a genuine equivalence

\[
e:Y\simeq Z.
\]

## 3. Gauge transport identity

The theorem

`quotientEquiv_comp`

proves the exact transport identity

\[
e\circ q=r.
\]

Thus one encoder is literally the other encoder after quotient-state
relabeling.

No source point, fibre, or quotient identity is changed.

## 4. Uniqueness

`quotientEquiv_unique` shows that any other equivalence carrying `q` to `r`
has the same forward map as the M-QD-generated relabeling.

The main characterization is

`sameFibers_iff_existsUnique_equiv`:

\[
\boxed{
\text{SameFibers}(q,r)
\Longleftrightarrow
\exists!\,e:Y\simeq Z, e\circ q=r
}
\]

for surjective representations.

This is a set-level quotient uniqueness theorem: an exact quotient object is
unique up to unique relabeling once its source fibres are fixed.

## 5. Why this matters for moving encoders

Suppose an encoder sequence `C_n` and a reference encoder `C_*` induce the same
source partition but choose different labels.

Raw statements such as

\[
C_n(h)=C_*(h)
\]

are unnecessarily strong and depend on arbitrary coordinates.

The gauge-invariant statement is instead:

\[
\exists!\,e_n,
\qquad
e_n\circ C_n=C_*.
\]

The present theorem supplies exactly this normalization whenever the fibres
agree.

Therefore any future moving-encoder convergence theorem should distinguish:

1. changes in the underlying quotient partition;
2. pure state relabelings of the same quotient;
3. control/model defects after the representations are gauge-aligned.

## 6. Relation to M-QD

This is not a new generator.

The proof is entirely built from the existing M-QD surface:

- fibre compatibility;
- surjective descent;
- factorization identity;
- uniqueness of descended maps.

The new value is architectural: M-QD now controls not only whether quantities
descend through one representation, but also the exact equivalence relation
between two representations of the same quotient object.

## 7. Scientific boundary

### Exact fibres only

`SameFibers` is exact.  It does not define a distance between two nearby but
nonidentical partitions.

### No approximate relabeling theorem

If encoder fibres differ slightly, there may be no bijection carrying one
encoder exactly to the other.  An approximate matching theorem would need an
additional defect notion and probably a transport/assignment argument.

### No topology on quotient types

The theorem is set-level and makes no continuity, measurability, metric, or
probability claim about the quotient-state equivalence.

### Labels are gauge; fibres are structure

The theorem supports treating quotient labels as representational gauge in the
exact set-level theory.  It does not imply that every downstream semantic
structure is invariant under arbitrary relabeling unless that structure is
transported along the equivalence as well.

## 8. Compression disposition

Recommended classification:

**M-QD-DERIVED REPRESENTATION GAUGE THEOREM: PASS, UNCOUNTED.**

This result strengthens the conceptual interpretation of the current minimal
core without changing the four-generator count.

It also prevents a likely future mistake: declaring two changing encoders
different merely because their quotient-state labels differ.

## 9. Next pressure test

The next nontrivial problem is **approximate quotient gauge**.

A useful theorem would need to separate:

- fibre mismatch or partition defect;
- relabeling/assignment ambiguity;
- reward/transition defects after alignment.

Only after such an alignment layer is explicit does a moving-encoder limit
become scientifically interpretable rather than coordinate-dependent.

One possible route is to define a finite matching cost between quotient states
from source-fibre overlap and then ask whether M-TC can propagate aligned
control defects.  That is a new research question; it is not established by
the exact theorem here.
