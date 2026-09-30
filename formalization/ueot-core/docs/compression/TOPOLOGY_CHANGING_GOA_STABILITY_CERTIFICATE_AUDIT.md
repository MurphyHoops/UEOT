# Topology-Changing GOA Stability Certificate Audit

Status: **LOCAL LEAN PASS / POSITIVE STABILITY CERTIFICATE FORMALIZED / UNCOUNTED**

Module:

`UEOT/V3/Compression/TopologyChangingGoaStabilityCertificate.lean`

## 1. Motivation

The topology-changing GOA lane established an explicit two-state recurrent
merge in which arbitrarily small entrywise kernel perturbations leave one
prescribed source invariant law at TV distance exactly `1/2` from every target
invariant law.

That result is directional: it rules out lower/Hausdorff-type continuity or any
bound required to approximate **every prescribed source invariant law** across
an unrestricted topology bifurcation.  It does not show that all stationary-law
continuity notions fail.

The present module asks the corresponding positive question:

> Which explicit source-side certificate is already strong enough to recover
> quantitative tracking of a prescribed invariant law even if target recurrent
> topology is allowed to change?

## 2. Source contraction is sufficient

`prescribedInvariant_tracked_of_dobrushin` assumes:

- finite stochastic source kernel `P`;
- finite stochastic target kernel `Q`;
- source Dobrushin coefficient `alpha(P) < 1`;
- a prescribed source invariant law `mu`;
- uniform row-TV defect

\[
\sup_x D_{TV}(P_x,Q_x)\le\varepsilon.
\]

It proves there exists a target invariant law `muhat` such that

\[
\boxed{
D_{TV}(\mu,\hat\mu)
\le
\frac{\varepsilon}{1-\alpha(P)}.
}
\]

The proof uses exactly the existing architecture:

1. frozen P-GOA-01 supplies target invariant-law existence;
2. M-CF / `stationary_perturbation_via_mcf` supplies the perturbation bound;
3. only the **source** operator needs a strict contraction margin.

No common recurrent partition is assumed.  The target is not required to have
the same recurrent classes or even to be Dobrushin-contractive itself.

## 3. Set-valued lower tracking

`invariantLawSet_lower_tracking_of_dobrushin` packages the same result in the
direction directly relevant to the earlier no-go:

\[
\boxed{
\forall\mu\in\mathcal I(P),\;
\exists\hat\mu\in\mathcal I(Q):
D_{TV}(\mu,\hat\mu)
\le
\frac{\varepsilon}{1-\alpha(P)}.
}
\]

Thus strict source contraction restores precisely the source-to-target
lower-tracking direction that failed at the topology bifurcation.

Because `alpha(P) < 1` also gives source invariant-law uniqueness, this theorem
does not hide a branch-selection ambiguity on the source side.

## 4. The no-go source sits exactly at the boundary

The two-state source kernel used by the bifurcation counterexample is

\[
P_0=
\begin{pmatrix}
1&0\\
0&1
\end{pmatrix}.
\]

`twoStateSource_rowTV_zero_one` proves its two rows have TV distance exactly
one.

`twoStateSource_dobrushinAlpha_le_one` proves the universal finite probability
upper bound

\[
\alpha(P_0)\le1.
\]

Combining the lower and upper bounds,
`twoStateSource_dobrushinAlpha_eq_one` proves

\[
\boxed{\alpha(P_0)=1.}
\]

Therefore `twoStateSource_not_dobrushin_contractive` proves that the no-go
example cannot satisfy the positive certificate.

The negative and positive results are consequently compatible and meet at a
machine-checked boundary:

\[
\alpha(P)<1
\quad\Longrightarrow\quad
\text{quantitative prescribed-law tracking},
\]

while the explicit topology-bifurcation witness occurs at

\[
\alpha(P)=1.
\]

## 5. Architectural interpretation

This lane is another post-compression bridge, not a fifth generator.

It combines:

- M-OI / P-GOA-01 for invariant existence;
- M-CF for fixed-point perturbation;
- the topology-changing GOA no-go lane as the boundary pressure test.

The result shows why the bridge network is scientifically useful: it does not
merely classify old theorems, but lets a negative result immediately identify
which pre-existing structural certificate restores a positive theorem.

## 6. Scope discipline

The current result proves a **sufficient** certificate only.

It does **not** prove:

- that Dobrushin contraction is necessary;
- that `alpha(P) < 1` is the weakest possible assumption;
- full Hausdorff continuity of invariant-law sets;
- continuity through arbitrary split/merge bifurcations without a stability
  certificate;
- target recurrent topology preservation.

In particular, other weaker certificates may exist, for example local spectral
gaps, isolated stationary branches, or class-restricted contraction structures.
Those require separate formalization rather than being inferred from the
present theorem.

## 7. Next pressure test

The next scientifically useful question is whether strict global Dobrushin
contraction can be weakened while still tracking one prescribed stationary
branch.

The safest next candidates are:

1. **local/branch isolation:** a stationary law is isolated by a quantitative
   fixed-point inverse or spectral-gap certificate;
2. **carrier-restricted contraction:** contraction only on the recurrent carrier
   supporting the selected branch rather than on the entire state space;
3. **two-sided set stability:** if both source and target have uniform
   contraction margins, derive a genuine symmetric/Hausdorff-style invariant-
   law bound.

These should be investigated in that order, and any claimed weakening must be
proved rather than described heuristically.

No frozen theorem, counted generator, P-ID disposition, or ledger count is
changed by this lane.
