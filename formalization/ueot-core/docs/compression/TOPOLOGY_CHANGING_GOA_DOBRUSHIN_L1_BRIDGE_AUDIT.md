# Topology-Changing GOA Dobrushin-to-L1 Residual Bridge Audit

Status: **LOCAL CANDIDATE / TRACK S / UNCOUNTED**

Module:

`UEOT/V3/Compression/TopologyChangingGoaDobrushinL1Bridge.lean`

## 1. Purpose

Two quantitative stability routes are already present in the merged library:

1. the M-CF / finite-Dobrushin route, where a stochastic source kernel with
   `alpha(P) < 1` yields TV contraction and the standard stationary perturbation
   radius

   \[
   \frac{\varepsilon}{1-\alpha(P)};
   \]

2. the Track-S direct-residual route, where the canonical zero-mass L1 conorm

   \[
   \kappa_1^*(P)
   \]

   yields the kernel-specific stationary radius

   \[
   \frac{\varepsilon}{\kappa_1^*(P)}.
   \]

Before this checkpoint, these were parallel sufficient-certificate APIs. This
checkpoint proves a direct bridge between them.

## 2. Sharp signed-L1 extension of Dobrushin contraction

The existing theorem `tv_step_le_dobrushin` is stated for two probability
simplex laws. The bridge extends it to every real zero-total-mass signed vector
without losing a factor:

\[
\boxed{
\|vP\|_1
\le
\alpha(P)\,\|v\|_1,
\qquad
\sum_x v_x=0.
}
\]

The Lean theorem is `signedL1_vecMul_le_dobrushin`.

The proof uses the finite Jordan-style decomposition already available from
ordered real arithmetic:

- write `v = v^+ - v^-`;
- zero total mass implies equal positive and negative masses;
- for `v != 0`, normalize `v^+` and `v^-` to two simplex laws `nu` and `mu`;
- then `v = c (nu - mu)` and `D_TV(mu,nu)=1`;
- apply the existing exact Dobrushin simplex contraction;
- rescale back to signed L1.

No new stochastic theorem is postulated and no factor `2` is lost.

## 3. Residual lower gain from contraction

For the residual

\[
R_P(v)=vP-v,
\]

signed-L1 triangle inequality gives

\[
\|v\|_1
\le
\|vP\|_1+\|R_Pv\|_1.
\]

Combining this with the signed Dobrushin contraction yields

\[
\boxed{
(1-\alpha(P))\|v\|_1
\le
\|R_Pv\|_1.
}
\]

This is formalized as `one_sub_dobrushin_signedL1_le_residual`.

Hence strict Dobrushin contraction gives an explicit direct-L1 residual
certificate:

\[
\boxed{
\alpha(P)<1
\Longrightarrow
\operatorname{ZeroSumL1Isolation}(P,1-\alpha(P)).
}
\]

## 4. Canonical conorm dominates the Dobrushin margin

On a nontrivial finite state space (`1 < card S`), the merged canonical-conorm
optimality theorem then implies

\[
\boxed{
1-\alpha(P)
\le
\kappa_1^*(P).
}
\]

This is `one_sub_dobrushin_le_l1ResidualConorm`.

Consequently, for every nonnegative perturbation envelope,

\[
\boxed{
\frac{\varepsilon}{\kappa_1^*(P)}
\le
\frac{\varepsilon}{1-\alpha(P)}.
}
\]

So the canonical direct-L1 residual certificate recovers the standard
Dobrushin stationary radius and may improve it using finer kernel geometry.

## 5. End-to-end stationary tracking

Under the same source assumptions used by the Dobrushin lane:

- `P` row stochastic;
- `alpha(P) < 1`;
- a prescribed invariant source law `muStar`;
- target stochastic kernel `Q`;
- rowwise source-target TV defect at most `epsilon`;
- nontrivial finite state space;

`canonical_l1_stationary_tracking_of_dobrushin` proves existence of a target
invariant law `muhat` with

\[
\boxed{
D_{TV}(\mu_*,\hat\mu)
\le
\frac{\varepsilon}{\kappa_1^*(P)}.
}
\]

Together with the previous comparison, this canonical radius is no worse than
`epsilon/(1-alpha(P))` under the exact same Dobrushin source margin.

## 6. Structural interpretation

This bridge identifies the relation between the two stability languages:

- Dobrushin `alpha(P)` measures **forward contraction** of law differences;
- the canonical residual conorm measures **invertibility/minimum gain** of
  `I-P` on the zero-mass signed-law space;
- strict forward contraction automatically creates residual invertibility with
  margin at least `1-alpha(P)`.

Thus M-CF/Dobrushin contraction is a sufficient quantitative source for the
Track-S residual-inverse certificate.

## 7. Boundaries retained

- Strict Dobrushin contraction is **not claimed necessary** for residual
  isolation. A kernel may have `alpha(P)=1` while `I-P` remains injective with a
  positive zero-mass L1 conorm.
- No claim is made that `kappa_1^*(P)=1-alpha(P)` for every kernel.
- No uniform strict improvement over the Dobrushin radius is claimed; only
  `canonical radius <= Dobrushin radius` is proved.
- The signed-L1 contraction theorem requires row stochasticity because it is
  derived from the existing finite Dobrushin theorem.
- No frozen P-ID, counted mapping, generator count, ledger row, or Track-H
  theorem changes.

## 8. Next pressure test

A high-value separation test is to formalize a finite stochastic kernel with

\[
\alpha(P)=1
\quad\text{but}\quad
\kappa_1^*(P)>0.
\]

A two-state deterministic flip/permutation is the natural candidate. If it
passes, it will formally prove that residual isolation is strictly weaker than
strict Dobrushin mixing and therefore genuinely enlarges the stable source
class rather than merely reparameterizing M-CF.
