# Track S — Dobrushin / residual-isolation separation

Status: **LOCAL CANDIDATE / TRACK S / UNCOUNTED**

Counted-core impact: **NONE**.

## 1. Question

The merged Dobrushin-to-L1 bridge established

`alpha(P) < 1 => kappa1*(P) > 0`.

The immediate scientific pressure test is whether this is merely a
reparameterization of strict mixing, or whether the residual-conorm route
actually covers stable sources that strict Dobrushin contraction excludes.

The required separation witness is a finite stochastic kernel with

`alpha(P) = 1`

but

`kappa1*(P) > 0`.

## 2. Witness

Reuse the already merged deterministic two-state flip

```
P = [0 1
     1 0].
```

Its rows are disjoint point masses, so their total-variation distance is one.
Hence the global Dobrushin coefficient is exactly

`alpha(P) = 1`.

Therefore the strict mixing certificate `alpha(P) < 1` is unavailable.

## 3. Exact residual geometry

For a zero-total-mass signed vector on two states,

`v = (a,-a)`.

The deterministic flip sends

`vP = (-a,a) = -v`.

Thus the residual is exactly

`R_P(v) = vP-v = -2v`,

and therefore

`||R_P(v)||_1 = 2 ||v||_1`.

Lean formalizes this pointwise, not by assuming a pre-existing residual-inverse
constant.

Consequences:

- `kappa = 2` is a valid `ZeroSumL1Isolation` certificate;
- the canonical conorm satisfies `2 <= kappa1*(P)`;
- in particular `kappa1*(P) > 0`.

This checkpoint does not need the exact equality `kappa1*(P)=2`; the strict
positive lower bound is already sufficient for the separation theorem.

## 4. Main separation

The new public theorem proves simultaneously:

- no strict Dobrushin certificate is available, because `alpha(P)=1`;
- the canonical direct-L1 residual conorm remains strictly positive.

Therefore:

**strict Dobrushin mixing is sufficient but not necessary for Track-S residual
isolation.**

This confirms that the residual-inverse/conorm lane genuinely enlarges the
stable source class rather than merely rewriting the M-CF Dobrushin condition.

## 5. End-to-end stability consequence

The checkpoint also feeds the positive isolation certificate into the already
merged canonical stationary-law theorem.  For any finite target stochastic
kernel whose source-to-target row-TV defect is bounded by `epsilon`, Lean
produces a target invariant law `muhat` satisfying

`D_TV(mu*, muhat) <= epsilon / kappa1*(P)`.

Thus the deterministic flip remains quantitatively trackable through the
residual-conorm route even though the ordinary denominator
`1-alpha(P)` vanishes.

## 6. Boundaries

- No claim is made that every kernel with `alpha(P)=1` has positive residual
  conorm.
- No claim is made that Dobrushin mixing and residual isolation are equivalent.
- No exact global classification of nonmixing-but-isolated kernels is claimed.
- This checkpoint does not promote a new generator, primitive, frozen P-ID
  mapping, or counted ledger row.
- Track H is unchanged.

## 7. Next question

After this separation, the next useful Track-S problem is structural rather
than merely existential: characterize a broader computable family of
`alpha(P)=1` kernels with positive residual conorm, or identify matrix/recurrent
geometry that guarantees a positive direct-L1 lower gain without requiring
strict one-step mixing.
