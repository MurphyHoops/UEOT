# Primitive Reward / Automatic Value-Span Closure Audit

Status: **LOCAL PASS**

Track: S

Risk tier: L1 additive, uncounted

Canonical base: `main@3cbec434411980af701d0342bbdd9531e1a9a813`

## Scientific result

The former moving-GOA closure required an externally supplied uniform bound on
all moving macro optimal-value spans.  This stage derives that control from
primitive quotient data instead.

For any finite discounted model whose actual rewards satisfy `|r| <= R`, Lean
proves

`|V*(s)| <= R / (1 - beta)`

and hence

`span(V*) <= 2 R / (1 - beta)`.

For approximate quotients sharing one literal micro model, surjectivity and the
primitive reward approximation imply

`|r_macro,n| <= R_micro + epsilonReward_n`.

Therefore each moving macro model has the explicit span envelope

`span(V*_n) <= 2 (R_micro + epsilonReward_n) / (1 - beta)`.

Substituting this state-independent envelope into the existing P-QUO radius
bound gives an explicit primitive upper bound for `D_n`.  If
`epsilonReward_n -> 0` and `epsilonTransition_n -> 0`, the upper bound tends to
zero and Lean proves

`D_n -> 0`

without any external uniform-span hypothesis.

## Significance

This removes a genuine auxiliary hypothesis from the moving representation/GOA
pipeline.  The value-span control is not independent data once the quotients
share a finite micro model and primitive reward defects vanish.

## Boundary

The conclusion still uses a common literal micro model and a fixed discount.
It does not cover sequences whose underlying micro dynamics/reward model itself
changes.

No counted generator or frozen source theorem is modified.

## Validation

- focused Lean compile: PASS;
- proof-escape scan: CLEAR;
- `git diff --check`: PASS;
- counted core impact: NONE.
