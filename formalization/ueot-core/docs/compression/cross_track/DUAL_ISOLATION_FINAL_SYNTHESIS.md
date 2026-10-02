# Dual Isolation Theory — Local Final Synthesis

Status: **LOCAL CLOSED / IMPLEMENTATION 648a9b65 / FULL VALIDATION PASS / REMOTE FROZEN**

Remote lifecycle: **NOT AUTHORIZED**.

## 1. Central result

The local mission formalizes two independent inverse-stability margins:

`beta_bind` — parent-assembly identifiability from lower-level diagnostics;

`kappa_sem` — long-run semantic isolation of the parent dynamics.

They are linked by the forward parent-realization sensitivity `L_bind`.

The resulting finite-state quantitative theorem is

`semantic diameter <= 2 * L_bind * eta / (beta_bind * kappa_sem)`.

Equivalently, the machine-checked causal/error chain is

`diagnostic error`

-> `inverse binding identification`

-> `assembly error`

-> `forward parent-dynamics realization`

-> `kernel error`

-> `inverse long-run semantic stabilization`.

## 2. DI0 — lower-gain identifiability certificate

`BindingIsolation diagnostic beta` requires only

`beta > 0`

and

`beta * dist(a,b) <= dist(D a,D b)`.

It implies diagnostic injectivity and converts one diagnostic uncertainty ball
of radius `eta` into assembly diameter at most `2 eta / beta`.

No long-run conclusion is encoded in the certificate.

## 3. DI1 — dual-isolation semantic theorem

`dualIsolation_pairwiseSemanticBound` and
`dualIsolation_fiberSemanticDiameter_normalized` compose:

- DI0 binding isolation;
- Parent-Binding `ParentBindingLipschitz`;
- Track-S `l1ResidualConorm` isolation.

The normalized fibre-wide result is

`fiberSemanticDiameter <= 2 * L * eta / (beta * kappaMin)`.

## 4. DI2 — canonical finite beta

For finite nontrivial metric assembly spaces,

`bindingIsolationConorm(D)`

is the minimum distinct-pair diagnostic gain.

Lean proves

`bindingIsolationConorm(D) > 0 <-> Function.Injective D`,

and proves that this canonical value is the greatest admissible binding
isolation constant.

This makes the binding side structurally parallel to the Track-S canonical
semantic residual conorm without identifying the two mechanisms.

## 5. DI3 — canonical dual-isolation theorem

`canonicalDualIsolation_fiberSemanticDiameter` replaces a supplied finite
`beta` with the canonical binding conorm whenever the diagnostic is injective:

`semantic diameter <=`

`2 * L * eta / (bindingIsolationConorm(D) * kappaMin)`.

## 6. DI4 — independence no-go

`semanticIsolation_does_not_imply_bindingIsolation` proves that positive
semantic isolation cannot replace binding isolation.

The explicit witness has stable, isolated parent kernels and maximally
separated invariant semantics, while a constant lower-level diagnostic admits
no positive binding-isolation margin.

Thus the two denominator factors encode genuinely distinct failure modes.

## 7. DI5 — exact P-RES-06 branch

P-RES-06 endpoint collapse gives exact microscopic realization on active
coarse fibres.

`resolutionEndpointCollapse_parentSemanticDiameter_zero` composes that frozen
resolution theorem with Parent Binding and Track S to obtain exact zero
semantic diameter for the corresponding parent fibre.

This is a real source-facing exact identifiability mechanism, not a newly
assumed `beta`.

## 8. DI6 — quantitative P-CAR-04 branch

P-CAR-04's optimal decoder radius `r` controls within-readout-fibre assembly
diameter by `2 r`.

`decoderRadius_parentSemanticDiameter` therefore gives

`semantic diameter <= 2 * L * r / kappaMin`.

This turns an existing retained adapter into a quantitative parent-semantic
certificate.

## 9. DI7 — dynamic observational exactification

If a shared diagnostic error radius `eta_n -> 0`, while positive binding
isolation and a uniform positive semantic-isolation floor persist, then

`lawTV(mu(thetaBar n), mu(theta n)) -> 0`.

This observational route is complementary to the Parent-Binding M-TC route;
neither route is claimed to subsume the other.

## 10. DI8 — sharp benchmark

The explicit two-completion benchmark proves:

`beta_bind = 1`,

`L_bind = 1`,

`kappa_sem = 1`,

`eta = 1/2`,

and actual semantic TV `= 1`.

The theorem returns upper bound `1`, so the complete constant chain is attained
with equality on this witness.

## 11. DI9 — P-MET-01 realization bridge

No unconditional `L_bind <= 1` theorem is promoted for arbitrary parent
kernels.

Instead the local continuation introduces

`CommonMarkovParentRealization`.

For models satisfying its explicit factorization guard, P-MET-01 proves row-TV
nonexpansion and automatically constructs Parent Binding with

`L_bind = 1`.

This yields:

- `dualIsolation_commonMarkov_pairwiseSemanticBound`;
- `dualIsolation_commonMarkov_fiberSemanticDiameter`;
- `canonicalDualIsolation_commonMarkov_fiberSemanticDiameter`.

In the canonical finite case the bound becomes

`semantic diameter <=`

`2 eta / (bindingIsolationConorm(D) * kappaMin)`.

The sharp two-completion benchmark is also realized through the identity
Markov channel, and its exact unit bound is preserved.  Thus the P-MET bridge
is not only abstractly well typed; it has a nontrivial exact instance.

## 12. Architecture verdict

Dual Isolation is a **new uncounted bridge calculus**, not a new G0 primitive.

The four counted generators remain

`{M-QD-01, M-TC-01, M-PE-01, M-OI-01}`.

Nothing in this mission supports:

- 4 -> 5;
- 4 -> 3;
- a universal parent constructor;
- automatic diagnostic injectivity;
- automatic decay of observational error;
- automatic `L_bind <= 1` without a realization-factorization guard;
- Objecthood, objective, fitness, or selection semantics from binding alone.

## 13. Scientific meaning

The strongest justified interpretation is:

> a higher-level parent is observationally well identified only when the
> lower-level diagnostic has positive binding isolation, and its long-run
> semantics is stable only when the induced parent dynamics also has positive
> semantic isolation.

Failure of either margin is a distinct obstruction.

## 14. Local validation

Original Dual-Isolation implementation:

`648a9b65ce006d8717d559383010105a749a30f8`.

P-MET realization extension:

`116231f229129da0c43423efbdcc3f405aa11ddb`.

Validation on the extended implementation:

- public `UEOT.V3.Compression.CrossTrack`: **PASS**;
- full `lake build UEOT`: **PASS (9093 jobs)**;
- research-track governance: **PASS (24 changed paths relative to remote
  canonical base, including the preceding local Parent-Binding closure)**;
- research-governance regression suite: **PASS**;
- frozen Compression live-reference validator: **PASS**;
- Compression validator regression suite: **PASS**;
- source/final accounting: **106/106**;
- counted generators: **4**;
- unresolved: **0**;
- proof-escape scan: **PASS**;
- `git diff --check`: **PASS**;
- public theorem axiom audit: only
  `propext / Classical.choice / Quot.sound`;
- remote branch
  `compression/cross-track-dual-isolation-local`: **absent**.

Two validator-regression invocations during this local research sequence
encountered transient GitHub API read failures while checking historical FINAL
metadata (one TLS handshake timeout and one failed PR metadata read). Both were
retried without code changes, and the complete regression suite passed. These
were external-read transients, not theorem or ledger failures.

## 15. Closure outcome

**LOCAL CONDITIONAL CLOSURE: PASS.**

The abstract double inverse-stability chain, canonical finite binding margin,
independence boundary, exact/quantitative source specializations, dynamic
observational convergence route, sharp finite benchmark, and P-MET
common-channel realization bridge are all formally closed.

The remaining scientific work is domain construction: derive the diagnostic
and `beta_bind` from actual lower-level interaction laws; prove a valid
realization factorization for the parent kernel; and connect the identified
parent to constitutive Omega-loop persistence.  In domains satisfying the
common-Markov factorization, `L_bind` no longer needs to be separately fitted
or assumed.
