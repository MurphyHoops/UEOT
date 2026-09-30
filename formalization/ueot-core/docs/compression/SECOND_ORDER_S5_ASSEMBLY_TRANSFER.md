# Second-Order Structural Defect Compression — S5 Assembly Transfer

Status: **LOCAL LEAN PASS / BRIDGE GENERATIVITY ESTABLISHED / UNCOUNTED**

Baseline counted compression core remains:

\[
\{M\text{-QD-01},M\text{-TC-01},M\text{-PE-01},M\text{-OI-01}\}.
\]

This document records the independent-domain transfer required by S5 of
`SECOND_ORDER_STRUCTURAL_DEFECT_MISSION.md`.  It does **not** claim that the
four-generator basis can be reduced.

## 1. Why control quotient is a valid stress test

The structural-defect hypothesis was inferred from M-QD, M-TC, and M-OI.

The frozen Core v3 control layer is independent of that inference route:

- `ApproxControlQuotient` is the P-QUO-02 approximate finite discounted control
  interface;
- `ExactControlQuotient` is the P-QUO-01 exact control interface;
- `CoreOperationalAssembly.FixedSourceApproximation` is the source-identity
  wrapper used by P-CORE-01.

Therefore a theorem that closes a vanishing approximate-control sequence onto
an exact control quotient is an out-of-sample transfer rather than a rephrasing
of the source families used to discover SDC.

## 2. New Lean module

Module:

`UEOT/V3/Compression/StructuralDefectControlLimit.lean`

The module is imported by `UEOT/V3/Compression.lean` but remains uncounted.

## 3. Fixed-target exactification

The first theorem constructs an `ExactControlQuotient` from one fixed micro
model, quotient map, and macro target when there are certified envelopes

\[
|r_{\rm micro}(x,a)-\bar r(fx,a)|\le \epsilon_r(n),
\]

and

\[
TV(f_\#P_{\rm micro}(\cdot\mid x,a),
   \bar P(\cdot\mid fx,a))\le \epsilon_p(n)
\]

for every `n`, with

\[
\epsilon_r(n)\to0,
\qquad
\epsilon_p(n)\to0.
\]

Lean object:

`exactControlQuotient_of_vanishing_defects`.

The proof does not duplicate P-QUO-01:

1. constant nonnegative defects squeezed by vanishing envelopes are zero;
2. zero finite-PMF TV is converted to PMF equality through the registered
   measure-level zero-TV theorem;
3. PMF equality gives exact fibre transition closure;
4. the resulting data are assembled into `ExactControlQuotient`.

The wrapper

`p_quo_01_of_vanishing_defects`

then calls the existing `ExactControlQuotient.p_quo_01` theorem to obtain exact
value pullback, action-value equality, and optimal-policy lifting.

## 4. P-CORE-01 fixed-source adapter

The theorem

`exactControlQuotient_of_fixedSourceApproximation`

consumes the actual P-CORE-01 interface

`CoreOperationalAssembly.FixedSourceApproximation`.

It assumes:

- fixed micro source;
- fixed quotient map;
- one fixed macro target;
- sample/index-dependent certified radii `εr n`, `εp n` tending to zero;
- all wrappers refer to the same macro target.

It returns an exact control quotient.  The theorem

`p_quo_01_of_fixedSourceApproximation`

then transfers the exact P-QUO-01 conclusions.

This already satisfies the narrow S5 requirement that the second-order layer
operate on an assembly interface not used to infer SDC.

## 5. Convergent estimated macro models

The stronger transfer allows the estimated macro model itself to vary with
`n`.

For each stage let `Q n` be a P-CORE-01 `FixedSourceApproximation` with source
defects

\[
\epsilon_r(n),\qquad \epsilon_p(n).
\]

Let `macroLimit` be a fixed candidate limit model.  Assume additional target
errors

\[
|\widehat r_n(m,a)-\bar r(m,a)|\le \rho_r(n),
\]

\[
TV(\widehat P_n(\cdot\mid m,a),
   \bar P(\cdot\mid m,a))\le \rho_p(n),
\]

with all four envelopes tending to zero.

Triangle inequalities give

\[
|r_{\rm micro}-\bar r|
\le \epsilon_r(n)+\rho_r(n),
\]

and

\[
TV(f_\#P_{\rm micro},\bar P)
\le \epsilon_p(n)+\rho_p(n).
\]

Hence the target model is an exact quotient.

Lean objects:

- `exactControlQuotient_of_convergent_fixedSourceApproximation`;
- `p_quo_01_of_convergent_fixedSourceApproximation`.

This is the strongest current out-of-sample result in the second-order lane.

## 6. What this result does and does not establish

### Established

The compression layer now has genuine generative content beyond the frozen 106
P-IDs:

\[
\text{approximate certified structure}
+
\text{vanishing defect}
+
\text{model convergence}
\Longrightarrow
\text{exact limiting control structure}.
\]

This is directly compatible with Core v3's P-CORE source-identity discipline.

### Not established

The result does **not** show that M-QD, M-TC, or M-OI can be deleted.

- exact M-QD remains more general than the metric defect presentation;
- M-TC remains the independent finite quantitative propagation engine;
- M-OI remains the independent topological/observable invariance closure;
- the control-limit theorem uses elementary scalar/TV closure and P-QUO-01,
  not the full M-OI theorem surface.

Therefore this S5 success upgrades SDC from a speculative pattern to a
**validated second-order bridge architecture**, but not to a counted
second-order generator.

## 7. Current classification

Recommended classification after local Lean validation:

**SECOND-ORDER BRIDGE — GENERATIVE, UNCOUNTED.**

The current four-generator FINAL checkpoint should remain unchanged.

## 8. Next falsifiable question

The next useful test is not another cosmetic wrapper.  It is whether the same
architecture can connect M-PE to the structural core through a normalization or
projective-invariance bridge:

\[
\text{positive eigenstructure}
\xrightarrow{\text{normalization / Doob / projectivization}}
\text{invariant structure}.
\]

If such a bridge only rephrases existing M-PE wrappers, reject it.  If it
generates a new cross-family theorem or materially shortens an existing
generator route, continue to a dedicated feasibility audit.
