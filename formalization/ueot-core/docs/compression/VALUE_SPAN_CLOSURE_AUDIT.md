# Value-Span Closure Audit

Status: **LOCAL LEAN PASS / PRIMITIVE DEFECT-TO-`D` CLOSURE ESTABLISHED / UNCOUNTED**

Module:

`UEOT/V3/Compression/ValueSpanClosure.lean`

This lane removes the last externally supplied convergence certificate from the
moving-encoder optimal-policy GOA chain.

Previously the end-to-end theorem assumed

\[
D_n\to0,
\]

where the P-QUO global radius is

\[
D_n
=
\frac{
\epsilon_r(n)+\beta_n\epsilon_p(n)\,\operatorname{span}(V_n^*)
}{1-\beta_n}.
\]

The explicit assumption was necessary because
`epsilon_r(n) -> 0` and `epsilon_p(n) -> 0` alone do not control a potentially
diverging optimal-value span.

## 1. Common micro semantics fixes the discount

`macroDiscount_eq_ref_of_commonMicro` proves that if the reference quotient and
one moving quotient describe the same literal micro control model, then their
macro discounts agree.  Hence the moving family has one fixed

\[
0<\beta<1.
\]

No additional discount-convergence hypothesis is introduced.

## 2. Uniform span gives an explicit `D` upper bound

Assume one finite constant `C` satisfies

\[
\operatorname{span}(V_n^*)\le C
\]

for every moving macro model.  `D_le_of_span_le` proves

\[
D_n
\le
\frac{
\epsilon_r(n)+\beta\epsilon_p(n)C
}{1-\beta}.
\]

The proof uses only:

- the exact P-QUO definition of `D`;
- nonnegativity of the transition defect and discount;
- the common-micro discount identity;
- the supplied uniform span bound.

There is no hidden reward/model closeness assumption beyond the existing
approximate quotient certificates.

## 3. Primitive defects now imply `D_n -> 0`

`D_tendsto_zero_of_uniform_span` combines the preceding bound with

\[
\epsilon_r(n)\to0,
\qquad
\epsilon_p(n)\to0
\]

to derive

\[
\boxed{D_n\to0}.
\]

Thus `D_n -> 0` is no longer an independent asymptotic hypothesis in the
uniform-span regime.

## 4. Moving optimal-policy GOA theorem no longer needs supplied `D` convergence

`eventually_existsUnique_optimalPolicyNearGoaGaugeAt_of_uniformSpan` combines:

- weighted representation gauge convergence;
- finite full-support eventual exact fibre lock;
- one common literal micro model;
- exact reference reward/transition defects;
- moving reward/transition defects tending to zero;
- one uniform moving optimal-value span bound;
- a positive source action gap;
- source greedy closed-loop Dobrushin contraction.

It derives `D_n -> 0` internally and then invokes the already checked
action-gap / moving-GOA bridge.  Eventually there is one unique quotient gauge
under which the target's own canonical greedy policy is the transported source
greedy policy and the target invariant structure lies in the certified GOA
tube.

## 5. Fully primitive tail closure

`eventually_optimalPolicyNearGoa_arbitrarily_close_of_uniformSpan` additionally
uses transition-defect convergence to obtain, for every `eta > 0`, eventually

\[
R_{GOA}(n)<\eta.
\]

The resulting chain is now

\[
\boxed{
\text{representation gauge}\to0
\to
\text{eventual exact fibre gauge}
\to
\text{primitive semantic defects}\to0
\to
D_n\to0
\to
\text{greedy-policy lock}
\to
\text{GOA radius}\to0.
}
\]

Within the stated finite/common-micro/uniform-span/Dobrushin regime, no separate
`D_n -> 0` certificate is left to the caller.

## 6. Relation to the four-generator core

No counted generator is added or removed, and no frozen P-ID is reclassified.

This is a post-FINAL bridge theorem using existing P-QUO semantics and the
already formalized representation/gauge/GOA bridge network.  The counted core
remains

`{M-QD-01, M-TC-01, M-PE-01, M-OI-01}`.

## 7. Boundary retained

The uniform value-span hypothesis is substantive.  Without it, vanishing
reward and transition defects do not by themselves force the product

\[
\epsilon_p(n)\,\operatorname{span}(V_n^*)
\]

to vanish.

This lane therefore closes the previous gap without pretending the gap never
existed.

The next structural extension is no longer another exactification step.  It is
to weaken the unique-Dobrushin-GOA regime and transport the **full recurrent /
invariant / occupation structure modulo gauge**, including systems with
multiple invariant laws or recurrent classes.
