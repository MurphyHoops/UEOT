# Moving Encoder Semantic / GOA Closure Audit

Status: **LOCAL LEAN PASS / END-TO-END TAIL CLOSURE ESTABLISHED / UNCOUNTED**

Module:

`UEOT/V3/Compression/MovingEncoderSemanticGoaClosure.lean`

This lane reconnects the previously separate moving-representation and
semantic/GOA gauge lines.

The starting point is the already proved finite full-support fact

\[
d_{G,\mu}(C_n,C_*)\to0
\quad\Longrightarrow\quad
\exists N\;\forall n\ge N:\;SameFibers(C_n,C_*).
\]

The new module carries that eventual exact representation lock through
approximate control semantics and then through long-run closed-loop structure.

## 1. Representation lock -> unique semantic gauge

For a fixed reference approximate quotient `Qref` and moving quotients `Qseq n`
sharing the same literal micro model, the moving encoder theorem supplies
eventual `SameFibers`.

`eventually_existsUnique_approxSemanticRelabel` then applies the M-QD quotient
gauge and `ApproximateSemanticGauge` to obtain, eventually, one unique

\[
e_n:S\simeq S
\]

with the complete approximate semantic certificate.

Thus the moving representation is eventually not merely close by a scalar
gauge distance: it lies in the exact same fibre partition, with one canonical
semantic state relabeling.

## 2. Three semantic envelopes are deliberately separated

The module defines

\[
E_r(n)=\epsilon_r^*+\epsilon_r(n),
\]

\[
E_p(n)=\epsilon_p^*+\epsilon_p(n),
\]

and

\[
E_V(n)=D_*+D_n.
\]

If the reference is exact in the corresponding quantity and the moving
certificate tends to zero, each envelope tends to zero.

This produces `eventually_approxSemanticRelabel_arbitrarily_close`: for every
positive tolerance, eventually the **unique** state gauge simultaneously has
reward, transition and value-envelope radii below that tolerance.

### Important boundary: `epsilon -> 0` does not automatically give `D -> 0`

The P-QUO radius is

\[
D_n=\frac{
\epsilon_r(n)+\beta\epsilon_p(n)\,sp(V_n^*)
}{1-\beta}.
\]

Therefore

\[
\epsilon_r(n)\to0,\qquad\epsilon_p(n)\to0
\]

alone do **not** formally imply `D_n -> 0` if the moving optimal-value span is
allowed to grow without a uniform bound.

The module consequently requires `D_n -> 0` explicitly for value and policy
closure.  This is a genuine mathematical boundary, not a proof inconvenience.

Future work may replace this explicit hypothesis by a derived theorem under a
uniform reward/value-span bound.

## 3. Fixed-policy moving GOA closure

For a fixed source selector `sigma`, define

\[
R_{GOA}(n)
=
\frac{\epsilon_p^*+\epsilon_p(n)}{1-\alpha_*},
\]

where `alpha_*` is the Dobrushin coefficient of the reference closed loop.

If `alpha_* < 1`, eventual exact gauge lock yields one unique fixed-policy
gauge certificate at every sufficiently late index.

`eventually_existsUnique_fixedPolicyNearGoaGaugeAt` proves that every invariant
law of the moving target closed loop under the transported same policy lies
inside the radius `R_GOA(n)` around the relabeled reference invariant law.

The helper `selectorClosedLoop_exists_invariant`, reconstructed through
M-OI/P-GOA-01 finite Cesaro invariance, proves that the target invariant law
actually exists.  Thus the statement is nonvacuous.

If the reference transition defect is zero and

\[
\epsilon_p(n)\to0,
\]

then

\[
R_{GOA}(n)\to0.
\]

`eventually_fixedPolicyNearGoa_arbitrarily_close` packages the exact tail
statement: every requested positive GOA tolerance is eventually achieved under
the unique quotient gauge.

## 4. Moving action-gap closure

The optimal-policy lane adds two hypotheses:

1. `D_* = 0` and `D_n -> 0`;
2. the fixed reference model has a uniform positive action gap `gamma > 0`.

Then eventually

\[
2(D_*+D_n)<\gamma,
\]

so the static action-gap theorem applies at every state and competitor action.

`eventually_actionGap_of_D_tendsto_zero` formalizes exactly this step.

## 5. Optimal-policy moving GOA closure

Combining

- eventual exact representation gauge lock,
- common micro semantics,
- vanishing P-QUO value radius,
- a positive reference action gap,
- and source greedy closed-loop Dobrushin contraction,

`eventually_existsUnique_optimalPolicyNearGoaGaugeAt` proves that eventually:

1. one unique quotient-state gauge exists;
2. the target's **own canonical greedy policy** equals the transported reference
   greedy policy;
3. the reference greedy closed loop has one unique invariant law;
4. every target greedy invariant law lies in the quantitative GOA tube.

Again, finite Cesaro invariance proves that a target greedy invariant law
exists.

Finally, if the moving transition defects also tend to zero,
`eventually_optimalPolicyNearGoa_arbitrarily_close` gives the tail theorem

\[
\boxed{
\text{moving representation}
\to
\text{eventual exact gauge lock}
\to
\text{semantic convergence}
\to
\text{eventual greedy-policy lock}
\to
\text{GOA radius}\to0.
}
\]

This is the first formal end-to-end convergence route joining the moving
representation gauge directly to target-optimal long-run structure.

## 6. Relation to the four-generator core

No counted generator is added or removed.

The proof network uses:

- **M-QD-01** through exact quotient fibre descent / unique quotient gauge;
- **M-TC-01** indirectly through the already established approximate control
  and defect-propagation infrastructure;
- **M-OI-01** for existence of finite invariant long-run structure;
- the post-FINAL M-CF contraction bridge for quantitative stationary
  perturbation;
- P-QUO-02 for the value radius `D`;
- the new action-gap bridge for policy identity.

The scientific classification remains:

**FOUR-GENERATOR CORE UNCHANGED / BRIDGE NETWORK GENERATIVITY STRENGTHENED.**

## 7. Boundaries retained

- Full support and finite source cardinality are needed for “gauge distance to
  zero -> eventual exact fibre lock.”
- Exact fibre gauge is reached only eventually; before that point no semantic
  conclusion is inferred from label mismatch alone.
- `D_n -> 0` is separate from raw reward/transition defect convergence unless a
  uniform value-span theorem is added.
- A positive action gap is required for literal greedy-policy lock; ties remain
  unstable under arbitrarily small perturbations.
- Dobrushin contraction is one quantitative GOA lane, not a universal
  definition of GOA.
- The theorem concerns a common literal micro control model.  Cross-micro-model
  perturbation remains a separate bridge problem.

## 8. Next pressure test

The value-span pressure test identified here is now **CLOSED** by
`Compression/ValueSpanClosure.lean`: under one uniform moving optimal-value span
bound, primitive reward/transition defect convergence derives `D_n -> 0` and
feeds the existing optimal-policy GOA tail theorem.

The next structural extension is therefore to replace the unique Dobrushin GOA
lane by recurrent-class / invariant-set / occupation-structure gauge results,
so the theory covers nonunique and noncontractive long-run regimes without
silently identifying GOA with one globally attracting stationary law.
