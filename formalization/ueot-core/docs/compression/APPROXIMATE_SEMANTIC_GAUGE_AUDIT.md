# Approximate Semantic Gauge Stability Audit

Status: **LOCAL LEAN PASS / QUANTITATIVE SEMANTIC GAUGE STABILITY ESTABLISHED / UNCOUNTED**

Module:

`UEOT/V3/Compression/ApproximateSemanticGauge.lean`

This lane is the first step beyond the exact quotient-gauge program.  It asks
what survives when the quotient representations are exactly aligned, but their
macro control semantics are only approximately faithful to one common micro
system.

## 1. Anti-overclaim principle

Representation closeness is not semantic closeness.

Accordingly, this lane does **not** infer reward, transition, value, policy, or
GOA proximity from a small quotient-label mismatch alone.  It requires:

1. one literal common micro control model;
2. an exact quotient-state relabeling `e` aligning the two encoder fibres;
3. each quotient's already certified reward defect `epsilonReward`;
4. each quotient's already certified transition-TV defect
   `epsilonTransition`.

Only then are semantic errors composed.

## 2. PMF / TV transport infrastructure

The module proves small reusable finite-TV helpers:

- symmetry of `FiniteProbabilityRow.tvDist`;
- triangle inequality;
- exact invariance under an equivalence map.

It also proves `pushforwardTransitionPMF_relabel`:

if

\[
e\circ q=r,
\]

then for every micro transition row

\[
e_\#(q_\#P)=r_\#P.
\]

This identity uses the exact fibre-mass relabeling theorem from the preceding
semantic-gauge lane, so the transition proof does not approximate the
representation map itself.

## 3. Reward semantic stability

For approximate quotients `Q` and `R` of the same micro system and an exact
state relabeling,

`macroReward_relabel_le` proves

\[
|r_Q(s,a)-r_R(e(s),a)|
\le
\epsilon_r^Q+\epsilon_r^R.
\]

The proof is the exact triangle through the common micro reward.  No reward
regularity or Bellman argument is needed.

## 4. Transition semantic stability

`macroTransition_relabel_tv_le` proves

\[
D_{TV}
\left(
e_\# P_Q(s,a),
P_R(e(s),a)
\right)
\le
\epsilon_p^Q+\epsilon_p^R.
\]

The route is:

\[
e_\#P_Q^{macro}
\leftrightarrow
e_\#(Q.f_\#P^{micro})
=
R.f_\#P^{micro}
\leftrightarrow
P_R^{macro}.
\]

Both endpoint arrows use the two source approximation certificates; the middle
equality is exact representation gauge.

The TV convention is the canonical UEOT event-supremum TV used in P-QUO and
P-GOA.  No L1 surrogate or normalization conversion is introduced.

## 5. Optimal-value semantic stability

Each P-QUO-02 approximate quotient already proves that its macro optimal value,
pulled back to the micro state space, lies within its global radius `D` of the
true micro optimal value.

Using the same micro state as the common anchor,

`macroOptimalValue_relabel_le` proves

\[
|V_Q^*(s)-V_R^*(e(s))|
\le
D_Q+D_R.
\]

This is a genuine cross-quotient consequence not present in either individual
P-QUO-02 certificate.

## 6. Unique approximate semantic relabeling

`ApproxSemanticRelabel Q R e` packages:

1. `e ∘ Q.f = R.f`;
2. reward bound `epsilonReward_Q + epsilonReward_R`;
3. transition-TV bound `epsilonTransition_Q + epsilonTransition_R`;
4. optimal-value bound `D_Q + D_R`.

`existsUnique_approxSemanticRelabel_of_sameFibers` proves that exact
`SameFibers` plus one common micro model yields one unique equivalence carrying
all three semantic certificates.

The uniqueness is structural and comes from M-QD quotient gauge; the numerical
semantic bounds do not manufacture uniqueness.

## 7. Why this matters for the compression program

The exact gauge lanes established invariance under perfect quotient
equivalence.  This lane establishes the first robust version:

\[
\boxed{
\text{exact fibre gauge}
+
\text{two semantic defect certificates}
\Longrightarrow
\text{quantitative cross-quotient semantic stability}
}.
\]

It uses existing P-QUO approximation machinery as domain evidence while the
cross-quotient composition is new.

## 8. Boundaries

### Exact fibre alignment is still required

This lane does not yet combine a nonzero representation-gauge mismatch with
semantic errors.  That would require an additional mechanism relating changed
fibres to reward/transition semantics.

### Same micro model is essential

Without a shared micro anchor, two macro approximations can each be accurate to
different systems and still be arbitrarily far from each other.

### Uniform action type

The theorem uses one finite `Act` on every quotient state.  State-dependent
action families require an action-admissibility transport theorem.

### Value bound is P-QUO radius based

The value certificate `D_Q + D_R` is robust and already machine-checked, but it
need not be sharp for a particular pair of macro models.

### No policy or GOA closeness yet

Small reward/transition/value errors do not imply equality of greedy selectors
when action gaps are small or tied.  No policy identity is claimed here.

Likewise, near-GOA stability requires a fixed-policy or action-gap bridge plus
a long-run contraction hypothesis.

## 9. Scientific disposition

Recommended classification:

**APPROXIMATE SEMANTIC GAUGE STABILITY: PASS.**

**COUNTED GENERATORS: unchanged at four.**

The result is generative and quantitative, but it does not delete or replace
any counted generator.

## 10. Next pressure test

The immediate next theorem should keep policy identity explicit:

1. choose one deterministic selector and transport it through the quotient
   relabeling;
2. use the actionwise transition-TV bound to control the two induced
   closed-loop rows;
3. under a source Dobrushin margin, use M-CF fixed-point perturbation to bound
   the invariant-law distance by

\[
\frac{\epsilon_p^Q+\epsilon_p^R}{1-\alpha};
\]

4. only after that add an action-gap theorem if one wants the selector to be
   certified optimal for both approximate macro models.

This separation avoids the false implication
"small model error implies identical greedy policy."
