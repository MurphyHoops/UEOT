# Agency -> GOD -> GOA Assembly — Decisive Out-of-Sample Audit

Status: **LOCAL LEAN PASS / END-TO-END GENERATIVITY ESTABLISHED / UNCOUNTED**

This audit records the strongest out-of-sample theorem produced so far by the
UEOT Core compression program.

Module:

`UEOT/V3/Compression/AgencyGodGoaAssembly.lean`

The result does not change the frozen four-generator accounting.  Its purpose
is different: test whether the compressed interfaces can be composed to
reconstruct a nontrivial part of the original UEOT conceptual spine.

## 1. Target chain

The tested chain is

\[
\text{history-level sufficient state}
\to
\text{recursive state update}
\to
\text{finite control}
\to
\text{optimal selector / GOD}
\to
\text{policy-induced closed-loop dynamics}
\to
\text{invariant GOA with geometric stability}.
\]

The theorem is deliberately finite and explicit.  It does not use the words
GOD or GOA as new primitives; it identifies them with already formalized
objects:

- GOD: the Bellman-greedy action selector;
- closed loop: the literal `CoreOperationalAssembly.policyMatrix` induced by
  the stationary greedy selector;
- GOA: the unique invariant law of that closed-loop matrix under an explicit
  Dobrushin contraction margin.

## 2. Why the first assembly attempt was insufficient

An initial theorem placed:

- a recursively sufficient history representation, and
- an independently supplied finite control model

on the same state type `S`.

That is not enough for a strong cross-layer result.  Sharing a type does not
prove that the control model is actually the quotient dynamics of the history
process.

The final theorem therefore adds an explicit identity guard.

## 3. HistoryControlSpec

`HistoryControlSpec H S Act C` supplies history-level:

- reward `r(h,a)`;
- next-effective-state row `P(h,a,·)`;
- stochasticity;
- a uniform reward bound;
- one discount factor in `(0,1)`;
- one shared sufficiency condition

\[
C(h)=C(h')
\Longrightarrow

\bigl(r(h,a),P(h,a,\cdot)\bigr)
=
\bigl(r(h',a),P(h',a,\cdot)\bigr)
\quad\forall a.
\]

The action type is uniform in this first end-to-end theorem.  This restriction
is intentional: a history-level state-dependent action family requires its own
quotient-compatibility condition and is not silently assumed here.

## 4. M-QD-derived state realization

When

\[
C:H\to S
\]

is surjective, `RecursiveSufficientState` now proves

`existsUnique_ambientUpdate_of_surjective`.

Applied to the paired reward/transition response, this gives a unique

\[
U:S\to Act\to\bigl(\mathbb R\times(S\to\mathbb R)\bigr)
\]

whose value at `C h` reproduces the history response exactly.

`HistoryControlSpec.toModel` then constructs the finite discounted control model
from that unique state response.  Theorems

- `toModel_reward_on_history`;
- `toModel_transition_on_history`

are explicit identity guards: the state model reproduces the original
history-level reward and next-state row on every represented history.

This closes the main loophole in the weaker assembly.

## 5. Control -> GOD

For the history-derived model `M`, the existing finite-control layer supplies

\[
Q^*(s,\sigma^*(s))=V^*(s),
\]

where

\[
\sigma^*(s)=M.\texttt{greedyAction}(s).
\]

The theorem also consumes `selector_optimal_against_all_causal`, so the
stationary selector is not merely locally greedy: its infinite discounted
value equals `V*`, and every history-dependent randomized causal policy is
bounded above by `V*`.

Thus the formal GOD object is a genuine optimal action-selection rule, not a
renamed gradient vector.

## 6. GOD -> closed-loop dynamics

The selector is embedded as

`StationaryPolicy.ofSelector M.greedyAction`.

The closed-loop matrix is exactly

`CoreOperationalAssembly.policyMatrix M (...)`.

`greedyClosedLoopMatrix_rowStochastic` proves that this matrix is stochastic
from the same model/policy data.  No unrelated Markov kernel is supplied to the
GOA theorem.

This identity guard is essential.

## 7. Closed loop -> GOA existence through M-OI

The theorem seeds the finite Cesaro construction from one simplex vertex and
calls

`OccupationLimitInvariance.p_goa_01_via_occupationLimit`.

Therefore invariant-law existence is obtained through the counted M-OI route:

\[
\text{Cesaro compactness}
+
\text{vanishing evolution residual}
\Longrightarrow
\text{exact invariant limit}.
\]

The theorem does **not** assume an invariant law in advance.

## 8. GOA uniqueness and attraction through M-CF

The only additional long-run hypothesis is the explicit Dobrushin condition

\[
\alpha(P_{\sigma^*})<1.
\]

Under this condition, the M-CF bridge supplies:

1. uniqueness of the invariant law `μ*`;
2. the geometric attraction certificate

\[
D_{TV}\bigl(P_{\sigma^*}^n\mu,\mu^*\bigr)
\le
\alpha(P_{\sigma^*})^n
D_{TV}(\mu,\mu^*).
\]

This is stronger than merely asserting an invariant long-run object: every
initial finite law converges geometrically in the certified TV distance.

## 9. Main theorem

The strongest theorem is

`agency_god_goa_from_history`.

It simultaneously establishes:

- exact history -> state reward realization;
- exact history -> state transition realization;
- unique recursive update on the effective state;
- Bellman-greedy action optimality;
- optimality against the full causal policy class;
- one invariant law for the policy-induced closed loop;
- uniqueness of that invariant law;
- geometric TV attraction to it.

This theorem is not one of the frozen 106 P-IDs and was not used to infer the
four counted generators.

## 10. What has actually been validated

The compression program now has a genuine out-of-sample assembly result:

\[
M\text{-QD-derived recursive closure}
+
\text{finite Control}
+
M\text{-OI}
+
M\text{-CF}
\Longrightarrow
\text{Agency -> GOD -> GOA}
\]

under explicit finite/stability assumptions.

This is materially stronger evidence than proof deduplication.  The compressed
interfaces can generate a theorem whose conclusion spans multiple frozen Core
chapters.

## 11. Boundaries that remain

### Finite-state theorem

The current assembly is finite-state and finite-action.  It does not establish
the compact/Feller or continuous-time analogue.

### Uniform history-level action type

`HistoryControlSpec` uses one finite `Act`.  State-dependent action families in
the finite-control core are more general.  A future extension must formalize
action-admissibility descent instead of pretending it is automatic.

### Sufficiency is assumed, not learned

The theorem assumes the paired history reward/transition response is fibre
compatible with `C`.  It does not infer the sufficient state from raw data.

### Full history path-law Markovization is not claimed

The one-step reward and effective next-state law are exactly represented by the
state model.  The theorem does not separately prove equality of a pre-existing
history-space path law with the generated Markov path law.  That stronger claim
would require the relevant P-PROC/P-DYN path-law interface.

### Dobrushin is a sufficient stability hypothesis

`α < 1` is not claimed to be necessary for a GOA.  Periodic classes, multiple
invariant classes, recurrent decompositions, or weaker ergodic conditions can
produce other long-run structures.

### GOA meaning is scoped

Here GOA means the unique globally attracting invariant probability law of the
optimal finite closed loop under TV contraction.  This theorem does not prove
that every UEOT system or every physical system has such a GOA.

### No new generator deletion

The result composes M-QD and M-OI with Control and the uncounted M-CF bridge.
It does not make M-QD, M-TC, M-PE, or M-OI redundant.

## 12. Scientific disposition

Recommended classification:

**DECISIVE OUT-OF-SAMPLE ASSEMBLY: PASS.**

**GENERATOR COUNT: unchanged at four.**

The important advance is generativity: the current compressed architecture is
now strong enough to reconstruct a rigorous finite version of the original
UEOT Agency -> GOD -> GOA chain without inserting the final GOA conclusion as
an assumption.

## 13. Next pressure test

The next valuable extension is not another abstract bridge name.  It is one of
the following harder identity-preserving generalizations:

1. **state-dependent action descent:** derive admissible-action fibres together
   with reward/transition fibres;
2. **path-law realization:** connect the history process to the generated
   Markov model through the existing P-PROC/P-DYN interfaces;
3. **non-Dobrushin GOA:** replace strict global contraction by recurrent-class
   or occupation-limit long-run structure;
4. **approximate sufficient state:** combine M-TC/structural-defect bounds with
   the assembly to obtain quantitative near-optimality and near-GOA results.

Of these, the fourth would be the strongest cross-check of the complete
second-order bridge network because it would bring M-TC back into the
end-to-end chain.
