# N1 — finite controlled stochastic quotient: exact Lean theorem

**Local conditional mathematical result**. No scientific closure or novel
physical law claimed. Based on `SISCFiniteStochasticQuotient.lean`, which is
publicly imported and compiles in the same post-Core hierarchy.

Given a finite microstate set `X`, a controlled stochastic transition
`K : X → A → X → ℝ`, `K ≥ 0`, `∑_y K(x,a,y)=1`, and an independently
registered representation `q : X → Q`, write the target-class mass

`M_q(x,a,c) = ∑_{y:q(y)=c} K(x,a,y)` for `c∈range(q)`.

The fundamental conditional criterion is **strong lumpability**:

`q(x)=q(x') ⇒ M_q(x,a,c)=M_q(x',a,c)` for every action and target class.

`strong_lumpability_iff_existsUnique_class_kernel` proves that this
condition is necessary and sufficient for a **unique exact real-valued
quotient update** on the reachable quotient. More importantly,
`strong_lumpability_iff_existsUnique_stochastic_quotient` upgrades this to
existence and uniqueness of a **nonnegative normalized controlled stochastic
quotient kernel**. The latter is nontrivial: class mass nonnegativity and
the sum-to-one property are separately derived from the original finite
stochastic kernel and the partition of X into reachable fibres.

The proof reuses the already-reviewed M-RS quotient universal property;
this is a typed finite Kemeny–Snell strong-lumpability theorem, not an
original probabilistic lumpability theorem (1960). Prior-art example:
https://www.sciencedirect.com/science/article/pii/S0167715203001263

## What it does NOT say

- It does not claim that **all-future observation-law equivalence** is
  automatically strongly lumpable. That logically different question must
  be tested against explicit stochastic trace equivalence counterexamples.
- It does not infer physical cause, constitutive objecthood, transport or
  world identity from a chosen `q`.
- It does not establish a standard-Borel measurable quotient kernel for an
  arbitrary state space, nor does it solve estimator identification.
- It applies to finite normalized state transitions, not arbitrary signed
  linear response operators.

Next: test future-trace equivalence vs strong lumpability and, if necessary,
formalize a counterexample together with the missing strengthening condition
for canonical stochastic predictive states.
