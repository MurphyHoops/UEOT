# UEOT Core v3 — Formalization Feedback Log (2026-09-10)

Status: maintenance evidence only; canonical v3.0 source is unchanged.

This note records theory-level conclusions exposed by the active Lean proof lanes.  It follows `EVOLUTION_MAINTENANCE.md`: proof-engineering issues do not alter Core, while genuine statement-typing or hidden-assumption issues are proposed explicitly for the next compatible revision.

## P-DYN-02 — finite CTMC generator criterion

**Classification: F2 clarification + completed source obligation.**

The v3.0 prose says that an exact finite CTMC semigroup quotient implies the generator block-sum condition by differentiating `exp(tL)` at zero.  Probabilistic CTMC time is one-sided (`t >= 0`), whereas the first Lean analytic helper used equality for all real `t`.  The all-real statement is a valid stronger algebraic helper but must not be labeled as the source theorem.

The source-facing formalization therefore uses right-derivative uniqueness on `Ici 0`.  It proves that equality of the semigroup quotient for every `t >= 0` already implies `L F = F Lbar`; the converse follows from the exponential power series.  In addition, the finite block-sum construction has been strengthened to discharge an obligation already present in the source wording: if `L` is a CTMC generator and the partition is surjective, the common block sums define an `Lbar` whose off-diagonal entries are nonnegative and whose rows sum to zero.  Thus `Lbar` is a genuine CTMC generator, not merely an intertwining real matrix.

**v3.1 wording candidate:** state explicitly that the semigroup quotient is required for `t >= 0`, say “take the right derivative at `t=0`”, and include one sentence proving that the common block sums satisfy the CTMC generator sign and row-sum conditions.

No new UEOT axiom is required.

## P-PER-03 — finite-state viability kernel

**Classification: F0 proof/interface clarification.**

The finite deletion recursion, stabilization, stationary preserving policy and maximal controlled-invariant-set direction are already compatible with the v3 statement.  Formalization exposed a semantic distinction worth keeping explicit in exposition:

- `P(X_n in K)=1` for every fixed `n` is a family of marginal statements;
- `P(forall n, X_n in K)=1` is a single path event.

For countable discrete time, the second follows from the first by taking the countable union of the null bad-coordinate events, but this bridge should be stated rather than left implicit.  The Lean lane now also realizes the stationary policy as a genuine Markov kernel and feeds it into the repository's Ionescu--Tulcea trajectory construction, so the final nonexit theorem can be stated on an actual measure on `N -> X`.

This is not a correction to Core; it is a recommended proof-expansion in v3.1.

## P-REC-02 — continuous stochastic recovery

**Classification: F0; previous possible F1 concern cleared by source audit.**

The exact v3.0 statement already requires the generator-domain/Dynkin/localization/integrability conditions needed to obtain local absolute continuity of `m(t)=E[W(X_t)]`, then an almost-everywhere differential inequality.  Consequently no extra regularity assumption should be inserted into Core merely to simplify Lean.

The current formalization correctly separates:

1. the process-level Dynkin output certificate (`m` locally absolutely continuous and `m' = E[LW(X_t)]` a.e.);
2. the a.e. drift inequality;
3. the AC/a.e. integrating-factor Gronwall argument;
4. the energy-to-mean-square-distance comparison.

The remaining work is to instantiate the process-level certificate for the exact stochastic-process class used by the source, not to weaken the theorem to pointwise differentiability.

## P-FAC-01 — representation covariance

**Classification: F0, with a reusable stronger infrastructure result.**

The source proof says primitive representation transport gives one-step pushforward equality, finite path-law equality by induction, then preservation of future records, rewards and control values.  The formalization now follows that dependency direction: finite causal feedback path laws are derived recursively from transported extension kernels; measure transport, expected finite-horizon rewards, policy-by-policy values and the policy supremum are then consequences.

Therefore final path-law equality must not appear as an independent source hypothesis.  Generic helper lemmas that accept a supplied path-law equality may remain in the library, but source-facing P-FAC-01 wrappers must derive it from primitive transport.

## P-PER-01 — one-sided semiflow warning remains active

**Classification: unresolved F2 audit.**

Forward invariance of an omega-limit set is natural for a semiflow.  Exact equality under time translation requires a separate reverse-inclusion argument and must not be obtained by silently replacing the one-sided semiflow with a two-sided flow.  Keep this P-ID out of `proved` status until the exact v3 assumptions and reverse direction are reconciled.

## P-INFO-01 — next high-value closure

The information lane has the chain identity and epsilon-retention direction.  The source's final discrete conclusion still requires a compatible finite/discrete proof of `I(M;Y) <= H(M)`.  This should be the next information-theory closure rather than promoting P-INFO-01 from only the chain identity.

## Theory-level conclusion from this round

The active failures have so far not produced a counterexample to the UEOT Core architecture.  Instead they are improving the typing of the theory in three important ways:

1. time orientation is part of the mathematical model (flow versus semiflow/CTMC semigroup);
2. marginal persistence and pathwise persistence are distinct propositions connected by explicit measure theory;
3. representation invariance must be derived from primitive transported dynamics, not asserted at the final value layer.

These distinctions make the Core more reusable across deterministic, stochastic and controlled model classes without broadening its axioms.
