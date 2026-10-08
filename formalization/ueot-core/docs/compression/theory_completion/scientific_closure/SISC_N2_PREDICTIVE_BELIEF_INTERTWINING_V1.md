# SISC N2.2 — A commuting predictive diagram for finite stochastic dynamics

Status: **LOCALLY LEAN-PROVED, CONDITIONAL, NOT ONTIC**. Source: `SISCStochasticPredictiveIntertwining.lean`. This is an exact mathematical bridge in UEOT's existing post-Core layer, not an originality claim against established Bayesian filtering, linear systems, predictive state representations or Hankel/operator models.

## The problem this solves

Previous N1 proof produced a normalized six-state stochastic counterexample: two microscopic tokens can have identical distributions of *all* finite output traces, while the token-level predictive quotient has no Markov transition kernel. Therefore `future trace equality on microstates ⇒ closed Markov state quotient` is false.

The positive replacement is **not** to add an unverified `StrongLumpability` axiom. Instead, make the source a finite *belief vector* `b:X→ℝ`, retain its mixture weights, and derive its event update from K and the emission protocol. Only then quotient beliefs by their complete predicted event-word functions.

## Exact theorems

Fix a finite stochastic K, output `read`, and **pre-action** emission convention. Define

`F_b(w) = Σ_x b(x) F_x(w)`

and, for event `(a,o)`,

`U_(a,o)(b)(y) = Σ_x b(x) 1_{read(x)=o} K_a(x,y)`.

The central **intertwining square** is

`F_(U_(a,o)b)(w) = F_b((a,o)::w)`

for every event, future word and source vector. `belief_event_update_intertwines_future_response` is proved by finite sum interchange and the recursive microstate response definition. No strong lumpability, unobserved `SameObject`, selected parent transporter or purpose function is assumed.

Then:

1. `belief_future_equality_is_event_congruence`: if two belief sources predict *all future words* equally, their event-updated sources also predict equally.
2. `unique_event_update_on_reachable_predictive_beliefs`: the **reachable quotient of complete belief predictions** admits an exact **unique** recursive event update; this follows using the existing M-RS universal descent machinery and a *derived* congruence.
3. `belief_event_step_nonnegative`: nonnegative source weights remain nonnegative in the unnormalized update.
4. `pre_event_evidence_eq_one_word_response`: the total updated weight is exactly the registered one-event response probability.
5. `normalized_event_predictive_intertwining`: conditional on nonzero evidence, the normalized predictive continuation equals the event-prefixed response divided by that evidence.
6. `normalized_event_mass_one`, `pre_event_evidence_nonnegative` and `normalized_event_weights_nonnegative`: the weight normalization and positivity obligations of the posterior are separately demonstrated. Positive evidence is required to interpret the normalized continuation as a physical conditional probability.

The unique quotient construction is **not** asserting it has a probability-valued Markov kernel on microscopic-token classes. The recursive event update is over **distributional prediction states**. The signed ambient carrier is a linear technical device; physically admissible beliefs form a positive normalized subset where the evidence is nonzero.

## Relation to other proved UEOT modules

- `SISCFutureResponseCore`: deterministic microscopic prediction equivalence is action-congruent.
- `SISCStochasticTraceNoGo`: stochastic microscopic *trace* equivalence may not be strongly lumpable.
- `SISCLinearPredictiveLift`: the future response functions span a finite-rank linear invariant space (rank upper bound ≤|X|).
- `SISCStochasticBeliefBridge`: Core's finite Bayes filter updates hidden-state beliefs under the **post-transition** emission convention.
- `SISCObservationOrderBridge`: those timing conventions are correctly aligned at one step; the present theorem deliberately uses *pre-transition* observation consistently on both sides.
- `SISCFiniteFormation` / `SISCFormationIdentityBridge`: formation residuals, candidate causal edges and observational discriminability remain **additional** obligations, not consequences of predictive recurrence.

## Scientific impact and limits

The genuinely stronger global understanding is **typed recursive closure of operational prediction**: whenever raw observational token classes are not closed, a richer carrier (belief distribution or linear response function) may restore exact recursion. Different representations have distinct admissibility, positivity, normalization, identifiability and time-index contracts. A physical object requires a further evidence-backed bridge from these informational structures to boundaries, causal parentage, persistence, repair and autonomy.

This theorem is finite, exactly modeled and conditional on a declared intervention/emission interface. It does not identify that interface from noisy data, prove a universal physical object-identity law, construct a causal parent transporter, or establish emerging GOD/GOA.

The next research stage should attempt an **evidence-limited object formation theorem** that chooses candidates from independently registered finite measurements and causal edges rather than taking a parent transporter `tp` as an input, and should explicitly output an unresolved/ambiguous case when experiments cannot distinguish candidates.

No changes to counted Core 106/106, Compression generators, earlier C7 evidence or frozen source summaries. Continue `SCIENTIFIC_FINAL=HOLD` and `CLOUD_PUSH=HOLD`.
