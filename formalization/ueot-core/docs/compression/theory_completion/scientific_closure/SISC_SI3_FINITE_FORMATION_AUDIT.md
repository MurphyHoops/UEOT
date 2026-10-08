# SISC SI-3 — Mechanistic Formation From a Finite Response Channel

Status: **LOCAL LEAN-CHECKED CONDITIONAL SUBCLASS**. Generic C4 remains OPEN;
real-world support is UNVERIFIED; independently measured physical mechanism
parameters are NOT yet available. No new counted theorem is claimed.

## What is newly derived

The finite lower response protocol has a registered nonnegative, row-sum-one
channel `FiniteResponseChannel.weight : New → Old → ℝ`. Actual lower-system
responses and parent candidate responses each approximately obey this *same*
registered channel, with **separately testable** residual bounds:

- world response evolution defect: `deltaWorld`;
- candidate parent response evolution defect: `deltaParent`;
- starting all-coordinate formation discrepancy: `tau`.

`finite_channel_error_nonexpansive` proves that positive normalized channel
averaging does not increase a worst-coordinate response error. Therefore
`finite_mechanism_preserves_formation` proves

`F0(x,p,tau) → F1(tx x,tp p,deltaWorld + tau + deltaParent)`.

In particular, `finite_mechanism_derives_directed_coverage` proves **the
existing C4 directed formation coverage** with parent defect 0; it does not
assume `DirectedFormationCoverage` in its premises. Then
`finite_mechanism_to_fbt_continuation` composes this derived coverage with
the existing quantitative C4 FBT theorem, obtaining a realized discrepancy
bounded by `L * 0 + epsB` for the admitted parent completion.

The independently declared common stochastic response channel (and its two
evolution residuals) are meaningful and refutable *mechanism* premises;
they are not merely the target-to-source matching relation in disguise.

## Positive and negative controls

The deterministic standard-library benchmark
`evidence/sisc_si3_finite_channel_benchmark.py` uses a genuine normalized
two-coordinate mixing matrix, perturbed world and parent predictions, and
checks both residuals and the derived outcome bound. Its negative example
uses an unnormalized channel with total weight 2: the nonexpansive inequality
then fails, demonstrating that normalization is essential.

## What is still missing

- A generally applicable construction/identification of the common channel
  from independently measured lower-level process or interventions.
- Fixed-protocol finite responses are not arbitrary histories, changing
  protocol spaces, infinite trajectories or physical formation discovery.
- This subclass gives exact transported parent representation `p1 = tp p0`
  and hence `epsF = 0` **only in this model**. Nonzero approximate parent
  formation distance and competing target births need separate machinery.
- Neither `FormedByResponse` nor FBT output implies a globally unique
  parent instance, same physical object, viable persistence or lineage.
- Its numeric benchmark is a method test, not external natural-system data.

Acceptance: focused Lean compilation, public-root/full build, no proof
escapes, separate stage commit and evidence log, without frozen ledger changes.
