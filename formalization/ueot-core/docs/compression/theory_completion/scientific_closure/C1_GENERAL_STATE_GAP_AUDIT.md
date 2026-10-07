# C1 — Measurable Existence / General-State Gap Audit

Package status: **LOCAL COMPLETE / COUNTABLY-GENERATED SUBPORT CLOSED / FULL PORT OPEN**
Conclusion class: **CONDITIONAL THEOREM + EXPLICIT BOUNDARY**

## Already canonical before this package

Core v3 already has Standard-Borel/countable-protocol predictive-state
factorization and common-version machinery. P10 additionally proves, for one
fixed probability belief `b` and action `a` with a Standard-Borel latent state
and arbitrary measurable observation space:

- `measurable_generalPosterior_readout`;
- probability of `posteriorBeliefLaw`;
- `generalPosterior_barycenter_consistency`;
- `p10_terminal_generalState_belief_update`.

Therefore C1 is not a finite→Standard-Borel upgrade and does not re-count those
fixed-parameter results.

## New theorem obtained by the C1 re-audit

The original C1 audit identified the genuinely stronger target as one common
posterior version jointly measurable in current belief, action and observation,
followed by a Markov transition on the whole belief space. A direct audit of the
current Mathlib Giry/disintegration API shows that this target is derivable under
Mathlib's exact parameterized-disintegration side condition:

- latent state `Z`: Standard Borel and nonempty;
- action space `A`: arbitrary measurable;
- parameter/observation pair:
  `CountableOrCountablyGenerated (ProbabilityMeasure Z × A) Y`;
- controlled transition and observation kernels: Markov.

Thus the machine theorem is slightly stronger than a countably-generated-`Y`
statement: it also applies when the whole belief/action parameter space is
countable.  In the intended non-countable belief-space regime, countable
generation of `Y` is the operative and much more useful sufficient condition;
the file exposes it as a direct corollary.

`C1ParametricBelief.lean` then constructs, rather than assumes:

1. a measurable `(belief, action) ↦ belief × δ_action` measure;
2. a Markov one-step joint kernel
   `Kernel (ProbabilityMeasure Z × A) (Y × Z)`;
3. a single parameterized disintegration
   `Kernel ((ProbabilityMeasure Z × A) × Y) Z` via `Kernel.condKernel`;
4. a jointly measurable posterior-belief map into `ProbabilityMeasure Z`;
5. a Markov belief transition
   `Kernel (ProbabilityMeasure Z × A) (ProbabilityMeasure Z)`.

The strongest terminal theorem is `c1_parameterized_belief_recursion`; the
common specialization is `c1_countablyGenerated_belief_recursion`.

## Compatibility with the existing P-REF-02 posterior

This is not a second Bayesian model. The new one-step joint law is proved equal
to `GeneralBayesPosterior.jointLaw` after the expected coordinate swap.
Consequently, for every fixed `(b,a)`, the selected parameterized posterior
section agrees with the existing `GeneralBayesPosterior.posteriorKernel`
**almost everywhere under the predictive observation law**.

The a.e. qualifier is essential: regular conditional probabilities are versions,
and values on zero-probability observations are not canonically identified by
the joint law. The parameterized `condKernel` provides one total measurable
version, but C1 does not falsely promote version-dependent null-event values to a
pointwise uniqueness theorem.

The resulting belief transition is exactly the push-forward

`observationLaw(b,a).map (y ↦ posteriorBelief(b,a,y))`,

so the result supplies genuine recursive belief-state dynamics rather than the
pre-existing generic adapter “assume measurable update, then obtain a kernel”.

## Remaining stronger boundary

The fully arbitrary-measurable-observation target is **not** unconditionally
closed. Mathlib's parameterized kernel disintegration requires
`CountableOrCountablyGenerated α β`; in the normal C1 regime the belief/action
parameter space is not assumed countable, so countable generation of the
observation sigma-algebra supplies the operative branch of that hypothesis.

Accordingly C1 does not claim a common jointly measurable posterior version for
every measurable observation space. Such a theorem would require either a
stronger disintegration/common-version theorem or additional structure.

The broader Core §31.2 concerns about legal continuation/protocol domains and
model-specific predictive fibres also remain separate from this pure Bayesian
measurability closure; they are not silently discharged by the kernel theorem.

## C1-03 noncompact occupation boundary

No current C2–C7 package is blocked by a noncompact occupation theorem. The
Roadmap-v2 dependency rule therefore keeps C1-03 inactive. Tightness or
escape-to-infinity machinery should be activated only for a concrete model where
compact/finite interfaces actually fail.

## Acceptance

- C1-01 audit: **PASS**.
- C1-02 exact `CountableOrCountablyGenerated` parameterized posterior and belief
  recursion: **THEOREM / PASS**; countably-generated-observation corollary:
  **PASS**.
- C1-02 fully arbitrary measurable observation version: **OPEN**.
- C1-03: **DEFERRED BY DEPENDENCY RULE**, not falsely closed.

Therefore the C1 package is locally closed with a strictly stronger formal
result than the original boundary audit, while the full Core §31.2 C1 port
remains open at its genuinely stronger arbitrary-observation boundary.
