# C1 — Measurable Existence / General-State Gap Audit

Package status: **LOCAL COMPLETE / PORT OPEN**
Conclusion class: **METHOD + EXPLICIT BOUNDARY**

## Already canonical

Core v3 already has Standard-Borel/countable-protocol predictive-state
factorization and common-version machinery.  P10 additionally proves, for one
fixed probability belief `b` and action `a` with a Standard-Borel latent state
and arbitrary measurable observation space:

- `measurable_generalPosterior_readout`;
- probability of `posteriorBeliefLaw`;
- `generalPosterior_barycenter_consistency`;
- `p10_terminal_generalState_belief_update`.

Therefore C1 must not be presented as a finite→Standard-Borel upgrade.

## Exact missing theorem target

A genuinely stronger target would construct a jointly measurable update

`U : (Belief Z × A × Y) → Belief Z`

representing a common regular-posterior version over the declared legal
belief/action domain, and then induce a Markov kernel on the whole belief state
space.

The proof obligations are not cosmetic:

1. one common posterior version jointly measurable in prior belief and action;
2. legal continuation/protocol closure;
3. fibre compatibility of the predictive state after update;
4. explicit zero-probability observation convention;
5. one common null-set/version story compatible with recursive iteration.

## Why no new Lean theorem is added in this package

The repository already contains the generic adapter pattern
`noiseDrivenReflexiveKernel` / `isMarkovKernel_noiseDrivenReflexiveKernel`:
**if** a jointly measurable update map is supplied, a Markov kernel follows.
Writing another Scientific Closure wrapper with joint measurability as an input
would merely assume the missing result.

The missing mathematics is the jointly measurable posterior construction itself.
That construction is not presently derived by P10 and is not supplied by this
package.

## C1-03 noncompact occupation boundary

No current C2–C7 package is blocked by a noncompact occupation theorem.  The
Roadmap-v2 rule therefore keeps C1-03 inactive.  Tightness/escape-to-infinity
should be activated only for a concrete model where compact/finite interfaces
actually fail.

## Acceptance

C1-01 audit: PASS.
C1-02 theorem brief: PASS / construction remains OPEN.
C1-03: DEFERRED BY DEPENDENCY RULE, not falsely closed.

The Core §31.2 C1 port remains OPEN.
