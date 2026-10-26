# R3b: an observable quotient of the actual C1 belief kernel

This increment follows R2/#375 and the scoped registry successor #376, at base
`e045cca43a94abbff00fd0da53e6200e0bd6ae2e`. It adds two modules and two public-root
imports. It addresses audit section 10.2 in a concrete binary generating-test
model with an explicit closed image and measurable section. It does not claim
a quotient for arbitrary countable coordinates or arbitrary measurable worlds.

## Source, coordinate, and construction

Let X be a nonempty standard Borel space, A a measurable action space, P a
Markov source kernel, and q:X→Bool a measurable observation with explicit
representatives zero and one. The coordinate T(b)=b(q=true) lies in [0,1]. Its
image is exactly this closed interval; the section assigns the two-Dirac mixture
(1-c)δzero+cδone. Both coordinate and section are proved measurable.

The source-test closure premise is equality of P(x,a)(q=true) for every pair
with the same q and every action. Binary normalization gives equality on both
observation classes. Prefix integration preserves functions of q; induction
then factors every finite action-observation word response through q. Equal
belief coordinates therefore give equal probabilities of all these tests.

The belief transition is the existing `c1BeliefTransitionKernel`, using its
common parameterized posterior version. Deterministic observation implies that
its posterior q-pushforward is δy only observation-almost everywhere. Mapping
the actual belief transition by T consequently gives the observation law
mapped to the interval's vertices. Null observations require no pointwise
posterior identity.

The quotient kernel is constructed by composing that same C1 transition with
the explicit belief section and mapping by T. Source-test closure proves its
factorization for every belief and action. Surjectivity of the section proves
uniqueness. This uses the existing surjective-descent uniqueness principle;
the new bridge supplies the actual C1 law and measurable Markov construction.
Conversely, any factorization kernel, even without a Markov
premise, forces source-test closure by evaluating Dirac input beliefs.
Thus closure is equivalent to existence of a unique measurable Markov quotient;
the desired target kernel is not an external input.

## A stochastic model and an actual predictive coordinate

The witness has latent state Bool×Bool, observes the first bit, and has two
actions. A Bernoulli(1/4) noise bit flips the hidden second bit. The probe action
preserves the first bit; the other action xors the same noise into it. The
hidden-flip probability is formally 1/4 for every source row, and source-test
closure is proved from these actual transition measures.

The one-step future probe event has probability exactly T(b). Together with
finite-test factorization this proves that equality of all finite future test
probabilities is equivalent to equality of T. Distinct hidden-state Dirac
beliefs supply a strict alias example with all future observation tests equal.
The model's actual C1 belief kernel descends through the constructed quotient.

## Falsifiable boundaries and independent readouts

A second source reveals the hidden bit under one action. Two states with the
same observation then yield different next observation probabilities. A proof
by contradiction rules out every kernel factorization of its actual C1 belief
transition through this coordinate.

The positive reward is the observed-bit indicator minus action cost 1/8;
its expected value factors as T(b)-cost(a). The probability of the observed-safe
class factors as 1-T(b). These are separate proofs from predictive descent.
For the aliased hidden beliefs, hidden-bit reward and hidden-safe probability
differ. Hence no functions of T can represent these hidden readouts on all
beliefs. Predictive equivalence alone does not certify arbitrary control or
safety objectives.

## Scope and evidence

The construction is mathematical and noncomputable; it makes no arbitrary-real
posterior runtime or finite-memory minimization claim. Measurability, source
normalization, deterministic observations, source closure, and the standard
Borel/common-version setting remain explicit. The witness supplies these
premises for a finite stochastic source. External scientific validity remains
UNVERIFIED and strong global closure remains NOT_ESTABLISHED. Frozen 106/106,
four counted generators, and 11/89/6 retain their existing scope.

Actual focused Lean and full `lake build UEOT` passed for 701 modules. The
full build completed with exit 0 and 9407 jobs. Native export and fixed replay
passed with identical complete JSON and log bytes: 30 public source candidates,
84 owned constants, 132990 cross-layer and 435 internal comparisons, no
collisions, and 29 direct registered edges. The complete 102-module UMC audit
found 1808 compiled theorem constants using only Lean standard axioms. Reuse
70, parser 89, FKRG 30, the immutable 68-row clone table, governance 38, and
12 expected mission rejections passed. All 40 prior overlay/certificate/native/
clone assets retain their exact bytes.

The initial full build failed because root imports followed the doc comment;
that actual log and identity are preserved, with a later exact-SHA reconstruction
of its failed root source. The corrected full build is `full-build-02`.
[Local release acceptance](RELEASE_ACCEPTANCE.json) records the actual evidence.
Exact Git-object preflight, independent final-head review and resulting-main
verification remain separate publication receipts; pending publication is not
a verified merge.
