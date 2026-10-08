# Cross-module audit: observation timing is an independent semantic boundary

Status: **FORMAL COUNTEREXAMPLE AND EXACT CROSS-INTERFACE FORMULA**.

The newly verified stochastic response function
`controlledOutputTrace` emits the observed state `read(x)` **before** the
transition under action a. The already existing `FiniteBayesBelief` Core
module first computes `nextMass` (the post-action predicted state) and then
generates evidence from that next state. These two protocols share the
microscopic transition kernel but do **not** have identical sample timing.

`SISCEmissionTiming.lean` now proves:

- `one_word_trace_is_pre_transition_observation`: the law of the first
  output in the controlled trace depends exactly on `read(current)`;
- `point_belief_observes_post_transition`: for a point-source belief,
  the Core belief adapter assigns next-observation probability
  `∑_y K(x,a,y) · 1_{read(y)=o}`;
- `pre_and_post_emission_are_not_interchangeable`: a normalized two-state
  deterministic **flip** process has probability **1** of observing `false`
  before the action from state `false` and probability **0** of observing
  `false` after that action, despite using the same process and readout.

The adapter `finiteKernelToBeliefModel` is still valid as a post-transition
HMM model. The six-state no-go and the generic linear predictive lift also
remain valid under their separately specified pre-transition trace
convention. What is **not licensed** is equating the two observation laws
without a time-shift / indexing map or a state-update/observation-order
bridge. A normalised belief law is not by itself a proof that it reproduces
the specific `stochasticOutputTrace` experiment at the same clock index.

## Next bridge

Prove an exact shifted trace formula when the observation is recorded at the
new state (or equivalently re-index the trace to include an initial emission
before the first action). Keep separate test fixtures for both conventions.
Only then claim the Bayesian filter **matches** the same trace protocol,
instead of merely providing another normalized predictive interface for
the same underlying K.

No existing formal proof is weakened or changed. This is a source-facing
semantic guard that does not establish ontic identity, physical purpose,
nontrivial object formation or independent external validity.
