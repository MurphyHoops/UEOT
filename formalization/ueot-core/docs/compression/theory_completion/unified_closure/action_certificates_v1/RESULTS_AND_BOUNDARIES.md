# Finite same-source conditional paths: executable certificates

This package closes the gap between an existential action-mixture result and
the **specific table returned by a computation**. A checked table is interpreted
directly as `policy weights`; its complete state-path law equals the original
baseline experiment conditioned on the declared safety event. A checked strict
separator excludes every real-valued, time-varying current-observation policy.
Neither conclusion depends on the searcher's success claim.

## Frozen question

Inputs are nonempty finite state/action alphabets, a finite observation alphabet,
an observation map, rational normalized transition and baseline-policy rows,
an original initial distribution, a safety predicate, a transition horizon and
an **actual deployment initial distribution**. Source, baseline, event, actions,
information and preparation are distinct parts of the question. The source
transition model is stationary; the implemented current-observation policy may
vary with time. Safety includes the initial and terminal state.

`sourceRemaining`, `sourceMass`, `sourceInitial`, and `sourceTarget` compute the
target from that same input. Null/unsafe target rows use an explicit self-loop.
`sourceTargetPath_eq_actual` proves their interpreted path equals the existing
`actualConditionedPrefix`; no target identity is an input hypothesis. Zero
survival means undefined conditioning. The checker computes positive target
occupancy, rather than trusting a certificate's coverage list.

`specified_policy_path_iff` proves that a specified policy implements the full
state path iff its actual initial law equals the target initial law and its
mixed original action rows agree at every target-occupied state before the
horizon. Necessity uses prefix projection and cancellation of a positive,
finite history mass. Terminal-state agreement alone is insufficient.

## Scientific consumers

| Frozen input | Conclusion |
| --- | --- |
| Original three states, singleton risk action, horizon 1, prepared initial | Strict separating certificate: original actions cannot implement the original conditional full path. |
| Explicitly added safe-selection actions, original risk baseline, horizon 2 | Checked returned table implements the full conditional state path. `Z=1/4`, prepared initial `(3/4,1/4,0)`, risk/selection weights `(0,3/4,1/4)` then `(0,1/2,1/2)`. |
| Same added actions and horizon, actual original uniform initial | Full path is impossible; TV error at least `1/4` for **any future causal state kernel**. Initial preparation is an independent obligation. |
| Three-state same-source constant observation, two actions each safe only at its own safe state, uniform baseline, horizon 1 | Both safe states have positive target occupancy and individually feasible rows; no common observation weights exist. A checked separator excludes the full path for this policy class. |
| Separate unreachable-fallback variant | All source actions from the unreachable unsafe state go to state 0, while its target fallback is the self-loop at state 2. This row is impossible but irrelevant; occupied rows still realize the complete path. This variant explicitly changes the source's unsafe row. |
| Independent baseline variant using safe actions with weights `(1/3,2/3)` | New source-derived target and table are checked, preventing reference-answer replay. |
| Zero horizon | Only the actual initial equality is required; the accepted empty table has the correct conditional path. |
| Zero survival / wrong weights / bad separators | Undefined conditioning / rejected candidates, respectively. Rejection is not an infeasibility proof. |

The original risk rows are `(3/8,3/8,1/4)` and `(1/8,1/8,3/4)`;
the original cemetery is absorbing and initial law is `(1/2,1/2,0)`. The two
added actions deterministically select safe state 0 or 1. They are an explicit
extension of the action set, not a conclusion about the original source.
The two-step eight safe path masses are `(9,9,3,3,3,3,1,1)/32` in lexicographic
order. These values are recomputed from the source and checked, not returned
by instance-name lookup.

The computed negative certificates use `t=0` and the common observation 0.
For the original actions, the sole nonzero coefficient is
`c(s1,cemetery)=-1`, with `b=-3/4`, gap `3/4`. For the aliased source,
`c(s0,cemetery)=c(s1,cemetery)=-1`, with `b=-1`, gap `1`.
In each case every original action score is at most `b`, while the target
score is zero. Both certificates are rechecked on the computed occupied fiber.

## Executable trust boundary

`exact_certificates.py` uses Python `Fraction` for candidate search and an
independent small-horizon path enumeration. Its outputs are **CANDIDATE**
statuses. Its target is always rederived internally. Bounded vertex/separator
search may return UNKNOWN; floating point and solver failure are never proofs.

`certify.py` emits closed source/row/checker obligations through
`emit_lean_witness.py`, builds the semantic source module and invokes Lean on
the generated file. Only an actual successful check with unchanged source
identity promotes candidates to CERTIFIED statuses. `decide +kernel` performs
kernel reduction, not native proof bypass. The receipt retains input tables,
candidate data, generated Lean, commands, logs and hashes. A Lean failure stays
UNKNOWN. The mathematical PMF interpretation is noncomputable; rational
recursion, occupancy, weight checking and separator checking are executable.

`FiniteActionCertificate.checkPositive_sound` certifies the literal accepted
weight table's original-model action experiment. `checkNegative_path_no_go`
combines rational strict separation with path necessity and quantifies over
arbitrary real PMFs, not merely enumerated rational candidates. The witness
module connects both results to the actual same-source conditional experiment.

## Reproduction

From `formalization/ueot-core`:

```sh
python3 -B docs/compression/theory_completion/unified_closure/action_certificates_v1/test_exact_certificates.py
python3 -B docs/compression/theory_completion/unified_closure/action_certificates_v1/test_certify.py
python3 -B docs/compression/theory_completion/unified_closure/action_certificates_v1/emit_lean_witness.py
lake build UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionCertificateWitness
python3 -B docs/compression/theory_completion/unified_closure/action_certificates_v1/certify.py --registered --output /tmp/ueot-fresh-certificates
```

Use a new output directory. For another finite input, replace `--registered`
with a JSON file containing `P`, `q`, `base`, `p0`, `deployed`, `safe`, `T`.
Probability entries are integers or exact rational strings, never JSON floats.
The generated Lean checker, rather than the Python status, is authoritative.

Full source/build/native/reuse integration uses the existing immutable protocol
through this directory's `native_protocol` adapters. Actual execution and
independent-review receipts, rather than this explanatory document, record the
verified source identity and publication state.

## Boundaries

This is equality of finite **state-path distributions**, not samplewise identity,
ontic parent identity or unrestricted history-policy identification. The action
separator covers time-varying current-observation randomized policies. The
initial-TV obstruction covers arbitrary future causal kernels. No universal LP
search completeness or efficient large-horizon occupancy enumeration is claimed.
External source calibration and scientific applicability remain independent
obligations. The counted frozen core is unchanged; global strong closure remains
NOT_ESTABLISHED and external scientific validation remains UNVERIFIED.

C5 noisy anchors require independent calibrated intervention data; general C4
time-varying sources require a concrete source-drift consumer. They are activation
conditions for later work and are not part of this package.
