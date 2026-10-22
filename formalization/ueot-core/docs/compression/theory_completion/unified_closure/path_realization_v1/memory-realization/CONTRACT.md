# Actual finite-memory realization and physical safety

## Scope and current evidence

This work extends the accepted `FiniteMemoryPolicy`, `SupportMemoryController`,
`SameSourceInfinitePrefix`, and `ViabilityPath` APIs. It constructs the actual
state–memory process of one controller and proves the source identities needed
to transfer physical safety to its infinite state path.

All three modules have now passed focused actual Lean execution, with empty
successful logs. Their exact accepted source hashes and durations are:

| Module | Source SHA-256 | Actual duration |
|---|---|---:|
| `FiniteMemoryRealization` | `8306c376acbf26db8ae70a5064460c9e423da527a0c89efe4ec18e0e6150191f` | 5.195 s |
| `FiniteMemoryPhysicalSafety` | `7f231017ef32eb607c0187dc659a139101f92ee4ad2ed434f35d4f0687a46cdd` | 3.703 s |
| `FiniteMemorySafetyWitness` | `fcc011bd9c7571e9ae95e6df606baaf500e2f7767453be6788af5da470b934e7` | 3.801 s |

The first realization attempt had two PMF-rewrite elaboration failures. The
first safety attempt had a coordinate-simplification failure. The first witness
attempt had a PMF receiver parsing error and two uses of the no-argument ENNReal
nonnegativity lemma with an extra argument. These proof-level failures were
corrected without changing the mathematical statements, and their original
failed receipts remain retained by the coordinator. This current-state contract
does not rewrite those receipts or substitute for the still separate full-build,
native, canonical, and release certificates.

Owned source files:

- `UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteMemoryRealization.lean`
- `UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteMemoryPhysicalSafety.lean`
- `UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteMemorySafetyWitness.lean`

The public namespace of the first file is
`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteMemoryRealization`.
The second uses the corresponding namespace `FiniteMemoryPhysicalSafety`.

## One original experiment

Fix an initial PMF `p₀ : PMF X`, observations `q : X → Y`, the complete numeric
source sequence `P : ℕ → X → A → PMF X`, and the already defined controller

```lean
controller : FiniteMemoryController M Y A
```

Its initial memory is `controller.initialMemory (q x₀)`. Before action `aₙ`, its
memory is the existing `controller.memory n` evaluated on the original
observation/action record. Action `aₙ` is sampled from `controller.action mₙ`;
the next state is sampled from `P n xₙ aₙ`; then

\[
m_{n+1}=\operatorname{update}(m_n,a_n,q(x_{n+1})).
\]

The original history law is the accepted
`microLaw p₀ q P controller.policy n`. The new definitions do not replace this
policy by a finite-horizon selector or by a separately chosen witness.

## Constructed augmentation

`augmentedInitial` maps the original initial state to its actual initialized
memory:

\[
\widetilde p_0=\bigl(x\mapsto
 (x,\operatorname{initialMemory}(q(x)))\bigr)_*p_0.
\]

`augmentedRow controller q P n (x,m)` first samples the original action and
source transition, and then maps the result to
`(z, controller.update m a (q z))`. On finite types its point masses are

\[
\widetilde P_n((x,m),(z,m'))
=\sum_a\operatorname{action}(m)(a)P_n(x,a)(z)
\mathbf 1\{m'=\operatorname{update}(m,a,q(z))\}.
\]

`augmentHistory` replays the recorded actions and retains every state–memory
pair, including time zero. Its last pair is proved to be the original last
state and the original controller's replayed memory.

The principal finite theorem, `actual_augmented_history_law`, proves

\[
(\operatorname{augmentHistory}_n)_*\operatorname{microLaw}_n
=\operatorname{causalLaw}_n(\widetilde p_0,\widetilde P).
\]

This is an equality of complete history PMFs, stronger than an equality of
terminal marginals. It follows by induction using a dependent PMF map/bind
identity. No initial-law, row-law, or history-law agreement is an input field.

`eraseMemory_augmentHistory` and `augmented_history_state_projection` show that
erasing memory retains the entire original state record. The original
state-only marginal is not asserted to be Markov. Actions may be lost by the
augmentation, so an event that depends on unrecoverable actions needs its own
retained-action map; it is not automatically an event on the augmented path.

## Infinite law with the same numeric rows

`sequenceTrajMeasure` applies the existing Ionescu–Tulcea construction to the
row sequence `J : ℕ → S → PMF S`. At step `n`, the kernel reads the last state
of the supplied prefix and applies `J n`. Its full finite-prefix identity
`state_history_eq_sequence_prefix` is proved from the actual zero-time and
one-step identities of that construction.

`augmentedTrajMeasure` instantiates this construction with the exact
`augmentedInitial` and `augmentedRow`. Its theorem
`actual_augmented_prefix_eq` identifies every finite prefix with the
pushforward of the original `microLaw`. The event-mass theorem makes the
same statement for every finite state–memory-prefix event.

`stateTrajMeasure` is the coordinatewise first-coordinate projection of this
same infinite augmented law. `actual_state_prefix_eq` and
`actual_state_prefix_event_mass` prove complete state-prefix identities. In
particular, `stateTrajMeasure_coordinate_mass` identifies every time-`n`
event with the original microscopic terminal event, including `n = 0` and
the unmodified initial PMF.

| Layer | Type assumptions |
|---|---|
| Augmented initial law, rows, replay, complete finite PMF equality | No finiteness or measurability assumptions; `Y` arbitrary |
| Infinite augmented law and PMF-to-prefix measure identity | Finite `X` and `M`, with measurable singletons; `Y` and `A` arbitrary |
| Original finite-event mass and physical support arguments | Additionally finite `A`, with measurable singletons |
| Support-controller consumer | Existing finite support-memory type, supplied with its finite discrete measurable structure |

All numeric transition rows may vary with time. A fixed support relation is
not required by the general realization or physical-safety theorem. In the
support-controller consumer, support homogeneity is an explicit premise
needed by the existing controller's winning-support proof. It does not turn
the numeric rows into one fixed stochastic or killed matrix.

## From certification to physical safety

For a physical safe set `K`, the additional premises are:

1. **Original initial support is safe.** Every `x ∈ p₀.support` lies in `K`.
2. **Certified actual transitions preserve safety.** For every time `n`,
   safe state `x`, certified action `a`, and actual successor
   `z ∈ (P n x a).support`, the successor lies in `K`.
3. **The same policy has zero uncertified occupancy.** At every `n`, the
   accepted `coverageDeploymentRowLaw p₀ q P π n` assigns zero real mass to
   the uncertified state/action rows.

`supported_micro_history_safe` first works for any complete causal policy
`π`. A supported successor history gives a supported original prefix,
selected action, and actual transition. The existing zero-occupancy/support
equivalence certifies that selected action at the realized state. Induction
then propagates the physical safe set. `actual_finite_safety_one` gives
probability one for the physical no-failure event in every original finite
experiment, with time zero included.

For the finite-memory policy, the proved coordinate identity transfers these
finite guarantees to `stateTrajMeasure`. The existing countable-intersection
theorem `ViabilityPath.all_times_safe_eq_one` yields

\[
\operatorname{stateTrajMeasure}
 \{\omega:\forall n,\ \omega_n\in K\}=1.
\]

This endpoint is `controller_all_times_physical_safe`. Its physical
conclusion and its path-law identity are both proved from the original data.
Zero uncertified occupancy alone supplies neither initial safety nor a
physical interpretation of certification.

## Existing support controller as an actual consumer

`supportMemoryController_all_times_physical_safe` instantiates the generic
controller theorem with the already accepted `supportMemoryController`. It
uses the same initial PMF, observation map, numeric source sequence, fallback,
fixed support relation `R`, and fixed certification predicate `C`.

Its exact support matching, certification matching, and initial-winning
premises are those of the existing controller. The existing
`supportMemoryController_zero_uncovered` discharges the zero-occupancy
premise. The new premises are the original physical initial safety and the
statement that certified `R`-successors preserve `K`.

The resulting theorem refers to the newly constructed support controller's
own actual infinite state law. It does not equate that controller with an
earlier horizon-dependent policy, alter a reference process, or reduce the
reference process's complete-history checking budget.

## Positive source and independent physical-premise boundaries

`FiniteMemorySafetyWitness` uses `X = Bool`, `M = A = Y = Unit`, a constant
observation, and the complete one-memory/one-action controller. The physical
safe set is `K = {false}`, proved proper and nonempty. Certification is true
for every row, and `all_rows_zero_uncovered` derives zero uncertified occupancy
in every actual deployment row of each example.

| Actual source | Initial safety | Certified transition closure | All-times safe mass |
|---|---|---|---|
| `p₀ = δfalse`, every transition returns `false` | Holds | Holds | `1` |
| `p₀ = δfalse`, every transition returns `true` | Holds | Fails | `0`, already at time one |
| `p₀ = δtrue`, every transition returns `false` | Fails | Holds | `0`, already at time zero |

The positive theorem invokes the actual infinite physical-safety endpoint.
Each negative theorem uses `stateTrajMeasure_coordinate_mass`, proves the
corresponding original microscopic PMF event has mass zero from its support,
and bounds the all-times event by that coordinate event. Consequently neither
physical premise can be removed merely because all uncertified occupancies
are zero. In the third example the source repairs the state immediately;
repair does not remove the original failure at time zero from this event.

These examples test the physical premises, not a lower bound on memory
requirements. The accepted `FiniteMemorySeparation` remains the independent
two-memory example separating memory control from homogeneous randomized
current-observation feedback. The new realization theorem applies to that
controller without changing its already proved policy or occupancy result.

## Integration obligations

Compilation order is `FiniteMemoryRealization`, `FiniteMemoryPhysicalSafety`,
then `FiniteMemorySafetyWitness`. All must compile against the accepted base
and their actual dependency closure. The resulting infinite-law and safety
endpoints should receive an axiom audit and independent source review.

The finite-prefix identity must be reviewed before accepting the physical
safety transfer. In particular, review must check the memory-update timing,
the original initial law, the same controller action distribution, all
numeric rows of `P`, and the absence of a state-only Markov assumption.

No existing production file, root import, frozen ledger, reference-risk
budget, or physics/QM source was changed by this work. Public aggregation
and release validation belong to the coordinator after actual verification.
