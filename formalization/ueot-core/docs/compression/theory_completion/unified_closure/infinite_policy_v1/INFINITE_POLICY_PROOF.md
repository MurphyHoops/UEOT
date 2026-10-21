# One infinite causal policy from all finite horizons

Primary class: **CONDITIONAL THEOREM**. Integration and execution status are
recorded separately in the enclosing release evidence; this note does not
substitute for a Lean compile or resulting-main receipt.

## Final integrated proof acceptance

The enclosing integration now binds the final 678-module source fingerprint
`60cd5f8ab161c5b51394463c466947a4c6a6c1742ecdcd9c2bbfc41c0c06bd31`.
The infinite-policy module itself retains the `57bd13aa…` source hash below.
The actual final full build passed in 39.787 seconds; both native executions
passed and produced equal complete JSON. The new 12-module native census
covers all 199 owned theorem constants, including this module's private
selection proof, and accepts only the standard three axioms. Independent
source and execution review is CLEAR. Full UMC audit also passed over 79
modules and 1,073 owned theorem constants. Canonical Git/publication status is
recorded separately in the [integration evidence](../longterm_control_statistics_v1/RESULTS_AND_BOUNDARIES.md#5-acceptance-evidence).

## Earlier integrated-source execution checkpoint (retained history)

The final source SHA256 is
`57bd13aae378429d71bb3c6f9094d0f837378d7127924b51a15e7e8b65e71757`
(259 lines). Relative to the first focused compile below, the only proof change
replaces the hand-written pure-PMF support argument by direct reuse of
`PMF.support_pure` and `Set.mem_singleton_iff`. Its theorem types and source
construction are unchanged. This removed an exact repeated proof block rather
than disguising it by formatting.

The root executed **`lake build UEOT`: PASS**, exit code **0**, in
**19.151 seconds** for that earlier integrated 678-module source inventory. The
inventory fingerprint is
`692626c6e91e1513843a6a6c8a37585c810d39ce2efd009e3a4aa347a022b8f5`;
it is a source-inventory digest, not a Git commit ID. The full-build log SHA256
is `3fbbcd49ca412f8148301542f7404a6f03e9db915c43a99636562ff9bed693b5`.
The actual receipt is retained in
`/Users/murphyhoops/Documents/ueotlean-worktrees/core-books-handoff-20261020/longterm-policy-sisc-evidence-20261021/full-build-02/FULL_BUILD_RECEIPT.json`.

The complete 678-module exact-clone diagnosis reports the same 68 historical
groups, with no new or missing groups. Independent static review of this final
source is separate from the root's compiler execution. Native axiom/type-reuse
checks, final integrated-head review and resulting-main acceptance remain
root-owned gates; this note does not predeclare those outcomes.

## First focused execution checkpoint (retained history)

The root agent executed the actual focused Lean command on the isolated Mac
validation tree and verified **PASS**, exit code **0**, in **32.873 seconds**.
The source SHA256 at that checkpoint was
`ea807dac62763c9e3b455e6a686087e7b07c831fc67e3965938bec94b2e45856`.
The compiler log is empty, with SHA256
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

The actual receipt and source snapshot are retained in
`/Users/murphyhoops/Documents/ueotlean-worktrees/core-books-handoff-20261020/longterm-policy-sisc-evidence-20261021/infinite-policy/attempt-01/`;
the receipt is `STATUS.json`. Toolchain: Lean **4.33.1**. The governing base at
execution is `ff71e63256c88ad2bb527fdd3004d55c77894ab7`; its governance-only
changes leave the imported Lean baseline unchanged from the preceding Core
checkpoint.

This historical checkpoint establishes the first focused module compile. It
does not itself assert unified production imports, full-library regression,
native axiom/type-reuse checks, independent review, or resulting-main acceptance.
The current integrated-source checkpoint above supersedes its source freeze;
the original snapshot and receipt remain unchanged.

Two earlier child-channel Local Mac tool requests returned `aborted` without a
PID, output or execution receipt. They are not compiler attempts and supply no
PASS/FAIL evidence; the root-executed `attempt-01` is the first confirmed
compiler invocation for this candidate.

## Exact new mathematical responsibility

The source module is
`UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/InfiniteSupportViability.lean`.
It imports and consumes the existing production `FiniteSupportViability`
definitions and actual-law theorems. It does not redefine the source support,
causal history, deployment row law or finite viability predicate.

Fix one initial PMF `p₀`, one observation `q`, the whole sequence
`P : ℕ → X → A → PMF X`, and the whole certification predicate
`certified : ℕ → X → A → Prop`. For a complete causal policy `π`, write

\[
U_n(\pi)=
\bigl(\operatorname{coverageDeploymentRowLaw}(p_0,q,P,\pi,n)\bigr)
  \{(x,a):\neg C_n(x,a)\}.
\]

The terminal endpoint
`arbitrarily_long_zero_uncovered_iff_single_all_times_policy` proves

\[
\boxed{
(\forall T\;\exists\pi_T\;\forall n<T:\ U_n(\pi_T)=0)
\quad\Longleftrightarrow\quad
(\exists\pi_\infty\;\forall n:\ U_n(\pi_\infty)=0).
}
\]

The quantification over `T` occurs after the source data have been fixed. The
policies supplied at different horizons need not agree. The proof constructs a
new complete policy and proves its own actual supported-history invariant.

## Assumptions and source identity

| Item | Exact scope |
|---|---|
| State and action | `Fintype X`, `Fintype A` in the actual row-law endpoint |
| Observation | Arbitrary `Y`; no `Fintype Y` and no observation-measurability premise |
| Time dependence | `P n` and `certified n` may be nonautonomous |
| Initial law | Original `p₀`; no safe filtering or renormalization |
| Policy | Complete action-observation history to an action PMF at each time |
| Totalization | One explicit complete fallback `πbase` |
| Events | Existing measurable-space and measurable-singleton instances on `X` and `A` |
| Source agreement | All occurrences use the same `p₀`, `q`, `P`, `certified`, and the constructed policy |

The all-horizon support predicate has no policy or occupancy conclusion as a
field:

\[
\operatorname{InfiniteViable}(n,S)
\;:=\;\forall k,\operatorname{Viable}(n,k,S).
\]

The finite-action selection theorem itself does not require finite `X` or finite
`Y`; finite `X` is inherited by the actual finite-PMF support/row-law bridge.
No separate `Nonempty A` premise is hidden: the first viable step supplies an
action. The actual theorem keeps the complete fallback as an explicit input,
as the existing finite-horizon theorem does.

## Proof, without exchanging a limit and an existential quantifier

1. `viableWith_horizon_pred` proves by induction that deleting the final required
   row preserves viability. It applies to the existing abstract successor
   recursion, including time-dependent data.
2. For a fixed viable `(n,S)`, let `Dₖ` contain actions certifying all states in
   `S` and leaving every nonempty observation successor viable for `k` steps.
   Every `Dₖ` is nonempty and `Dₖ₊₁ ⊆ Dₖ`.
3. The private finite-selection proof argues directly. If every action were
   excluded at some depth `k(a)`, the finite maximum of these depths would
   exclude all actions, contradicting nonemptiness. The action selected from
   the intersection therefore works at every depth.
4. `infiniteViable_step` concludes that this one action certifies `S` and that
   all of its nonempty observed successors are again all-horizon viable.
5. `infiniteViablePolicy` selects the corresponding pure action at a viable
   history and uses `πbase` at every other history.
6. `infiniteViablePolicy_supported_histories_viable` inducts over **the actual
   histories of this same policy**. The old production
   `mem_coarseLaw_zero_support_iff` supplies the initial support and
   `mem_coarseLaw_succ_support_iff` supplies the exact positive-history,
   positive-action and nonempty-successor conditions at each step.
7. `infiniteViablePolicy_zero_uncovered` consumes the existing
   `zero_uncovered_iff_support_certified`. This converts the invariant into
   zero uncertified mass in the actual deployment row law at every time.
8. The two terminal equivalences use the existing
   `initial_viability_iff_exists_zero_uncovered_policy` to move between the
   finite-horizon policy witnesses and the initial all-horizon support
   predicate. The reverse infinite-to-finite implication reuses the same
   infinite policy for every horizon.

## Reuse and genuine strengthening

The original production endpoint fixes one `T`. Its output is an existential
policy whose rows before `T` are certified. The new endpoint changes the order
of the horizon and policy quantifiers by proving the missing finite-choice
construction. It is neither an alias nor a change of the source experiment.

| Existing theorem | New use |
|---|---|
| `initial_viability_iff_exists_zero_uncovered_policy` | Translate each finite existence claim into the same backward support predicate |
| `mem_coarseLaw_zero_support_iff` | Identify initial reachable observation fibers |
| `mem_coarseLaw_succ_support_iff` | Propagate the invariant on this policy's actual positive histories |
| `zero_uncovered_iff_support_certified` | Convert pointwise support certification to actual zero row-event mass |

The source contains no `sorry`, `admit`, new axiom, unsafe proof escape, or
`native_decide`. Public and private theorem axiom closure remains an execution
gate; the textual absence of escapes is not a substitute for that gate.

## Boundaries preserved

- **Infinite consistency is not finite memory.** On actual viable histories,
  the chosen action depends on time and the current trace support. An arbitrary
  nonautonomous source may require unbounded time information. A finite support
  fixed-point controller with a cardinality/stabilization bound is a separate
  next result and is not asserted by this module.
- **The finite witnesses are not the constructed policy.** Neither the original
  `viablePolicy T` choice nor a previously supplied `πT` is identified with the
  new `Classical.choose` action. This module proves its own row-law claim.
- **Fallback remains complete.** It may depend on all past history at null or
  nonviable histories. The theorem does not replace it with a stationary rule.
- **Reference histories remain separate.** A reference process may visit
  histories with zero source mass. The actual-source invariant does not
  establish policy equality there or rewrite a reference-check budget.
- **Certification is not physical safety.** The result requires extra source
  semantics to imply preservation of any separately specified safe set. It
  does not show positive infinite survival or a QSD/Doob conclusion.
- **No exchange of source data with the horizon.** Changing `P`, `p₀`, `q` or
  `certified` with `T` exits the terminal theorem's hypothesis.
- **No finite-state memory claim about the probability simplex.** Only exact
  supports appear here; no assertion is made that full posterior probability
  vectors range over a finite set.

This is additive, uncounted TheoryCompletion research. It changes no frozen
P-ID, no MINCORE generator classification, and no global scientific closure
status. The finite-support-memory realization and physical-safety bridge remain
separate obligations.
