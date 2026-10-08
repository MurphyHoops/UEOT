# SISC SI-4 — Directed Finite Paths and Lineage Ambiguity

Status: **LOCAL LEAN-CHECKED FINITE-HORIZON SUBCLASS**. C4 scientific port
remains OPEN. No infinite path/measurable selector or physical identity result.

## Exact positive theorem

`SISCFinitePaths.lean` defines a proof-relevant `DirectedFinitePath edge n p q`
with intermediate causal edges, rather than a single opaque endpoint. If:

1. every registered state has *some* causal successor whose realized transport
   error is at most `delta`, and
2. the declared realized transport is `M`-Lipschitz for nonnegative `M`,

then `finite_directed_history_with_bound` constructs an n-step path and
certifies its terminal error. With zero initial error the recurrence is

`E(0)=0; E(n+1)=delta+M*E(n)`.

The finite result does not choose a universal global successor function.
Existential witnesses at each step are enough for this **finite** induction.
Infinite-time path claims, regular selection or a unique composition law
require strictly stronger assumptions and independent work.

## Negative controls

- `split_and_merge_can_coexist` gives a single causal relation with both
  one-to-many successors and many-to-one predecessor events.
- `without_coverage_one_step_path_may_fail` demonstrates that a lost source
  need not have even a one-step path, if coverage is absent.
- The SI-1/2 no-go proofs remain active: finite path existence does not
  entail unique token identity, unique genealogy, or universal physical
  persistence.

## Scientific limits

The constant `delta` and `M` are **inputs**, not empirical quantities inferred
by SI-4. SI-3 derives local forward coverage in one finite response-channel
model, but combining this across changing kernels and protocols still requires
explicit intermediate validity and quantitative transport assumptions. An
edge-based lineage graph is a certificate model, not a derived metaphysical
object semantics.

The named next extension is non-autonomous kernels, finite-time variable
`delta_t, M_t`, time-dependent candidate birth/death and externally measured
lineage, followed *only later* by path-space measurability.

Acceptance requires public import, focused and full clean Lean compilation,
negative examples, a separate stage commit, no frozen Core ledger mutation.
