# Independent review: physical-safety witness API revision 02

**Status: SOURCE_SEMANTIC_CLEAR_FOCUSED_PASS_NATIVE02_PENDING.**

Reviewer: `/root/c3_executable_search`. Author: `/root/finite_memory_realization`.
This is a new review; it does not rewrite the original source review, original
77-candidate source hints, first full-build receipt or interrupted native01.

| Identity | SHA-256 |
|---|---|
| Original complete witness, saved before editing | `fcc011bd9c7571e9ae95e6df606baaf500e2f7767453be6788af5da470b934e7` |
| Revised witness reviewed here | `08060447a92c3b129351b95615ed2e1b3214e12e9ded21c638d0c6554c400c88` |
| Original complete source corpus | `c344bf6657ab31a32c46fba9feff6d5c04846b8f061d444aec8accb4994ad41b` |
| Revised complete source corpus | `de7c7e287bd1b351ed3f790de58bfd71edf18df4013f7e5aaf2af55a6b3f6379` |

The immutable integration baseline remains
`d503586107974c56e0773b4ea106b41a7d144b43`. The source check confirms 691 modules
and **73 public source candidates** across the seven new modules. This number
comes from the unchanged source parser; actual native confirmation is separate.

## Exact source delta

I read the complete original and revised source and their complete diff. An
independent byte check reverses only the declared changes and recovers the
original file exactly. Those changes are:

1. Three explanatory module-comment lines.
2. `private` on the five original closed trajectory-mass calculations.
3. One public `physical_safety_premises_independent` conjunction theorem and
   its explanatory comment.

Thus all original definitions, original theorem statements and proof bodies
are unchanged. The four other original public witness theorems remain public.
The other six new Lean modules and all five Python protocol files have their
previous exact hashes. Replacing only the revised witness with its saved
original bytes recovers the entire previous corpus fingerprint, confirming
that no other Lean source changed under this review.

The review scans the complete production Lean corpus with comments removed.
There are no references to the five privatized names outside this witness
module. Historical export candidates and historical review records are
evidence for their own sources, not production consumers to be rewritten.

## The public theorem preserves the entire three-source witness

The theorem is unconditional: no safety conclusion, path identity, initial
law identity or support fact is added as an input. Observation, controller,
certification, the safe set and all three actual sources retain their original
definitions. The first conjunct establishes that the safe set is nonempty
and proper. Every subsequent branch binds its own occupancy and path facts
to the same explicit initial PMF and source:

| Original initial state / successor | Actual occupancy | Physical premises | Actual masses |
|---|---|---|---|
| `false / false` | Zero uncertified occupancy at every time | Initial safety and certified-support closure | All-times safety has mass `1`. |
| `false / true` | Zero uncertified occupancy at every time | Initial safety; explicit failure of certified-support closure | Time-one safety and all-times safety both have mass `0`. |
| `true / false` | Zero uncertified occupancy at every time | Explicit failure of initial safety; certified-support closure | Time-zero safety and all-times safety both have mass `0`. |

The closure negation is proved at the actual support point `n = 0`,
`x = false`, the unique action, and `z = true`. The initial-negation proof
uses `true` in the support of the original `PMF.pure true`. Both contradictions
are the explicit fact that `true` is not in `{false}`. Neither negation assumes
the desired failed premise or infers a missing source from a different source.

These are independent counterexamples to deleting either physical premise
from the general sufficient-condition theorem while retaining zero occupancy
and the other premise. They do not claim that the sufficient conditions are a
necessary-and-sufficient characterization of every physically safe process.

### Each original mass fact is still a public consequence

Let `h` be `physical_safety_premises_independent`, and write
`positive := h.2.1`, `badTransition := h.2.2.1`, and
`badInitial := h.2.2.2`. The right-associated conjunction gives the following
direct eliminations:

| Original fact | Projection of the public theorem |
|---|---|
| `safe_source_all_times_mass_one` | `positive.2.2.2` |
| `unsafe_transition_time_one_mass_zero` | `badTransition.2.2.2.1` |
| `unsafe_transition_all_times_mass_zero` | `badTransition.2.2.2.2` |
| `unsafe_initial_time_zero_mass_zero` | `badInitial.2.2.2.1` |
| `unsafe_initial_all_times_mass_zero` | `badInitial.2.2.2.2` |

The public proof explicitly invokes each of those five private helpers once.
The source check verifies all five named references. The upcoming native
export must independently confirm the corresponding actual private constants
in the public proof's `direct_constants`; a source occurrence is not itself
a compiler dependency certificate.

## Why this is an acceptable interface change

The stated trigger was an actual nonterminating-in-practice public stored-type
comparison involving two large, closed trajectory-mass expressions. That is a
performance failure, not a completed comparison or a detected type collision.
The original interrupted run and diagnostic must remain recorded as such.

The revised public unit has a coherent mathematical purpose: a complete,
source-matched independence witness, with the two missing physical premises
explicitly shown false. Its private calculations all serve that public
statement and remain extractable as public consequences. There is no opaque
wrapper, artificial tag, new nominal certificate type, or extra conclusion
field supplied by the caller. This is more than renaming a declaration to
force a cheap type mismatch, although its origin in the performance blocker
must remain disclosed.

The scope of public pairwise comparison **does change**. The old nine public
witness declarations become five, so the whole increment has 73 source
candidates instead of 77. The five closed calculations are no longer separate
members of the public `Meta.isDefEq` comparison domain. It would be inaccurate
to say that every former public pair has now passed, or that all audit scopes
are identical to native01.

The comparator implementation, stored-type discipline, transparency, universe
handling and complete all-public comparison rules remain unchanged. The full
compiler-owned theorem audit still includes the private calculations and
checks their owners, visibility, types, standard axiom closure and direct
constants. Public registered direct edges can consequently differ; the full
native audit must preserve the private proof path instead of fabricating a
public direct edge to a transitively used theorem.

## Actual focused execution and remaining gates

I independently read the unmodified coordinator output
`FOCUS_10_TOOL_OUTPUT.txt`. It records the revised source SHA above, Lean exit
code `0`, **3.559897708 seconds**, and an empty log with SHA-256
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
The accompanying JSON binds that original output and its actual command.

This establishes focused Lean success for the revised witness. The original
full-build success at the old fingerprint is not transferred to this source.
Manifest02, full build02, both unchanged-algorithm native executions, actual
complete private ownership/axiom/dependency coverage, fixed export equality,
registration and final current-source gates require their own receipts.
The 89-test immutable parser result can be reused because its tested inputs
are unchanged; the parser suite need not be rerun for this Lean API change.

The earlier source hints and semantic CLEAR remain historical records bound
to their original sources. `source-hints-03` and a separate semantic supplement
provide the revised binding. No counted-ledger authority, frozen P-ID category,
physical empirical claim or `NOT_ESTABLISHED` global-closure status is changed.
