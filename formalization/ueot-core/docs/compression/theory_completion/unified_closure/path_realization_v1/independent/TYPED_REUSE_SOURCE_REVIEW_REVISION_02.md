# Source semantic reuse review — API revision 02

**Status: `SOURCE_SEMANTIC_REUSE_CLEAR_NATIVE02_PENDING`.**

Reviewer: `/root/c3_executable_search`. This supplement binds the source-level
reuse assessment to the revised physical-safety witness. It preserves the
original review and all three source-hint snapshots. It does not certify an
uncompleted native comparison or transfer a prior full-build result to changed
source.

## Current source identity

| Item | Value |
|---|---|
| Immutable integration baseline | `d503586107974c56e0773b4ea106b41a7d144b43` |
| Complete current source fingerprint | `de7c7e287bd1b351ed3f790de58bfd71edf18df4013f7e5aaf2af55a6b3f6379` |
| Revised `FiniteMemorySafetyWitness.lean` | `08060447a92c3b129351b95615ed2e1b3214e12e9ded21c638d0c6554c400c88` |
| Current source modules | `691` |
| Public source candidates in the seven-module increment | `73` |
| Nonempty lexical hint groups | `25` |
| New/old candidate pairs | `61` |
| Distinct previously registered hinted theorems | `38` |

The source-only tool was run again against the exact immutable baseline, using
the unchanged baseline parser and reuse consumer. It checks source identities
before and after its run. The historical consumer is reconstructed as input;
this source-hint calculation does not substitute for the eventual live
consumer's current-source freshness check.

Evidence:

- [Source-hints-03 receipt](../reuse-review/source-hints-03/SOURCE_ONLY_HINTS_RECEIPT.json),
  SHA-256 `721487fe65cbc45a8f6cb3e0833ae5ce83cb0c9ad2a00c81da5d189a91648a26`.
- [Source-hints-03 complete hints](../reuse-review/source-hints-03/LEXICAL_REUSE_HINTS.json),
  SHA-256 `4be35fb5fd08e2aa7a8ea61f504462fbdd439b17bedc52af9daf1f86c8c5e0ac`.
- [Machine-readable semantic supplement](TYPED_REUSE_SOURCE_REVIEW_REVISION_02.json),
  SHA-256 `b30b5cae09c36f09616f8f69a602481bb9f59cbfb0402db58e0fbf4dd741357d`.

These are source observations. Actual compiler ownership, stored types,
private/generated theorem enumeration and registered edge counts remain the
responsibility of the new native export.

## Which previous assessments remain applicable

The [original semantic review](TYPED_REUSE_SOURCE_REVIEW.md) and its
[complete per-pair evidence](TYPED_REUSE_SOURCE_REVIEW.json) remain unchanged.
The latter has SHA-256
`75c0f68c4a7436fb7404e2b92a3001a66d719b1be64f54e091cd737ac082a081`.

For every one of the current 25 nonempty hint groups, the supplement checks
that its entire hint record equals the corresponding prior record, including
the candidate list and ordering, and that its complete new Lean source file
has the previously reviewed hash. It also checks the old candidate names
against the exact prior pair assessments. All 61 retained pairs therefore
retain the prior semantic decision on unchanged declarations and unchanged
candidate evidence. The retained review indices are `1–9` and `11–26`.

The prior C3 authorship disclosure and the separately authored C3 review remain
applicable. This supplement does not turn an author's self-check into an
independent mathematical review.

The only formerly hinted public declaration removed from the comparison
domain is `FiniteMemorySafetyWitness.safe_source_all_times_mass_one`, prior
review index `10`. Its two old candidates were the generic all-times safety
results in `ViabilityPath` and `ViabilityTrajectory`. Its statement and proof
are still present, byte-for-byte, as a private computation used by the new
public theorem. Both original candidate assessments and all original source
hints remain historical evidence. The other four privatized mass calculations
had no lexical candidates; their absence from the new public hint table does
not remove their mathematical content or their compiler-owned audit duties.

## Manual assessment of the new public endpoint

The new `physical_safety_premises_independent` endpoint has no automatic lexical
hint. Absence of such a hint is not evidence of novelty and is not a completed
stored-type comparison. Its mathematical content was reviewed directly in
the [API revision source review](memory-api-revision-02/REVIEW.md), with exact
byte checks and identities in [its JSON receipt](memory-api-revision-02/REVIEW.json),
SHA-256 `1fb1b5a98eb3973fdbcaa8e4fe59ff60feb1ddb9b41a09edd37d966704bc0aca`.

The theorem is an unconditional conjunction about the original three actual
initial/source pairs. It establishes a proper nonempty safe set and, for each
pair, its own all-times zero uncertified occupancy. The positive pair has
initial safety, certified transition-support closure and all-times safety
mass one. One counterexample has initial safety but explicitly lacks the
transition condition, with time-one and all-times safety masses zero. The
other has transition closure but explicitly lacks initial safety, with
time-zero and all-times masses zero.

The generic physical-safety bridge remains the canonical result for the
positive implication. The unchanged positive private computation invokes
`controller_all_times_physical_safe`; that bridge reuses the existing
countable-intersection safety mechanism. The new public proof consumes the
positive computation rather than reproving that generic bridge. Its two
negative support statements use explicit points in the actual pure-PMF
supports. They add the precise independence conclusions missing from the
earlier separate scalar mass endpoints.

The public proof explicitly invokes all five original private mass
calculations, and each original mass equality is a direct projection of the
public conjunction. The source review lists those five projections. There is
no opaque or nominal wrapper, new caller-supplied conclusion, artificial tag,
or added premise. The result demonstrates that neither physical premise can
be universally dropped from the sufficient-condition theorem while keeping
the other premise and zero occupancy. It does not assert an if-and-only-if
characterization of physical safety.

The mathematical unit of the new API is consequently coherent and does not
duplicate the earlier generic positive theorem. The implementation-triggering
performance failure remains relevant evidence and is explicitly disclosed in
the source review and the author's [revision explanation](../memory-realization/API_REVISION_02.md).

## Audit scope and execution status

The five scalar calculations leave the public pairwise `Meta.isDefEq` domain;
the new conjunction enters that domain. Public candidates therefore decrease
from `77` to `73`. The comparator implementation and its rules remain
unchanged, but the old 77-element comparison domain must not be described as
having completed the new run. The interrupted native01 and its diagnostic are
not a native PASS and do not establish that the stalled pair was equal or
unequal.

The five private calculations remain in the complete compiler-owned theorem
audit, including owner, visibility, actual stored type, axiom closure and
direct constants. The new native output must confirm that the public proof
actually references their compiled private constants. The source-level named
references checked here do not themselves supply that compiler evidence.

The revised witness has actual focused Lean PASS at the stated SHA,
`3.559897708` seconds with exit code `0` and an empty log; the independent API
review read the original coordinator output. The earlier immutable parser
suite's **89-test PASS** remains applicable because none of its tested inputs
changed. This supplement did not rerun that suite.

New full build, both native executions and their equality, actual private
dependencies, overlay registration, the final live consumers, the complete
current-source clone gate and FKRG still require their own exact-source
receipts. No fixed native hashes, direct-edge counts or current native PASS
are inferred from this source review. No frozen P-ID, counted result or global
`NOT_ESTABLISHED` status changes here.
