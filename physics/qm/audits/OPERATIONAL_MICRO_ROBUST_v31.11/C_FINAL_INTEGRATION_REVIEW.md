# C final integration review: chapter 67 and the source-to-output checker

Reviewer: native research agent C, 2026-11-11. This is an independent internal
AI review of root's integration, not external human peer review. No public
repository file was edited by C during this review. Only this report and
`research_c/v38_increment_checks.py` were written.

## Verdict

**The integrated mathematical chain is accepted within its stated ideal
complex-quantum model. Two substantive wording corrections identified in
this review have been applied in both languages and read back.** No remaining
mathematical blocker was found. Final execution/source identity and publication
metadata were still in preparation at the inspected checkpoint; they must not
be described as completed merely because this paper review passes.

In particular, the current `verify_integration.py` had changed since its
existing receipt. The narrow current-source execution needs to be performed
and bound before the new source is called accepted. This is a receipt/identity
issue, not a theoretical counterexample.

## 1. Exact inspected identities

After the two bilingual wording corrections, the manuscript identities read
by C were:

| Artifact | SHA-256 |
|---|---|
| `physics/qm/book/UEOT_PHYSICS.md` | `5dbbb8601391e319caaa12c72f326d5cd6d8f5b004c5cdc354619e8f6af48017` |
| `physics/qm/book/UEOT_PHYSICS.en.md` | `2bd7159cbb463c21cdd2fc29ddb4fb9cc6ab4c948c3eb6019cd75ea86cd46228` |
| `physics/qm/operational_micro_robust/verify_integration.py` | `5e8d79c6184162526e23223644fa8aab2bf3c8238c178d52eeb4bb19e933c361` |
| Existing `runtime/independent-integration.json` | `de5cf6b3ca97cf5ab8e295e7bcb0fa9a5b853679107bf92e182750a288bd890f` |
| `runtime/micro-truncation.json` | `26579b0bedaf2d27ef377a9963ec4f03ec1e8b7d078efa3242a200e86d93c31d` |
| `runtime/synthetic/synthetic_analysis.json` | `1409cdbef6e2bd796f126a19011b4858ea7dc74ced4c7f852450c18a1418edf5` |
| Current and prior-v3.8-copy `CHAPTER_DOSSIER.json` at inspection | `dc91293f87333c20d0d96897137981456b1dbf8710f58a1818461d503057d960` |

Runtime paths in the table are relative to `physics/qm/kernel/evidence/v31.11/`.
Later edits or executions need their actual identities. This report does not
retroactively certify bytes not yet inspected.

## 2. Complete preparation-failure output

The common physical output must include `prep_fail` and the original seven
records prefixed by `pass/`. The ideal target has a zero prep_fail block.
The actual filter has Kraus Pi_N and I-Pi_N; it retains the fail output.
The book now explicitly states this enlargement and forbids free retries of
unknown quantum input/reference states.

The proof decomposes into two actual comparisons:

1. Ideal always-pass target on rho versus physical pass/fail filtering
   followed by that same target on the pass branch. The full difference is
   bounded by b(delta)=[sqrt(delta(4-3delta))+delta]/2.
2. Replace the target by the compiled finite implementation only on the pass
   branch. Its error is at most s_N times the conditional implementation
   error, hence at most that error.

Thus using the safe b(delta)<=sqrt(delta)+delta is valid; no failure mass is
deleted, and no second independent cutoff penalty is charged. With
delta<=1/4096 and adaptive radius 1/50,

    65/4096 + 1/50 = 3673/102400 = 0.035869140625 < 1/20.

The remaining allowance is exactly 1447/102400. It remains an unconsumed
model-error allowance, not evidence of measured device precision.

### Which actual executable covers which part?

Root's inherited-interpreter run uses a known G<=1 entangled input. Its
projection failure probability is zero, so it checks all seven source leaves,
same-source conditioning, adaptive compilation, retained reference and costs
without numerically testing a nonzero prep_fail block. The chapter correctly
says this. The general high-cutoff guarantee is analytic, not a giant-matrix
experiment or a numerical proof of an infinite quantifier.

B's separate `micro-truncation.json` contains the nonzero preparation-failure
pressure test: delta=1/4, normalized-projection distance 1/2, and full physical
distance (sqrt(13)+1)/8 approximately 0.575693909433. Its complete-failure bound
is saturated. This directly checks that replacing the full physical output by
a success-only posterior would give the wrong distance. These two execution
scopes should remain separate in the final evidence summary.

An ideal high-cutoff spectral filter is an additional preparation operation.
The microscopic conservation theorem does not by itself certify that a real
device implements that filter. This limitation is stated in B's report and
the book's device-error qualification and must remain visible.

## 3. Actual source, controller, and uncertainty quantifiers

The original source has f,0f,1f failure leaves and four two-success leaves.
The scalar backward effect formula applies only at successful prefixes;
failure leaves have zero acceptance effect. This restriction is now explicit.
The conditional target is input-independent CPTP because H_0=s^2 I, so its
truncation comparison legitimately avoids generic rare-event amplification.

Root's exact integration formulas and inherited source interpreter use the
same q, same actual gates and same ordered gate products. The exact matrix
witnesses use two different basis orders in C and root/B, but the current
script includes an explicit permutation identity connecting them. This
identity was added after the earlier integration receipt, so it must be
included in the current-source execution, not attributed to the old one.

The 1/50 minimax claim is valid over the frozen design interval [.48,.52]
with deterministic-label actions and no additional parameter-sensitive
in-run observation. The realized confidence interval [.4861,.5061] is
narrower; the manuscript correctly says the design policy is conservative
there and does not inherit the design lower bound or optimality.

### Correction R-C-1: given weights versus asserted existence — resolved

The initial integrated P-ROB-01 omitted explicit nonnegative normalized
weights and displayed a standalone existential deployment quantifier inside
the inequality statement. This could wrongly suggest that a triangle bound
constructs a small-residual policy. C requested a correction.

Both languages now require a **given** candidate w(D_cal), w_a>=0,
sum_a w_a=1, and a certified nominal residual. The bound is for that candidate.
The required design quantifier exists-w/for-all-theta is explained separately,
with an explicit statement that the sufficient inequality does not supply
such a small-residual candidate automatically. The actual proof uses exactly
these assumptions. The correction was read back in both languages.

## 4. Calibration, held-out records, and evidence classification

C independently recounted the integrated raw files, without using the
generating parameter in the analysis:

| Data | Actual counts |
|---|---|
| Calibration, 80000 ordered flags | 0:30401; 1:29755; f:19844 |
| Source holdout, 4096 records | f:986; 0f:425; 1f:366; 00:528; 01:626; 10:589; 11:576 |
| Compiled holdout, 4096 records | f:0; 0f:0; 1f:0; 00:1032; 01:1030; 10:992; 11:1042 |

The integrated raw-file SHA-256 values match the analysis receipt. The source
actually executes 7206 source steps in these synthetic attempts; the compiled
sample executes 8192 gates. These counts are not a resource advantage, since
the two samples have different acceptance and neither carries measured costs.

The q estimate is 4961/10000, with interval [4861/10000,5061/10000]. The fixed-n
Hoeffding coverage proof uses iid, fixed q and the source relation P(f)=q/2.
All flags are included. The correlated-shot counterexample is retained.
Phase/exchange nuisance and source/action gate matching are not calibrated by
those flag counts. The two heldout outcomes are only “not rejected by frozen
finite record testers”; the chapter does not call them empirical support,
device-model identification or measured complete-CQ distance. This is correct.

The book and code preserve the distinction between a pointwise policy oracle
and one deployable policy over a joint set. The interval images used for
record-cell testing are conservative sufficient envelopes, not a proof of
joint model identification from passing cells.

## 5. Costs and repetition quantifiers

For a genuinely fresh, independently repeatable source, the original formula

    [c_prep+(1+s)c_step+(1-s^2)c_reset+c_other]/s^2

is valid when c_other denotes the expected additional cost **per attempt**,
c_reset is charged on failure, and c_step is a common comprehensive step cost.
It does not require the cost of one attempt to be independent of its success;
it requires new trials after actual resets to be iid under the fixed source.
Unequal leaf costs are handled by the actual complete leaf-weighted mean.

### Correction R-C-2: one-time calibration versus per-attempt overhead — resolved

The initial wording included “amortized calibration” in a term inside the
success-probability division. That could double-amortize a campaign cost.
C requested a separation.

Both languages now define c_other as per-attempt overhead not already counted
in preparation/step costs. A one-time batch cost C_cal is separately allocated
as C_cal/M across M delivered successful outputs and is not again divided by
s^2. Compiled cost still includes actual preparation/failure, randomization,
gates, readout, reset, records and classical processing. Unknown quantum inputs
do not acquire an iid reset assumption. No hardware cost advantage is claimed.

## 6. Execution identity still requiring finalization

At inspection the integration receipt bound script hash
`d9f4d82ee420abc49d6a367db26dbbbbe403889ed850573f0109b09b74d176ef`,
whereas the current script hash is
`5e8d79c6184162526e23223644fa8aab2bf3c8238c178d52eeb4bb19e933c361`.
The shared-model and inherited-interpreter hashes did match. The discrepancy
is explained by the additional explicit basis bridge; the old 25-check receipt
must remain historical and cannot cover the new script. Root was informed.
A new narrow run of the current script is sufficient to resolve this risk;
unrelated old scientific gates need not be repeated.

No final Lean execution/axiom status is inferred by C from nearby compilation
or from the text of the new source. Actual source-bound machine receipts decide
that status. The full abstract OPT quotient, infinite-dimensional dynamics,
trace-class theorem, robust bounds and mixing retain their stated paper scope.

## 7. Independent v3.8 increment checker supplied

`research_c/v38_increment_checks.py` is standalone and does not import the
production book verifier. It independently checks:

- The prior dossier contains 173 unique result objects, and every one remains
  exactly equal and in the same order in the current dossier.
- Both manuscript bodies contain those 173 IDs followed by exactly the nine
  new chapter-67 IDs, with their reviewed Chinese and English titles.
- Chapters 0–67, unique anchors, twelve new numbered sections, twelve literal
  bilingual-identical display-math blocks and the reviewed exact constants.
- Actual operational Lean declaration names, no new sorry/axiom declaration,
  and explicit partial-machine versus paper-only classification in new
  dossier records when those records are installed.
- Any Lean-tagged new record has named formal source bindings and an actual
  receipt reference; receipt bytes are bound but Lean is not re-executed by
  this document validator.
- The derived bilingual result mapping contains the nine new IDs.

A read-only draft execution completed **69 identity/scope checks**. It returned
`CONTENT_PASS_METADATA_PENDING`, with exactly three preparation items: the
current dossier still has only the old result records, its edition is not yet
3.8, and the derived mapping has not yet received the nine new IDs. These
known metadata tasks are not classified as scientific failures.

Root can execute after integration with:

```bash
python research_c/v38_increment_checks.py \
  --repo-root /absolute/path/to/UEOT \
  --output /absolute/path/to/increment-review.json \
  --require-complete
```

Without `--require-complete`, unfinished metadata remains explicit PENDING;
with it, pending items stop release acceptance. Any changed historical result
object or inconsistent bilingual/new-result identity is an actual failure
in either mode. PDF visual acceptance and remote integration are separate
gates, not conclusions of this checker.

## 8. Versioned follow-up: machine and runtime identity issues resolved

**Read-back time:** 2026-11-11 09:32:57 UTC / 2026-11-11 17:32:57 Asia/Shanghai.
**Research increment:** v31.11. Reviewer: the same independent native agent C.
This section follows the earlier inspection; it does not rewrite the old
pending findings or attribute later execution to earlier source bytes.

Root subsequently completed the actual public-path narrow Lean gate and the
final runtime gate. C read the current receipts, relevant final theorem
statements, and source/log bytes. **The earlier machine-pending condition and
the integration-script source mismatch are now resolved.** C did not rerun
Lean, the scientific scripts, or the synthetic experiment during this follow-up.

### Final source and receipt identities

| Artifact | Current SHA-256 |
|---|---|
| `formalization/ueot-qm/UEOTQM/OperationalEquivalence.lean` | `99fd7ecfa58322321269c7504b27923f36e5c7f36fadad6a938b640c78c14f37` |
| `kernel/evidence/v31.11/lean-verification.json` | `45afc9ee3bc2d02fd0c687c60910b5775831844a68416373e05f32fcdf21af8c` |
| `kernel/evidence/v31.11/proof-axioms.json` | `38c39683f99e1707ae3841457858e46d11066f4a73816326249d49c8a553cf60` |
| `operational_micro_robust/verify_integration.py` | `5e8d79c6184162526e23223644fa8aab2bf3c8238c178d52eeb4bb19e933c361` |
| `kernel/evidence/v31.11/runtime/independent-integration.json` | `0424cfab7334403aaac6f787a44c404a9b1c3da2a1f8c2711faa595dd0774b5f` |
| `kernel/evidence/v31.11/runtime/execution_receipt.json` | `b5398b9536e0c0f38bd19f79353907f08a61c3ff1511fb1049d6638352c710ce` |

The shortened paths in the last five rows are relative to `physics/qm/`.

### Machine acceptance that is now justified

The public-path Lean receipt was recorded at 09:31:58.034904 UTC. Its three
actual subprocesses—dependency check, new-module build, and named namespace
axiom audit—all have exit code zero. C matched the final Lean source to its
recorded hash and matched all three recorded log hashes to the current log
bytes. The receipt reports one new module, 43 explicit named declarations,
28 explicit theorems, and 80 exported namespace constants including generated
constants. C independently inspected the 80-entry axiom report: every entry
uses only `propext`, `Classical.choice`, and `Quot.sound`, with no additional
physical axiom admitted.

C read the final statements of `ContextStatistics` and its iff theorems.
They retain all normalized joint states and all effects on every finite
positive-dimensional reference, not merely product inputs. The genuine
one-dimensional scalar context supplies the reverse implication. The actual
accepted source includes:

- `contextStatistics_iff_singleStatistics`;
- `singleStatistics_iff_map_eq`;
- `contextStatistics_iff_map_eq`;
- `contextStatistics_iff_choi_eq`;
- rectangular Kraus-event positivity and trace-nonincreasing results;
- the equality between the actual Kraus amplification and the tensor-id
  linear map, and complete positivity on the enlarged system;
- `labelled_comp_congr` and `labelled_sum_congr`.

Accordingly, the finite operational-identity bridge now has the claimed
source-bound machine support. P-OPT-03's full parallel/test/tree/quotient
construction remains paper-level beyond the explicitly listed composition
and sum congruences. The infinite-dimensional dynamics, trace-class
postselection, robust-mixture inequalities and long-time mixing proofs are
not converted to Lean theorems by this gate. The receipt's 158-file source
closure remains root's recorded scope; this follow-up checked the new
source and actual receipts/logs and did not rerun the unchanged historical
closure.

### Current runtime execution and mismatch resolution

The final runtime receipt was created at 09:31:23.726849 UTC. It records
seven actual commands, each with exit code zero: operational controls,
microscopic truncation, certificate production, independent certificate
checking, B's independent check, source-to-CQ integration, and synthetic
calibration/holdout. C hashed the current files against every listed input,
output and per-command log: **13 inputs, 18 outputs and seven command logs
all matched**, with no discrepancies.

The updated source-to-CQ integration receipt records execution at
09:31:23.435839 UTC and binds the current `5e8d79…` script. It now contains
26 exact checks, including the explicit C/root basis bridge, and the same
five floating inherited-interpreter cases. All three consumed source hashes
(the script, inherited interpreter and final shared model) match current
bytes. The earlier 25-check receipt was an earlier execution identity; this
new record is the basis for acceptance of the current script.

The final synthetic analysis and raw records retain their previously checked
values and identity. Their successful algorithmic execution is still
synthetic evidence. All updated receipts state no new hardware data, and the
runtime receipt explicitly says the unchanged historical suites were not
re-executed.

**Follow-up verdict:** the two previously pending machine/runtime matters
are closed for the exact sources and executions identified here. This does
not decide still-separate publication metadata, PDF visual acceptance,
remote integration, or empirical validation. Earlier observations remain
preserved as the history of how these concrete gaps were resolved.

## 9. Bounded follow-up: execution-context schema v2 and preserved PR artifact

**Read-back time:** 2026-11-11 09:55:44 UTC / 2026-11-11 17:55:44 Asia/Shanghai.
**Scope:** execution-provenance correction only, within scientific v31.11.
Reviewer: the same native agent C. This follow-up was read-only outside this
isolated report. No Lean gate, runtime experiment, publication build, or
remote action was rerun by C.

### Why a correction was necessary

The initial PR #457 runtime artifact used the old runner, whose actor string
was unconditionally `primary agent on Linux workspace`. That described the
original local execution but was inaccurate when the same program ran under
GitHub Actions. C inspected the retained raw ZIP rather than inferring this
from a later corrected local receipt.

The unchanged raw artifact is
`/workspace/scratch/a6fba8f7e18e/remote_ci/pr457/runtime.zip`, SHA-256
`7c5097db497e24d6b7e6dd5e326e74bfcf94fa46edb780f8181ad1d9d5845150`.
Its member `ueot-qm-operational-micro-robust/execution_receipt.json` has
SHA-256
`f690fc1e53f34ec1eb6a1ba088353963d4b2a03256b14843792e0bf5bc20a8a7`,
schema `ueot-qm.runtime-increment/1`, seven commands, and recorded status PASS.
It was created at 09:52:18.012022 UTC and records command working directory
`/home/runner/work/UEOT/UEOT` while retaining the inaccurate hard-coded actor.
The old field is still present in those raw bytes; it has not been rewritten
to claim that the later metadata correction was already part of that run.

The separate legacy finite-conditioning member in the ZIP has its own
`ueot-qm.finite-reference-execution/1` schema and identity. It was not confused
with the v31.11 increment's actor field. This bounded review did not make a
new GitHub API query or independently re-establish the remote PR head; the
supplied first-head reference is
`78aad3c7859084a918c00e655cf198b7b5beecf2`.

### Corrected runner logic and actual new local execution

The current `run_verification.py` has SHA-256
`6baf8614aca24ca0170ecb606b8e33c84cd5c1631a38c4dc81b0be65fafa6b37`.
C read its actual logic:

- `GITHUB_ACTIONS == "true"` selects provider `github_actions` and actor
  `GitHub Actions runner`; otherwise provider and actor describe a local
  Python process without assuming which agent launched it.
- The CI branch records the repository, run ID, run attempt, job, event name
  and `GITHUB_SHA` from their explicit environment variables.
- `git rev-parse HEAD` records the observed checkout head, or null on a
  failed lookup. The receipt explicitly states that consumed-input hashes
  bind actual bytes and that HEAD alone does not identify a dirty worktree.
- Before/after consumed-input identities must agree. The runner itself is
  one of those inputs. Output enumeration excludes the preserved `prior`
  archive, so historical outputs are not relabelled as fresh outputs.

The current canonical runtime receipt has schema
`ueot-qm.runtime-increment/2`, SHA-256
`44c4d1a1e06144c1b8f7932fc576cba5e17e0fdf669a0198f480e390c5547523`.
It records a real new **local** execution completed at
09:54:18.614635 UTC, provider `local_python_process`, actor `local Python
process`, and observed git HEAD
`16a89154183c22030d4526413167d095d94e6890`. A read-only current HEAD check
returned that same commit, and the working tree contains the staged increment;
the new warning about source-hash authority therefore matters in this actual
case. This local run is not presented as a new GitHub Actions execution.

C verified all seven command exit codes are zero, all **13 input hashes**,
all **18 output hashes**, and all **seven command-log hashes** against the
current files. There were no mismatches. Compared with the prior local
receipt's 13 inputs, the **only changed consumed input is the runner**:
its previous hash was
`9e90ed3d1e44028ac645d8852988b3f98d5c6f19321ff184f18e78ce0f1b166d`.
The exact/numerical scientific inputs were not silently revised to obtain
another result. The regenerated integration receipt has current SHA-256
`433bd5e5525889dd878cfe54f3544b886ab6ed9e2f6b32378218bba0eb257024`;
its different execution identity is kept separate from the earlier receipt.

The corrected CI branch was **source-reviewed**, while the supplied new
execution is the local branch. Actual provider/run/job fields from a future
CI run must be read from that run's new receipt. The old schema-1 CI artifact
cannot serve as evidence that schema 2 was already executed remotely.

### Original local receipt and all outputs are preserved byte-for-byte

The original local outputs now reside in
`physics/qm/kernel/evidence/v31.11/runtime/prior/before-execution-context-v2/`.
Its original `execution_receipt.json` has SHA-256
`b5398b9536e0c0f38bd19f79353907f08a61c3ff1511fb1049d6638352c710ce`,
exactly the identity reviewed in §8. It retains schema 1 and the original
local actor string. C matched every one of its 18 output entries and seven
log entries to the corresponding archived files, with zero mismatches.
The archive README explicitly says its original paths and scientific-commit
reference identify the original run, not the current regenerated files.

### Lean source identity remains valid without another build

C read the current recorded 158-item Lean source manifest and checked the
SHA-256 and byte size of every entry against current files. All **158/158**
match; the aggregate identity remains
`f9ea1e3e9bc695e3916d764e8f005d98556e4541653d439a60e57a5fb8c4cacf`.
The Lean verification receipt remains
`45afc9ee3bc2d02fd0c687c60910b5775831844a68416373e05f32fcdf21af8c`,
and the axiom receipt remains
`38c39683f99e1707ae3841457858e46d11066f4a73816326249d49c8a553cf60`.
This is a byte-identity readback, not a repeat Lean execution. The source-bound
machine acceptance and its limited theorem scope from §8 are unchanged.

**Bounded follow-up verdict:** PASS for the corrected execution-identity logic,
the actually executed local schema-2 receipt, current file/log bindings, and
preservation of the original local and raw remote identities. The provenance
defect is accurately recorded and repaired for the new runner. Remote
schema-2 acceptance awaits its own actual CI receipt; mathematical conclusions,
machine-proof scope, synthetic classification and lack of hardware evidence
are unchanged.
