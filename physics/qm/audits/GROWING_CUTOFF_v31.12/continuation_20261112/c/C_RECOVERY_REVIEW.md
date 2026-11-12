# C recovery review: v31.12 source, robust certificate and evidence

Reviewer: the newly created native child agent `/root/c_robust_evidence`.
Date: 2026-11-12, Asia/Shanghai. This review is separate from the original C
drafts recovered under `reviewer_originals/c/`. It is internal non-author AI
review, not external human peer review.

## Decision

**The recovered scientific candidate is acceptable within its declared ideal
segmented-control model. No blocking mathematical or numerical-certificate
defect was found.** The runtime and publication evidence match the recovered
bytes. One publication pointer was dangling at first inspection and was
reported to root for completion before release. Remote publication and CI are
outside this local decision and must be bound to their actual later commits.

The reviewed repository is
`/workspace/scratch/2331c99c0713/ueot-physics`, whose scientific baseline is
`aea2fceef3c62cc8dc749b6cbb1b40a7d89df80d`. At initial remote read, the recovery
branch contained part of the new code and reviews while its CURRENT remained
v31.11. This was evidence of a partial upload, not a complete release. The local
candidate retained the v31.12 files and actual execution receipts from the
interrupted recovery session; these receipts are no longer merely statements
quoted in the user's message.

## Independent byte and history checks

`recovery_identity_and_bound.py` is a fresh independent checker. It imports none
of the production model, integration checker or original exact checker. Its
actual output is `C_RECOVERY_IDENTITY_AND_BOUND.json`.

The checker read and matched:

| Scope | Matching identities |
|---|---:|
| Inherited proof/configuration inputs | 158 / 158 |
| Inherited runtime inputs | 13 / 13 |
| New runtime inputs | 12 / 12 |
| New runtime output files | 8 / 8 |
| New runtime command logs | 4 / 4 |
| Publication-verifier consumed files | 208 / 208 |
| New paper and release inputs | 18 / 18 |

These are overlapping, separately scoped inventories; they are not summed into
a proof-completeness count. All 182 inherited result objects and all 105
inherited claim objects, including their order, match the current dossier and
ledger exactly. The six appended result IDs are P-MICRO-04, P-OPT-04,
P-MICRO-05, C-MICRO-02, P-ROB-03 and C-ROB-02.

The existing new runtime receipt records four successful commands and a dirty
local checkout. Its input hashes, rather than the parent commit alone, identify
the executed code. The receipt is accurately labelled `local_python_process`;
it is not rewritten as a GitHub execution or as an execution by this new
reviewer. No historical Lean or numerical suite was reexecuted for this review.

## Robust certificate: the two strongest claims

### 1. The complete-output approximation is below the frozen target

The target and matched compiler use the same theta and the same gate word in
each visible record. Orthogonality of the records therefore gives exact CQ
trace distance equal to the path-law TV. The fixed deployed weights have both
label-one marginals equal to one half, and their expected selected blue count
is one. The minimax result remains restricted to the full frozen design
interval, rather than every narrower realized calibration set.

The physical preparation instrument preserves its failure flag and the
unnormalized failure-conditioned reference marginal. Its sharp bound is
`F(e)=(sqrt(4e-3e^2)+e)/2`; the comparator cannot discard the failure mass.
The ideal low-spectral filter keeps the passing mean excitation no larger than
the original mean. This is a property of this filter, not general postselection.

Each blue-omission term uses the no-blue prefix, which preserves the mean
excitation budget. The actual future suffix is common and contracts distance.
Thus the coefficient of `abs(beta)*sqrt(E+1)` is the actual compiled path
expectation one, not the source conditional count `2q` and not the hard cutoff
N. The source-derived acceptance effect `s^2 I` makes this particular target
CPTP; preparation contraction in this model does not omit a required general
postselection amplification.

An independent integer square-root enclosure at denominator `10^24` gives

`D_full <= 4988777535926672669484889 / 10^26 < 1/20`.

The paper formula being enclosed is

`1/50 + (sqrt(4e-3e^2)+e)/2 + sqrt(2)/100`, with `e=1/4096`.

The certified remaining allowance is at least
`11222464073327330515111 / 10^26`, approximately `0.0001122246407332733`.
This interval encloses an analytic upper-bound formula. It is neither a
confidence interval nor a measured error, nor a lower bound on physical error.

### 2. The parameter and resource claims do not exceed the available evidence

The new omission certificate assumes an independent `abs(beta)<=1/100` bound.
The existing logical flag likelihood is beta-independent and cannot establish
that bound. The beta-zero versus beta-pi/2 vacuum control gives identical flag
counts while word 01 alone contributes `156/625` to the compiler comparison's
CQ distance. This is a valid failure-of-identifiability control when the
independent beta assumption is absent; it does not contradict the small-beta
conditional theorem.

The complete source attempt succeeds with `s_N*s^2`. The independent exact
calculation gives the lower bound `1121211/2048000`. Read-flag-then-act costs
count selected blue calls; coherent hardware may schedule a controlled pulse
in every active slot. The two cost contracts are correctly distinguished.
Fresh-reset repeatability is explicit, and the one-time calibration cost is
separately amortized over outputs. The texts do not claim measured resource
advantage or assume arbitrary unknown entangled inputs can be repeatedly
prepared for free.

## Cross-review of A

I attacked the two most consequential operational claims in the recovered A
bridge.

First, the finite rectangular process is derived from actual blue doublets,
not from an asserted intertwining field. Per-path canonical inclusions give
the same physical Fock-space output; depth-based padding and the smaller
path-specific carriers are equivalent embeddings. All seven source terminal
records remain in the complete CPTP channel. The fixed-window negative control
checks actual missing probability, so it is not invalidated by Kraus-phase
equivalences.

Second, the failure-reset map acts only on S and keeps `Tr_S[Q rho Q]` on R.
The accepted scalar effect and the explicit zero target masses on failure
records justify the exact comparator. A neither equates arbitrary hidden-memory
processes from a single slot nor promotes an infinite-dimensional proof to Lean
coverage. Both strongest claims are accepted in the finite classical protocol,
untouched finite-reference domain stated in the bridge.

## Workflow reuse and execution identity

The proposed workflow reuses Lean only after
`verify_inherited_evidence.py` checks pinned historical receipt hashes, all 158
proof/configuration input hashes and sizes, and the complete Git diff/untracked
inventory under both formalization trees and the kernel tools. The pinned
successful historical workflow is tied to scientific main
`06ca0dce8b03cd34e86785e97fdc3c7aa2c582bd` and run `43001276385`.

A mismatch or exception does not silently pass: either `reuse` is false or the
step outcome is not success, so the workflow retains and executes the existing
full build, dependency check, escape check, axiom audit and exact positive and
negative witness steps. The continue-on-error setting is justified by this
explicit fallback. Reuse identifies unchanged machine evidence; it does not
machine-prove Chapter 68. The proof archive includes the actual reuse decision.

The new runtime runner records whether it runs locally or in GitHub Actions and
captures checkout, run, attempt, job and ref identity in CI. Root must inspect
the actual new archive and bind it to the accepted head before recording remote
verification. The local original is retained separately.

## Publication finding and remaining scope

At first inspection CURRENT's `book.local_acceptance` pointed to
`physics/qm/book/evidence/v3.9/local-acceptance.json`, which did not exist. The
actual `increment-verification.json` was present, PASS, and matched all 208
consumed identities, including the current bilingual source, TeX, PDFs and
scoped visual review. This is an entrypoint completion issue, not a mathematical
defect. Root has been asked to generate an accurate summary acceptance receipt
or redirect the pointer before publication.

This reviewer has not performed a fresh PDF visual review; matching existing
PDF and reviewed-page identities preserves that earlier scoped evidence. The
existing receipt explicitly limits its visual coverage and does not claim all
613 pages were inspected.

The final acceptance remains conditional on completing that pointer and the
actual repository/CI integration. Real pulse/filter/readout errors, actual
device membership, complete-CQ empirical error and cost advantage remain
unverified. No new Lean theorem, external peer review or full physical-theory
closure is claimed.
