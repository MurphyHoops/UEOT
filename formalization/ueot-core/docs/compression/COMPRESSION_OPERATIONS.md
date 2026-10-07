# UEOT Core Compression Formalization — Operations Manual v2

## 0. Identity

- Repository: `MurphyHoops/UEOT`
- Integration branch: `main`
- Frozen Core v3 source theorem baseline: **106/106 FULL-GREEN**
- Compression LIVE STATE: GitHub Issue **#146**
- Scientific completion contract: `COMPRESSION_MISSION.md`
- Machine ledger: `COMPRESSION_LEDGER.yaml`
- Human coverage view: `COMPRESSION_COVERAGE.md`
- Source theorem index: `CORE_COMPRESSION_THEOREM_INDEX.csv`
- Research policy/registry: `COMPRESSION_RESEARCH_TRACKS.json`
- Post-FINAL governance: `POST_FINAL_RESEARCH_GOVERNANCE.md`
- Official full regression target: `lake build UEOT`

Compression is a post-106 meta-formalization mission. Nothing in ordinary research may
silently change the meaning or counted status of the frozen 106 P-IDs.

## 1. Authority hierarchy

When records disagree:

1. frozen Core v3 source controls original P-ID semantics;
2. `V3_COVERAGE_STATUS.md` on `main` controls the 106/106 proof baseline;
3. `COMPRESSION_MISSION.md` controls the scientific Definition of Done;
4. `COMPRESSION_LEDGER.yaml` on `main` controls counted compression claims;
5. canonical `main` source + PR/CI state controls integrated implementation facts;
6. `COMPRESSION_RESEARCH_TRACKS.json` controls machine path/track policy;
7. Issue #146 controls only the current recovery index/intent;
8. task trackers control detailed active scientific plans;
9. prior chats/comments are supplemental history only.

No Issue or chat may promote an uncounted theorem into counted status.

## 2. Governance model

Post-FINAL work uses the risk-tiered model defined in
`POST_FINAL_RESEARCH_GOVERNANCE.md`:

- **L0** read-only analysis;
- **L1** additive uncounted research — default;
- **L2** existing/shared uncounted interface change;
- **L3** frozen/counted/minimal-core change.

The validator protects existing L1 surfaces by comparing the candidate with the immutable
PR base. A track may own a broad namespace while still being unable to rewrite already
merged files.

## 3. Branch model

Use one branch for one durable scientific objective:

- Track S: registered `compression/topology-*`, `compression/goa-*`,
  `compression/recurrent-*`, `compression/contractive-*`, etc.;
- Track H: `compression/hierarchy-*`;
- Track X: `compression/cross-track-*`;
- Track O: `compression/objecthood-*`;
- Track TC: `compression/theory-completion-*`;
- governance/L2/L3 policy work: `ops/compression-*`;
- emergency quarantine only: `hold/compression-*`.

Do not create `fresh`, `clean-v2`, `final-v3`, `scratch` remote branch families. Iteration
belongs in commits on the same branch. Ordinary L1 work does not need a clean-integration
branch or a ledger branch.

## 4. Minimal preflight

Before starting a new mutating task:

1. `git fetch --prune origin`;
2. confirm canonical `origin/main`;
3. identify the task/Issue and risk tier;
4. confirm the work is not already represented by an active branch/PR;
5. confirm its track/namespace is registered;
6. reuse an existing active branch when it already owns the task.

For L1, this is sufficient. Do **not** require reading every historical audit or lane before
writing a new theorem. Read prior material only when it is a scientific dependency.

Before L2/L3, additionally read the relevant policy/ledger/mission sections because those
changes have larger blast radius.

## 5. L1 research workflow

Normal post-FINAL research:

1. create/reuse one track branch from current `main`;
2. add a dedicated new theorem/audit subtree;
3. iterate locally;
4. for each theorem stage, normally run focused compile + `git diff --check`;
5. at a meaningful milestone, run the Compression namespace checks;
6. before first/final push, run the relevant local regression once;
7. open one PR to `main`;
8. obtain required CI and one exact-head independent review;
9. merge;
10. require resulting-main full regression when Lean source changed;
11. close/update the task tracker and Issue #146 current block;
12. delete the merged branch.

There is **no separate authorization PR** and **no separate final-governance PR** for L1.

## 6. CI matrix

### L0

No repository CI required.

### L1 PR

Required when applicable:

- base-policy ownership validation;
- research-governance regression tests;
- proof-escape scan;
- `lake build UEOT.V3.Compression` for Compression Lean changes;
- ledger witness/axiom checks when the changed surface reaches them;
- UEOT Core Lean full build once on the PR for Lean-source changes;
- exact-head independent review once at PR boundary.

Documentation/registry-only changes do not run a Lean proof build solely because they live
under `formalization/ueot-core/`.

### Resulting main

For Lean-source changes, `UEOT Core Lean` is the canonical owner of the full
`lake build UEOT` regression. `Compression Guard` does not duplicate it.

### L2/L3

Run full exact-head regression and the additional governance/promotion checks defined by
the relevant exception/Mission Contract.

## 7. Local validation cadence

Do not make each theorem stage pay final-release cost.

Default stage cadence:

`focused compile → diff-check → scientific assertion check → commit`.

Milestone/PR cadence:

`namespace build → proof-escape → governance validator/tests → axiom/witness audit as needed → full regression once → review`.

Repeat the full regression only when the semantic surface or integration state actually
changed enough to justify it.

## 8. Protected surfaces

L1 branches may not modify existing files on their PR base except explicit root-import
exceptions. In addition, tracks may never mutate cross-owned/protected files such as:

- `COMPRESSION_LEDGER.yaml`;
- `COMPRESSION_COVERAGE.md`;
- `COMPRESSION_MISSION.md`;
- compression ablation/finalization evidence;
- governance validators/workflows;
- another track's source namespace;
- frozen Core v3 source.

Changing one of these is L2/L3, not an L1 workaround.

## 9. L2 exception workflow

Use L2 only when a new adapter cannot honestly solve the problem and an already merged
uncounted/shared interface must change.

1. document the exact existing path(s) and why additive extension is insufficient;
2. make one scoped `ops/compression-*` base-policy exception;
3. validate the exception without theorem mutation;
4. perform the scientific change on its track branch;
5. run full exact-head UEOT regression and review;
6. merge and validate main;
7. remove/expire the exception if it was temporary.

L2 is exceptional, not the default task bootstrap.

## 10. L3 promotion / counted-core workflow

Counted mappings, G0 generator changes, frozen source semantics, minimal-core membership,
ledger/coverage and finalization use the original Mission Contract discipline.

The heavy lifecycle remains conceptually:

`candidate theorem → source/assumption audit → exact mapping → integration → scoped ablation → ledger promotion → candidate main → exact candidate-main CI → closure evidence → resulting-main CI`.

A later generator that changes counted mappings/minimal-core membership must reopen Gate C
and re-finalize as specified in `COMPRESSION_MISSION.md`. Historical FINAL checkpoints
remain immutable.

### 10.1 Durable FINAL Actions receipts

FINAL creation still requires live exact-event verification. The receipt mechanism is for
later provider-retention loss; it is not a substitute for online finalization.

After the candidate-main Core Lean and Compression Guard push runs are successful and the
closure PR number is recorded in the ledger, capture the run receipt while all references
are still live:

```bash
python3 formalization/ueot-core/scripts/validate_compression.py \
  --repo-root . \
  --baseline-ref origin/main \
  --verify-finalization-refs \
  --capture-finalization-receipt finalization_live_capture
```

Commit the generated
`docs/compression/finalization_receipts/<candidate_main_sha>.json` through the closure PR.
The closure PR CI still verifies the live run IDs, names, `push/completed/success` state,
candidate SHA and exact PR head. Once merged, that receipt is immutable historical evidence.

For later validation, live GitHub data remains authoritative when available. Receipt
fallback is permitted only when an Actions run returns explicit HTTP 404, and only from a
receipt that already exists unchanged in the validation baseline. TLS/timeouts, auth/rate
errors, malformed responses and other failures remain hard failures after any bounded
transport/5xx retry. The closure PR is still live-verified and its merge ancestry is still
checked.

## 11. Parallelism

- up to four of the registered S/H/X/O/TC tracks may mutate concurrently;
- one mutating branch per track by default;
- read-only audits/workers are unlimited by this rule;
- cross-track dependencies come from canonical `main`, not another unmerged branch;
- two agents must not edit the same branch/file concurrently.

If future demand requires same-track parallel mutation, implement path-disjoint concurrency
checks before raising the per-track limit.

## 12. Live state

Issue #146 current section should remain short:

- canonical `main`;
- counted minimal core / mission state;
- active tasks/trackers;
- active branch/PR;
- blocker;
- exact next action;
- protected/nonrepeat boundaries.

Do not duplicate historical CI/PR narratives there. Durable history already exists in
Git/PR/CI/audit evidence.

## 13. Cross-chat recovery

A new chat should execute `COMPRESSION_BOOTSTRAP.md`, recover only active state, and then
continue the scientific next action. It should not re-read every old Track-S/H/X/O/TC audit
unless scientifically necessary.

At handoff:

- commit/push meaningful WIP on the same branch;
- update the task tracker/Issue #146 only if the active state changed;
- persist genuine architecture decisions;
- do not create a handoff-only branch.

## 14. Branch retirement

After merge and required resulting-main validation, delete the remote feature/governance
branch. Merged PRs and commits are the archive. Governance branches must not become
permanent history.

## 15. Future task / track expansion

- Existing track + new scientific subtree: **L1**, no central governance edit.
- Existing track + existing shared interface mutation: **L2**.
- New top-level track: add its branch pattern, owned namespace and protected boundaries
  once; subsequent tasks inherit them.
- Counted/frozen change: **L3**.

This keeps policy growth proportional to stable architecture, not to the number of tasks.

## 16. Definition of operational success

Governance is healthy when:

- scientific iteration is normally `edit → compile → next theorem`;
- an ordinary task uses one research PR;
- full UEOT builds are not duplicated by multiple workflows for the same semantic check;
- old merged theorem surfaces cannot be rewritten by an L1 branch;
- counted/frozen claims remain harder to change than ordinary research;
- a new task inside an existing track can start without a governance rewrite.
