# UEOT Core Compression Formalization — Operations Manual

## 0. Identity

- Repository: `MurphyHoops/UEOT`
- Integration branch: `main`
- Frozen Core v3 source theorem baseline: **106/106 FULL-GREEN**
- Compression LIVE STATE: GitHub Issue **#146**
- Scientific completion contract:
  `formalization/ueot-core/docs/compression/COMPRESSION_MISSION.md`
- Machine ledger:
  `formalization/ueot-core/docs/compression/COMPRESSION_LEDGER.yaml`
- Post-FINAL research governance:
  `formalization/ueot-core/docs/compression/POST_FINAL_RESEARCH_GOVERNANCE.md`
- Machine research-track registry:
  `formalization/ueot-core/docs/compression/COMPRESSION_RESEARCH_TRACKS.json`
- Human coverage view:
  `formalization/ueot-core/docs/compression/COMPRESSION_COVERAGE.md`
- Source theorem seed index:
  `formalization/ueot-core/docs/CORE_COMPRESSION_THEOREM_INDEX.csv`
- Official regression target: `lake build UEOT`

Compression is a post-106 meta-formalization mission. It must never alter the
meaning or counted status of the frozen 106 source P-IDs.

## 1. Authority hierarchy

When records disagree:

1. frozen Core v3 source controls original P-ID semantics;
2. `V3_COVERAGE_STATUS.md` on `main` controls the completed 106/106 proof
   baseline;
3. `COMPRESSION_MISSION.md` defines the scientific Definition of Done and the
   permitted strength of minimality claims;
4. `COMPRESSION_LEDGER.yaml` on `main` controls counted compression claims;
5. live branches/PRs/Actions control code and CI facts;
6. Issue #146 body controls current active compression intent/blocker/next step;
7. active compression branch controls unfinished code;
8. prior chats/comments are supplemental history only.

## 2. IDs and state machines

Meta-generators use permanent IDs such as:

- `M-QD-01` — Quotient Descent;
- `M-TC-01` — Transport Certificate Calculus.

Generator states:

`candidate -> schema_locked -> lean_wip -> lean_green ->
cross_family_green -> integration_green -> main_green -> ledger_green ->
counted_generator`.

Mapping states:

`conjectured -> source_aligned -> statement_matched ->
lean_rederived_partial | lean_rederived -> assumption_audited -> main_green ->
counted`.

`rejected` is a valid terminal research result for a compression hypothesis.

## 3. Evidence discipline

A compression claim is not established merely because two theorems look
similar. A counted mapping requires:

1. frozen source statement identified;
2. generic M-ID theorem Lean-green;
3. explicit specialization/wrapper theorem;
4. assumption relation recorded;
5. conclusion relation recorded;
6. full source-facing conclusion recovered for `lean_rederived`;
7. feature exact-head CI green;
8. clean integration/PR/resulting-main CI green;
9. separate ledger promotion green.

`partial` may never be counted as a full P-ID rederivation.

## 4. Branch governance

Repository-wide governance in `docs/REPOSITORY_BRANCH_GOVERNANCE.md` remains
binding.

Compression branch classes:

- governance/mission maintenance: `ops/compression-<topic>` (temporary);
- generator feature: `compression/<m-id-lower>-<topic>`;
- clean integration: `compression/<m-id-lower>-main-integration`;
- ledger promotion: `compression/ledger-<checkpoint>`;
- emergency quarantine only: `hold/compression-<topic>`.

Default: one active mutating branch per M-ID. Do not create `v2`, `fresh`,
`final`, or scratch branch families.

## 5. Branch creation preflight

Before any new compression branch:

1. fetch/prune remote state;
2. read this manual and `COMPRESSION_MISSION.md` from `main`;
3. read `COMPRESSION_LEDGER.yaml` and `COMPRESSION_COVERAGE.md`;
4. read Issue #146 body;
5. list remote branches and open PRs;
6. verify the M-ID is not already active/integrated;
7. reuse the existing branch whenever one already represents the work;
8. verify repository branch count remains <= 8 target / <= 12 hard cap.

## 6. CI gates

Every compression feature head must pass:

1. Compression ledger/matrix validator;
2. protected baseline audit;
3. proof-escape scan in `UEOT/V3/Compression`;
4. `lake build UEOT.V3.Compression`;
5. compression theorem axiom print;
6. full `lake build UEOT`.

The general `UEOT Core Lean` workflow also runs on `compression/**` and
temporary `ops/compression-*` governance branches.

## 7. Promotion lifecycle

`CANDIDATE/SCHEMA -> FEATURE -> FEATURE CI -> SOURCE/ASSUMPTION RE-AUDIT ->
CLEAN INTEGRATION FROM LATEST MAIN -> INTEGRATION CI -> PR EXACT-HEAD CI ->
MERGE MAIN -> RESULTING-MAIN CI -> LEDGER-ONLY BRANCH/PR -> LEDGER MAIN CI ->
COUNTED`.

Feature green alone never changes counted compression coverage.

## 8. Issue #146 LIVE STATE

The Issue body, not comment tail, is the high-frequency recovery record.

Required fields:

- current Core baseline/main;
- compression counted metrics;
- active M-ID/lane;
- active branch/head;
- open PR;
- latest relevant CI;
- current scientific hypothesis;
- blocker/root cause;
- exact next action;
- do-not-repeat guards.

Comments are reserved for durable milestones/rejections/audits, not CI polling.

## 9. Cross-chat recovery

New chats execute `COMPRESSION_BOOTSTRAP.md`. Never open a replacement branch
merely because the chat or AI platform changed.

At handoff:

1. commit/push meaningful WIP on the same active branch;
2. update Issue #146 body;
3. persist architecture decisions not already in code/docs;
4. do not modify counted ledger files unless a real lifecycle transition
   occurred;
5. continue useful work if the current chat still has room.

## 10. Parallel conversations

Parallelism is allowed only for genuinely separate M-IDs/tracks or read-only
audits. Two chats must not mutate the same M-ID, research-track branch, or file
ownership surface concurrently.

Recommended maximum:

- active mutating compression lanes: 2;
- open repository PRs: 2 total under repository governance;
- read-only theorem/source audits: may run without branches.

For post-FINAL research, the two mutating slots are explicitly:

- Track S — Structural Defect / Long-Run Stability;
- Track H — Hierarchy / Assembly Audit.

There may be at most one active mutating branch per track. Cross-track
dependencies are main-only; neither track may stack on the other's unmerged
branch.

## 11. Mission completion gate

`COMPRESSION_MISSION.md` is the authoritative scientific Definition of Done.
No chat, issue comment, PR description, or green CI run may weaken it.

The validator must reject `ready_for_finalization` or `final` unless the
machine ledger shows all 106 P-IDs analyzed and schema-classified, 106 final
per-P-ID dispositions, zero unresolved P-IDs, a frozen minimal core that
exactly accounts for every generated dependency, complete ablation with
remaining-core non-derivability evidence, and counted exact evidence for every
generated disposition.

Finalization uses two stages:

1. `ready_for_finalization` — all scientific gates are satisfied and merged to
   a candidate `main`;
2. require successful **push** runs of Core Lean and Compression Guard for that
   exact candidate-main SHA;
3. open a dedicated closure PR from the candidate main, then commit the
   `final` ledger state on that closure branch with the candidate SHA, both run
   IDs, and the closure PR number;
4. Compression Guard live-verifies that both runs succeeded for the recorded
   candidate SHA and that the open PR targets `main`, is based on that SHA, and
   matches the current closure head;
5. merge the closure PR with a normal merge commit; on resulting `main`, the
   verifier requires the merge ancestry to include both the candidate main and
   recorded closure head;
6. announce FINAL only after resulting-main Core Lean and Compression Guard are
   green and Issue #146 is updated.

This two-stage rule avoids circularly requiring a CI run to attest to the very
commit that is trying to record its own completed run ID. Final closure uses a
merge commit rather than squash/rebase so the audited ancestry remains
machine-verifiable.

## 12. v4 gate

Do not write a compressed Core v4 merely from conceptual elegance. A v4
reorganization is justified only after the Mission Contract's resolution and
minimal-core gates are satisfied. Conceptual elegance alone is insufficient.

## 13. Post-Gate-D extension and re-finalization

A `FINAL` checkpoint is immutable historical evidence, but it does not forbid
later research from formalizing a genuinely new replacement/generator route.
If such a route changes counted mappings or minimal-core membership, the
project must **reopen and re-finalize** rather than silently mutate a closed
ledger.

Required lifecycle:

1. preserve the previous Gate-D SHA, metrics, minimal core and
   `finalization_evidence` in an explicit historical checkpoint record;
2. integrate the new theorem surface through the normal feature / PR /
   resulting-main lifecycle;
3. rerun scoped Gate-C ablation on the enlarged registered theorem-surface DAG,
   including deletion of the new generator and rechecking every historical
   generator while the new theorem surface is retained;
4. on a dedicated ledger/governance branch, update counted mappings,
   per-P-ID final dispositions, live minimal core and coverage, and set
   `mission_contract.state = ready_for_finalization`;
5. clear the live `finalization_evidence`; historical evidence remains
   immutable in its checkpoint record;
6. merge the ready-for-finalization ledger/governance PR to `main`;
7. require successful **push** Core Lean and Compression Guard runs on that
   exact candidate-main SHA;
8. open a fresh dedicated closure PR from that candidate main;
9. record the new candidate SHA, run IDs and closure PR in live
   `finalization_evidence`, set state to `final`, and use a **normal merge
   commit**;
10. require resulting-main Core Lean and Compression Guard green before
    announcing the new FINAL state.

The older FINAL result remains valid for the theorem surface available at its
checkpoint. A later closure supersedes it only for **current live compression
accounting**; repository history must never be rewritten as though the new
generator existed earlier.

## 14. Post-FINAL research-track ownership

The authoritative split is defined by
`POST_FINAL_RESEARCH_GOVERNANCE.md` and machine-registered in
`COMPRESSION_RESEARCH_TRACKS.json`.

Track S owns the existing structural-defect/gauge/GOA/recurrent-topology and
stationary-stability line, including residual-inverse and spectral/local
isolation follow-ups.

Track H owns hierarchy inventory, existing-generator coverage, parent-object
assembly residual analysis, and hierarchy no-go/separation work. Its initial
scope is H0-H3. New GOA/recurrent/spectral stability work is forbidden on Track
H until the explicit cross-track integration gate opens.

Branch naming:

- Track S continues the registered compression research branch families;
- Track H uses `compression/hierarchy-<topic>`;
- governance changes use temporary `ops/compression-<topic>`.

Track H implementation and documentation live only under
`UEOT/V3/Compression/Hierarchy/` and `docs/compression/hierarchy/`, plus
the public `Hierarchy.lean` root. The global `Compression.lean` root already
imports `Hierarchy.lean` and is not Track H-owned.

The Compression Guard runs
`scripts/validate_compression_research.py` and rejects cross-track path
ownership violations, unclassified governed branches, duplicate live remote
branches within one track, direct-main research mutation without an associated
classified PR, or Track H mutation of counted/governance/global-root files.

After the research-track registry is present on `main`, branch/path authority
is evaluated from the **base-ref registry**, not from a candidate replacement
in the same PR. Governance permission changes therefore require two steps when
they are intended to authorize a new surface: first merge the policy change
under the old policy, then use the new permission in a later PR. This prevents
candidate-policy self-authorization.

The immutable executor for that rule is
`.github/workflows/ueot-compression-research-policy.yml`. It uses
`pull_request_target`, checks out only the base SHA, and executes the
base-version validator while reading the candidate only as Git diff data. Never
change this workflow to checkout or execute PR-head code under
`pull_request_target`.

The initial governance PR #198 is the sole bootstrap because its base predates
this workflow/registry. Its bootstrap allowlist is intentionally explicit and
must contain governance artifacts only; after merge, all later changes are
authorized by the already-merged base policy.

Every mutating post-FINAL PR must state its track and counted-core impact, pass
exact-head CI, request Codex exact-head review, and use the recorded fallback
only after an explicit quota refusal.
