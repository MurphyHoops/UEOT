# UEOT Core Compression — Post-FINAL Research Governance v2

Status: **RISK-TIERED v2 / STATIC RESEARCH NAMESPACES / POST-FINAL / COUNTED CORE FROZEN**

Authority:

- parent mission: GitHub Issue **#146**;
- scientific contract: `COMPRESSION_MISSION.md`;
- counted claims: `COMPRESSION_LEDGER.yaml`;
- machine policy/track registry: `COMPRESSION_RESEARCH_TRACKS.json`;
- operational procedure: `COMPRESSION_OPERATIONS.md`.

This document replaces the former per-cycle authorization/closure model for ordinary
post-FINAL research. The old model successfully prevented branch/state entropy while
Core v3 and the compression kernel were being stabilized, but it became too expensive
once the project entered rapid scientific extension. Governance v2 keeps the scientific
safety invariants and removes repetitive ceremony.

## 1. Fixed scientific invariants

The counted minimal core remains exactly the live ledger state. Ordinary post-FINAL
research is **UNCOUNTED** and may not change that state implicitly.

The following remain hard invariants:

1. frozen Core v3 source semantics and 106/106 counted proof status are not silently changed;
2. no `sorry`, `admit`, proof-bypass `native_decide`, or unsourced proof escape is accepted;
3. a new theorem does not become a counted generator/mapping merely because it compiles;
4. cross-track dependencies are consumed from canonical `main`;
5. `main` is the only integration truth;
6. protected ledger/coverage/minimal-core changes use the Mission Contract promotion and
   re-finalization lifecycle;
7. historical audit evidence is immutable.

Machine-captured FINAL Actions receipts are part of that immutable evidence. Ordinary
research tracks may not add, edit or delete them. A governance/finalization change may add
a new receipt only after live exact-event verification; once present on the baseline, the
receipt must remain byte-identical. Historical fallback never applies to generic network
failure and does not relax closure-PR identity or ancestry checks.

Receipt creation is also separated from its trust machinery: a PR that adds a new FINAL
receipt may not simultaneously modify the counted FINAL verifier, either evidence-producing
workflow, the research-policy workflow/registry, or their regression tests. Those surfaces
must first become canonical independently, so candidate evidence cannot authorize the code
or workflow that judges it.

The optimization target is **scientific information gained per proof/governance cost**.

## 2. Risk tiers

Governance cost scales with semantic blast radius.

| Tier | Meaning | Default validation | Lifecycle |
|---|---|---|---|
| **L0** | read-only analysis, `/tmp` proof design, source/literature audit | none beyond local sanity checks | no branch required |
| **L1** | additive, uncounted research in an owned namespace | focused compile, Compression proof checks, policy validator, one PR review | one research branch → one PR → main |
| **L2** | modification of an existing uncounted/shared interface or cross-track surface | L1 + full UEOT exact-head regression + explicit governance exception | exceptional governed PR path |
| **L3** | frozen source, counted mapping/generator, ledger, minimal core, Mission Contract semantics | full proof/audit/ablation/re-finalization gates | Mission Contract lifecycle |

**Default is L1.** A task is not promoted to L2/L3 because it is scientifically
important; it is promoted only because it mutates a wider semantic surface.

## 3. Static research namespaces

Registered tracks are persistent research capabilities, not per-task locks:

- **Track S** — structural defect / long-run stability;
- **Track H** — hierarchy / assembly;
- **Track X** — cross-track composition;
- **Track O** — Objecthood / persistence / repair / homeostasis / reconstruction;
- **Track TC** — Theory Completion / semantic constitution / scientific integration.

Once a track exists, a new task inside that track does **not** need a fresh governance
authorization PR. A substantial task should still have a tracker Issue so humans/agents
can recover intent, but the tracker records the scientific objective; it does not grant
code authority.

A genuinely new top-level track or namespace needs one policy extension. Individual
research tasks within an existing track do not.

## 4. L1 additive-research contract

L1 is the normal post-FINAL mode.

A research branch may:

- add new Lean files under its track-owned namespace;
- add new audit/evidence files under its track-owned documentation namespace;
- add the minimal public root import required to expose those new modules, where the
  track policy explicitly permits an import-only root exception.

It may **not**:

- modify or delete a theorem/audit file that already exists on the PR base;
- rewrite a historical root declaration or prior import;
- modify another track's namespace;
- modify counted ledger/coverage/minimal-core evidence;
- modify frozen Core v3 theorem source;
- use a candidate policy edit to self-authorize a protected mutation.

The machine validator compares the candidate against the immutable PR base. Existing
files are therefore protected automatically even when the track owns a broad namespace.
This is the key extensibility mechanism: future work can create a new dedicated subtree
without editing the central registry, while merged science remains immutable by default.

One narrow exception exists for machine-pinned **live status artifacts**. A registered
track may declare `mutable_existing_exact_paths`; those paths remain inside the track's
owned namespace but are intentionally mutable across later L1 stages. The candidate
cannot widen this list: the validator pins the exact pre-authorized set. Currently the
only such path is Track TC's `THEORY_COMPLETION_STATUS.json`. Mission/roadmap/audit and
theorem files remain additive-only historical surfaces.

## 5. L2 shared-interface changes

L2 is intentionally rarer. It applies when a scientific result genuinely requires
changing an already merged uncounted/shared interface rather than adding a new module.

Requirements:

1. state the exact existing path(s) that must change and why an additive adapter is
   insufficient;
2. obtain an explicit base-policy governance exception scoped to those paths;
3. run full UEOT exact-head regression and independent review;
4. merge normally and validate resulting `main`;
5. retire the temporary exception when it is no longer needed.

Do not use L2 merely for convenience. Prefer a new adapter/module when scientifically
honest.

## 6. L3 counted/frozen changes

L3 retains the existing heavy governance. It covers:

- frozen P-ID semantics/status;
- counted compression mappings;
- G0 generator promotion/removal;
- minimal-core membership;
- ledger/coverage state;
- Gate-C ablation and Gate-D/re-finalization evidence;
- changes that weaken the scientific Definition of Done.

L3 must follow `COMPRESSION_MISSION.md` and the promotion/re-finalization section of
`COMPRESSION_OPERATIONS.md`. Governance v2 does not weaken those requirements.

## 7. Normal L1 lifecycle

The ordinary lifecycle is now:

`SCIENTIFIC PREFLIGHT → ONE RESEARCH BRANCH → LOCAL ITERATION → ONE PR → REQUIRED CI/REVIEW → MERGE → RESULTING-MAIN FULL REGRESSION → TRACKER CLOSE → BRANCH DELETE`.

There is no separate authorization PR and no separate final-governance PR for L1.

For a multi-stage theorem program, stage commits are useful scientific checkpoints, not
separate governance events. During iteration, each stage normally needs only:

1. focused Lean compile for the touched/new module;
2. `git diff --check`;
3. a short scientific audit note when a real semantic decision was made.

At meaningful milestones or before the PR, run the namespace/Compression checks. The
full repository regression is not repeated after every theorem stage.

## 8. CI ownership

To avoid duplicate proof work:

- **UEOT Core Lean** is the sole workflow that owns `lake build UEOT`;
- feature-branch pushes do not run another full build merely because a PR exists;
- PR runs supersede stale PR runs (`cancel-in-progress: true`);
- **Compression Guard** owns governance validation, proof-escape scanning, Compression
  namespace build, ledger witness checks and axiom audit;
- Compression Guard does not repeat the full UEOT build;
- documentation/registry-only governance changes skip the Lean proof job;
- resulting `main` receives the canonical full regression for theorem-source changes.

A green targeted check is not a substitute for the resulting-main regression when Lean
source changed; it only avoids repeating the same full build at every intermediate step.

## 9. Review discipline

- L1: one independent exact-head scientific/code review at the PR boundary is sufficient;
  per-stage independent review is not required.
- L2: exact-head independent review is mandatory because an existing shared surface is
  changing.
- L3: retain all Mission Contract review/audit requirements.

If an external review service is quota-limited, a documented independent exact-head
review remains an acceptable fallback; do not block science solely on reviewer quota.

## 10. Parallelism

Governance v2 permits up to **four active mutating tracks** across the registered
S/H/X/O/TC tracks, one branch per active track, provided path ownership remains disjoint. Read-only workers are not counted.

Within a single track, keep one mutating branch by default. If future throughput requires
multiple same-track branches, add machine-checked path-disjoint concurrency rather than
simply raising the cap.

## 11. Issue #146 and task trackers

Issue #146 is a **small live recovery index**, not an append-only database. Its current
section should contain only:

- canonical `main`;
- frozen counted-core state;
- active scientific task(s)/tracker(s);
- active branch/PR;
- blocker;
- exact next action;
- nonrepeat/protected-boundary notes.

Detailed historical evidence belongs in merged PRs, commits, CI runs, audit files and the
machine registry/ledger. Do not copy large old lane histories into the current recovery
section.

Task trackers record stage plans and scientific decisions. Closing an ordinary L1 tracker
after merge/resulting-main green does not require a separate repository governance PR.

## 12. Historical Objecthood completion records

`objecthood_completion_history` is retained as immutable evidence of the old guarded
cycles (O/ER/AR/GCR/RH/QT). Under governance v2 it is **frozen history**, not a live
permission state machine. New L1 Objecthood tasks are closed by tracker + merged PR +
resulting-main evidence and do not append another central completion record.

The legacy `objecthood_omega_gate` remains open as a compatibility marker for the static
Track-O namespace. It is no longer toggled per task.

## 13. RLSR migration

Issue **#257 / RLSR0–RLSR9** is the first task intended to use governance v2.

After this governance-v2 migration PR merges and its resulting-main governance checks are
green, RLSR may start directly on one `compression/objecthood-*` research branch in a new
`Objecthood/RepairLawSelfReconstruction/` subtree. It does not need another authorization
PR. Its historical Objecthood/RH/QT dependencies remain protected because L1 cannot
modify existing files.

RLSR's scientific boundary remains unchanged: it may reconstruct mutable object-level
repair organization relative to an explicit trusted substrate; it does not claim that the
ambient mathematical laws reconstruct themselves. EC/OC/AP remain separate future tasks.

## 14. Future-task compatibility

A future task should fit one of three cases:

1. **existing track + new subtree** → L1, no central policy edit;
2. **existing track + must alter shared existing interface** → L2 exception;
3. **new top-level scientific track or counted/frozen change** → one policy extension or
   L3 lifecycle.

This keeps governance complexity approximately proportional to the number of stable
scientific domains, not to the number of experiments/theorem programs ever attempted.

## 15. Design principle

The governing rule is:

> **Research is open by default inside a machine-enforced owned namespace; historical and
> counted surfaces are closed by default.**

The project should spend governance effort on semantic blast radius, not on repeating the
same authorization ceremony for every new scientific question.
