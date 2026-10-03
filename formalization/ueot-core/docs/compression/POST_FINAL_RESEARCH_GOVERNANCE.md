# UEOT Core Compression — Post-FINAL Parallel Research Governance

Status: **GUARDED ARCHITECTURE ACTIVE / TRACK X MERGED SURFACE REGISTERED / TRACK O GATE OPEN / POST-FINAL / UNCOUNTED**

Authority:

- parent mission: GitHub Issue **#146**;
- scientific contract: COMPRESSION_MISSION.md;
- counted claims: COMPRESSION_LEDGER.yaml;
- machine track registry: COMPRESSION_RESEARCH_TRACKS.json.

This document governs research after the frozen four-generator FINAL checkpoint.
It does not reopen any frozen Core v3 P-ID and does not change the counted
compression ledger by itself.

## 1. Fixed scientific baseline

The live counted core remains the exact minimal core recorded by the ledger:

\[
\{M\text{-QD-01},M\text{-TC-01},M\text{-PE-01},M\text{-OI-01}\}.
\]

All post-FINAL bridge, synthesis, assembly, gauge, stability, topology, and
hierarchy work is **UNCOUNTED** unless it later completes the separate
promotion/re-ablation/re-finalization lifecycle already required by the Mission
Contract.

No research track may change the ledger merely because a new abstraction is
elegant or compiles.

## 2. Source tracks and cross-track integration

### Track S — Structural Defect / Long-Run Stability

Track S continues the already integrated post-FINAL line:

- structural-defect closure;
- representation / semantic / GOA gauge;
- Agency -> GOD -> GOA assembly where used as a stability interface;
- recurrent support topology;
- topology-changing GOA semantics;
- stationary-branch perturbation certificates;
- fixed-point residual inverse;
- spectral/local isolation certificates that explain residual bounds.

Scientific question:

> Given an already typed state/object/control/long-run structure, under what
> weakest explicit certificates does its selected long-run semantics remain
> meaningful and quantitatively trackable under representation, model, or
> topology change?

Track S owns this theorem family. Track H must not independently re-prove or
fork it.

### Track H — Hierarchy / Assembly Audit

Track H tests a different question:

> Can the hierarchy structures already present in Core v3 be generated or
> organized by the existing four counted generators and integrated post-FINAL
> bridges, and what irreducible residual remains for genuine parent-object
> assembly?

Initial scope is deliberately limited to:

- H0 — hierarchy inventory / typing;
- H1 — existing-generator and bridge coverage;
- H2 — parent/assembly residual analysis;
- H3 — no-go / separation theorems.

Track H does **not** own GOA stability, stationary-law perturbation, recurrent
merge/split stability, fixed-point inverse, or spectral isolation.  Those
theorem families remain Track-S-owned even after the Track-X gate opens.
Track X may consume their merged public interfaces from canonical `main`, but
may not re-prove or mutate the Track-S source surfaces.

### Track X — Parent Formation × Long-Run Semantic Stability

Track X is the dedicated integration lane opened only after the independent
Track-S finite-state closure and Track-H H0--H3 closure are both merged and
auditable on canonical `main`.

Detailed tracker: **Issue #225**.

Scientific question:

> When one child/coarse evidence state admits multiple richer parent
> completions, under what exact or quantitative conditions is the parent's
> long-run semantics nevertheless well-defined or stable?

Track X owns only the **composition of already merged H and S interfaces**.  It
does not reopen either source track.  In particular it must keep separate:

- assembly ambiguity: one child evidence state admits multiple parent
  completions;
- dynamical semantic ambiguity: one fixed parent dynamics admits multiple
  invariant long-run laws.

The first required negative result is that unique GOA semantics for every
completion does not imply child-determined parent GOA.  Positive work then
proceeds through exact parent-semantic descent, quantitative
`epsilon / kappa` stability, fibre-wide semantic diameter, a derived robust
parent-semantic certificate, and finally an out-of-sample P-COMP assembly test.

All ordinary Track-X results are uncounted G1/G2/G3 research.  A new G0
primitive is outside Track X and would require a later dedicated promotion
lifecycle.

### Track O — Objecthood / Omega-loop Self-Repair

Track O is the dedicated lane for the residual exposed by the merged Track-X
endogenous-persistence result.

Completed first-cycle tracker: **Issue #230 / O0--O8**.

Current continuation tracker: **Issue #234 / ER0--ER3**.

Scientific question:

> Once a parent/object candidate has been formed, identified, and equipped with
> constitutive runtime persistence, under what exact conditions can the same
> autonomous system recover its legitimate organization after transient internal
> corruption rather than merely preserving a controller that was initialized
> correctly?

Track O must separate three notions that earlier source material can otherwise
blur:

1. **closure** — legitimate constitutive states remain legitimate;
2. **convergence** — states in a declared transient-fault/repair basin return
   to the legitimate domain;
3. **specification** — the recovered domain still carries the required UEOT
   formation/persistence semantics.

The first O0--O8 finite target is deliberately narrower than universal
Objecthood.  That lifecycle is complete.  The reopened #234 cycle has the
strictly narrower endogenous-repair objective of removing one supplied
assumption from O4/O5: instead of accepting a `PhysicalRepairCertificate`, it
must derive a strong finite repair basin, rank, descending stationary selector,
and unit-drift repair certificate from the controlled dynamics and target set.
The #234 cycle stops after ER3 and explicitly does not claim full stochastic
repair-basin maximality, recurrent-fault tolerance, dynamic semantic recovery,
repair-law self-reconstruction, autopoiesis, or a fifth counted generator.
Controller-only corruption is handled before physical-state recovery. Physical
recovery must reuse the frozen P-REC hitting/Lyapunov interfaces where possible.
P-OMG failure structure and integrity margins are diagnostic/robustness inputs;
they may not be treated as recovery theorems.

The semantic target is a **functional legitimate-controller class**, not exact
return to one arbitrary stationary selector. For a stabilized winning kernel
`K`, successful repair should target controllers that preserve `K`, because
P-PER generally need not make the preserving controller unique.

Track O consumes frozen P-OMG/P-REC/P-PER/P-REF interfaces and merged Track-X
surfaces from canonical `main` only. It may not reopen or mutate those source
theorem families. Ordinary Track-O results are uncounted G1/G2/G3 research.
Any proposal for a new G0 primitive must wait until the O0--O8 architecture and
deletion audit in #230 and then enter a separate promotion/re-ablation lifecycle.

## 3. Why the split is scientific, not administrative

The tracks address opposite halves of one future synthesis:

\[
\boxed{\text{Track H: how a higher-level object forms}}
\]

versus

\[
\boxed{\text{Track S: how an established long-run structure remains stable}}.
\]

Those independent checkpoints are now complete.  They may meet only through
the explicitly governed Track-X lane; neither Track S nor Track H may absorb
the other's theorem family directly.

## 4. Main-only dependency rule

Cross-track dependencies are **main-only**:

1. Track H may import Track S results only after those results are merged to
   main;
2. Track S may import Track H results only after those results are merged to
   main;
3. no Track H branch may be based on an unmerged Track S branch, and vice
   versa;
4. stacked branches are allowed only within one track when the existing
   Compression Operations Manual explicitly permits them.

This prevents invisible assumptions and cross-chat branch capture.

## 5. File ownership

Track H uses a dedicated namespace:

    formalization/ueot-core/UEOT/V3/Compression/Hierarchy/
    formalization/ueot-core/docs/compression/hierarchy/

and the optional root import:

    formalization/ueot-core/UEOT/V3/Compression/Hierarchy.lean

P0a installed only the immutable base-policy surface. P0b installs the guarded
Hierarchy implementation/documentation roots and wires the empty public
`Hierarchy.lean` root into the global `Compression.lean` import surface. This
activation is namespace/governance only: H0 theorem work starts in a later
Track H PR. Track H itself never owns `Compression.lean`; later hierarchy
modules are wired only through its dedicated root.

On compression/hierarchy-* branches, direct edits to the frozen ledger,
coverage, Mission Contract, ablation record, post-FINAL governance, workflow,
or validators are forbidden. Governance changes travel through a temporary
ops/compression-* branch.

Track S branches are forbidden from editing the Track H namespace. They may
consume merged Track H interfaces from canonical `main` only.

Track X uses a third dedicated namespace:

    formalization/ueot-core/UEOT/V3/Compression/CrossTrack/
    formalization/ueot-core/docs/compression/cross_track/

and the optional public root:

    formalization/ueot-core/UEOT/V3/Compression/CrossTrack.lean

Track-X branches are restricted to that namespace plus the one-line public
`CrossTrack` root import in `Compression.lean`.  They may import Track-S and
Track-H results only from canonical `main`; they may not edit either source
track's owned theorem files.

Track O uses a fourth dedicated namespace:

    formalization/ueot-core/UEOT/V3/Compression/Objecthood/
    formalization/ueot-core/docs/compression/objecthood/

and the optional public root:

    formalization/ueot-core/UEOT/V3/Compression/Objecthood.lean

Track-O branches are restricted to that namespace plus the one-line public
`Objecthood` root import in `Compression.lean`. They may consume frozen
Core-v3 interfaces and merged Track-X public interfaces from canonical `main`
only; they may not edit the source P-OMG/P-REC/P-PER/P-REF theorem files or
Track-X theorem files.

The base-policy guard machine-checks these ownership rules, rejects
unclassified branches touching governed Compression paths, resolves normal
`main` merge pushes back to their associated PR branch, and checks live GitHub
branch state so each research track has at most one remote mutating branch.

Research-governance permissions use **base-policy enforcement**. Once
`COMPRESSION_RESEARCH_TRACKS.json` exists on canonical `main`, a candidate PR
may update that registry but the same PR is authorized only by the registry at
its base ref. Therefore a governance PR cannot widen its own file/branch
permissions and immediately use the wider candidate policy. The initial #198
bootstrap is the one case where no base registry exists yet; after it lands,
subsequent permission changes take effect only for later PRs.

The authorization executor is also base-owned.  The workflow
`.github/workflows/ueot-compression-research-policy.yml` runs on
`pull_request_target`, checks out the PR **base SHA**, fetches the candidate
commit only as inert Git data, and executes the validator from that base
checkout.  Candidate workflow or validator code is therefore never executed by
the authorization job.  A PR that changes the validator, registry, or ordinary
Compression workflow remains subject to the previous main policy for that same
PR.

The base-policy workflow intentionally has **no path filter**. It runs for every
pull request so a rename or deletion cannot evade authorization by moving a
governed source path outside a trigger pattern. The validator itself decides
whether the trusted base/candidate Git diff touches governed Compression paths.

The workflow also listens to the pull-request `edited` event. Any PR base
branch change therefore forces a fresh authorization against the new base SHA;
a successful authorization obtained against a temporary or permissive base
cannot be carried forward after retargeting the unchanged head to `main`.

Mutating Track S, Track H, Track X, Track O, and `ops/compression-*` governance branches must be
hosted in the canonical repository. Fork-based mutating Compression branches
are rejected; read-only/external work can still be reviewed separately without
entering the governed mutation lanes.

Canonical `main` is protected at the repository level: updates require a pull
request, the rule is enforced for administrators, and force-push/delete are
disabled. This repository setting is the direct-main enforcement boundary; it
does not depend on candidate workflow code.

PR #198 is the one bootstrap exception because no immutable research-policy
workflow exists on its base commit. To remove self-authorization from that
bootstrap, #198 is deliberately **installation-only**: it adds the base-policy
workflow, registry, policy document, validator, and validator regression tests,
and makes no Track S/H theorem change, no global `Compression.lean` edit, and
no ordinary Compression workflow edit. Exact-head CI and independent Codex
review audit that minimal diff. Once #198 lands, every activation/follow-up PR
is evaluated by the already-merged immutable base policy.

P0b is the first such guarded activation. It also makes the architecture
taxonomy machine-readable through five independent fields:

- `architecture_role = G0 | G1 | G2 | G3`;
- `lifecycle_status`;
- `track_owner = CORE | S | H | X | O`;
- `authority_provenance`;
- `counted_core_impact`.

The validator rejects invalid combinations. In particular only
`G0 + COUNTED + counted_core_impact=COUNTED` may match the live counted minimal
core; G1/G2/G3 never become counted merely because they are merged; Track X
records are forbidden while the integration gate is closed; and frozen Core v3
authority remains CORE-owned.

## 6. Concurrency

At most **two mutating post-FINAL research lanes** may be active at once across
Track S, Track H, Track X, and Track O. Within each track there is at most one active
mutating branch.  Additional
workers may perform read-only source/theorem audits without branches.

Opening Track X does not reopen the closed scientific subproblems in S or H.
If a future separately authorized S or H extension runs in parallel with X,
the global two-track cap and main-only dependency rule still apply.

This is stricter than simply allowing arbitrary parallel PRs and is intended to
keep Issue #146 recoverable across chats.

## 7. Track H gates

### H0 — Inventory complete

Produce a source/Lean-backed classification of every hierarchy-relevant frozen
P-ID and every post-FINAL theorem actually needed by the audit. Do not create
new mathematics merely to make the table complete.

### H1 — Existing architecture coverage

For each hierarchy family, record whether the route is generated by:

- M-QD;
- M-TC;
- M-PE;
- M-OI;
- an already integrated uncounted bridge;
- or a residual domain structure.

Every claimed route must identify actual theorem surfaces. Similar wording is
not derivation evidence.

### H2 — Assembly residual

Focus on the multi-input parent-object question:

\[
(O_1,\ldots,O_m,U)\rightsquigarrow O_P.
\]

Determine whether the existing architecture reconstructs the parent-object
formation obligations in P-COMP without hiding cut irreducibility, new parent
predictive information, realization, or child-fidelity assumptions.

Failure to derive a parent structure is recorded as a residual, not immediately
renamed as a new generator.

### H3 — No-go / separation

Machine-check or recover explicit separations such as:

- quotient does not imply parent object;
- correlation does not imply parent object;
- parent object does not imply selection unit;
- parent objecthood does not uniquely determine parent objective;
- value alignment does not imply objecthood.

These results are positive scientific outputs because they block false
unification.

### H4+ / Track X — Common structure and cross-track synthesis

**OPEN through Issue #225.**

The opening prerequisites are satisfied: H0--H3 are merged/auditable and Track
S has a stable merged finite-state long-run semantic interface.  The approved
sequence is X0--X8 from #225.  Cross-track work must not bypass that tracker or
mutate H/S source-track files.

### Track O — completed O0--O8 + active ER0--ER3 endogenous-repair gate

**AUTHORIZED TRACK; O0--O8 CLOSED through #230/#232; ER0--ER3 ACTIVE through
fresh Issue #234.**

Track O starts from the merged Track-X boundary that constitutive persistence
does not repair a corrupted controller. The approved O0--O8 sequence is:
functional legitimacy -> controller convergence -> controller-stabilization
certificate -> physical repair basin/P-REC hitting-time bridge -> finite
autonomous stabilization -> P-OMG repairability boundary -> end-to-end formed
parent repair synthesis -> architecture/deletion audit.

The first O0--O8 lifecycle is now complete on canonical main.  PR #232 merged
reviewed head `cda03d1c7bf2199643f0197e74597405ffd87b03` as
`d827d5bc0d1facf6e59669265e3e26fb9d1beaa7`; exact-head Core Lean / Compression
Guard passed, Codex found no major issue after its O6 counterexample P2 was
repaired, and resulting-main Core Lean `37042673290` plus Compression Guard
`37042673416` both passed.

The first lifecycle closure remains immutable in the append-only completion
history.  The Objecthood mutation gate is now **reopened** by the fresh #234
authorization with stage plan `ER0-ER3`; Track O is again in the active
mutating-track set only for that registered cycle.  A
`compression/objecthood-*` branch therefore derives its current authority from
#234/ER0--ER3, never from historical Issue #230.  The counted four-generator
core remains unchanged.

The strongest merged result before #234 is a finite self-repairing constitutive
Omega-loop certificate under an intact repair law and an explicit supplied
repair basin/certificate.  The active #234 question is whether a strong finite
repair certificate can instead be generated from `P` and `K` themselves.  Its
registered stages are: ER0 path-level eventual-always legitimacy; ER1 strong
controlled repair attractor; ER2 least repair rank plus descending stationary
selector; ER3 endogenous `PhysicalRepairCertificate` synthesis.  After ER3 the
cycle must stop and close before any further Objecthood mutation.

The deeper boundary **repair-law self-reconstruction** remains outside this
cycle: damage or absence of the repair-producing organization is not covered by
O5/O7 or by ER0--ER3.  Any later continuation must again register a fresh
tracker issue and fresh stage plan after #234 closes.  The validator
machine-checks freshness before Track O can be active in a later cycle.
Completed Objecthood cycles are stored in an **append-only completion history**:
an authorization PR may not delete, reorder, or rewrite an earlier completion
record to make a closed tracker/stage appear fresh again.  A later close cycle
**must append exactly one** record corresponding to the Track O tracker/stage
that was active on its base, and must close the mutation gate at the same time.

No Track-O result may be renamed full universal or biological Objecthood /
autopoiesis without a separate theorem and governance lifecycle.

## 8. Candidate primitive discipline

Terms such as Assembly, CommonWitness, HierarchyLift, or any proposed new M-ID
are **analysis labels only** until evidence exists.

Before any new primitive may be proposed for counted status:

1. show material reuse across independent hierarchy families;
2. show an existing-generator route is genuinely insufficient without hiding
   assumptions;
3. provide an out-of-sample theorem;
4. run deletion/nonredundancy analysis against the live registered theorem
   surface;
5. complete exact-head CI and independent review;
6. use the normal ledger promotion and re-finalization lifecycle.

The desired number of generators is not fixed. Honest 4 -> 5, 4 -> 4, 4 -> 3,
or no further compression are all permitted outcomes.

## 9. PR and review discipline

Every mutating post-FINAL research PR must:

- target main;
- state Track S, Track H, Track X, or Track O;
- state counted-core impact: NONE unless it is a dedicated promotion lifecycle
  PR;
- identify exact scientific nonclaims;
- pass Core Lean and Compression Guard;
- request Codex review on the exact head;
- if Codex explicitly refuses due to quota, record an independent exact-head
  review before merge;
- validate resulting main before retiring the branch.

One coherent scientific claim per PR is preferred over a long-lived research
mega-branch.

## 10. Live-state discipline

Issue #146 remains the single compression authority. It must record:

- current canonical main;
- frozen counted-core state;
- active Track S branch/PR/next action;
- active Track H branch/PR/next action;
- active Track X branch/PR/stage/next action;
- active Track O branch/PR/tracker/stage/next action whenever the Objecthood
  mutation gate is open;
- cross-track gate state;
- Objecthood mutation-gate state;
- explicit do-not-repeat / ownership guards.

A child Track H issue may be used as a detailed checklist, but it may not
override Issue #146, the Mission Contract, or the live ledger.

## 11. Completion of the hierarchy audit

Track H is complete when it returns one of these evidence-backed outcomes:

1. existing counted generators + merged bridges suffice;
2. a smaller deeper architecture is justified;
3. an additional irreducible assembly primitive is justified;
4. no useful further common generator exists beyond typed adapters/boundaries.

All four are valid outcomes. The research objective is to determine the
structure, not to force a unification.
