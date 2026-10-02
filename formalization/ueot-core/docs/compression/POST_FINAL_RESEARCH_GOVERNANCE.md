# UEOT Core Compression — Post-FINAL Parallel Research Governance

Status: **GUARDED ARCHITECTURE ACTIVE / POST-FINAL / UNCOUNTED**

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

## 2. Two active research tracks

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

#### Track-S finite-state closure and S∞ continuation

The finite-state Track-S mission is **CLOSED** through PRs #220--#222.  Its
canonical merged conclusion must not be reopened merely to add another
equivalent finite-state qualitative certificate:

\[
\kappa_1(P)>0
\Longleftrightarrow
\text{unique finite invariant probability semantics},
\]

with the canonical finite-state perturbation radius already recorded on main.

The next separately governed Track-S mission is **S∞**, tracked by Issue
**#223**.  Its scope is deliberately narrower than "continue Track S":

- move from finite-dimensional residual isolation to an honest
  infinite-state / operator-level interface;
- separate invariant-law **existence** from **uniqueness/isolation** and from
  **perturbation tracking**;
- test bounded-below/coercive residual operators on an appropriate zero-mass
  signed-measure or Banach-space difference space;
- require at least one non-finite realization before scientific closure;
- retain a no-go/separation lane, especially because uniqueness does not imply
  a positive bounded-below constant in arbitrary infinite-dimensional spaces.

S∞ must begin at the API/feasibility audit in #223.  It may not start by
postulating the desired residual inverse as a renamed definition and may not
infer invariant-law existence from injectivity/coercivity.  It remains
post-FINAL and uncounted unless a later, separate primitive-promotion lifecycle
is explicitly authorized.

Preferred S∞ branch prefix: `compression/goa-infinite-*`.  The existing
Track-S branch regex already authorizes this prefix after this governance
transition is merged.  There is still at most one live Track-S mutating branch.

S∞ does **not** own hierarchy/parent assembly or Track-X integration.  If the
research requires H/X assumptions to proceed, it must return the residual to
Issue #146 rather than crossing ownership boundaries.

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

Track H initially does **not** own GOA stability, stationary-law perturbation,
recurrent merge/split stability, fixed-point inverse, or spectral isolation.
Those remain Track S until a later explicit cross-track integration gate is
opened.

## 3. Why the split is scientific, not administrative

The tracks address opposite halves of one future synthesis:

\[
\boxed{\text{Track H: how a higher-level object forms}}
\]

versus

\[
\boxed{\text{Track S: how an established long-run structure remains stable}}.
\]

They may eventually meet in a theorem about the stability of a genuinely
formed parent object's long-run semantics. That theorem is **not** licensed
yet. First each side must reach an independently audited checkpoint.

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
consume merged Track H interfaces from main later.

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

Mutating Track S, Track H, and `ops/compression-*` governance branches must be
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
- `track_owner = CORE | S | H | X`;
- `authority_provenance`;
- `counted_core_impact`.

The validator rejects invalid combinations. In particular only
`G0 + COUNTED + counted_core_impact=COUNTED` may match the live counted minimal
core; G1/G2/G3 never become counted merely because they are merged; Track X
records are forbidden while the integration gate is closed; and frozen Core v3
authority remains CORE-owned.

## 6. Concurrency

At most **two mutating post-FINAL research lanes** may be active at once:

- one Track S branch;
- one Track H branch.

Within each track there is at most one active mutating branch. Additional
workers may perform read-only source/theorem audits without branches.

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

### H4+ — Common structure and cross-track synthesis

Closed initially.

The cross-track integration gate may open only after H0-H3 are auditable and
Track S has a stable merged interface for the long-run/stability concepts H
would consume.

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
- state Track S or Track H;
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
- cross-track gate state;
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
