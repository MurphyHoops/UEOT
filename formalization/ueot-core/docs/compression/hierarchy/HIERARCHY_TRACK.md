# Track H — Hierarchy / Assembly Audit

Status: **H0 INVENTORY COMPLETE CANDIDATE / EXACT-HEAD VALIDATION REQUIRED**

Authority:

- parent compression mission: Issue #146;
- Track H tracker: Issue #197;
- guarded-activation tracker: Issue #200;
- P0b activation PR: #202;
- H0 branch: `compression/hierarchy-h0-inventory`;
- counted-core impact: **NONE**.

## Purpose

This directory is the owned documentation surface for Track H. P0b installed
the namespace and governance boundary; H0 now inventories and types the existing
hierarchy-relevant theorem surface before H1/H2/H3 introduce any new theorem.

Canonical H0 artifact:

- `H0_HIERARCHY_INVENTORY.md`

Track H proceeds in order:

1. **H0 — inventory / typing**: source/Lean-backed hierarchy inventory;
2. **H1 — existing-generator coverage**: test G0 plus merged G1/G2 against every H0 row;
3. **H2 — parent-object assembly residual**: isolate any genuinely irreducible multi-input parent-formation obligation;
4. **H3 — no-go / separation**: machine-check or recover false-unification boundaries.

H0 is considered closed only after this candidate passes exact-head CI/review,
merges to canonical `main`, and resulting-main validation is green.

Track H must not independently implement stationary-law / GOA perturbation,
recurrent topology, residual inverse, or spectral/local isolation; those remain
Track S until the cross-track integration gate opens.

## Machine governance

The post-FINAL architecture uses five independent record fields:

`(architecture_role, lifecycle_status, track_owner, authority_provenance, counted_core_impact)`.

Roles are G0/G1/G2/G3. Role does not imply lifecycle or counted status. In
particular, G2 Composite Assembly is not the same question as H2 Parent-Object
Assembly Residual.

The canonical enum values and combination checks live in
`COMPRESSION_RESEARCH_TRACKS.json` and are enforced by
`validate_compression_research.py`.

Track X is CLOSED during H0-H3/S1-S2 parallel work. Cross-track dependencies
must be consumed from canonical `main`, never from another unmerged branch.

## H0 nonclaims

The H0 inventory does not claim:

- a universal hierarchy operator;
- a new counted primitive;
- a 4 -> 3, 4 -> 4, or 4 -> 5 outcome;
- that quotienting implies parent formation;
- that the existing G2 Agency -> GOD -> GOA theorem solves H2;
- any Track-S-owned stability theorem.

Frozen Core v3 accounting remains:
`11 generated + 89 retained_adapter + 6 retained_boundary / 0 unresolved`,
with counted generators
`{M-QD-01, M-TC-01, M-PE-01, M-OI-01}`.
