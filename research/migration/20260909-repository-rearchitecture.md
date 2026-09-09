# Repository Migration Log — 2026-09-09

## Decision

The project adopted the derivation-first architecture approved in
`council/resolutions/20260909-derivation-first-repository-architecture.md`.

## Completed

- created active `core/`, `physics/`, `validation/`, `research/`,
  `applications/`, `publications/`, and `archive/` roots;
- rewrote the repository README around the derivation/validation chain;
- added `docs/PROJECT_ARCHITECTURE.md`;
- completed RFC and architect resolution;
- aligned constitution and method with the new canonical routing;
- retained all legacy source/book/domain/council materials.

## In progress

- exact Core v3 specification synchronization;
- restoration/completion of Lean Core modules;
- UEOT-QM/physics synchronization.

## Legacy routing

- `domains/formal-foundations/` → historical precursor to `core/` +
  `formalization/`;
- `domains/physics-cosmos/` → historical precursor to `physics/`;
- other `domains/*` → evaluate for migration under `applications/`;
- `book/` → future `publications/book/`;
- `source/paper/` and root manuscript artifacts → future publication/release
  layout.

## Non-destructive rule

No legacy path is removed until:

1. active replacement exists;
2. links are updated;
3. provenance is recorded;
4. governance dependencies are checked.

Git history is not used as a substitute for an explicit archive/provenance
record.
