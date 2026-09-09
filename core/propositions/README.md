# UEOT Proposition and Claim Registry

This directory defines the repository-wide identity contract for serious claims.

## Stable identity

Core mathematical propositions retain their existing `P-...` IDs. New claim
families should use a stable namespace appropriate to their layer; IDs are not
recycled when a claim is deprecated.

A claim record connects:

```text
source statement
   ↓
dependencies
   ↓
formal theorem(s)
   ↓
bridge / sector assumptions
   ↓
observable / validation target
```

## Status is not inferred

The registry does not infer `proved` from the existence of a Lean declaration
or `empirical` from the existence of a data file. Status changes are explicit
and auditable.

## Required fields

See `schema.yaml`.

For Core P-IDs, the current source-level status remains maintained by the v3
coverage ledger until a machine-readable 106-item registry is restored.
