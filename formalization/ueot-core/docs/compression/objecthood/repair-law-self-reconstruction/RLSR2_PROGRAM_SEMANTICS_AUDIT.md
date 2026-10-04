# RLSR2 — behavioral program identity audit

Status: **LOCAL PASS**

## Result

A repair program is valid exactly when the controller obtained by trusted
execution preserves the declared carrier.  Program identity is the weaker,
scientifically relevant relation of equal executed actions on that carrier.
Validity is proved invariant under this relation in both directions.

## Independent audit / optimization

The key question was whether RLSR should reconstruct code identity or repair
behavior.  Requiring syntactic equality would make arbitrary compiler/encoding
choices part of object identity.  The audited endpoint therefore uses
carrier-relative behavioral equivalence as the identity notion, while retaining
`RepairProgramImplementsPolicy` only as an explicit later bridge to a selected
parent's already-certified repair policy.

This avoids both overclaiming code identity and weakening the operational
preservation contract.
