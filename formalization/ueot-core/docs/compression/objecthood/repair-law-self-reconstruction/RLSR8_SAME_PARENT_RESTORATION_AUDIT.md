# RLSR8 — same-parent / semantic restoration audit

Status: **LOCAL PASS**

## Intended terminal result

The RLSR reconstruction benchmark is tied to one exact
`SemanticallyStableSelfRepairingOperationalParent`.  A mutable repair program
must satisfy two independent contracts:

1. it behaviorally implements that exact parent's certified physical repair
   policy, so the parent's existing repair basin transfers to the reconstructed
   program;
2. it is behaviorally valid/preserving on that parent's persistence kernel, so
   after recovery it cannot immediately destroy the restored identity.

From a one-replica program fault and arbitrary ordinary-controller corruption,
the terminal theorem combines exact first-step internal reconstruction, the
unchanged Track-X semantic bound for the same selected parent, almost-sure
eventual-permanent physical restoration, and closure of the recovered joint
target.

## Independent assumption audit

`PhysicalRepairCertificate` does **not** itself state that its `repairPolicy`
preserves the target after entry.  Therefore RLSR8 deliberately does not derive
`hvalid` from physical recoverability; both are needed for the stronger
"eventually always" identity claim.

The semantic machinery is a specification of the exact same selected parent;
RLSR8 does not claim to reconstruct that semantic certificate if the semantic
machinery itself is destroyed.

## Validation

- focused Lean compile/build of `SameParentRestoration.lean`: PASS;
- theorem-surface lint cleanup removed all new-file warnings;
- `git diff --check`: PASS.
