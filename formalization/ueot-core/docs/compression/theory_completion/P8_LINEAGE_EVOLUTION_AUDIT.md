# Theory Completion P8 — Reproduction / Lineage / Evolutionary Object Audit

Status: **LOCAL COMPLETE / TRACK TC / UNCOUNTED**

Immediate local dependency: review-tightened P7 exact head
`bae75cdb8e31abd52c61ea3c479b1e234f6ca7bd`.

## Result

P8 introduces a typed `LineageSemantics` with object identity and a separate
`parentOf` relation. `OffspringOf` requires both genealogy and a new identity;
therefore same-object restoration cannot be counted as reproduction.

A population transmission kernel is `ReproductiveTransmission` only when each
positive parent→child entry is an actual offspring edge. Under that explicit
bridge, the existing Core P-EVO-01 Price decomposition applies to the same
kernel. The existing P-EVO-03 Perron growth theorem is re-exported unchanged
under its primitive-matrix certificate and valuation assumptions. Core P-BRG-02
continues to state only that behaviorally equivalent objects have equal bridge
fitness.

Terminal theorem: `p8_terminal_lineage_evolution` packages the identity boundary
and the exact Price decomposition without deriving reproduction from Objecthood.

## Claim class

**CONDITIONAL THEOREM + DOMAIN BRIDGE.**

## Boundaries

P8 does not prove that every object reproduces, that behavior alone uniquely
identifies fitness, that mutation is absent, or that a primitive offspring
operator follows from object identity. Frequency-dependent fitness, mutation,
material costs and type-dependent channels require a changed model. P8 also does
not equate repair, construction and reproduction.

No frozen Core theorem, counted generator or ledger entry is changed.
