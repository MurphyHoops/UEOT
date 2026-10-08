# N6-B — transfer-audited finite parent set and reused SI-2 source uniqueness

Source: SISCInterventionTransferAudit.lean. Status: conditionally Lean-checked, no independent physical data.

The prior repository already contains SI-2's formed-target response triangle, LocalResponseGap and unique_formed_target_of_local_gap, plus N3's finite three-way candidate resolver and P4's generic inverse objecthood evidence semantics. None of these statements are copied or redeclared.

N6-B introduces a small typed interface specifically for a *registered source-candidate universe*, an independently audited material/program transfer relation into a declared child, reference responses under registered interventions, measured responses, and a real tolerance.

The operational candidate set is FINITE and computed as:
- parent is registered,
- parent has an independently authenticated transfer record into the child,
- parent reference response agrees with the observed child intervention fingerprint on every probe within tolerance.

There is no selected parent or transporter tp among the inputs; the parent variable in the correctness theorem is only a proof witness.

Lean proves:
- exact candidate membership decomposition into the three conditions;
- under a genuine fitting parent and SI-2 LocalResponseGap, any accepted candidate is that parent, by *calling the old unique_formed_target_of_local_gap*;
- under registration, transfer record, fit and strict separation, the returned candidate set is exactly the singleton true source;
- two distinct accepted candidates preclude any singleton answer, making abstention mandatory;
- only under an external soundness condition connecting a verified transfer record to P8's parentOf does a unique operational candidate imply a P8 genealogical edge;
- P8 OffspringOf requires an *additional* independently certified identity difference. Same-identity repair must not be relabeled reproduction.

Scientific limits: an 'authenticatedTransfer' predicate is an explicit external evidence input, not verified by the Lean theorem; a fake/spoofed or incompletely logged transfer breaks soundness. Probe fidelity, intervention assignment, chain-of-custody, object-level candidate type, and causal effect isolation remain experiment-facing tasks. This module does not assert full P8 compatibility for every positive K transition or reconstruct the P12 lifecycle.

Future concrete fixtures must check that an uninformative transfer ledger still leaves two passive parent candidates and a registered active probe separates them. No cloud promotion.
