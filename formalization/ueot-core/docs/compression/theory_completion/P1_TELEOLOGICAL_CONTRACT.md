# P1 Teleological Contract — terminal scientific audit

Tracker: #271
Program: #265
Canonical base: `effd4ea8acf543a55f5dadc3cbd23232c9a453ef`

## Scientific result

P1 formalizes purpose as a representation/equivalence problem over admissible
futures.  The general contract is intentionally weaker than a numerical reward:
it contains a nonempty admissible-future set and a preorder preference relation.
Stronger scalar, expected-value and Pi/Phi representations require additional
structure and are not silently identified with the contract.

## Stage disposition

| Stage | Formal result | Claim class |
| --- | --- | --- |
| P1.0 | `purpose_not_identified_of_valid_counterexample`; `unconstrained_objectEvidence_projection_not_purposeIdentifying` | conditional no-go schema + interface boundary; **PARTIAL**, no physical UEOT witness pair claimed |
| P1.1 | `AdmissibleFutures`, `AdmissibleFuture` | definition / typed interface |
| P1.2 | `PreferenceRelation`, `IsPreferencePreorder`, `TeleologicalContract` | definition / semantic contract |
| P1.3 | `finiteContractOrdinalUtility_represents`, `TeleologicalContract.exists_finite_ordinal_representation` | conditional theorem: finite admissible domain + total preference |
| P1.4 | `ExpectedUtilityRepresents`; `ordinal_equivalence_does_not_determine_expected_value` | stronger interface + no-go/boundary theorem |
| P1.5 | `TeleologicalObjectiveClass`, `ObjectiveRepresentsContract`, `ContractObjectiveClass` | definition + representation theorems |
| P1.6 | `DualDrivePair`, `DualDriveAdmissibilitySpec`, `ValidDualDriveRepresentation`, `DualDriveGaugeClass` | algebraic pair + explicit semantic-validity interface + DDH adapter |
| P1.7 | `gaugeClass_of_validRepresentation_representsContract`; `gaugeTransform_preserves_validRepresentation` under `GaugeClosed` | conditional one-way bridge |
| P1.8 | `teleologicalEquivalent_not_imply_sameAlgebraicGaugeOrbit`; `incomparableBoolContract_has_no_numerical_representation`; `incomparableBoolContract_has_no_validDualDriveRepresentation` | algebraic converse no-go + semantic representation no-go: a legal non-total contract need not admit any scalar or valid Pi/Phi representation |

## Exact semantic hierarchy

At the contract level:

- a `TeleologicalContract` is a nonempty admissible-future domain plus a preorder preference;
- finite admissible domain + total preference implies a real ordinal representation;
- a legal non-total contract can fail to admit **any** real-valued numerical representation;
- ordinal representation alone does not imply expected-value semantics.

At the dual-drive level:

- `DualDrivePair` is only algebraic Pi/Phi data;
- `DualDriveAdmissibilitySpec` supplies domain-specific admissibility conditions for the two axes;
- `ValidDualDriveRepresentation` additionally requires the combined objective to represent the declared contract;
- an algebraic DDH gauge transform preserves the combined objective pointwise;
- if the source pair is valid, every algebraic gauge representative has a combined objective representing the same contract;
- `GaugeClosed` is an explicit **sufficient** condition guaranteeing that every gauge transform of a valid pair remains valid; P1 does not claim this condition is necessary.

No reverse implication or universal semantically valid Pi/Phi decomposition is claimed.

## P1.3 representation boundary

The general `TeleologicalContract` does **not** assume totality. P1.3 adds:

- finiteness of the admissible set;
- totality of the declared weak preference.

Under those assumptions, the strict-lower-contour rank gives a real ordinal
utility u satisfying exactly:

`u(x) <= u(y) iff x is weakly preferred to y`.

No positive-affine uniqueness follows from this theorem.

## P1.4 expected-value boundary

Expected-value semantics is exposed only through the explicit stronger
`ExpectedUtilityRepresents` obligation.  The three-outcome counterexample
proves that two strictly order-equivalent outcome utilities can disagree on the
ordering of lotteries under expectation.  Therefore ordinary ordinal utility
cannot be promoted to cardinal/expected utility without extra mixture/cardinal
axioms.

## P1.0 identifiability discipline

`purpose_not_identified_of_valid_counterexample` is the reusable scientific criterion: if two **valid** models share the same object evidence but induce different weak orderings, then purpose is not identified by that evidence.

P1 does not currently construct such a pair of physically admissible full UEOT Objecthood models. The separate theorem `unconstrained_objectEvidence_projection_not_purposeIdentifying` proves only that a bare evidence coordinate does not identify the purpose coordinate on an unconstrained product extension.

Therefore P1.0 is **PARTIAL / EXPLICIT BOUNDARY**, not a completed model-theoretic Objecthood-alone no-go.

## P1.6-P1.8 Pi/Phi discipline

A bare algebraic pair is deliberately **not** a valid teleological representation. Semantic validity requires:

1. Pi satisfies the domain-supplied Pi admissibility predicate;
2. Phi satisfies the domain-supplied Phi admissibility predicate;
3. Pi - lambda Phi represents the declared contract preference.

Because axis admissibility is external domain structure, `HasValidDualDriveRepresentation` is not derived from teleological ordering alone in P1. The algebraic theorem `teleologicalEquivalent_not_imply_sameAlgebraicGaugeOrbit` separately shows that weak-order equivalence is strictly coarser than one fixed-lambda DDH gauge orbit.

## Explicit nonclaims

P1 does not claim:

- Objecthood uniquely determines a reward or objective;
- two physically valid same-Objecthood models with different purposes have already been constructed;
- every teleological preorder has a semantically valid Pi/Phi decomposition;
- ordinal utility is positive-affine unique;
- maximizer equivalence is the same as weak-order equivalence;
- algebraic DDH gauge equivalence exhausts teleological equivalence;
- DDH gauge transformations preserve domain-specific axis semantics unless `GaugeClosed` is explicitly supplied;
- a numerical objective is itself the UEOT object;
- P1 establishes same-object Objecthood → Agency → GOD → GOA.

## Input to P2

P2 may consume the reusable `TeleologicalContract` interface only after it
constructs or identifies the contract from the **same** formed/self-maintaining
object whose history, effective state and control dynamics are used downstream.
P1 supplies purpose semantics and representation boundaries; it does not supply
the P2 identity guard.

## Counted status

Track-TC results remain uncounted.  P1 does not modify frozen Core v3, counted
compression ledger/coverage, minimal-core membership, or S/H/X/O theorem source.
