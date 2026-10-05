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
| P1.0 | `objectEvidence_projection_not_purposeIdentifying` | no-go / identifiability boundary |
| P1.1 | `AdmissibleFutures`, `AdmissibleFuture` | definition / typed interface |
| P1.2 | `PreferenceRelation`, `IsPreferencePreorder`, `TeleologicalContract` | definition / semantic contract |
| P1.3 | `finiteContractOrdinalUtility_represents`, `TeleologicalContract.exists_finite_ordinal_representation` | conditional theorem: finite admissible domain + total preference |
| P1.4 | `ExpectedUtilityRepresents`; `ordinal_equivalence_does_not_determine_expected_value` | stronger interface + no-go/boundary theorem |
| P1.5 | `TeleologicalObjectiveClass` and equivalence-class laws | definition + theorem |
| P1.6 | `DualDriveRepresentation`, `DualDriveGaugeClass`, orbit laws, `gaugeTransform_valueEqual` | representation interface + canonical DDH adapter |
| P1.7 | `gaugeClass_to_teleologicalClass` | theorem / one-way bridge |
| P1.8 | `teleologicalEquivalent_not_implies_sameGaugeClass` | no-go / converse boundary |

## Exact semantic hierarchy

The formal hierarchy is:

[
	ext{TeleologicalContract}
supseteq
	ext{finite ordinal representation when finite+total}
]

and, independently at the numerical-representation level,

[
	ext{DDH gauge orbit}
Longrightarrow
	ext{pointwise-equal combined objective}
Longrightarrow
	ext{same weak ordering}
Longrightarrow
	ext{same teleological objective class}.
]

The converse from teleological weak-order equivalence to one DDH gauge orbit is
false in general and is machine-checked by
`teleologicalEquivalent_not_implies_sameGaugeClass`.

## P1.3 representation boundary

The general `TeleologicalContract` does **not** assume totality.  P1.3 adds:

- finiteness of the admissible set;
- totality of the declared weak preference.

Under those explicit assumptions, the strict-lower-contour rank gives a real
ordinal utility (u) satisfying exactly

[
u(x) le u(y) iff x preceq y.
]

No positive-affine uniqueness follows from this theorem.

## P1.4 expected-value boundary

Expected-value semantics is exposed only through the explicit stronger
`ExpectedUtilityRepresents` obligation.  The three-outcome counterexample
proves that two strictly order-equivalent outcome utilities can disagree on the
ordering of lotteries under expectation.  Therefore ordinary ordinal utility
cannot be promoted to cardinal/expected utility without extra mixture/cardinal
axioms.

## P1.0 identifiability discipline

The P1.0 no-go is a projection-identifiability statement.  Holding one object
evidence value fixed while forgetting the purpose extension does not determine
one teleological weak ordering on the unconstrained extension space.

It does **not** assert that every mathematical extension is physically
realizable by one concrete UEOT object.  Physical/endogenous identification is
a separate bridge problem.

## Explicit nonclaims

P1 does not claim:

- Objecthood uniquely determines a reward or objective;
- every teleological preorder has a Pi/Phi decomposition;
- ordinal utility is positive-affine unique;
- maximizer equivalence is the same as weak-order equivalence;
- DDH gauge equivalence exhausts teleological equivalence;
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
