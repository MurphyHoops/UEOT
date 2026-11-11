# C -> A independent internal review

Reviewer: native research agent C. Reviewed `research_a/OPERATIONAL_SEMANTICS_BRIDGE.md`,
the initially supplied `UEOTQM/OperationalEquivalence.lean`, and the ten-check
exact-control receipt. This is internal AI cross-review, not external peer
review. The proof file was uncompiled at the time of this source review.

## Attack 1: can unnormalized/zero events defeat statistical identity?

Attempted counterexample: maps X -> X/4 and X -> X/2 have equal posterior
states on every positive-probability input and different actual events.
A's stated theorem uses raw probabilities for all effects including I,
which immediately distinguishes them. The zero event is included without
forming a posterior. The paper first separates Hermitian outputs with
possibly unequal traces, then extends equality from densities to PSD,
Hermitian and finally all complex matrices. These are the needed steps;
no equal-trace assumption is smuggled in. The corresponding Lean statement
`hermitian_eq_of_all_effect_pairings_eq` does not assume trace equality.

Result: no mathematical counterexample found within the declared full
complex state/effect model. Restricted effects or restricted inputs break
the implication, and A records both controls. Complex linearity is needed
for the final extension; A states it rather than appealing to a merely
real-linear operation on complex matrices.

## Attack 2: can hidden refinements or context changes defeat composition?

Attempted counterexample: replace one identity Kraus operator by two
proportional identity Kraus operators and let the controller react to the
new hidden index. The controlled processes can differ, despite equal
forgotten channels. A's congruence theorem retains the same visible labels
and permits controls only on those labels, so that attack is outside the
claimed domain. Label swaps fail already on a one-dimensional classical
readout and are not identified by the quotient. Equality of actual linear
maps implies equality after the derived tensor-id amplification, including
entangled inputs. Sequential substitution and finite-tree induction are
then valid under the same typed terminal spaces/record embeddings.

Result: no mathematical gap found, provided actual implementations do not
promote Kraus indices to visible records without changing the contract.

## Required scope clarifications

1. In the OPT inventory, closed event/test sets means fixed finite system
   types and a fixed finite outcome alphabet in finite matrix coordinates.
   A union over all finite test shapes has no ambient topology specified
   by this draft, so it must not be called a single closed set.
2. Paper and Lean coverage must be separate. The inspected Lean draft
   contains unnormalized separation, normalized-input linear-map identity,
   rectangular Choi injectivity, the forward context-statistics implication,
   TNI Kraus events and their actual tensor amplification, plus elementary
   composition and sum congruences. It does not yet bundle all four
   equivalences into a context-iff theorem, implement a full labelled
   rectangular Test with closure and tensor coherence laws, construct an
   abstract quotient category, or machine-check the complete finite-tree
   quotient induction. The paper proofs can be accepted with these machine
   limits stated; the new file must still compile and pass axiom audit.

These clarifications were sent to A and root. They narrow evidence claims,
not the proved mathematical statement. No frozen Core changes are needed.

## Follow-up source review after A's correction

The revised paper (`OPERATIONAL_SEMANTICS_BRIDGE.md`, SHA-256
`1b9a46c9b7c4ca238dd8b66213983d8c2858dac37677267f16ccc735a530131e`)
now states closedness only for fixed finite carriers and a fixed visible
alphabet. That requested correction is resolved.

The inspected revised Lean source (`OperationalEquivalence.lean`, SHA-256
`33e5ce031569ca882f1361847b8987d08c2192e21f08e6a704fa986ee12e915c`)
adds `ContextStatistics` over all finite positive-dimensional reference
carriers and all joint states/effects, a genuine one-dimensional
`scalarDensity`, `scalarEffect`, the proved tensor-unit pairing identity,
and context iff single-system/map/Choi theorems. C read this block and
found it faithfully expresses the paper's tensor-unit argument. The
earlier statement that the context-iff theorem was absent applies only
to the initial draft; this subsequent addition is explicitly recorded.

The rest of the scope limitation remains: a fully bundled rectangular
instrument/OPT quotient with all tensor coherence and adaptive-tree
laws is a paper construction, not a newly accepted formal bundle. No
compilation result is asserted by this review; root's actual compiler
and axiom-audit receipt determines that status. Later source changes
require their own identity rather than silently changing this review.

Verdict: paper-level bridge accepted within the declared full complex
sector and exact-equality scope; final machine acceptance remains tied
to its actual execution receipt. No mathematical blocker remains from C.
