# UEOT Core Compression — Gate C Ablation Audit

This document records the scoped nonredundancy audit required by Mission
Contract v1 before the compression core can be frozen.

It does **not** claim model-theoretic independence or a uniquely privileged
axiomatization.  The audited claim is exactly:

`nonredundant_under_declared_derivation_system`.

## 1. Declared derivation system

The Gate C ablation audit is relative to a **registered theorem-surface
derivation DAG** frozen at canonical Gate-B main
`db880cfc96820b9069a127caa44cd9255237cd97`.

This point is essential.  Gate C does not ask whether a removed theorem can be
re-proved from Lean's foundations or from arbitrary Mathlib lemmas.  Every
proved theorem in the repository is ultimately re-provable from lower-level
facts, so that interpretation would make theorem-level ablation vacuous.  The
Mission Contract instead asks for nonredundancy under the declared derivation
system used by this formalization.

The **allowed nodes** after ablating one candidate core generator are fixed
before the deletion test:

1. canonical theorems of the remaining **counted** M-IDs;
2. already integrated compression wrappers/specializations attached to those
   remaining M-IDs;
3. source/domain adapter theorems or definitions that were already registered
   for counted mappings before Gate C.

The **allowed edges** are:

- application and specialization of an allowed theorem node;
- composition of allowed theorem nodes;
- equality rewriting and definitional reduction;
- discharge of an allowed theorem's stated hypotheses using registered adapters;
- routine Mathlib side-condition/normalization lemmas that do not synthesize a
  replacement compression theorem.

“Registered adapters” therefore does **not** mean the entire frozen source
namespace, and “Mathlib infrastructure” does **not** license synthesizing an
arbitrary new macro proof after seeing which generator was deleted.  A new
proof route whose conclusion reconstructs the removed generator primitive is a
new derivation node.  It must first be independently registered, audited and
promoted before it can participate in a later ablation.

The following are **not** allowed as a way to defeat an ablation:

- calling a theorem from the ablated generator namespace;
- calling the frozen source endpoint of the generated P-ID used as the
  ablation witness;
- treating an unregistered source helper as an adapter merely because it exists
  in the frozen source namespace;
- promoting an analysis-only candidate such as M-BU-01 or M-OI-01 during the
  same ablation;
- synthesizing or inlining a new theorem/proof route that reconstructs the
  removed generator primitive from lower-level library facts.

This last rule is not an assertion of logical independence.  It fixes the
graph whose nonredundancy is being audited.  If a future analysis discovers a
better replacement route, that route can be formalized and promoted, after
which Gate C may legitimately be rerun on the enlarged theorem surface.

Thus “not derivable” here means **not reachable in the frozen registered
theorem-surface DAG without reintroducing the removed primitive**.  This is the
scoped architectural minimality notion permitted by Mission Contract v1, not
absolute logical non-derivability across Lean/Mathlib or all future
axiomatizations.

## 2. Candidate frozen core

The generated final dispositions use exactly three counted generators:

- **M-QD-01 — Quotient Descent**
- **M-TC-01 — Transport Certificate Calculus**
- **M-PE-01 — Positive Eigenstructure Calculus**

The nine generated P-IDs depend on them as follows:

| M-ID | Generated P-IDs that directly depend on it |
|---|---|
| M-QD-01 | P-PRED-01, P-INT-02 |
| M-TC-01 | P-API-01, P-ID-01, P-ID-02, P-DYN-03, P-DYN-04 |
| M-PE-01 | P-QSD-02, P-EVO-04 |

No generated P-ID names more than one M-ID, so each mapping has an unambiguous
generator attribution.  That attribution is not by itself an ablation result:
each deletion experiment separately checks whether registered adapters already
provide an alternate source-faithful route.

## 3. Ablation A — remove M-QD-01

Remaining counted core:

- M-TC-01
- M-PE-01

Broken generated mapping used as the nonredundancy witness:

- P-PRED-01

M-QD-01 supplies the countable almost-everywhere quotient/factorization
primitive used by P-PRED-01: separate protocol factorizations are assembled
into one common full-measure set and one measurable product decoder.

The remaining generators do not supply that primitive:

- M-TC-01 assumes maps/defects are already given and transports equalities or
  quantitative certificates through them; it does not construct a common-null-
  set measurable decoder for a countable family.
- M-PE-01 is finite positive-operator/eigenvector calculus; it has no
  countable-a.e. measurable-family descent theorem.

The registered P-PRED-01 adapters supply kernel measurability, coordinate
evaluation, and the sigma-factor consequence once a common decoder is
available.  They do not provide `countableAEFamily_descend` itself.

P-INT-02 is **not** used as an ablation witness.  Its source-side
`StructuredQuotient.quotientResponse_mk` adapter already gives the canonical
factorization conjunct, and the minimal-refinement conjunct can be recovered
directly from the supplied separated factorization by the equality rewrites
exhibited in `StructuredQuotient.internal_refinement` and
`environment_refinement`.  Those operations are within the declared adapter
and rewriting surface.  Therefore deleting M-QD-01 does not honestly make
P-INT-02 unavailable, even though M-QD-01 remains its counted compression
derivation.

P-PRED-01 still loses its common-null-set measurable descent route.  Therefore
M-QD-01 remains nonredundant under the declared derivation system.

## 4. Ablation B — remove M-TC-01

Remaining counted core:

- M-QD-01
- M-PE-01

Broken generated mapping used as the nonredundancy witness:

- P-DYN-03

M-TC-01 supplies the generic multiplicative certificate recurrence used by the
P-DYN-03 compression derivation.  The registered source/domain adapters retain
finite-PMF common mass, the one-step TV-to-overlap estimate, the exact
TV/common-mass identity, and the product-to-sum inequality, but none of the
remaining counted generators supplies the multi-step product-survival
accumulation theorem.

The remaining generators do not supply that primitive:

- M-QD-01 proves quotient/factorization statements and has no product
  certificate recurrence.
- M-PE-01 proves consequences of positive left/right eigenrelations and has no
  path-coupling survival recurrence.

The other M-TC generated mappings remain correctly attributed to M-TC, but this
Gate-C audit does not need to assert that every one of them becomes unavailable
after deletion.  In particular, simple two-stage or commuting-factor conclusions
may admit direct reconstruction from already registered composition/transport
infrastructure and therefore are deliberately not used as nonredundancy
witnesses.

P-DYN-03 still loses the only registered route to the multi-step multiplicative
certificate recurrence without reintroducing the removed M-TC primitive or
calling the frozen source endpoint/full source recurrence.  Therefore M-TC-01
remains nonredundant under the declared derivation system.

## 5. Ablation C — remove M-PE-01

Remaining counted core:

- M-QD-01
- M-TC-01

Broken generated mapping used as the nonredundancy witness:

- P-EVO-04

M-PE-01 supplies the positive right-eigenstructure-to-martingale calculus used
by P-EVO-04: the Perron right eigenrelation is transported through the frozen
conditional-mean dynamics to the normalized reproductive-value martingale,
together with nonnegativity, integrability, and constant expectation.

The remaining generators do not supply that primitive:

- M-QD-01 concerns quotient/factorization universal properties and does not
  construct or exploit positive eigenvectors.
- M-TC-01 transports equalities/defect certificates and supplies finite-chain
  recurrences, but it does not turn conditional-mean Perron dynamics into a
  stochastic eigenvector martingale.

The concrete conditional-mean law, positivity, adaptedness, integrability,
initial state, and Perron eigenrelation remain admissible source assumptions.
No theorem in the remaining counted core yields the normalized martingale
bundle from those data.  P-QSD-02 remains correctly attributed to M-PE but is
not needed as a second ablation witness.

Therefore M-PE-01 is nonredundant under the declared derivation system.

## 6. Candidate schemas do not invalidate the ablation

M-BU-01 and M-OI-01 remain analysis-only candidates.  They have no counted
generic theorem surface and no counted generated mappings, so they are not
members of the declared derivation system used for Gate C.  Likewise, retained
P-QSD-04, P-EVO-03 and other retained rows may suggest future generalizations,
but Gate C does not silently promote them into replacement generators.

This is consistent with Mission Contract v1: the frozen core is minimal
relative to the formalized derivation system, while alternative future
presentations may still exist.

## 7. Gate C conclusion

All three counted generators are required by at least one final generated
mapping, and after deleting each one the remaining counted core plus registered
adapters lacks the mathematical primitive needed by at least one designated
generated ablation witness.  A generated mapping that remains reconstructible
through the pre-existing registered adapter surface is not counted as broken.

Therefore the final core

`{M-QD-01, M-TC-01, M-PE-01}`

is **nonredundant under the declared derivation system**.

This conclusion is deliberately scoped.  It is sufficient for Mission
Contract Gate C, but it is not an assertion of absolute logical independence
among all possible future axiomatizations.
