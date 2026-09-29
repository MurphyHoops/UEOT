# UEOT Core Compression — Gate C Ablation Audit

This document records the scoped nonredundancy audit required by Mission
Contract v1 before the compression core can be frozen.

It does **not** claim model-theoretic independence or a uniquely privileged
axiomatization.  The audited claim is exactly:

`nonredundant_under_declared_derivation_system`.

## 1. Declared derivation system

The Gate C ablation audit is relative to the formalized compression system
already integrated on canonical main after Gate B.

Allowed ingredients after ablating one candidate core generator are:

1. the canonical theorems of the remaining **counted** M-IDs;
2. the already integrated compression wrappers/specializations attached to
   those remaining M-IDs;
3. registered source/domain adapters needed to instantiate a generic theorem
   or discharge its domain hypotheses;
4. ordinary composition, specialization, equality rewriting, finite algebra,
   measure-theoretic transport, and Mathlib infrastructure already present in
   the frozen formalization.

“Registered adapters” does **not** mean the entire frozen source namespace.
It means domain-local facts already recorded as adapters or already used to
instantiate/discharge hypotheses of the counted compression mappings. A
lower-level source lemma that would itself reconstruct the mathematical core of
the ablated M-ID is not an admissible replacement unless it had been separately
registered and promoted before the deletion experiment.

The following are **not** allowed as a way to defeat an ablation:

- calling a theorem from the ablated generator namespace;
- calling the frozen source endpoint of a P-ID whose generated derivation is
  being tested;
- promoting an analysis-only candidate such as M-BU-01 or M-OI-01 during the
  same ablation;
- hiding the missing mathematical primitive inside a newly invented adapter or
  stronger assumption.

Thus “not derivable” means that the current formalized remaining core plus
registered adapters contains no source-faithful route to the affected generated
P-ID without reintroducing the removed primitive.  This is the relative
minimality notion explicitly permitted by Mission Contract v1.

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

Broken generated mappings:

- P-API-01
- P-ID-01
- P-ID-02
- P-DYN-03
- P-DYN-04

M-TC-01 supplies the generic certificate-recursion primitive:

- two-stage quantitative transport;
- exact commuting transport;
- additive finite-chain accumulation;
- weighted/discrete-Gronwall accumulation;
- multiplicative certificate accumulation.

The remaining generators do not supply this structure:

- M-QD-01 proves quotient/factorization statements, but has no theorem that
  accumulates real-valued local defects through a chain or product recurrence.
- M-PE-01 proves consequences of positive left/right eigenrelations, but has no
  generic defect metric, local-error recursion, weighted chain, or
  multiplicative survival theorem.

The five generated source-facing wrappers instantiate these M-TC theorems
directly.  Their source/domain adapters provide TV contraction, triangle
inequalities, measurable pushforwards, Lipschitz bounds, PMF overlap, and
related local hypotheses; those adapters do not replace the missing generic
recurrence.

Therefore M-TC-01 is nonredundant under the declared derivation system.

## 5. Ablation C — remove M-PE-01

Remaining counted core:

- M-QD-01
- M-TC-01

Broken generated mappings:

- P-QSD-02
- P-EVO-04

M-PE-01 supplies finite positive-eigenstructure calculus: normalized positive
left/right eigenvectors, Doob-transform normalization and invariant weights,
and the stochastic right-eigenvector martingale construction.

The remaining generators do not supply that primitive:

- M-QD-01 concerns quotient/factorization universal properties and does not
  construct or exploit positive eigenvectors.
- M-TC-01 transports already supplied equalities/defect certificates and does
  not derive eigenrelations, h-transforms, invariant eigenweights, or
  eigenvector martingales.

The QSD wrapper is built from `qsdDoob_bundle` (plus the substochastic scale
adapter where required).  The evolutionary wrapper is built from
`stochasticRightEigen_bundle`.  Domain/source adapters provide the concrete
matrix, killed-kernel, or conditional-mean semantics, but they do not replace
the positive-eigenstructure theorem.

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
