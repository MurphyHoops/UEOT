# UEOT Core Compression Formalization — Mission Contract v1

## 0. Purpose

This document defines the scientific completion contract for the post-106
compression mission. It answers **what must be true before the mission may be
called complete**. Operational procedures live in `COMPRESSION_OPERATIONS.md`;
counted facts live in `COMPRESSION_LEDGER.yaml`.

The frozen Core v3 source proof baseline remains **106/106 FULL-GREEN**.
Compression does not reopen, weaken, renumber, or rewrite any frozen P-ID.

The mission asks a different question:

> What smaller, explicit, machine-verified generating architecture explains the
> 106 source theorems, and which domain-specific or boundary structures remain
> irreducible after honest compression?

## 1. Scientific objective

The mission is complete only when all 106 frozen P-IDs have been analyzed,
semantically classified, and given a final audited disposition; every claimed
cross-theorem compression is witnessed in Lean; the retained generating core
has passed a documented ablation audit; and the final repository/ledger/CI
state is closed and reproducible.

The target is **not** the smallest-looking theory. The target is the smallest
honest architecture supported by the frozen source and machine evidence.

No fixed number of final generators is predeclared. A kernel of 9 honest
generators is preferable to 4 generators obtained by hiding assumptions,
regularity, domain machinery, or no-go boundaries.

## 2. Three compression questions must remain separate

1. **Proof-dependency compression** — what dominates the actual Lean proof DAG?
2. **Semantic/schema compression** — which P-IDs instantiate one abstract law?
3. **Scientific-primitive compression** — what concepts remain irreducible?

Evidence in one layer does not automatically settle the others.

## 3. Two-axis classification

Do not conflate derivability with scientific role.

### 3.1 Derivation status

During research, a P-ID may be unresolved, partially rederived, fully
Lean-rederived, or finally resolved.

A final resolved P-ID receives exactly one primary disposition:

- `generated` — the full frozen source-facing claim is recovered from one or
  more counted meta-generators through explicit Lean wrapper/specialization
  theorems;
- `retained_adapter` — domain-specific mathematics remains necessary and is
  deliberately retained rather than hidden inside a universal generator;
- `retained_boundary` — the theorem is retained primarily because it states a
  scope limit, obstruction, no-go result, identifiability limit, or other
  boundary that prevents an invalid universalization.

Secondary scientific role tags may still be recorded separately. The primary
disposition is an accounting device, not a claim that mathematical roles are
ontologically disjoint.

### 3.2 Why final dispositions are explicit

Final counts are derived from per-P-ID ledger entries. They must never be typed
as free-standing summary numbers. At completion:

`final dispositions = 106` and `unresolved = 0`.

## 4. What counts as generated

Similarity, shared notation, or a human classification is insufficient.

A P-ID may receive final disposition `generated` only when:

1. the frozen source statement and canonical Lean endpoint are identified;
2. the relevant M-ID generic theorem is integrated and counted;
3. an explicit compression-namespace wrapper/specialization exists;
4. assumption relation is audited and is source-faithful: exactly the frozen
   assumptions or genuinely weaker assumptions; stronger-assumption surrogates do
   not count as full rederivations;
5. conclusion relation is **exact** for the source-facing claim;
6. the mapping has completed feature, integration, main, and ledger gates;
7. ledger witness theorem names resolve under Lean.

A partial theorem, stronger-assumption surrogate, weaker conclusion, or
set-level result standing in for a measurable/kernel result is not generated.

This rule intentionally makes false compression more expensive than honest
retention.

## 5. What counts as retained

`retained_adapter` and `retained_boundary` are not failure states.

They are valid final scientific results when the audit records:

- the exact source theorem retained;
- why the current generating core does not recover it without hiding a genuine
  assumption or changing semantic scope;
- the standard/domain mathematics responsible for the residual structure;
- whether the retained result is a candidate for a future, more general
  generator;
- explicit audit-evidence references sufficient to recover the reasoning and
  source/Lean identity without relying on a prior chat.

Retained classifications must contain an explicit rationale and evidence. “Did not manage
to compress” is not a sufficient rationale.

Existing Core v3 Lean proofs remain the proof evidence for retained source
theorems; the compression project should not duplicate those proofs merely to
increase activity.

## 6. Minimal generating core

The final minimal core is a set of counted M-IDs selected after coverage and
ablation analysis.

“Minimal” in this project means:

> nonredundant under the declared source semantics, registered adapters,
> compression wrappers, and derivation system used by this formalization.

It does **not** automatically mean an absolutely unique logical basis among all
possible equivalent axiom systems. Alternative equivalent minimal
presentations may exist.

A generator belongs to the frozen minimal core only if its ablation audit shows
that it is not derivable from the retained alternatives under the declared
derivation system and that removing it loses a recorded class of final
generated mappings. The frozen core must exactly account for every generator
named by final `generated` dispositions; a counted dependency may not sit
outside the advertised core.

If a generator is derivable from the others, it may remain useful as a lemma
but must not be counted as a primitive member of the final minimal core.

## 7. Ablation requirements

Before the minimal core is frozen, every proposed final generator must have an
ablation record answering:

- what mappings fail if the generator is removed;
- whether the generator is derivable from remaining generators plus registered
  adapters;
- the exact remaining-core M-ID set after removal;
- a typed non-derivability status, explicit assumptions, and recoverable audit
  evidence under the declared derivation system;
- the concrete frozen P-IDs whose generated derivations break under removal;
- which assumptions are essential to that conclusion;
- whether the result is exact, relative, or currently limited by formalized
  infrastructure.

The permitted final ablation conclusion for a minimal-core member is
`nonredundant_under_declared_derivation_system`.

Absolute logical independence is not required unless separately proved. The
project must state the strength of the minimality claim rather than overclaim
it.

## 8. Efficiency rules

Scientific rigor must not create avoidable proof work.

- Existing 106 source proofs are reused for retained P-IDs.
- New Lean work is required for generic generators and claimed generated
  mappings, not for re-proving unchanged retained theorems.
- A mapping is promoted only after it has a plausible multi-theorem reuse case;
  speculative schemas may remain analysis-only until useful.
- Summary metrics are derived automatically from detailed ledger evidence.
- One rich 106-row matrix is preferred over multiple overlapping status files.
- Failed or rejected compression hypotheses are recorded when scientifically
  informative, then closed rather than repeatedly retried without new evidence.

The optimization target is information gained per proof/governance cost, not
maximum theorem count per week.

## 9. Completion stages

The mission has four meaningful completion gates.

### Gate A — Audit complete
- 106/106 P-IDs have explicit `audit_records`;
- every audit record is tied to the frozen theorem-index source title/line;
- every audited Lean identity resolves under generated Lean `#check`;
- 106/106 have substantive analysis summaries and schema classification
  rationale.

The analyzed/schema summary counts are derived from these records; they are not
independently editable evidence.

### Gate B — Resolution complete
- 106/106 have final per-P-ID dispositions;
- unresolved P-IDs = 0;
- all `generated` dispositions point to counted exact Lean mappings;
- all retained dispositions contain explicit scientific rationale.

### Gate C — Core frozen
- final minimal-core M-ID list is frozen;
- every final M-ID is counted;
- ablation is complete for every final M-ID;
- minimality claim is explicitly scoped and no final M-ID has unresolved
  redundancy.

### Gate D — Repository final
- finalization ledger is integrated on `main`;
- Core Lean and Compression Guard are green on the final closure lifecycle;
- no active compression PR remains;
- no temporary compression/governance branch remains;
- Issue #146 records the final canonical main and evidence.

## 10. Formal Definition of Done

The scientific state may enter `ready_for_finalization` only if:

- `analyzed_pids = 106`;
- `schema_classified_pids = 106`;
- `final_disposition_pids = 106`;
- `unresolved_pids = 0`;
- final disposition counts are derived from 106 unique P-ID entries;
- every generated disposition has a counted exact Lean mapping;
- every retained disposition has a nonempty audit rationale;
- minimal core state is `frozen`;
- ablation state is `complete`;
- minimality claim is
  `nonredundant_under_declared_derivation_system`;
- every final-core generator is a counted generator with a completed,
  nonredundant ablation record.

The ledger may enter `final` only through the final closure lifecycle defined
in `COMPRESSION_OPERATIONS.md`. The recorded candidate-main SHA, Core Lean
run, Compression Guard run and closure PR must be verified against live GitHub
state; identifiers that merely have the right textual shape do not count as
evidence. A green CI run by itself is never sufficient to declare scientific
completion.

## 11. Core v4 gate

Core v4 may be drafted only after Gate C is satisfied and the 106/106
resolution is stable enough that the compressed architecture is no longer a
speculative grouping.

A legitimate v4 should have the form:

`Minimal Kernel + Derived Theorems + Domain Adapters + Boundary Theorems`

and must preserve a traceable map back to all frozen Core v3 P-IDs.

## 12. Current state

At Mission Contract v1 adoption, the infrastructure is green but the scientific
mission is early:

- 3/106 P-IDs analyzed;
- 3/106 schema-classified;
- 2/106 fully Lean-rederived;
- 0 final dispositions;
- 0 counted compressed P-IDs;
- minimal core not frozen;
- ablation not started.

Therefore the compression mission is **active**, not near completion.

## 13. Post-final scientific extensions

Gate D freezes a reproducible scientific checkpoint relative to the registered
theorem surface available at that time. A later formally integrated theorem
route may justify rerunning Gate C if it changes derivability, generated
coverage, or minimal-core membership.

Such a later result does not invalidate or rewrite the earlier checkpoint.
Instead:

- the earlier FINAL evidence remains immutable historical evidence;
- the enlarged theorem surface must satisfy the same exact-mapping and scoped
  ablation standards;
- every old minimal-core member must be rechecked for redundancy with the new
  generator retained;
- every new generator must receive its own deletion witness;
- live mission state returns to `ready_for_finalization`;
- Gate D must be closed again through the normal candidate-main / closure-PR /
  resulting-main lifecycle before a new FINAL state is announced.

This rule keeps the minimal-core claim corrigible under new formalized evidence
without permitting silent post-hoc mutation of a closed scientific record.
