# UEOT Core v3 — global source audit and derived core theorem: decision record

Decision date: 2026-10-08. Local-only branch:
`research/sisc-local-20261008`. Canonical source baseline:
`f744194dabdbb8632e69b1d9cbc1f0e347877571`.
Disposition: **LOCAL FORMAL CORE CANDIDATE / FULL SCIENTIFIC CLOSURE HOLD**.
No push, no PR, no change to frozen 106/106 theorem ledger.

## 1. What was globally reviewed

The independent-style reproducible inventory reads all **574 first-party
Lean files**, **103159** source lines, **3486** lexical theorem/lemma
declarations, computes a SHA-256 for each source and follows all local
UEOT import edges. **572** modules are reachable from `UEOT.lean`, with no
missing imports and no cycles; the two other files are standalone Lake/audit
entrypoints. This is a *complete mechanical source/dependency pass* plus
focused scientific semantic review of key common architectures, **not**
thousands of independent theorem-by-theorem external peer reviews.

Proof correctness is separately tested via the full Lean kernel build,
selected theorem `#print axioms`, and regression/governance tests.

## 2. A minimal mathematical backbone emerged

Old source: M-QD universal fibre descent, M-RS recursive sufficiency, exact
quotient gauge, canonical prediction, intervention dynamics, P4 inverse
identifiability and SISC formation/lineage all depend in different ways on
**which distinctions must survive evolution**.

New in `SISCFutureResponseCore.lean` is a direct source construction:

- input: actual deterministic controlled process `step` and response `read`;
- generate `F(x)(w) = read(runInterventions(step,x,w))` for every finite
  registered intervention word `w`;
- take only the **reachable** image of `F`, not a fictitious ambient state;
- derive, rather than assume, that `F` is closed under input-action updates;
- prove that this update is **unique**, and that `F` is the *coarsest*
  current-observation-preserving recursive sufficient state;
- any exactly equivalent state representation is unique **up to relabeling**.

`SISCFiniteFutureProbes.lean` proves that for finite source X, a finite
family of **at most |X|²** intervention words suffices to distinguish all
future-response classes. The test family is selected *noncomputably*; no
worst-case word-length/runtime theorem has been established in Lean.

## 3. Two mandatory no-go boundaries

Two process states can have identical **present** observations but different
**future** observations; thus naive instantaneous observational quotienting
may break dynamical closure.

Different physical source tokens can have identical responses for **every
admissible future experiment**; thus the canonical quotient is a behavioral
prediction state, not an ontic `SameObject` predicate. Causal provenance and
autonomous persistence cannot be inferred from the quotient alone.

## 4. Triangulated evidence

- Lean: deterministic process minimality, auto-congruence, gauge equivalence,
  finite-protocol existence and no-go witnesses proved and publicly imported.
- Independent software method: exhaustive **5898** binary-output/two-action
  deterministic processes up to three states, plus **640** deterministic
  larger-state samples, pass finite partition refinement consistency.
- External literature: Myhill–Nerode, computational mechanics causal states,
  predictive state representations are substantial existing prior art.
  See `SISC_CORE_PRIOR_ART_CHECK_V1.md`; no originality claim is permitted
  for minimal predictive quotients alone.
- First-party import/declaration inventory in
  `SISC_GLOBAL_LEAN_INVENTORY_V1.json` with reproducible regeneration script.

## 5. The central UEOT scientific gap, now sharper

The answer to *what is the most uniform backbone?* is **closed prediction
under evolution**, expressed as a canonical quotient/universal factorization.
This unifies representation, action-recursive state, observable equivalence,
information sufficiency and a finite-system test existence principle.

The answer to *what is the full physical object?* is **not** the quotient
alone. Necessary independent bridges remain:

1. causal-origin and external intervention evidence;
2. nonempty/separating measurement protocols and complete candidate coverage;
3. structure formation, boundary delimitation and constitutive persistence;
4. physical repair/viability and closed-loop autonomy;
5. independently registered teleological objectives and the related GOD/GOA
   specialization under honest stochastic/asymptotic assumptions.

The experimentally novel proposition would be a **noncircular theorem and
measurement procedure** deriving these additional objecthood certificates
from actual lower-level controlled process data, together with negative
controls. Neither the old frozen theorem collection nor the current
deterministic process core proves that universal physical claim.

## 6. Next theorem target (N1)

For a *finite stochastic* controlled kernel K on microscopic histories and
registered response experiments, construct its predictive response-law
equivalence. Prove that transition probabilities into equivalence classes
depend only on the class and action **if and only if** a concrete
intervention-invariance condition holds. Derive the unique quotient Markov
kernel, then provide explicit counterexamples when lumpability, candidate
coverage or measurable selection fails. This is the most direct next bridge
from deterministic process semantics toward physically applicable UEOT.

**Do not substitute** pointwise probability predictions, aggregate matching,
or a chosen candidate transport for that stochastic-kernel theorem.

## 7. Publication policy

No scientific C4/C7/identity status promotion, no external-review PASS and
no push to origin merely because the local Lean build and audits pass.
Current dispositions: `real_world_support=UNVERIFIED`,
`independent_review=REVIEW_PENDING`, `SISC_SCIENTIFIC_FINAL=HOLD`,
`CLOUD_PUSH=HOLD`.

Run the reproducible gate from repository root:

```sh
python3 -O formalization/ueot-core/docs/compression/theory_completion/scientific_closure/scripts/audit_sisc_local.py
```
