# SISC: Structural Identity & Scientific Closure — Local Mission

Status: **ACTIVE, LOCAL-ONLY**. Started 2026-10-08. Do not push, open a PR,
or mutate `main` until each requested stage has been locally audited and the
entire agreed scope can pass the final scientific/evidence review.

## Source and compatibility contract

- Canonical start: `main@f744194dabdbb8632e69b1d9cbc1f0e347877571`.
- Working branch: `research/sisc-local-20261008`; remote `origin/main` is not
  a workspace. Existing unrelated untracked `.cos-test/`, `.lake/` and `.DS_Store`
  are intentionally untouched.
- Frozen Core v3: 106/106 FULL-GREEN, 4 counted generators. **No** counted
  promotions, modifications to frozen semantics, or alternate coverage ledger.
- Reuse C4 `C4FBT` and `C4SetValuedFBT`; former establishes the realized
  bound, latter assumes directed formation coverage. Reuse P8
  `LineageEvolution` but do **not** infer independently identified `SameObject`
  from its pre-supplied identity map.
- `LOCAL_COMPLETE` means proved/tested for a **declared limited subproblem**.
  It does not mean C4, C5, C6 or C7 scientific port `CLOSED`.
- C7: independent review remains `REVIEW_PENDING`, external/natural-system
  support remains `UNVERIFIED` unless new eligible evidence is produced.

## Stage gates — each stage gets its *own local commit*

| Stage | Required result | Failure or limit |
|---|---|---|
| SI-0 | canonical source, assumption graph, explicit claim/evidence scope | no frozen changes |
| SI-1 | noninjective realization and clone/lineage no-go, checked Lean | observational equivalence is not identity |
| SI-2 | *non-circular* unique operational successor with independently given causal edges and separation | no ontic identity without extra bridge |
| SI-3 | derive formation coverage from a concrete lower dynamics and independent quantitative bounds; compose existing C4 FBT | never supply coverage as a hidden premise |
| SI-4 | compatible finite paths, split/merge and lineage; finite error budgets | infinite measurable paths remain open without regularity |
| SI-5 | external independent system, preregistration, held-out validation and independent reproducibility | no real-world PASS from local constructed pilot |
| C5 | exact same-budget joint-2D spectral rejection; mechanism metrology separate | low rank does not identify Pi/Phi |
| C6 | one independently anchored mechanism to purpose bridge | control optimality is not discovered purpose |
| FINAL | exact-head build, proof/axiom review, provenance, independent audit and failure register | no push before entire local mission is honestly closed |

The stage table is a queue, not a claim that any future stage has been done.
Completion means stage-scoped mathematics + runnable verification + audit and
commit; any unfulfilled empirical or reviewer requirement stays pending.

## Mathematical target discipline

1. **No-go before sufficiency.** The C4 bound
   `dist (B1 p1) (td (B0 p0)) ≤ L * epsF + epsB` does not imply token equality,
   unique predecessor, or persistence of a specific ontic instance.
2. **Operational identity vs. lineage.** A unique admissible target inferred
   from independent causal provenance and response separation is an
   **operational successor certificate**, not `SameObject` by definition.
3. **Formation mechanisms.** SI-3 starts with a restricted finite stochastic
   response model; identify its lower process dynamics, permitted protocols,
   normalization, error budget and positive/negative examples. Generic C4
   directed coverage remains an assumption *outside* that model.
4. **Finite vs. infinite paths.** A sequence of locally certified edges does not
   imply globally unique history if branching/merging or protocol drift is
   admitted; never hide a selector in an `exists` hypothesis.
5. **False and unresolved outcomes.** Each new substantive claim needs an
   explicit example, counterexample, and relevant UNRESOLVED outcome.

## Repository and commit policy

Additive files reside under
`UEOT/V3/Compression/TheoryCompletion/ScientificClosure/` and this folder's
`docs/.../scientific_closure/` documents. Modify a common import root only
after its new leaf modules have compiled. Each gate is one or more commits,
with a **distinct final stage commit**, targeted build evidence, and separate
scope/assumption/no-go audit. Do not add generated `.lake` artefacts or
unrelated tool session data to Git. Never rebase or reset another worker's work.

Before any later remote action: revisit branch and remote SHAs; verify the
whole local sequence; review `git diff main...HEAD`; run the project governance
and full `lake build UEOT`; obtain independent review and external experiment
evidence wherever demanded; only then propose publication.
