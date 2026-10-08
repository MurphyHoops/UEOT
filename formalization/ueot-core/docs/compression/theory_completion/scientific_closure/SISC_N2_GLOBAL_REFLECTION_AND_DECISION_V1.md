# UEOT Core N2 — Process, prediction, belief, and operational objecthood

**Local research decision.** 2026-10-09 (Asia/Taipei). Source branch `research/sisc-local-20261008`, frozen Core baseline `f744194dabdbb8632e69b1d9cbc1f0e347877571`.

**Status:** FINITE CONDITIONAL MATHEMATICS PROVED; GENERAL PHYSICAL OBJECTHOOD AND IDENTITY STILL OPEN. No changes to the 106/106 frozen theorem ledger, four counted Compression generators, or C7 independent-experiment status. No GitHub push.

## I. Global proof inventory and what the statements actually assert

The V4 manifest mechanically hashes and imports-checks **586** first-party Lean sources (104,769 source lines, 3,540 lexically declared theorem/lemma statements), of which 584 are reachable from public UEOT.lean. These are *not* 3,540 governed Core completion obligations; 106/106 remains the separate frozen theorem program. The two non-public-root files are Lake/package and audit entrypoints. Historical manifests V1/V2/V3 remain unchanged.

The proof structure now has five distinguishable types of statement:

| Layer | Already machine-checked | Additional assumption or unsolved bridge |
|---|---|---|
| Deterministic microstate prediction | All-future response equivalence is action-congruent; canonical minimal recursive quotient | Correct and complete intervention-output semantics; physical identity |
| Stochastic microstate Markov quotient | Unique normalized class kernel **iff** strong lumpability | Strong lumpability may fail even with equal full observed trace laws |
| Stochastic linear prediction | Finite-rank event-prefix invariant response space, rank ≤ microstate count | Minimal constructive basis, real-world calibration, positive state cone |
| Stochastic belief prediction | A supplied finite Bayes model yields normalized observation prediction, explicit conflict | Correct transition/emission model, observation timing |
| Causal object formation/persistence | SI-3 finite-channel formation coverage; SI-2/3 local gap uniqueness; C4 bounded realized continuation | Independently derive parents, boundary, viability, repair and external provenance |

These categories must never be collapsed into one untyped notion of `SameObject`.

## II. New positive mathematical result: distributional prediction automatically closes

Let K be a finite controlled stochastic kernel and r a declared *pre-transition* observable. Let `F_x(w)` be the controlled trace law of word w, and let b be a source weight function on X.

Define

`F_b(w) = Σ_x b(x) F_x(w)`

and for observed action-event (a,o),

`U_(a,o)(b)(y) = Σ_x b(x) 1_{r(x)=o} K_a(x,y)`.

**Commuting square, proved in Lean:**

`F_(U_(a,o)b)(w) = F_b((a,o)::w)` for all b,a,o,w.

The proof requires neither strong microstate lumpability nor an externally chosen object/parent transporter. It uses the actual microkernel transition and output interface and a finite-sum interchange. Therefore if `F_b=F_c` as entire future-word functions, then `F_(U b)=F_(U c)`. By the existing M-RS universal quotient theorem, the **reachable quotient of belief response functions has exactly one event update** compatible with U.

This is the correctly typed repair of the earlier false inference `microstate trace equality ⇒ Markov quotient of token classes`. It does **not** imply a Markov kernel on raw micro-token equivalence classes. The new carrier is **distributions/linear predictive states** rather than microscopic source-token labels.

**Evidence and zero-likelihood boundaries:** The update preserves nonnegative weights. Its total mass equals the one-event predicted probability. For strictly positive evidence, reweighting gives a nonnegative mass-one belief whose complete future prediction is the event-prefixed response divided by evidence. Zero evidence does not create a normalized posterior by fiat.

These are proved in `SISCStochasticPredictiveIntertwining.lean`, integrated via additive public-root import. The positive theorem is an exact formal integration of established probabilistic / predictive-state algebra, not mathematical novelty in its own right.

## III. New observation-time compatibility result

The old linear trace emits *before* action; Core P-REF-02 observationLaw emits *after* action. `SISCEmissionTiming` already proved they need not agree at the same clock index (two-state flip: 1 vs 0 for false output).

`SISCObservationOrderBridge.lean` now proves the missing **one-step time shift**:

`P_Bayes(o | δ_x,a) = Σ_y K_a(x,y) F_y([(dummyAction,o)])`.

Changing dummyAction leaves the last pre-action observation law unaffected. This reconciles the two models at the explicitly shifted index, without equating the unshifted laws. Full multi-step Bayesian filtering under post-action emission versus full pre-action trace words remains to be separately aligned and verified.

## IV. Independent exact-arithmetic falsification and repeatability

`evidence/sisc_belief_intertwining_exact_test.py` uses rational arithmetic, 10 source vectors (including all six pure tokens, mixtures and signed vectors), two output symbols and 127 possible future words through length six. **2,540 exact equalities** passed for update/prediction commutation, together with evidence, normalization, zero-evidence and different-but-predictively-equivalent token regression checks.

Prior stochastic N1 six-state negative control remains: six distinct tokens, five distinguishable observed trace classes, finite observation response matrix rank four under exact rational arithmetic, and two different micro-token transitions (probabilities 1 vs 0 to a destination predictive class) despite all-word observed trace agreement.

The finite-rational test is a *method check*, not external data or a replacement for Lean's all-word proof.

## V. The deeper structural relationship — precise, not speculative

**A.** Process-relative predictive information is the common mathematical skeleton. Two source states may be treated as equivalent only *relative to a fully declared observational and intervention protocol*.

**B.** The carrier matters. Deterministic token equivalence, stochastic strongly-lumpable token classes, an invariant linear response span, and normalized Bayesian beliefs are not interchangeable. Closure theorems must be proved for the correct carrier type and observation-time convention.

**C.** Predictive equivalence is not genealogy. Distinct physical objects can have identical future response functions. A persistent causal object additionally requires independent provenance, interaction/boundary semantics, maintained structure and exclusion or explicit representation of branching/merging histories.

**D.** Purpose is not a derived scalar consequence of prediction. The old C6 counterexample already proves that different evaluator objectives can reverse preference on the same registered resource/performance mechanism. GOD, GOA, Bellman, recurrence/QSD and autonomous repair are typed further obligations.

**E.** Finite tests may fail in the strongest sense: constant observations can agree while Markov class masses differ; empty observation protocols can make formation vacuous; correlated measurements require robust uncertainty management. The correct scientific result may be UNRESOLVED, not a forced identity.

## VI. Next coherent theorem: operationally identify candidates without presupposed transport

Given a source process x, a controlled transition kernel K, a causal provenance relation E(parent,candidate), a **finite independently registered** candidate universe C, and a calibrated family of candidate response laws R_c, form the auditable set

`Candidates(x,a,parent) = {c ∈ C : E(parent,c) ∧ ∀ observable j, |measured K-derived response(x,a,j) - R_c(j)| ≤ ε_j}`.

Prove a three-way *evidence-limited* result:

- one qualifying candidate + independently observed pairwise separation ⇒ uniquely identifiable **operational successor**;
- multiple qualifying candidates ⇒ ambiguous identity/lineage, not arbitrary tie-breaking;
- zero qualifying candidates ⇒ uncovered model, experimental conflict or inadequate candidate universe, not evidence that the object ceased to exist.

An independently calibrated margin must survive noise, registration completeness and intervention coverage. This path removes the externally supplied choice of `tp` in SI-3 for a **finite** registered candidate universe; it still cannot derive the causal relation E or real physical boundaries from prediction alone.

After that: time-varying stochastic formation, statistically certified provenance and candidate coverage, exact and approximate stochastic continuation bounds, geometric constraints, long-run viable repair, and external multi-party experiment.

## VII. Decision and reproducible gate

The SISC local gate asserts source anchoring, exact-head full Lean build, representative theorem axiom inspection, proof-escape scan, immutable historic inventories, numerical falsification, C7 audit evidence and existing Compression/Finalization governance regressions. It is self-review; no true author-separated independent audit has happened.

**Valid claim:** one further **mathematically checked and typed** process-to-predictive-state bridge has been integrated into UEOT. **Invalid claim:** complete physical unified theory, derived ontic identity, experimental discovery, autonomous object formation or settled GOD/GOA.

Preserve `LOCAL_FORMAL_PASS` (only after exact-head gate), `SCIENTIFIC_FINAL=HOLD`, `EXTERNAL_SUPPORT=UNVERIFIED`, `INDEPENDENT_REVIEW=REVIEW_PENDING`, `CLOUD_PUSH=HOLD`. No cloud activity until the locally authorized scientific program actually closes.
