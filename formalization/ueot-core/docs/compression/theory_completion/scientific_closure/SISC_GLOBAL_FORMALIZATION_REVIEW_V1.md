# UEOT global Lean formalization re-audit / intuitive core extraction

Date: 2026-10-08. Source branch: `research/sisc-local-20261008`.
Baseline: frozen main `f744194dabdbb8632e69b1d9cbc1f0e347877571`.
Scope: every **first-party** Lean source under
`formalization/ueot-core/UEOT/`, the public package root, Lake entrypoint and
standalone first-party audit `.lean` files. This is a **complete source-byte,
declaration and dependency inventory**, combined with a **focused semantic
audit of the mathematical bridges** most pertinent to the requested core.
It is **not** a line-by-line independent reproof of thousands of declarations
or any source under externally vendored Mathlib.

## I. Reproducible whole-source evidence

Run `python3 formalization/ueot-core/docs/compression/theory_completion/scientific_closure/scripts/audit_sisc_global_inventory.py`
from repository root to regenerate `SISC_GLOBAL_LEAN_INVENTORY_V1.json`.
The generator reads and SHA256-hashes every included first-party `.lean` file
and records each module's imports, declaration counts, line counts and public
root reachability, followed by a recursive import cycle/missing-import check.

| Inventory measure | Exact local result |
|---|---:|
| First-party Lean source files inspected | **574** |
| Source lines read | **103159** |
| Lexically declared theorems plus lemmas | **3486** |
| Modules reachable from public `UEOT.lean` root | **572** |
| Local import cycles | **0** |
| Missing local UEOT imports | **0** |
| Unreached source modules | **2**: `lakefile` and `scripts.CompressionAxiomAudit` |
| Explicit `axiom` and `opaque` declaration lines seen by this scanner | **0** |

The `3486` lexical theorem/lemma declarations include auxiliary claims and
post-Core extensions; they MUST NOT be confused with the project-governed
**106 counted Core v3 theorems**. Source scanning alone does not exclude
undetected code-generation/macro surfaces or imported axioms; the existing
Lean kernel build and `#print axioms` are separate checks.

| Architectural group | Sources | Lines | Theorem/lemma declarations |
|---|---:|---:|---:|
| V3 Core, mathematical physics and associated theory | 297 | 53953 | 1926 |
| Compression other than Objecthood and Theory Completion | 93 | 20875 | 706 |
| Objecthood | 88 | 16351 | 481 |
| Theory Completion incl. Scientific Closure/SISC | 85 | 11115 | 322 |
| Legacy Core | 7 | 545 | 51 |
| Public roots, package and proof audit entrypoints | 4 | 320 | 0 |

The full per-file inventory is machine-readable and contains each individual
source path and digest. The groups above do not assert scientific closure.

## II. The structural connections behind the 106-theorem landscape

**A. Evolution/process:** `DynamicsKernel`, `ProcessInterface`, stochastic
CTMC and diffusion, selection/Perron, path KL and path-law interfaces all
require a typed **world-process update**. They do not establish that any
particular subcarrier is a self-maintaining object.

**B. Prediction/information:** `PredictionDependent`, `PredictionUpdate`,
`InformationPredictiveFactorization` and canonical future-law results define
when a representation retains information relevant to future protocols.
Information equality is weaker than token/cause identity.

**C. Quotient/universality:** `Compression.QuotientDescent`,
`RecursiveSufficientState`, `QuotientGauge`, exact control quotient and scale
intertwining share a factorization/commutation diagram. The universal property
is genuine, but descent of a *measurable stochastic kernel* is stronger than
set-level descent and cannot follow merely from naming a quotient.

**D. Object formation/persistence:** endogenous formation/parent-binding,
constitutive persistence, repair, semantic-identity and inverse-objecthood
modules contain additional causal, protocol and viability obligations. The
predictive quotient cannot infer them without independent bridge conditions.

**E. Purpose/control:** P1/P2 teleology, control Bellman/GOD and long-run GOA
connect one objective representation to closed-loop dynamics, but the value
contract must be supplied or inferred independently. Different objectives
can rank the same physical process oppositely (existing C6 no-go).

**F. Long-time asymptotics:** mixing, QSD, survival, spectral stability and
recurrent structure describe *outcomes of dynamics under restrictive
assumptions*. No common word `GOA` licenses identifying QSD, stationary law,
recurrent classes and reward maximizers.

## III. The intuition tested, without smuggling conclusions

**Intuition:** forget precisely those distinctions between microscopic
histories that *cannot affect any permitted future response*; retain all
distinctions that can. This induces the **coarsest exact prediction-preserving
and action-recursive quotient**. The particular state representation may
change labels while preserving the mathematical evolution diagram.

`SISCFutureResponseCore.lean` constructs the quotient from controlled
transition plus present observable alone, instead of postulating a summary
with closure. It proves automatic action congruence, existence/uniqueness of
quotient updates, universal minimality and relabeling uniqueness using
existing M-QD/M-RS/Gauge abstractions.

`SISCFiniteFutureProbes.lean` derives finite distinguishability for finite
source states, with a chosen word per ordered candidate pair. At most
`|X|²` tests are needed *in existence*, with NO uniform witness-length or
runtime guarantee. This is a mathematical finite-protocol bridge to C3/P4,
not a polynomial constructive algorithm.

Two no-go tests show why this is **predictive** rather than metaphysical:

- Same present response need not imply same future response (there can be
  latent action-dependent differences).
- Even equality of **all allowed future responses** may merge distinct world
  tokens if the experiment protocol is non-separating.

These are exact negative controls; any claim of universal physical identity
from response equivalence alone would be false.

## IV. Candidate core theorem (scoped scientific statement)

> Given a deterministic controlled process and an output map, equality of
> responses over every finite intervention word defines a canonical minimal
> recursive predictive state. Its induced dynamics exist uniquely on the
> reachable quotient; any other exact recursive sufficient representation
> uniquely factors onto this state. For finite source state spaces, a finite
> family of future intervention words represents this entire equivalence.

This is a known **Myhill–Nerode / behavioral observational equivalence**
principle adapted to UEOT's typed process/prediction/quotient architecture.
It is **not** a claim of originating this established principle; its value
lies in making the UEOT interfaces share a proved minimal common skeleton.

## V. What this cannot unify automatically

Predictive minimality is not a sufficient condition for autonomous objecthood.
External physical ancestry, intervention-valid candidates, counterfactual
provenance, interaction boundaries, endogenous persistence, repairability,
real viability, purpose identification and long-run GOA remain **separate
typed evidence gates**. Without these, the strongest credible result is a
canonical *behavioral state*, not one unique physical object token.

Continuous-time/random processes require kernel-level congruence and
measurable descent; noisy empirical identification needs preregistered
simultaneous confidence sets and candidate-universe coverage. Physical
relevance and generality therefore remain OPEN.

## VI. Next falsifiable tests

1. Extend the source signature from exact deterministic response to
   **interventional stochastic future laws**, proving kernel congruence,
   measurability and valid process quotient under explicit conditions.
2. Make finite probe extraction constructive and bound worst-case word
   length/runtime; test against exact automata partition refinement and
   counterexamples with long delayed distinguishing words.
3. Add independently measured provenance, nonempty interventions and
   candidate coverage to distinguish behavioral classes from genealogical
   object classes; force `UNRESOLVED` for indistinguishable clones.
4. Connect the canonical predictive quotient to object-boundary,
   persistence and repair certificates on the **same physical source**;
   do not equate the notion of objective with one preferred scalar reward.
5. Run a genuinely independent external experiment and prior-art review.

The appropriate claim is **one derived minimal mathematical backbone, not
the completed unified theory of all physical objects**. Preserve 106/106
counted Core, four compression generators, C7 review status and no-cloud-push.
